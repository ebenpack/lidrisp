module Util

import DataTypes
import Environment
import Control.ST
import Control.ST.Exception
import Control.IOExcept
import Control.Catchable
import Data.IORef
import Data.SortedMap

%access public export

jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

infixl 1 =<<
(=<<) : Monad m => (a -> m b) -> m a -> m b
m =<< k = k >>= m

replicateM : (Applicative m) => Int -> m a -> m (List a)
replicateM cnt0 f = loop cnt0
    where
        loop cnt =
            if cnt <= 0
                then pure []
                else liftA2 (::) f (loop (cnt - 1))

foldl1M : Monad m => (a -> a -> m a) -> List a -> m a
foldl1M f (x::xs) = foldlM f x xs

logBase : Double -> Double -> Double
logBase x y = log y / log x

infixr 5 ~&&
(~&&) : Lazy Bool -> Lazy Bool -> Bool
a ~&& b = Force a && b

infixr 4 ~||
(~||) : Lazy Bool -> Lazy Bool -> Bool
a ~|| b = Force a || b

round : Double -> Integer
round n =
    let
        signum = if n > 0 then 1 else if n < 0 then -1 else 0
        frac = if n > 0 then n - floor n else negate (n - ceiling n)
        op = if signum == 1 then
                (if frac <= 0.5 then floor else ceiling)
             else
                (if frac <= 0.5 then ceiling else floor)
    in
        cast $ op n

boolBinop :
     (LispVal -> ThrowsError a)
  -> (a -> a -> Bool)
  -> List LispVal
  -> ThrowsError LispVal
boolBinop unpacker op args =
    case (index' 0 args, index' 1 args) of
        (Just arg1, Just arg2) =>
            do
                left <- unpacker arg1
                right <- unpacker arg2
                pure $ LispBool $ left `op` right
        _ => Left $ NumArgs (MinMax 2 2) (cast $ length args) args

Catchable (IOExcept' FFI_JS err) err where
    catch (IOM prog) h = IOM (do p' <- prog
                                 case p' of
                                      Left e => let IOM he = h e in he
                                      Right val => pure (Right val))
    throw = ioe_fail

Exception (IOExcept' FFI_JS err) err where
    throw err = lift (ioe_fail err)
    catch prog f = do io_res <- runAs prog
                      res <- lift (catch (do r <- io_res
                                             pure (Right r))
                                         (\err => pure (Left err)))
                      either (\err => f err) (\ok => pure ok) res

ConsoleIO (IO' FFI_JS) where
    putStr str = lift (Interactive.putStrLn' str)
    getStr = lift Interactive.getLine'
    putChar c = lift (Interactive.putStrLn' $ singleton c)
    getChar = lift (do
            str <- Interactive.getLine'
            pure $ 'a')

ConsoleIO (IOExcept' FFI_JS err) where
    putStr str = lift (ioe_lift (Interactive.putStrLn' str))
    getStr = lift (ioe_lift Interactive.getLine')

    putChar c = lift (ioe_lift (Interactive.putStrLn' $ singleton c))
    getChar = lift (ioe_lift (do
          str <- Interactive.getLine'
          pure $ 'a'))

private
showEnv' : (Show a, HasReference ffi) => EnvRef a -> IO' ffi String
showEnv' e = printEnv e
  where
  printBnd : Bindings a -> IO' ffi String
  printBnd (MkBindings bns) = bndHelp $ toList bns
      where
          bndHelp : List (String, IORef a) -> IO' ffi String
          bndHelp [] = pure ""
          bndHelp ((name,ref)::xs) = do
              bnds <- readIORef' ref
              let s = name ++ ": " ++ show bnds
              ss <- bndHelp xs
              pure (s ++ "," ++ ss)
  printEnv : EnvRef a -> IO' ffi String
  printEnv (Global bref) = do
      bnd <- readIORef' bref
      s <- printBnd bnd
      pure $ "Global<" ++ s ++ ">"
  printEnv (Frame bref env) = do
      bnd <- readIORef' bref
      s <- printBnd bnd
      pp <- printEnv env
      pure $ "Frame<" ++ s ++ "," ++ pp ++ ">"

private
initEnv' : HasReference ffi => List (String, a) -> IO' ffi (EnvRef a)
initEnv' l =
  do
      bindingsList <- traverse addBinding l
      let bindings = MkBindings (fromList bindingsList)
      bindingsRef <- newIORef' bindings
      pure $ Global bindingsRef

private
getVar' : HasReference ffi => EnvRef a -> String -> IO' ffi (Maybe a)
getVar' env name = getHelper env
    where
        getHelper (Global bindingsRef) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => pure Nothing
                Just ref => map Just (readIORef' ref)

        getHelper (Frame bindingsRef env) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => getHelper env
                Just ref => map Just (readIORef' ref)

private
setVar' : HasReference ffi => EnvRef a -> String -> a -> IO' ffi Bool
setVar' env name val = setHelper env
    where
        setHelper (Global bindingsRef) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => pure False
                Just ref => do writeIORef' ref val
                               pure True

        setHelper (Frame bindingsRef env) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => setHelper env
                Just ref => do writeIORef' ref val
                               pure True

private
defineVar' : HasReference ffi => EnvRef a -> String -> a -> IO' ffi ()
defineVar' env name val = defineHelper env
    where
        defineHelper (Global bindingsRef) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => do ref <- newIORef' val
                              modifyIORef' bindingsRef (insertVal name ref)
                Just ref => writeIORef' ref val

        defineHelper (Frame bindingsRef env) = do
            (MkBindings bindings) <- readIORef' bindingsRef
            case lookup name bindings of
                Nothing => do ref <- newIORef' val
                              modifyIORef' bindingsRef (insertVal name ref)
                Just ref => writeIORef' ref val

        insertVal : String -> IORef a -> Bindings a -> Bindings a
        insertVal k v (MkBindings bindings) = MkBindings $ insert k v bindings

private
bindVars' : HasReference ffi => EnvRef a -> List (String, a) -> IO' ffi (EnvRef a)
bindVars' env vars = bindHelper
    where
        bindHelper =
            do let bindingsRef = getBindingsRef env
               bindingsList <- traverse addBinding vars
               let bindings = MkBindings (fromList bindingsList)
               bindingsRef' <- newIORef' bindings
               pure (Frame bindingsRef' env)

HasReference ffi => Envir a (IO' ffi) where
    showEnv e = lift $ showEnv' e
    initEnv l = lift $ initEnv' l
    getVar env name = lift $ getVar' env name
    setVar env name val = lift $ setVar' env name val
    defineVar env name val = lift $ defineVar' env name val
    bindVars env vars = lift $ bindVars' env vars

HasReference ffi => Envir a (IOExcept' ffi err) where
    showEnv e = lift $ ioe_lift $ showEnv' e
    initEnv l = lift $ ioe_lift $ initEnv' l
    getVar env name = lift $ ioe_lift $ getVar' env name
    setVar env name val = lift $ ioe_lift $ setVar' env name val
    defineVar env name val = lift $ ioe_lift $ defineVar' env name val
    bindVars env vars = lift $ ioe_lift $ bindVars' env vars
