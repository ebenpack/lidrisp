module Eval

import Control.ST
import Control.ST.Exception
import DataTypes
import Util
import Lists
import Numbers
import Strings
import Vector
import Data.Complex
import Parse
import ParserCombinator
import Data.Complex
import Primitives
import Data.SortedMap
import Environment
import Data.IORef
-- import Data.Ratio
-- import Data.Maybe


-- import Control.Monad.Except
-- import Data.Array
-- import Data.Complex
-- import Data.IORef
-- import Data.Maybe (isNothing)
-- import Data.Ratio
-- import DataTypes
--        (Arity(..), Env, EnvFrame(..), IOPrimitiveFunc, IOThrowsError,
--         LispError(..), LispVal(..), PrimitiveFunc, ThrowsError,
--         extractValue, showVal, trapError)
-- import Parse
-- import ParserCombinators
-- import Paths_hascheme (getDataFileName)
-- import Primitives (eqv, ioPrimitives, primitives)
-- import System.Console.Haskeline
-- import System.IO
-- import Util (liftThrows)
-- import Vector (outOfBoundsError)
--
%access public export
--------------
-- Eval
--------------
makeFunc : String -> Maybe String -> EnvRef LispVal -> List LispVal -> List LispVal -> LispVal
makeFunc name varargs envRef params body = LispFunc name (map showVal params) varargs body envRef

makeNormalFunc : String -> EnvRef LispVal -> List LispVal -> List LispVal -> LispVal
makeNormalFunc name = makeFunc name Nothing

makeVarArgs : String -> LispVal -> EnvRef LispVal -> List LispVal -> List LispVal -> LispVal
makeVarArgs name varargs = makeFunc name (Just $ showVal varargs)

getHeads : Context m => List LispVal -> ST m LispVal []
getHeads [] = pure $ LispList []
getHeads (LispList (x::_)::ys) = do
  LispList result <- getHeads ys
  pure $ LispList (x :: result)
getHeads _ = throw $ Default "Unexpected error (getHeads)"

getTails : Context m => List LispVal -> ST m LispVal []
getTails [] = pure $ LispList []
getTails (LispList [_, xs]::ys) = do
  LispList result <- getTails ys
  pure $ LispList (xs :: result)
getTails _ = throw $ Default "Unexpected error (getTails)"

ensureAtom : Context m => LispVal -> ST m LispVal []
ensureAtom n@(LispAtom _) = pure n
ensureAtom _ = throw $ Default "Type error"

ensureAtoms : Context m => List LispVal -> ST m LispVal []
ensureAtoms [] = pure LispVoid
ensureAtoms (x::xs) = do
  ensureAtom x
  ensureAtoms xs

extractVar : LispVal -> String
extractVar (LispAtom atom) = atom


liftThrows : Context m => ThrowsError a -> ST m a []
liftThrows (Left err) = throw err
liftThrows (Right val) = pure val

mutual
    evalArgs : Context m => EnvRef LispVal -> List LispVal -> ST m (List LispVal) []
    evalArgs _ [] = pure []
    evalArgs {m} envRef (x::xs) = do
        arg <- eval envRef x
        args <- evalArgs envRef xs
        pure $ (arg :: args)

    evalList : Context m => EnvRef LispVal -> List LispVal -> ST m LispVal []
    evalList _ [] = pure LispVoid
    evalList {m} envRef [a] = eval envRef a
    evalList {m} envRef (y::ys) = do
        eval envRef y
        evalList envRef ys

    --------------
    -- Apply
    --------------
    apply' : Context m => LispVal -> List LispVal -> ST m (LispVal) []
    -- apply (LispPrimitiveFunc _ func) args = func args
    apply' {m} (LispPrimitiveFunc _ func) args = liftThrows $ func args
    apply' {m} (LispFunc _ params varargs body closure) args =
      if length params /= length args && isNothing varargs
        then throw $ NumArgs (Min $ cast $ length params) (cast $ length args) args
        else do env' <- bindVars closure $ zip params args ++ varargs'
                (x::xs) <- evalBody env' body
                pure $ last (x::xs)

      where
        remainingArgs : List LispVal
        remainingArgs = drop (length params) args
        evalBody : Context m => EnvRef LispVal -> List LispVal -> ST m (List LispVal) []
        evalBody env [] = pure []
        evalBody env (x::xs) = do v <- eval env x
                                  vs <- evalBody env xs
                                  pure (v :: vs)
        varargs' : List (String, LispVal)
        varargs' =
          case varargs of
            Just argName => [(argName, LispList $ remainingArgs)]
            Nothing => []
    -- apply' {m} (LispFunc _ params varargs body closure) args =
    --     if length params /= length args && isNothing varargs
    --     then throw $ NumArgs (Min $ cast $ length params) (cast $ length args) args
    --     else do (x::xs) <- evalBody !localEnv body
    --             pure $ last (x :: xs)
    --     where
    --         traverse' : Context m => (LispVal -> ST m LispVal []) -> List LispVal -> ST m (List LispVal) []
    --         traverse' f [] = pure []
    --         traverse' f (x::xs) = do v <- f x
    --                                  vs <- traverse' f xs
    --                                  pure (v :: vs)
    --         -- remainingArgs = drop (length params) args
    --         varArgs : List (String, LispVal)
    --         varArgs = let remaining = drop (length params) args in
    --                 case varargs of
    --                      Nothing  => []
    --                      Just arg => [(arg, LispList remaining)]
    --         localEnv : Context m => ST m (EnvRef LispVal) []
    --         localEnv = bindVars closure $ zip params args ++ varArgs
    --         evalBody : Context m => EnvRef LispVal -> List LispVal -> ST m (List LispVal) []
    --         evalBody env = traverse' (eval env)


-- HERE!

        -- num = toInteger . length
        -- evalBody env = fmap last $ mapM (eval env) body'
    -- apply' {m} (LispFunc _ params varargs body closure) args
    --       = if length params /= length args && varargs == Nothing
    --            then throw $ NumArgs (Min $ cast $ length params) (cast $ length args) args
    --            else do (x :: xs) <- evalBody !localEnv body
    --                    pure $ last (x :: xs)
    --       where optArg : List (String, LispVal)
    --             optArg
    --               = let remaining = drop (length params) args in
    --                     case varargs of
    --                          Nothing  => []
    --                          Just arg => [(arg, LispList remaining)]
    --             localEnv : Context m => ST m (EnvRef LispVal) []
    --             localEnv = bindVars closure $ zip params args ++ optArg
    --             evalBody : Context m => EnvRef LispVal -> List LispVal -> ST m (List LispVal) []
    --             evalBody env = traverseE (eval env)
    -- apply' (LispIOFunc _ func) args = func args
    apply' f _ = throw $ Default $
        "application: not a procedure; " ++
        "expected a procedure that can be applied to arguments; given: " ++ show f

    -- applyProc :: IOPrimitiveFunc
    -- applyProc [func, List args] = apply func args
    -- applyProc (func:args) = apply func args
    -- applyProc _ = throw $ Default "applyProc error"
    --
    -- readProc :: IOPrimitiveFunc
    -- readProc [] = readProc [Port stdin]
    -- readProc [Port port] = (liftIO $ hGetLine port) >>= liftThrows . readExpr
    -- readProc _ = throw $ Default "readProc error"
    --
    -- load :: String -> IOThrowsError [LispVal]
    -- load filename = (liftIO $ readFile filename) >>= liftThrows . readExprList
    --
    -- readAll :: IOPrimitiveFunc
    -- readAll [String filename] = fmap List $ load filename
    -- readAll _ = throw $ Default "readAll error"

    eval : Context m => EnvRef LispVal -> LispVal -> ST m LispVal []
    eval {m} _ val@LispVoid = pure val
    eval {m} _ val@(LispString _) = pure val
    eval {m} _ val@(LispCharacter _) = pure val
    eval {m} _ val@(LispInteger _) = pure val
    eval {m} _ val@(LispVector _ _) = pure val
    -- eval {m} _ (LispRational val) =
    --   if denominator val == 1
    --     then pure $ LispInteger $ numerator val
    --     else pure $ LispRational val
    eval {m} _ val@(LispFloat _) = pure val
    eval {m} _ (LispComplex val) =
      if imagPart val == 0
        then pure $ LispFloat $ realPart val
        else pure $ LispComplex val
    eval {m} _ val@(LispBool _) = pure val
    eval {m} _ (LispList [LispAtom "quote", val]) = pure val
    eval {m} envRef (LispList [LispAtom "if", pred', conseq, alt]) =
        do
            result <- eval envRef pred'
            case result of
                LispBool False => eval envRef alt
                _ => eval envRef conseq
    eval {m} envRef (LispList ((LispAtom "cond")::xs)) = evalCond xs
        -- TODO: [test-expr => proc-expr]
      where
        evalCond : List LispVal -> ST m LispVal []
        evalCond [] = pure LispVoid
        evalCond [LispList (LispAtom "else"::xs')] =
            evalList envRef xs'
        evalCond (LispList (LispAtom "else"::_)::_) =
          throw $ Default "cond: bad syntax (`else` clause must be last)"
        evalCond ((LispList (pred'::conseqs))::xs') = do
          result <- eval envRef pred'
          case result of
            LispBool False => evalCond xs'
            _ =>
              case conseqs of
                [] => pure result
                _ => evalList envRef conseqs
        evalCond a = throw $ Default (show a)
    eval {m} envRef (LispList ((LispAtom "case")::(key::clauses))) =
        do
            result <- eval envRef key
            evalClauses result clauses
        where
            inList : List LispVal -> ST m LispVal []
            inList [_, LispList []] = pure $ LispBool False
            inList [key', LispList (x::xs)] =
                do
                    eq <- liftThrows $ eqv [x, key']
                    case eq of
                        LispBool True => pure $ LispBool True
                        _ => inList [key, LispList xs]
            inList _ = throw $ Default "case: bad syntax"
            evalClauses : LispVal -> List LispVal -> ST m LispVal []
            evalClauses _ [LispList []] = pure LispVoid
            evalClauses key' (LispList (datum::exprs)::rest) =
                do
                    match <- call $ inList [key', datum]
                    case match of
                        LispBool True => evalList envRef exprs
                        LispBool False => evalClauses key' rest
                        _ => throw $ Default "case: bad syntax"
            evalClauses _ _ = throw $ Default "case: bad syntax"
    eval {m} _ (LispList ((LispAtom "case")::_)) =
      throw $ Default "case: bad syntax in: (case)"
    eval {m} envRef (LispList [LispAtom "set!", LispAtom var, form]) =
        do val <- eval envRef form
           setVar envRef var val
           pure LispVoid
    eval {m} envRef (LispList [LispAtom "define", LispAtom var, form]) =
        do val <- eval envRef form
           defineVar envRef var val
           pure LispVoid
    eval {m} envRef (LispList (LispAtom "define"::LispList (LispAtom var::params)::body)) =
        do defineVar envRef var (makeNormalFunc var envRef params body)
           pure LispVoid
    eval {m} envRef (LispList (LispAtom "define"::LispDottedList (LispAtom var::params) varargs::body)) =
        do let val = makeVarArgs var varargs envRef params body
           defineVar envRef var val
           pure LispVoid
    eval {m} envRef (LispList (LispAtom "lambda"::LispList params::body)) = do
        s <- showEnv envRef
        pure $ makeNormalFunc "λ" envRef params body
    eval {m} envRef (LispList (LispAtom "lambda"::varargs@(LispAtom _)::body)) =
        pure $ makeVarArgs "λ" varargs envRef [] body
    eval {m} envRef (LispList (LispAtom "lambda"::LispDottedList params varargs::body)) =
        pure $ makeVarArgs "λ" varargs envRef params body
    eval {m} envRef (LispList (LispAtom "let"::LispList pairs::body)) = do
            LispList atoms <- getHeads pairs
            ensureAtoms atoms
            LispList vals <- getTails pairs
            args <- evalArgs envRef vals
            envRef' <- bindVars envRef (zipWith (\a, b => (extractVar a, b)) atoms args)
            evalList envRef' body
    eval {m} envRef (LispList (LispAtom "let*"::LispList pairs::body)) = do
            LispList atoms <- getHeads pairs
            ensureAtoms atoms
            LispList vals <- getTails pairs
            buildEnv envRef atoms vals
            evalList envRef body
        where
        buildEnv : EnvRef LispVal -> List LispVal -> List LispVal -> ST m () []
        buildEnv env [] [] = pure ()
        buildEnv env (atomH::atomT) (valH::valT) = do
            val <- eval env valH
            defineVar env (extractVar atomH) val
            buildEnv env atomT valT
        buildEnv _ _ _ = throw $ Default "let*: bad syntax"
    eval {m} envRef (LispList (LispAtom "letrec"::LispList pairs::body)) = do
            LispList atoms <- getHeads pairs
            ensureAtoms atoms
            LispList vals <- getTails pairs
            envRef' <- bindVars envRef []
            buildEnv envRef' atoms
            args <- evalArgs envRef' vals
            setRec envRef' (zipWith (\a, b => (extractVar a, b)) atoms args)
            evalList envRef' body
        where
            buildEnv : EnvRef LispVal -> List LispVal -> ST m () []
            buildEnv env [] = pure ()
            buildEnv env (atomH::atomT) = do
                defineVar env (extractVar atomH) LispVoid
                buildEnv env atomT
            buildEnv _ _ = throw $ Default "let*: bad syntax"
            setRec : EnvRef LispVal -> List (String, LispVal) -> ST m () []
            setRec env [] = pure ()
            setRec env ((n,v)::xs) = do
                setVar env n v
                setRec env xs
    eval {m} envRef (LispList [LispAtom "or", expr1, expr2]) = do
        result <- eval envRef expr1
        case result of
            LispBool True => pure result
            _ => eval envRef expr2
    eval {m} envRef (LispList [LispAtom "and", expr1, expr2]) = do
        result <- eval envRef expr1
        case result of
            LispBool False => pure result
            _ => eval envRef expr2
    eval {m} envRef (LispList [LispAtom "print", expr1]) = do
        -- TODO: REMOVE
        result <- eval envRef expr1
        putStr $ show result ++ "\n"
        pure LispVoid
    -- eval envRef (LispList [LispAtom "load", String filename]) = do
    --   f <- load filename
    --   _ <- traverse_ (eval env) f
    --   pure LispVoid
    -- eval envRef (List [Atom "load-print", String filename]) =
    --   load filename >>= fmap List . mapM (eval env)
    -- eval envRef (List (Atom "vector-set!":args)) =
    --   case args of
    --     [Atom var, Integer n, v] -> do
    --       Vector vec <- getVar envRef var
    --       if n < (fromIntegral $ length vec)
    --         then setVar envRef var $ Vector $ vec // [(n, v)]
    --         else throw $ outOfBoundsError "vector-ref" n vec
    --     [a, b, c] ->
    --       throw $ TypeMismatch "vector, integer, integer" $ List [a, b, c]
    --     a -> throw $ NumArgs (MinMax 3 3) (length args) a
    eval envRef (LispList (function::args)) = do
        s <- showEnv envRef
        func <- eval envRef function
        argVals <- evalArgs envRef args
        results <- apply' func argVals
        pure $ results
    eval {m} envRef (LispAtom name) = do
        var <- getVar envRef name
        case var of
            Nothing => throw $ Default $ "Unknown atom: " ++ name
            Just var' => pure var'
    eval _ badForm = throw $ BadSpecialForm "Unrecognized special form" badForm

--------------
-- Env
-- Bindings
-- Primitives
--------------
nullEnv : Context m => ST m (EnvRef LispVal) []
nullEnv = initEnv []

primitiveBindings : Context m => ST m (EnvRef LispVal) []
primitiveBindings {m} = initEnv $ map (makeFunc' LispPrimitiveFunc) primitives
    where
        makeFunc' : (String -> (List LispVal -> a) -> LispVal) -> (String, (List LispVal -> a)) -> (String, LispVal)
        makeFunc' constr (var, func) = (var, constr var func)


-- | PrimitiveFunc String
--                   PrimitiveFunc
--   | Func { name :: String
--          , params :: [String]
--          , vararg :: (Maybe String)
--          , body :: [LispVal]
--          , closure :: Env }


-- -- loadStdLib :: Env -> IO Env
-- -- loadStdLib envRef = do
-- --   filename <- liftIO $ getDataFileName "lib/stdlib.scm"
-- --   _ <- evalString envRef $ "(load \"" ++ filename ++ "\")"
-- --   pure env
-- --
