module Repl

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
import Eval

%access public export

--------------
-- Run
-- Repl
--------------

trapError : Context m => LispError -> ST m String []
trapError err = pure $ show err

runIOThrows : Context m => ST m String [] -> ST m String []
runIOThrows action = catch action trapError

readOrThrow : Context m => Parser a -> String -> ST m a []
readOrThrow parser input =
  case parse parser input of
    ParseError (err, _) => throw $ ParseError err
    ParseSuccess [(val, _)] => pure val
    _ => throw $ Default "Read error"

readExpr : Context m => String -> ST m LispVal []
readExpr = readOrThrow parseExpr

readExprList : Context m => String -> ST m (List LispVal) []
readExprList = readOrThrow $ (skipMany space) >> (endBy parseExpr (skipMany space))

evalString : Context m => EnvRef LispVal -> String -> ST m String []
evalString envRef expr =
    do parsed <- readExpr expr
       evaled <- eval envRef parsed
       pure $ show evaled

evalAndPrint : Context m => EnvRef LispVal -> String -> ST m () []
evalAndPrint envRef expr = evalString envRef expr >>= putStrLn

evalExprList : Context m => EnvRef LispVal -> String -> ST m (List LispVal) []
evalExprList envRef expr =
    do parsed <- readExprList expr
       evaled <- traverse' (eval envRef) parsed
       pure $ evaled
    where
        traverse' : Context m => (LispVal -> ST m LispVal []) -> List LispVal -> ST m (List LispVal) []
        traverse' f [] = pure []
        traverse' f (x::xs) = do v <- f x
                                 vs <- traverse' f xs
                                 pure (v :: vs)

evalExprListAndPrint : Context m => EnvRef LispVal -> String -> ST m () []
evalExprListAndPrint envRef expr =
    do evalExprList envRef expr
       pure ()

-- runOne : Context m => List String -> ST m () []
-- runOne args =
--     do
--         envRef <- primitiveBindings >>=
--                 flip bindVars [("args", LispList $ map LispString $ drop 1 args)]
--         -- _ <- loadStdLib env
--         case args of
--             (x::xs) => do
--                 result <- eval envRef (LispList [Atom "load-print", LispString x])
--                 putStrLn $ show' result
--             _ => throw $ Default "TODO: MAKE ERROR"
--     where
--         printable : LispVal -> Bool
--         printable LispVoid = False
--         printable _ = True
--         showValNewline : LispVal -> String
--         showValNewline LispVoid = ""
--         showValNewline v = showVal v
--         unwordsList' : List LispVal -> String
--         unwordsList' = unlines . map showValNewline . filter printable
--         show' : LispVal -> String
--         show' (LispList contents) = unwordsList' contents
--         show' _ = ""

runRepl : Context m => ST m () []
runRepl {m} =
    do
        envRef <- primitiveBindings
        repl envRef
    where
    repl : EnvRef LispVal -> ST m () []
    repl envRef =
        do
            minput <- getStr
            case minput of
                "quit" => pure ()
                input => do
                    evalAndPrint envRef input
                    repl envRef
