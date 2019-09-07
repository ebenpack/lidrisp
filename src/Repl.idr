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

readOrThrow : (Show a, Context m) => Parser a -> String -> ST m a []
readOrThrow parser input =
  case parse parser input of
    ParseError (MkError err) _ pos => throw $ LispParseError err pos
    ParseSuccess val s pos => pure val

readExprList : Context m => String -> ST m (List LispVal) []
readExprList = readOrThrow $ (many' go) <* eof
    where
    go = do
        skipMany space
        e <- parseExpr
        skipMany space
        pure e

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
