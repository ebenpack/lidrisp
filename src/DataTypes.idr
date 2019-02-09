module DataTypes

import ParserCombinator
import Ratio
import Data.Complex
import Control.ST.Exception
import Control.ST
import Environment

%access public export

data Arity =
    Min Int
  | MinMax Int Int

mutual
    PrimitiveLispFunc : Type
    PrimitiveLispFunc = List LispVal -> ThrowsError LispVal

    ThrowsError : Type -> Type
    ThrowsError = Either LispError

    codata LispVal =
        LispVector Int (List LispVal) -- TODO: Array?
      | LispAtom String
      | LispList (List LispVal)
      | LispDottedList (List LispVal) LispVal
      | LispInteger Integer
      | LispFloat Double
      | LispComplex (Complex Double)
      | LispRational Rational
      | LispString String
      | LispCharacter Char
      | LispBool Bool
      | LispPrimitiveFunc String PrimitiveLispFunc
      | LispFunc String (List String) (Maybe String) (List LispVal) (EnvRef LispVal)
      | LispVoid

    data LispError = NumArgs Arity Integer (List LispVal)
        | TypeMismatch String LispVal
        | BadSpecialForm String LispVal
        | NotFunction String String
        | UnboundVar String String
        | ParseError String
        | Default String

mutual
  listEq : List LispVal -> List LispVal -> Bool
  listEq [] [] = True
  listEq (x::xs) (y::ys) = if x == y then listEq xs ys else False
  listEq _ _ = False

  Eq LispVal where
    (LispVector n a) == (LispVector m b) = if n == m then False else listEq a b
    (LispAtom a) == (LispAtom b) = a == b
    (LispList a) == (LispList b) = listEq a b
    (LispDottedList xs v1) == (LispDottedList ys v2) = if v1 == v2 then False else listEq xs ys
    (LispInteger n) == (LispInteger m) = n == m
    (LispFloat n) == (LispFloat m) = n == m
    (LispComplex n) == (LispComplex m) = n == m
    (LispRational n) == (LispRational m) = n == m
    (LispString a) == (LispString b) = a == b
    (LispCharacter a) == (LispCharacter b) = a == b
    (LispBool a) == (LispBool b) = a == b
    LispVoid == LispVoid = True
    -- LispPrimitiveFunc String PrimitiveLispFunc
    -- LispFunc String (List String) (Maybe String) (List LispVal) (EnvRef LispVal)
    x == y = False

interface (Exception m LispError, ConsoleIO m, Envir LispVal m) =>
          Context (m : Type -> Type) where

(Exception m LispError, ConsoleIO m, Envir LispVal m) => Context m where

mutual
    unwordsList : List LispVal -> String
    unwordsList = unwords . map showVal

    showVal : LispVal -> String
    showVal (LispString contents) = "\"" ++ contents ++ "\""
    showVal (LispAtom name') = name'
    showVal (LispInteger contents) = show contents
    showVal (LispFloat contents) = show contents
    showVal (LispComplex c) = show c
    showVal (LispRational (n .% d)) = show n++ "/" ++ show d
    showVal (LispBool True) = "#t"
    showVal (LispBool False) = "#f"
    showVal (LispList contents) = "(" ++ unwordsList contents ++ ")"
    showVal (LispVector n contents) = "#(" ++ unwordsList contents ++ ")"
    showVal (LispDottedList h t) = "(" ++ unwordsList h ++ " . " ++ showVal t ++ ")"
    showVal (LispFunc name _ _ _ _) = "#<procedure:" ++ name ++ ">"
    showVal LispVoid = ""
    showVal _ = ""

Show LispVal where
    show = showVal

showError : LispError -> String
showError (Default message) = message
showError (UnboundVar message varname) = message ++ ": " ++ varname
showError (BadSpecialForm message form) = message ++ ": " ++ (show form)
showError (NotFunction message func) = message ++ ": " ++ (show func)
showError (NumArgs expected found args) =
  let error' =
        case expected of
          Min min' =>
            "arity mismatch;\nthe expected number of arguments does not match the given number" ++
            "\nexpected: at least " ++ show min' ++ "\ngiven: " ++ show found
          MinMax min' max' =>
            "arity mismatch;\nthe expected number of arguments does not match the given number" ++
            "\nexpected: " ++
            (if min' == max'
               then show min'
               else "between " ++ show min' ++ " and " ++ show max') ++
            "\ngiven: " ++ show found
      argsError =
        case args of
          [] => ""
          a => "\narguments:\n" ++ unwordsList a
  in error' ++ argsError
showError (ParseError parseErr) = "Parse error at " ++ show parseErr
showError (TypeMismatch expected found) =
  "Invalid type: expected " ++ expected ++ ", found " ++ (show found)

Show LispError where
    show = showError
