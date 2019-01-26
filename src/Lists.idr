module Lists

import Control.ST
import Control.ST.Exception
import DataTypes
import Util

%access public export

car : List LispVal -> ThrowsError LispVal
car [LispDottedList (x::_) _] = pure x
car [LispList []] = Left $ Default "Unexpected error in car"
car [LispList (x::_)] = pure x
car [badArg] = Left $ Default $ "car expected pair, found " ++ show badArg
car badArgList =
  Left $ NumArgs (MinMax 1 1) (cast $ length badArgList) badArgList

cdr : List LispVal -> ThrowsError LispVal
cdr [LispDottedList [_] a] = pure a
cdr [LispDottedList (_::xs) a] = pure $ LispDottedList xs a
cdr [LispList []] = Left $ Default "cdr on empty list" -- TODO: FIX ERROR MSG
cdr [LispList (_::[])] = pure $ LispList []
cdr [LispList (_::a)] = pure $ LispList a
cdr [badArg] = Left $ Default $ "cdr expected pair, found " ++ show badArg
cdr badArgList =
  Left $ NumArgs (MinMax 1 1) (cast $ length badArgList) badArgList

cons : List LispVal -> ThrowsError LispVal
cons [a, LispList b] = pure $ LispList (a :: b)
cons [a, LispDottedList b c] = pure $ LispDottedList (a :: b) c
cons [a, b] = pure $ LispDottedList [a] b
cons badArgList =
  Left $ NumArgs (MinMax 2 2) (cast $ length badArgList) badArgList

isPair : List LispVal -> ThrowsError LispVal
isPair [LispList _] = pure $ LispBool True
isPair [LispDottedList _ _] = pure $ LispBool True
isPair _ = pure $ LispBool False

empty : List LispVal -> ThrowsError LispVal
empty [LispList []] = pure $ LispBool True
empty [LispList _] = pure $ LispBool False
empty _ = Left $ Default "Type error: `empty` called on non-list"

accessors : List (String, (List LispVal -> ThrowsError LispVal))
accessors =
  map (\a => ("c" ++ pack a ++ "r", makeAccessor a)) caaaars
  where
    caaaars : List (List Char)
    caaaars = (replicateM 2 ['a', 'd']) ++ (replicateM 3 ['a', 'd']) ++ (replicateM 4 ['a', 'd'])
    comp : (List LispVal -> ThrowsError LispVal) -> (List LispVal -> ThrowsError LispVal) -> (List LispVal -> ThrowsError LispVal)
    comp a b c = do
        d <- a c
        b [d]
    identity : List LispVal -> ThrowsError LispVal
    identity [n] = pure n
    identity a = pure $ LispList a
    makeAccessor : List Char -> (List LispVal -> ThrowsError LispVal)
    makeAccessor =
        foldr (\chr, acc =>
            if chr == 'a'
                then comp acc car
                else comp acc cdr)
            identity

listPrimitives : List (String, (List LispVal -> ThrowsError LispVal))
listPrimitives =
  [ ("pair?", isPair)
  , ("car", car)
  , ("cdr", cdr)
  , ("cons", cons)
  , ("empty?", empty)
  ] ++
  accessors
