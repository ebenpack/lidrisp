module Lists

import Control.ST
import Control.ST.Exception
import DataTypes
import Util

%access public export

car : PrimitiveLispFunc
car [LispDottedList (x::_) _] = pure x
car [LispList []] = Left $ Default "Unexpected error in car"
car [LispList (x::_)] = pure x
car [badArg] = Left $ Default $ "car expected pair, found " ++ show badArg
car badArgList =
  Left $ NumArgs (MinMax 1 1) (cast $ length badArgList) badArgList

cdr : PrimitiveLispFunc
cdr [LispDottedList [_] a] = pure a
cdr [LispDottedList (_::xs) a] = pure $ LispDottedList xs a
cdr [LispList []] = Left $ Default "cdr on empty list" -- TODO: FIX ERROR MSG
cdr [LispList (_::[])] = pure $ LispList []
cdr [LispList (_::a)] = pure $ LispList a
cdr [badArg] = Left $ Default $ "cdr expected pair, found " ++ show badArg
cdr badArgList =
  Left $ NumArgs (MinMax 1 1) (cast $ length badArgList) badArgList

cons : PrimitiveLispFunc
cons [a, LispList b] = pure $ LispList (a :: b)
cons [a, LispDottedList b c] = pure $ LispDottedList (a :: b) c
cons [a, b] = pure $ LispDottedList [a] b
cons badArgList =
  Left $ NumArgs (MinMax 2 2) (cast $ length badArgList) badArgList

isPair : PrimitiveLispFunc
isPair [LispList []] = pure $ LispBool False
isPair [LispList _] = pure $ LispBool True
isPair [LispDottedList _ _] = pure $ LispBool True
isPair _ = pure $ LispBool False

empty : PrimitiveLispFunc
empty [LispList []] = pure $ LispBool True
empty [LispList _] = pure $ LispBool False
empty _ = Left $ Default "Type error: `empty` called on non-list"

accessors : List (String, PrimitiveLispFunc)
accessors =
  map (\a => ("c" ++ pack a ++ "r", makeAccessor a)) caaaars
  where
    caaaars : List (List Char)
    caaaars = (replicateM 2 ['a', 'd']) ++ (replicateM 3 ['a', 'd']) ++ (replicateM 4 ['a', 'd'])
    comp : PrimitiveLispFunc -> PrimitiveLispFunc -> PrimitiveLispFunc
    comp a b c = do
        d <- a c
        b [d]
    identity : PrimitiveLispFunc
    identity [n] = pure n
    identity a = pure $ LispList a
    makeAccessor : List Char -> PrimitiveLispFunc
    makeAccessor =
        foldr (\chr, acc =>
            if chr == 'a'
                then comp acc car
                else comp acc cdr)
            identity

list : PrimitiveLispFunc
list xs = pure $ LispList xs

listPrimitives : List (String, PrimitiveLispFunc)
listPrimitives =
  [ ("pair?", isPair)
  , ("car", car)
  , ("cdr", cdr)
  , ("cons", cons)
  , ("empty?", empty)
  , ("list", list)
  ] ++
  accessors
