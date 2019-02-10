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
empty [args] = Left $ TypeMismatch "list" args
empty args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

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

isList : PrimitiveLispFunc
isList [LispList x] = pure $ LispBool True
isList _ = pure $ LispBool False

listLength : PrimitiveLispFunc
listLength [LispList xs] = pure $ LispInteger (cast $ length xs)
listLength [args] = Left $ TypeMismatch "list" args
listLength args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

listAppend : PrimitiveLispFunc
listAppend [LispList xs, LispList ys] = pure $ LispList (xs++ ys)
listAppend xs = helper [] xs 
  where
    helper : List LispVal -> PrimitiveLispFunc
    helper acc [] = pure $ LispList acc
    helper acc [LispDottedList ls v] = pure $ LispDottedList (acc ++ ls) v
    helper [] [v] = pure $ v
    helper acc [v] = pure $ LispDottedList acc v
    helper acc ((LispList xs)::rest) = helper (acc ++ xs) rest
    helper _ (x::xs) = Left $ TypeMismatch "list" x
    helper _ _ = Left $ Default "Unknown error in append"

listReverse : PrimitiveLispFunc
listReverse [] = Left $ NumArgs (MinMax 1 1) 0 []
listReverse [LispList xs] = pure $ LispList (reverse xs)
listReverse [arg] = Left $ TypeMismatch "list" arg
listReverse args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

listMember : PrimitiveLispFunc
listMember [needle, LispList xs] = helper xs
    where
      helper : PrimitiveLispFunc
      helper [] = pure $ LispBool False
      helper (x::xs) = 
        if x == needle 
          then pure $ LispList (x::xs)
          else helper xs
listMember [_, arg] = Left $ TypeMismatch "list" arg
listMember args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

listPrimitives : List (String, PrimitiveLispFunc)
listPrimitives =
  [ ("pair?", isPair)
  , ("car", car)
  , ("cdr", cdr)
  , ("cons", cons)
  , ("empty?", empty)
  , ("list", list)
  , ("list?", isList)
  , ("length", listLength)
  , ("append", listAppend)
  , ("reverse", listReverse)
  , ("member", listMember)
  ] ++
  accessors
