module Strings

import DataTypes
import Control.ST
import Control.ST.Exception
import DataTypes
import Util
import Data.String.Extra

%access public export

unpackStr : LispVal -> ThrowsError String
unpackStr (LispString s) = pure s
unpackStr notString = Left $ TypeMismatch "string" notString

strBoolBinop' : (LispVal -> ThrowsError String) -> (String -> String -> Bool) -> PrimitiveLispFunc
strBoolBinop' unpacker = boolBinop unpacker

strBoolBinop : (String -> String -> Bool) -> PrimitiveLispFunc
strBoolBinop = strBoolBinop' unpackStr

isString : PrimitiveLispFunc
isString [LispString _] = pure $ LispBool True
isString _ = pure $ LispBool False

makeString : PrimitiveLispFunc
makeString [n@(LispInteger _)] = makeString [n, LispCharacter $ chr 0]
makeString [LispInteger n, LispCharacter c] =
  pure $ LispString $ pack $ replicate (cast n) c
makeString _ = Left $ Default "Invalid arguments to `make-string`"

strLen : PrimitiveLispFunc
strLen [LispString s] = pure $ LispInteger $ cast $ length s
strLen _ = Left $ Default "Invalid arguments to `string-length`"

strAppend : PrimitiveLispFunc
strAppend [] = pure $ LispString ""
strAppend [s@(LispString _)] = pure s
strAppend ((LispString s1)::(LispString s2)::xs) = strAppend (LispString (s1 ++ s2) :: xs)
strAppend _ = Left $ Default "Invalid arguments to `string-append`"

stringToSymbol : PrimitiveLispFunc
stringToSymbol [LispString s] = pure $ LispAtom s
stringToSymbol [arg] = Left $ TypeMismatch "string" arg
stringToSymbol args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

stringRef : PrimitiveLispFunc
stringRef [LispString s, LispInteger n] =
    let idx = fromIntegerNat n
    in case index idx s of
            Just c => pure $ LispCharacter c
            Nothing => Left $ Default "string-ref: index is out of range"
stringRef [v, LispInteger n] = Left $ TypeMismatch "string" v 
stringRef [LispString s, v] = Left $ TypeMismatch "integer" v
stringRef args = Left $ NumArgs (MinMax 2 2) (cast $ length args) args

substring : PrimitiveLispFunc
substring [LispString s, LispInteger m, LispInteger n] =
    let start = fromIntegerNat m
        end = fromIntegerNat n
        len = fromIntegerNat (n - m)
    in if start >= 0 && end <= length s
            then pure $ LispString $ substr start len s
            else Left $ Default "substring: ending index is out of range"

strPrimitives : List (String, PrimitiveLispFunc)
strPrimitives =
  [ ("string=?", strBoolBinop (==))
  , ("string<?", strBoolBinop (<))
  , ("string>?", strBoolBinop (>))
  , ("string<=?", strBoolBinop (<=))
  , ("string>=?", strBoolBinop (>=))
  , ("string?", isString)
  , ("string->symbol", stringToSymbol)
  , ("string-ref", stringRef)
  , ("make-string", makeString)
  , ("string-length", strLen)
  , ("string-append", strAppend)
  , ("substring", substring)
  ]
