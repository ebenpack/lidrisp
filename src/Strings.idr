module Strings

import DataTypes
import Control.ST
import Control.ST.Exception
import DataTypes
import Util

%access public export

unpackStr : LispVal -> ThrowsError String
unpackStr (LispString s) = pure s
unpackStr notString = Left $ TypeMismatch "string" notString

strBoolBinop' : (LispVal -> ThrowsError String) -> (String -> String -> Bool) -> List LispVal -> ThrowsError LispVal
strBoolBinop' unpacker = boolBinop unpacker

strBoolBinop : (String -> String -> Bool) -> List LispVal -> ThrowsError LispVal
strBoolBinop = strBoolBinop' unpackStr

isString : List LispVal -> ThrowsError LispVal
isString [LispString _] = pure $ LispBool True
isString _ = pure $ LispBool False

makeString : List LispVal -> ThrowsError LispVal
makeString [n@(LispInteger _)] = makeString [n, LispCharacter $ chr 0]
makeString [LispInteger n, LispCharacter c] =
  pure $ LispString $ pack $ replicate (cast n) c
makeString _ = Left $ Default "Invalid arguments to `make-string`"

strLen : List LispVal -> ThrowsError LispVal
strLen [LispString s] = pure $ LispInteger $ cast $ length s
strLen _ = Left $ Default "Invalid arguments to `string-length`"

strAppend : List LispVal -> ThrowsError LispVal
strAppend [] = pure $ LispString ""
strAppend [s@(LispString _)] = pure s
strAppend ((LispString s1)::(LispString s2)::xs) = strAppend (LispString (s1 ++ s2) :: xs)
strAppend _ = Left $ Default "Invalid arguments to `string-append`"

strPrimitives : List (String, (List LispVal -> ThrowsError LispVal))
strPrimitives =
  [ ("string=?", strBoolBinop (==))
  , ("string<?", strBoolBinop (<))
  , ("string>?", strBoolBinop (>))
  , ("string<=?", strBoolBinop (<=))
  , ("string>=?", strBoolBinop (>=))
  , ("string?", isString)
  , ("make-string", makeString)
  , ("string-length", strLen)
  , ("string-append", strAppend)
  ]
