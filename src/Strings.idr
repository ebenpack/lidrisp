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

strPrimitives : List (String, (PrimitiveLispFunc))
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
