module Bools

import Control.ST
import Control.ST.Exception
import DataTypes
import Util
import Ratio
import Lists
import Numbers
import Strings
import Vector
import Data.Complex

%access public export

isBoolean : PrimitiveLispFunc
isBoolean [LispBool _] = pure $ LispBool True
isBoolean _ = pure $ LispBool False

or : PrimitiveLispFunc
or [] = pure $ LispBool False
or [x] = pure x
or (LispBool x::xs) =
    case x of
        True => pure $ LispBool True
        False => or xs
or (x::xs) = pure x

and : PrimitiveLispFunc
and [] = pure $ LispBool True
and [x] = pure x
and (LispBool x::xs) =
    case x of
        True => and xs
        False => pure $ LispBool False
and (x::xs) = and xs

not : PrimitiveLispFunc
not [LispBool False] = pure $ LispBool True
not [_] = pure $ LispBool False
not args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

boolPrimitives : List (String, PrimitiveLispFunc)
boolPrimitives =
  [ ("boolean?", isBoolean)
  , ("and", and)
  , ("or", or)
  , ("not", not)
  ]