module Procedures

import DataTypes
import Environment

%access public export

isProcedure : PrimitiveLispFunc
isProcedure [LispFunc _ _ _ _ _] = pure $ LispBool True
isProcedure [LispPrimitiveFunc _ _] = pure $ LispBool True
isProcedure [_] = pure $ LispBool False
isProcedure args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

procedurePrimitives : List (String, PrimitiveLispFunc)
procedurePrimitives =
    [ ("procedure?", isProcedure)
    ]