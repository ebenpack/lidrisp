module Symbols

import DataTypes

%access public export

isSymbol : PrimitiveLispFunc
isSymbol [LispAtom _] = pure $ LispBool True
isSymbol _ = pure $ LispBool False

symbolToString : PrimitiveLispFunc
symbolToString [LispAtom s] = pure $ LispString s
symbolToString [arg] = Left $ TypeMismatch "list" arg
symbolToString args = Left $ NumArgs (MinMax 1 1) (cast $ length args) args

symbolPrimitives : List (String, PrimitiveLispFunc)
symbolPrimitives =
  [ ("symbol?", isSymbol)
  , ("symbol->string", symbolToString)
  ]