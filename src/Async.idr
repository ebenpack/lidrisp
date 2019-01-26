
module Async

public export
data Async : Type -> Type -> Type -> Type where
  MkAsync : ((error -> r) -> (success -> r) -> r) -> Async r error success
