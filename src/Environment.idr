module Environment

import Control.ST
import Data.IORef
import Control.ST.Exception
import Data.SortedMap

%access public export

data Bindings : Type -> Type where
    MkBindings : SortedMap String (IORef a) -> Bindings a

BindingsRef : Type -> Type
BindingsRef a = IORef (Bindings a)

data EnvRef a =
    Global (BindingsRef a)
    | Frame (BindingsRef a) (EnvRef a)

interface Envir a (m: Type -> Type) | m where
    showEnv   : Show a => EnvRef a -> ST m String []
    initEnv   : List (String, a)             -> ST m (EnvRef a) []
    getVar    : EnvRef a -> String           -> ST m (Maybe a) []
    setVar    : EnvRef a -> String -> a      -> ST m Bool []
    defineVar : EnvRef a -> String -> a      -> ST m () []
    bindVars  : EnvRef a -> List (String, a) -> ST m (EnvRef a) []

addBinding : HasReference ffi => (String, a) -> IO' ffi (String, IORef a)
addBinding (k, v) =
    do ref <- newIORef' v
       pure (k, ref)

getBindingsRef : EnvRef a -> BindingsRef a
getBindingsRef (Global bindRef) = bindRef
getBindingsRef (Frame bindRef _) = bindRef
