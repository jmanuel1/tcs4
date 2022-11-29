module Types

import Context
import Data.DPair
import Data.IORef
import public TCS4Types

%default total

{- Environment -}

mutual
  public export
  data Env : (0 expr : Context -> TCS4Type -> Type) -> Context -> Type where
    Lin : Env expr [<]
    (:<) : Env expr context -> (binding : (String, interpretType' expr a)) -> Env expr (context :< (fst binding, a))

  public export
  0 interpretType' : (Context -> TCS4Type -> Type) -> TCS4Type -> Type
  interpretType' expr Unit = Builtin.Unit
  interpretType' expr IntNum = Integer
  interpretType' expr NatNum = Nat
  interpretType' expr Void = Void
  interpretType' expr (Pair a b) = (interpretType' expr a, interpretType' expr b)
  interpretType' expr (Fun a b) = interpretType' expr a -> interpretType' expr b
  interpretType' expr (Sum a b) = Either (interpretType' expr a) (interpretType' expr b)
  interpretType' expr (Command a) = IO (interpretType' expr a)
  interpretType' expr (Must a) = Exists (\context => (Env expr context, expr context a))
  interpretType' expr (Prop _) = Builtin.Unit
  interpretType' expr (Store a) = IORef (interpretType' expr a)
