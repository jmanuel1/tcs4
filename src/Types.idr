module Types

%default total

{- Types -}

public export
data TCS4Type : Type where
  Unit, IntNum, Void : TCS4Type
  Pair, Fun, Sum : TCS4Type -> TCS4Type -> TCS4Type
  -- M/diamond, L/box
  Command, Must : TCS4Type -> TCS4Type

public export
interpretType : TCS4Type -> Type
interpretType Unit = Builtin.Unit
interpretType IntNum = Integer
interpretType Void = Void
interpretType (Pair a b) = (interpretType a, interpretType b)
interpretType (Fun a b) = interpretType a -> interpretType b
interpretType (Sum a b) = Either (interpretType a) (interpretType b)
interpretType (Command a) = IO (interpretType a)
interpretType (Must a) = interpretType a

public export
mustAInterpretedAsA : interpretType (Must a) === interpretType a
mustAInterpretedAsA = Refl
