module TCS4Types

%default total

{- Types -}

public export
data TCS4Type : Type where
  Unit, IntNum, NatNum, Void : TCS4Type
  Pair, Fun, Sum : TCS4Type -> TCS4Type -> TCS4Type
  -- M/diamond, L/box
  Command, Must : TCS4Type -> TCS4Type
  -- Types corresponding to propositional variables
  Prop : String -> TCS4Type
  -- References
  Store : TCS4Type -> TCS4Type
