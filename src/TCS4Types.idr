module TCS4Types

{- Types -}

public export
data TCS4Type : Type where
  Unit, IntNum, Void : TCS4Type
  Pair, Fun, Sum : TCS4Type -> TCS4Type -> TCS4Type
  -- M/diamond, L/box
  Command, Must : TCS4Type -> TCS4Type
  -- Types corresponding to propositional variables
  Prop : String -> TCS4Type
