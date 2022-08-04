module Context

import Data.SnocList
import Data.Vect
import TCS4Types

%default total

-- Inspired by https://idris2.readthedocs.io/en/latest/tutorial/interp.html?highlight=interpreter
public export
Context : Type
Context = SnocList (String, TCS4Type)

public export
extend : Context -> Vect numberOfVars (String, TCS4Type) -> Context
extend context [] = context
extend context (binding :: bindings) = extend (context :< binding) bindings

-- TODO: Use `zip`
public export
niceZip : Vect n a -> Vect n b -> Vect n (a, b)
niceZip [] [] = []
niceZip (x :: xs) (y :: ys) = (x, y) :: niceZip xs ys

-- TODO: Experiment with `lookup`
-- TODO: If still using Stop/Go, make sure it compiles to nats
public export
data Typeof : String -> Context -> TCS4Type -> Type where
  Stop : (0 name : String) -> Typeof name (context :< (name, t)) t
  Go : (0 name : String) -> Typeof name context t -> {auto 0 notThisOneProof : So (name /= other)} -> Typeof name (context :< (other, _)) t
