module TCS4

import Data.DPair
import Data.SnocList
import Data.SortedMap
import Data.Vect
import Data.Vect.Quantifiers
import Types

%default total

-- Inspired by https://idris2.readthedocs.io/en/latest/tutorial/interp.html?highlight=interpreter
Context : Type
Context = SnocList (String, TCS4Type)

extend : Context -> Vect numberOfVars (String, TCS4Type) -> Context
extend context [] = context
extend context (binding :: bindings) = extend (context :< binding) bindings

niceZip : Vect n a -> Vect n b -> Vect n (a, b)
niceZip [] [] = []
niceZip (x :: xs) (y :: ys) = (x, y) :: niceZip xs ys

-- TODO: Experiment with `lookup`
data Typeof : String -> Context -> TCS4Type -> Type where
  Stop : (name : String) -> Typeof name (context :< (name, t)) t
  Go : (name : String) -> Typeof name context t -> {0 _ : Not (name === other)} -> Typeof name (context :< (other, _)) t

{- Syntax -}

data Expr : Context -> TCS4Type -> Type where
  Unit : Expr context Unit
  Pair : Expr context a -> Expr context b -> Expr context (Pair a b)
  First : Expr context (Pair a b) -> Expr context a
  Second : Expr context (Pair a b) -> Expr context b
  Pure : Expr context a -> Expr context (Command a)
  Let : All (Expr context) (map Must boxTypes) ->
        -- the boxed stuff is first so that `boxVars` is in scope later in the type
        (boxVars : Vect boundBoxCount String) ->
        (var : String) ->
        Expr context (Command computationResultType) ->
        Expr (extend [<(var, computationResultType)] (niceZip boxVars (map Must boxTypes))) (Command bodyResultType) ->
        {0 boxTypes : Vect boundBoxCount TCS4Type} ->
        Expr context (Command bodyResultType)
  -- constants
  IntNum : Integer -> Expr context IntNum
  Absurd : Expr context Void -> Expr context a
  AbsurdCommand : Expr context (Command Void) -> Expr context a
  Lam : (var : String) -> Expr (context :< (var, a)) b -> Expr context (Fun a b)
  App : Expr context (Fun a b) -> Expr context a -> Expr context b
  Left : Expr context a -> Expr context (Sum a b)
  Right : Expr context b -> Expr context (Sum a b)
  Case : Expr context (Sum a b) -> (left : String) -> Expr (context :< (left, a)) c -> (right : String) -> Expr (context :< (right, b)) c -> Expr context c
  Box : {0 bs : Vect n TCS4Type} ->
        (boxVars : Vect n String) ->
        Expr (extend [<] (niceZip boxVars (map Must bs))) a ->
        All (Expr context) (map Must bs) ->
        Expr context (Must a)
  Unbox : Expr context (Must a) -> Expr context a
  Var : (var : String) -> {0 _ : Typeof var context a} -> Expr context a

{- Interpreter -}

data Env : Context -> Type where
  Lin : Env [<]
  (:<) : Env context -> (binding : (String, interpretType a)) -> Env (context :< (fst binding, a))

data ErrorMessage = {-UnknownVar String |-} TODO

Error : Type
Error = (ErrorMessage, Exists (Prelude.uncurry Expr))

-- QUESTION: Is there a library for "heterogeneous functors" and what not?
mapAll : (f : forall x. prop x -> prop2 x) -> All prop xs -> All prop2 xs
mapAll _ [] = []
mapAll f (x :: xs) = f x :: mapAll f xs

sequenceAll : Applicative f => All (f . prop) xs -> f (All prop xs)
sequenceAll [] = [| [] |]
sequenceAll (x :: xs) = [| (::) x (sequenceAll xs) |]

bind : Env context -> (names : Vect n String) -> {0 tcs4Types : Vect n TCS4Type} -> All Types.interpretType tcs4Types -> Env (extend context (niceZip names tcs4Types))

covering
eval : Env context -> Expr context a -> interpretType a
eval _ Unit = ()
eval env (Pair a b) = (eval env a, eval env b)
eval env (First a) = fst (eval env a)
eval env (Second a) = snd (eval env a)
eval env (Pure a) = pure (eval env a)
eval env (Let exprs vars var computation body) = do
  computationResult <- eval env computation
  let boxes = mapAll (eval env) exprs
  eval (bind [<(var, computationResult)] vars boxes) body
eval _ (IntNum a) = a
eval env (Absurd a) = absurd (eval env a)
eval env (AbsurdCommand a) =
  -- sorry
  -- QUESTION: Should I perform the effect?
  absurd (unsafePerformIO (eval env a))
eval env (Lam var body) = \arg => eval (env :< (var, arg)) body
eval env (App fun arg) = (eval env fun) (eval env arg)
eval env (Left a) = Left (eval env a)
eval env (Right a) = Right (eval env a)
eval env (Case scrutinee left lbody right rbody) =
  case eval env scrutinee of
    Left a => eval (env :< (left, a)) lbody
    Right b => eval (env :< (right, b)) rbody
eval env a = ?todo

covering
evalClosed : Expr [<] a -> interpretType a
evalClosed a = eval [<] a
