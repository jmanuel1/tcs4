module TCS4

import Context
import Data.DPair
import Data.IORef
import Data.SnocList
import Data.So
import Data.SortedMap
import Data.Vect
import Data.Vect.Quantifiers
import Syntax
import TCS4Types
import Types

%default total

{- Interpreter -}

covering
Env : Context -> Type
Env = Types.Env Expr

-- QUESTION: Is there a library for "heterogeneous functors" and what not?
mapAll : (f : forall x. prop x -> prop2 x) -> All prop xs -> All prop2 xs
mapAll _ [] = []
mapAll f (x :: xs) = f x :: mapAll f xs

covering
bind : Env context -> (names : Vect n String) -> {0 tcs4Types : Vect n TCS4Type} -> All Syntax.interpretType tcs4Types -> Env (extend context (niceZip names tcs4Types))
bind env [] [] = env
bind env (name :: names) (val :: vals) = bind (env :< (name, val)) names vals

covering
eval : Env context -> Expr context a -> interpretType a
eval _ Unit = ()
eval _ (Natural n) = n
eval env (NatElim zero succ n) = case eval env n of
  Z => eval env zero
  S n' => (eval env succ) (eval env (NatElim zero succ (Natural n')))
eval env (Mult n m) = eval env n * eval env m
eval env (Pair a b) = (eval env a, eval env b)
eval env (First a) = fst (eval env a)
eval env (Second a) = snd (eval env a)
eval env (Pure a) = pure (eval env a)
eval env (Let exprs vars var computation body) = do
  computationResult <- eval env computation
  let boxes = mapAll (eval env) exprs
  eval (bind [<(var, computationResult)] vars boxes) body
eval env (Ref a) = newIORef (eval env a)
eval env (Get a) = readIORef (eval env a)
eval env (Set store value) = writeIORef (eval env store) (eval env value)
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
eval env (Box boxExprs boxVars body) =
  let boxes = mapAll (eval env) boxExprs in
    -- QUESTION: Can I do substitution instead so I can return just a closed
    -- term? Is that worth the effort?
    Evidence _ (bind [<] boxVars boxes, body)
eval env (Unbox box) =
  let Evidence _ (env, expr) = eval env box in
    eval env expr
eval env (Var name {inContextProof}) =
  case inContextProof of
    Stop _ =>
      let (_ :< (_, val)) = env in
        val
    Go _ prf =>
      let (env' :< _) = env in
        eval env' (Var name {inContextProof=prf})

covering
evalClosed : Expr [<] a -> interpretType a
evalClosed a = eval [<] a

{- https://www.cs.cmu.edu/~fp/courses/15816-s10/lectures/04-compmodal.pdf -}
Spec : TCS4Type
Spec = NatNum `Fun` Must (NatNum `Fun` NatNum)

eval' : Expr context (Must a `Fun` a)
eval' = Lam "x" (Unbox (Var {inContextProof=Stop "x"} "x"))

covering
main : IO Builtin.Unit
main = do
  let stagedExp : forall context. Expr context Spec
      stagedExp = Lam "n" (NatElim
        (Box {bs=[]} [] [] (Lam "b" (Natural 1)))
        (Lam "exp'" (Box {bs=[NatNum `Fun` NatNum]} [Var {inContextProof=Stop "exp'"} "exp'"] ["exp''"] (Lam "b" (Var {inContextProof=Stop "b"} "b" `Mult` (Unbox (Var {inContextProof=Go "exp''" (Stop "exp''")} "exp''") `App` Var {inContextProof=Stop "b"} "b")))))
        (Var {inContextProof=Stop "n"} "n"))
  let e : forall context. Expr context NatNum
      e = (eval' `App` (stagedExp `App` Natural 5)) `App` Natural 2
  printLn $ evalClosed e
  pure ()
