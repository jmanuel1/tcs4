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
import Types

%default total

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
bind env [] [] = env
bind env (name :: names) (val :: vals) = bind (env :< (name, val)) names vals

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
eval _ (Constant a) = a
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
    eval (bind [<] boxVars boxes) body
eval env (Unbox a) = eval env a
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

{- The robot task from the TCS4 paper (example). -}
Spec : TCS4Type
Spec = Must (Command (Prop "light"))

covering
main : IO Builtin.Unit
main = do
  state <- newIORef "light"
  let axSensor : Expr _ (Must (Command (Sum (Prop "light") (Prop "dark"))))
      axSensor = Box {bs=[]} [] [] (Constant $ do
        s <- readIORef state
        pure {f=IO} (if s == "light" then Prelude.Left () else Prelude.Right ()))
  let axToggle1 : Expr _ (Must (Fun (Prop "dark") (Command (Prop "light"))))
      axToggle1 = Box {bs=[]} [] [] (Constant $ \_ => writeIORef {io=IO} state "light")
  let axToggle2 : Expr _ (Must (Fun (Prop "light") (Command (Prop "dark"))))
      axToggle2 = Box {bs=[]} [] [] (Constant $ \_ => writeIORef {io=IO} state "dark")
  let e : Expr _ Spec
      e = Box {bs=[]}
        []
        []
        (Let {boxTypes=[Fun (Prop "dark") (Command (Prop "light"))]}
          [axToggle1]
          ["w"]
          "z"
          (Unbox axSensor)
          (Case {a=Prop "light", b=Prop "dark"} (Var {inContextProof=Go "z" (Stop "z")} "z") "u" (Pure (Var {inContextProof=Stop "u"} "u")) "v" (App (Unbox (Var {inContextProof=Go "w" (Stop "w")} "w")) (Var {inContextProof=Stop "v"} "v"))))
  evalClosed e
  putStrLn !(readIORef state)
  writeIORef state "dark"
  evalClosed e
  putStrLn !(readIORef state)
