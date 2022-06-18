module TCS4

import Data.DPair
import Data.IORef
import Data.SnocList
import Data.So
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
-- TODO: If still using Stop/Go, make sure it compiles to nats
data Typeof : String -> Context -> TCS4Type -> Type where
  Stop : (0 name : String) -> Typeof name (context :< (name, t)) t
  Go : (0 name : String) -> Typeof name context t -> {auto 0 notThisOneProof : So (name /= other)} -> Typeof name (context :< (other, _)) t

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
        {auto 0 boxTypes : Vect boundBoxCount TCS4Type} ->
        Expr context (Command bodyResultType)
  -- constants
  Constant : interpretType a -> Expr context a
  Absurd : Expr context Void -> Expr context a
  AbsurdCommand : Expr context (Command Void) -> Expr context a
  Lam : (var : String) -> Expr (context :< (var, a)) b -> Expr context (Fun a b)
  App : Expr context (Fun a b) -> Expr context a -> Expr context b
  Left : Expr context a -> Expr context (Sum a b)
  Right : Expr context b -> Expr context (Sum a b)
  Case : Expr context (Sum a b) -> (left : String) -> Expr (context :< (left, a)) c -> (right : String) -> Expr (context :< (right, b)) c -> Expr context c
  Box : {0 bs : Vect n TCS4Type} ->
        All (Expr context) (map Must bs) ->
        -- the boxed stuff is first so that `boxVars` is in scope later in the type
        (boxVars : Vect n String) ->
        Expr (extend [<] (niceZip boxVars (map Must bs))) a ->
        Expr context (Must a)
  Unbox : Expr context (Must a) -> Expr context a
  Var : (var : String) -> {inContextProof : Typeof var context a} -> Expr context a

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
