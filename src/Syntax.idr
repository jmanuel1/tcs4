module Syntax

import Context
import Data.Vect
import Data.Vect.Quantifiers
import Types

%default total

public export
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
