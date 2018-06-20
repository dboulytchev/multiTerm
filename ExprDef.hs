{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE FlexibleContexts           #-}

module ExprDef where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm
import Data.List ((\\), nub, concat, delete)
import Data.Maybe
import Unsafe.Coerce

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving (Show, Eq)
data Def  = Def String Expr deriving (Show, Eq)

instance Term Expr where
  type Var Expr = String
  type Sub Expr = Expr :|: Def :|: U

  subterms (Var   _)   = Nil
  subterms (Const _)   = Nil
  subterms (Bop _ l r) = Cons l (Cons r Nil)
  subterms (Let d e)   = Cons d (Cons e Nil)

  var (Var x) = Just x
  var _ = Nothing

  binder (Let (Def a _) _) = Just a
  binder _                 = Nothing

  make (Bop b _ _) subs = let ([l', r'] :+: [] :+: _) = reify subs in Bop b l' r'
  make (Let _ _  ) subs = let ([e'] :+: [d'] :+: _)  = reify subs in Let d' e'
  make t           _    = t

instance Term Def where
  type Var Def = String
  type Sub Def = Expr :|: Def :|: U

  subterms (Def _ e) = Cons e Nil

  var _ = Nothing

  binder (Def s _) = Just s

  make (Def s _) subs = let ([e'] :+: [] :+: _) = reify subs in Def s e'

flipBop = rewrite $ (\expr -> case expr of Bop b l r -> Bop b r l ; e -> e) :+: id :+: undefined

simplBop = rewrite (simpl :+: id :+: undefined)
  where simpl (Bop "+" (Const 0) r) = r
        simpl (Bop "+" l (Const 0)) = l
        simpl (Bop "*" (Const 1) r) = r
        simpl (Bop "*" l (Const 1)) = l
        simpl e                     = e

sb expr = sb' expr (simplBop expr)
  where sb' prev curr | prev == curr = curr
        sb' _    curr = sb' curr (simplBop curr)

fv :: Expr -> [Var Expr]
fv e = fold (shallowFv :+: shallowFv :+: undefined) e []

fv' e = fold makeFv e []

foldish e = fold ((\e a -> case e of Var x -> x : a ; _ -> a) :+: (\ d a -> case d of Def x _ -> x `delete` a ) :+: undefined) e []

test :: IO ()
test =
  do
    let t = Bop "+" (Var "a")  (Let (Def "b" (Bop "+" (Bop "*" (Const 1) (Const 7)) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print t
    putStrLn ""

    print $ flipBop t
    putStrLn ""

    print $ simplBop t
    putStrLn ""

    print $ sb t
    putStrLn ""

    print $ foldish t
    putStrLn ""

    print $ fv t
    putStrLn ""

    print $ fv' t
    putStrLn ""

    print $ freeVars t
    putStrLn ""