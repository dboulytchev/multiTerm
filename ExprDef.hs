{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}

module ExprDef where

import Prelude hiding (foldl)
import HeteroList
import MultiTerm
import Data.List ((\\), nub, concat, delete)
import Data.Maybe
import Unsafe.Coerce

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving Show
data Def  = Def String Expr deriving Show

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
  make t           _                     = t

rewriteE (Bop b l r) = Bop b r l
rewriteE t = t

rewriteD = id

instance Term Def where
  type Var Def = String
  type Sub Def = Expr :|: Def :|: U

  subterms (Def _ e) = Cons e Nil

  var _ = Nothing

  binder (Def s _) = Just s

  make (Def s _) subs = let ([e'] :+: [] :+: _) = reify subs in Def s e'

test :: IO ()
test =
  do

    let t = Bop "+" (Var "a")  (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print t
    putStrLn ""

    print $ rewrite (rewriteE :+: rewriteD :+: undefined) t
    putStrLn ""
