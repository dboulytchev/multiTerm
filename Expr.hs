{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}

module Expr where

import MultiTerm
import Data.List ((\\))
import Debug.Trace
import HeteroList
import Cas
import Eq

data Expr = Var String | Const Int | Bop String Expr Expr deriving (Show, Eq)

instance Term Expr where
  type Var Expr = String
  type Sub Expr = Expr :|: U

  var (Var s) = Just s
  var  _      = Nothing

  binder _    = Nothing

  subterms (Var _)     = Nil
  subterms (Const _)   = Nil
  subterms (Bop _ l r) = Cons l (Cons r Nil)

  make t@(Var _  )  _   = t
  make t@(Const _)  _   = t
  make (Bop b _ _) subs = let ([l, r] :+: _) = reify subs in Bop b l r

instance FreeVars Expr

instance CAS Expr where
  rename (Var _) x = Var x
  rename y       _ = y

  freshVar vs = let v = head $ names \\ vs in (v, Var v)
    where names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']

instance Equalushko Expr where
  equalushko (Var x) (Var y) = x == y
  equalushko (Const x) (Const y) = x == y
  equalushko (Bop b _ _) (Bop c _ _) = b == c
  equalushko _ _ = False

instance Equal Expr

elim0 t = case t of
            Bop "+" e (Const 0) -> e
            Bop "+" (Const 0) e -> e
            _                   -> t

rename_var r t = case t of
                   Var s -> Var $ r s
                   _     -> t

expand t = case t of
              Const n -> if n > 1 then Bop "+" (Const $ n-1) (Const 1) else t
              _       -> t

eval t = case t of
           Bop "+" (Const a) (Const b) -> Const $ a+b
           _                           -> t

vars t a = case t of
             Var v -> v:a
             _     -> a

expr1 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 1) (Const 0)) (Bop "+" (Const 0) (Var "b")))
expr2 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 7) (Const 0)) (Bop "+" (Const 6) (Var "b")))

expr3 = Const 1
expr4 = Const 2
expr5 = Bop "+" (Var "x") (Var "x")
expr6 = Bop "+" (Var "x") (Var "y")

subst subj v t = cas subj v t

testeq e1 e2 = do
  putStrLn $ show $ equal e1 e2 == (e1 == e2)
  putStrLn ""


test = do
  testeq expr3 expr3
  testeq expr3 expr6
  testeq expr3 expr4
  testeq expr5 expr5
  testeq expr5 expr6

  {-putStrLn $ show expr1
  putStrLn $ show expr2

  putStrLn $ show $ rewrite BottomUp (elim0 :+: undefined) expr1
  putStrLn $ show $ rewrite BottomUp ((rename_var (++"_renamed")) :+: undefined) expr1
  putStrLn $ show $ rewrite TopDown  (expand :+: undefined) expr2
  putStrLn $ show $ rewrite BottomUp (eval :+: undefined) (rewrite TopDown (expand :+: undefined) expr2)
  putStrLn $ show $ rewrite TopDown  (eval :+: undefined) (rewrite TopDown (expand :+: undefined) expr2)

  putStrLn $ show $ fold BottomUp (vars :+: undefined) expr1 []
  putStrLn $ show $ fold BottomUp (vars :+: undefined) expr2 []
  putStrLn $ show $ fold TopDown  (vars :+: undefined) expr1 []
  putStrLn $ show $ fold TopDown  (vars :+: undefined) expr2 []

  putStrLn $ show $ freeVars expr1
  putStrLn $ show $ freeVars expr2

  putStrLn $ show $ subst expr1 "a" (Bop "+" (Var "a") (Const 4))
  putStrLn $ show $ subst expr2 "b" (Bop "+" (Var "b") (Const 4))-}