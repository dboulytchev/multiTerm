{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE ScopedTypeVariables    #-}

import MultiTerm
import Debug.Trace
import Data.List

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving Show
data Def  = Def String Expr deriving Show

instance Term Def where
  type Var Def = String
  type Sub Def = [Expr] :+: [Def]

  var _ = Nothing

  binder (Def s _) = Just s

  eq _ _ = True

  subterms (Def _ e) = [e] :+: []

  make (Def s _) ([e] :+: []) = Def s e

instance Term Expr where
  type Var Expr = String
  type Sub Expr = [Expr] :+: [Def]

  var (Var s) = Just s
  var  _      = Nothing

  binder _    = Nothing

  eq (Var     _) (Var     _) = True
  eq (Const   _) (Const   _) = True
  eq (Bop _ _ _) (Bop _ _ _) = True
  eq (Let _ _  ) (Let _ _  ) = True
  eq  _           _          = False

  subterms (Var _)     = [] :+: []
  subterms (Const _)   = [] :+: []
  subterms (Bop _ l r) = [l, r] :+: []
  subterms (Let   d e) = [e] :+: [d]

  make t@(Var _  )  _               = t
  make t@(Const _)  _               = t
  make (Bop b _ _) ([l, r] :+: [] ) = Bop b l r
  make (Let _ _  ) ([e]    :+: [d]) = Let d e

elim0 t = case t of
            Bop "+" e (Const 0) -> e
            Bop "+" (Const 0) e -> e
            _                   -> t

rename r t = case t of 
               Var s             -> Var $ r s 
               Let (Def s e1) e2 -> Let (Def (r s) e1) e2
               _                 -> t 
                   
expand t = case t of
              Const n -> if n > 1 then Bop "+" (Const $ n-1) (Const 1) else t
              _       -> t

renameDef r (Def s e) = Def (r s) e

eval t = case t of
           Bop "+" (Const a) (Const b) -> Const $ a+b
           _                           -> t

expr1 = Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 1) (Const 0))) (Bop "+" (Const 0) (Var "b")))
expr2 = Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))

vars a t = case t of
             Var v -> v:a         
             _     -> a

varsDef a (Def v e) = v `delete` a

main = do
  putStrLn $ show expr1
  putStrLn $ show expr2

  putStrLn $ show $ rewriteBottomUp elim0 expr1
  putStrLn $ show $ rewriteBottomUp (rename (++"_renamed")) expr1
  putStrLn $ show $ rewriteTopDown expand expr2
  putStrLn $ show $ multiRewriteBottomUp (elim0  :+: renameDef (++"_renamed")) expr1
  putStrLn $ show $ multiRewriteTopDown (expand :+: renameDef (++"_renamed")) expr2
  putStrLn $ show $ rewriteBottomUp eval (rewriteTopDown expand expr2)
  putStrLn $ show $ rewriteTopDown eval (rewriteTopDown expand expr2)
  putStrLn $ show $ multiRewriteBottomUp (eval :+: id) (rewriteTopDown expand expr2)

  putStrLn $ show $ multiFoldBottomUp (vars :+: (\ c _ -> c)) [] expr1
  putStrLn $ show $ multiFoldBottomUp (vars :+: (\ c _ -> c)) [] expr2
  putStrLn $ show $ multiFoldTopDown  (vars :+: (\ c _ -> c)) [] expr1
  putStrLn $ show $ multiFoldTopDown  (vars :+: (\ c _ -> c)) [] expr2

  putStrLn $ show $ foldBottomUp vars [] expr1
  putStrLn $ show $ foldBottomUp vars [] expr2
  putStrLn $ show $ foldTopDown vars [] expr1
  putStrLn $ show $ foldTopDown vars [] expr2

  putStrLn $ show $ multiFoldBottomUp (vars :+: varsDef) [] expr1
  putStrLn $ show $ multiFoldTopDown  (vars :+: varsDef) [] expr1

  putStrLn $ show $ multiFoldBottomUp (vars :+: varsDef) [] expr2
  putStrLn $ show $ multiFoldTopDown  (vars :+: varsDef) [] expr2

  
