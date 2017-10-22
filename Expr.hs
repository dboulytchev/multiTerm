{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}

import MultiTerm
import Debug.Trace

data Expr = Var String | Const Int | Bop String Expr Expr deriving Show

instance Term Expr where
  type Var Expr = String
  type Sub Expr = [Expr] 

  var (Var s) = Just s
  var  _      = Nothing

  binder _    = Nothing

  eq (Var     _) (Var     _) = True
  eq (Const   _) (Const   _) = True
  eq (Bop _ _ _) (Bop _ _ _) = True
  eq  _           _          = False

  subterms (Var _)     = [] 
  subterms (Const _)   = [] 
  subterms (Bop _ l r) = [l, r] 

  make t@(Var _  )  _     = t
  make t@(Const _)  _     = t
  make (Bop b _ _) [l, r] = Bop b l r

elim0 t = case t of
            Bop "+" e (Const 0) -> e
            Bop "+" (Const 0) e -> e
            _                   -> t

rename r t = case t of 
               Var s -> Var $ r s 
               _     -> t 
                   
expand t = case t of
              Const n -> if n > 1 then Bop "+" (Const $ n-1) (Const 1) else t
              _       -> t

eval t = case t of
           Bop "+" (Const a) (Const b) -> Const $ a+b
           _                           -> t

vars a t = case t of
             Var v -> v:a         
             _     -> a

expr1 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 1) (Const 0)) (Bop "+" (Const 0) (Var "b")))
expr2 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 7) (Const 0)) (Bop "+" (Const 6) (Var "b")))

main = do  
  putStrLn $ show expr1
  putStrLn $ show expr2

  putStrLn $ show $ rewriteBottomUp elim0 expr1
  putStrLn $ show $ rewriteBottomUp (rename (++"_renamed")) expr1
  putStrLn $ show $ rewriteTopDown expand expr2
  putStrLn $ show $ rewriteBottomUp eval (rewriteTopDown expand expr2)
  putStrLn $ show $ rewriteTopDown eval (rewriteTopDown expand expr2)

  putStrLn $ show $ multiFoldBottomUp vars [] expr1
  putStrLn $ show $ multiFoldBottomUp vars [] expr2
  putStrLn $ show $ multiFoldTopDown vars [] expr1
  putStrLn $ show $ multiFoldTopDown vars [] expr2

  putStrLn $ show $ foldBottomUp vars [] expr1
  putStrLn $ show $ foldBottomUp vars [] expr2
  putStrLn $ show $ foldTopDown vars [] expr1
  putStrLn $ show $ foldTopDown vars [] expr2

  putStrLn $ show $ fv expr1
  putStrLn $ show $ fv expr2

