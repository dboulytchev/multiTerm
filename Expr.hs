{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}

import MultiTerm
import Data.List ((\\))
import Debug.Trace

data Expr = Var String | Const Int | Bop String Expr Expr deriving Show

instance Term Expr where
  type Var Expr = String
  type Sub Expr = [Expr] 

  var (Var s) = Just s
  var  _      = Nothing

  binder _    = Nothing

  subterms (Var _)     = [] 
  subterms (Const _)   = [] 
  subterms (Bop _ l r) = [l, r] 

  make t@(Var _  )  _     = t
  make t@(Const _)  _     = t
  make (Bop b _ _) [l, r] = Bop b l r

  rename (Var _) x = Var x
  rename y       _ = y

  fresh vs = Var $ head $ names \\ vs
    where names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']

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

vars a t = case t of
             Var v -> v:a         
             _     -> a

expr1 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 1) (Const 0)) (Bop "+" (Const 0) (Var "b")))
expr2 = Bop "+" (Var "a") (Bop "+" (Bop "+" (Const 7) (Const 0)) (Bop "+" (Const 6) (Var "b")))

main = do  
  putStrLn $ show expr1
  putStrLn $ show expr2

  putStrLn $ show $ rewrite BottomUp elim0 expr1
  putStrLn $ show $ rewrite BottomUp (rename_var (++"_renamed")) expr1
  putStrLn $ show $ rewrite TopDown expand expr2
  putStrLn $ show $ rewrite BottomUp eval (rewrite TopDown expand expr2)
  putStrLn $ show $ rewrite TopDown eval (rewrite TopDown expand expr2)

  putStrLn $ show $ multiFold BottomUp vars [] expr1
  putStrLn $ show $ multiFold BottomUp vars [] expr2
  putStrLn $ show $ multiFold TopDown vars [] expr1
  putStrLn $ show $ multiFold TopDown vars [] expr2

  putStrLn $ show $ fold BottomUp vars [] expr1
  putStrLn $ show $ fold BottomUp vars [] expr2
  putStrLn $ show $ fold TopDown vars [] expr1
  putStrLn $ show $ fold TopDown vars [] expr2

  putStrLn $ show $ fv expr1
  putStrLn $ show $ fv expr2

  putStrLn $ show $ subst expr1 "a" (Bop "+" (Var "a") (Const 4))
  putStrLn $ show $ subst expr2 "b" (Bop "+" (Var "b") (Const 4))
