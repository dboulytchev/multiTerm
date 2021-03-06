{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilies           #-}

import MultiTerm
import Debug.Trace
import Data.List ((\\))

data Lambda = Var String | Abs String Lambda | App Lambda Lambda deriving (Eq)

instance Show Lambda where 
{-  show (Var x) = x
  show (Abs x b) = "λ" ++ x ++ ". " ++ show b
  show (App p q) = "(" ++ show p ++ ") (" ++ show q ++ ")"
-}
  show l = show' l 7 where
    show' (Var x) _ = x
    show' (Abs x b) n = "λ" ++ x ++ ". " ++ if n > 1 then show' b (n - 1) else "⊥"
    show' (App p q) n = if n > 1 then "(" ++ show' p (n - 1) ++ ") (" ++ show' q (n - 1) ++ ")" else "⊥"


instance Term Lambda where
  type Var Lambda = String
  type Sub Lambda = [Lambda] 

  var (Var s) = Just s
  var  _      = Nothing

  binder (Abs x _) = Just x
  binder _         = Nothing

  subterms (Var _)   = [] 
  subterms (Abs _ b) = [b] 
  subterms (App l r) = [l, r] 

  make t@(Var _)  _     = t
  make (Abs x _) [b]    = Abs x b
  make (App _ _) [l, r] = App l r

  rename (Var _)   x = Var x
  rename (Abs _ b) x = Abs x b
  rename y         _ = y

  fresh vs = Var $ head $ names \\ vs
    where names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']

id_ = Abs "x" (Var "x")
const_ = Abs "x" (Var "y")
expr = Abs "x" (Abs "y" (App (Var "x") (Var "y")))
expr1 = Abs "x" (App (Var "x") (Var "y"))
expr2 = Abs "x" (Abs "y" (App (Var "y") (Var "y"))) 

expr_0 = Abs "y" (App (App id_ (Var "y")) $ Var "x")
expr_1 = App (Var "y") id_

test subj var obj = do
  putStrLn $ "[ " ++ show obj  ++ " / " ++ var ++ " ] " ++ show subj
  putStrLn $ show (cas subj var obj)
  putStrLn "==================================================================="

main = do  
  test id_ "x" $ Var "y"
  test expr_0 "x" $ expr_1
  test const_ "y" $ Var "x"
  test const_ "x" $ const_
  test const_ "y" $ const_
  test const_ "y" $ Var "a"
  test (Abs "x" (App (Var "x") (Var "z"))) "z" (Abs "y" (App (App (Var "x") (Var "y")) (Var "y")))
  test (Abs "y" (App (Var "y") (Var "z"))) "z" (Abs "y" (App (App (Var "x") (Var "y")) (Var "y")))