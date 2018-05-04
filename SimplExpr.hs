{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}

{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances   #-}
--{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ExistentialQuantification  #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}


module SimplExpr where

import IntrospectionWorkout
import Data.List ((\\), nub)

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving Show
data Def  = Def String Expr deriving Show

subtermsExpr :: (Apply f Def c, Apply f Expr c) => Expr -> AppList f c
subtermsExpr (Var   _)   = Nil
subtermsExpr (Const _)   = Nil
subtermsExpr (Bop _ l r) = Cons l (Cons r Nil)
subtermsExpr (Let d e)   = Cons d (Cons e Nil)

subtermsDef :: Apply f Expr c => Def -> AppList f c
subtermsDef (Def _ e) = Cons e Nil

fv :: Expr -> [String]
fv expr = nub $ polyfoldr (f :+: g) (Cons expr Nil) []
  where
    f e acc =
      case e of
        Var   x -> x : acc
        _ -> polyfoldr (f :+: g) (subtermsExpr e) acc
    g e@(Def s _) acc = polyfoldr (f :+: g) (subtermsDef e) acc \\ [s]

ssFv :: Expr -> [String]
ssFv expr = nub $ polyfoldr (f :+: g) (Cons expr Nil) []
  where
    f e acc =
      case e of
        Var   x -> x : acc
        Const _ -> acc
        Bop _ l r -> f l (f r acc)
        Let d b -> g d (f b acc)
    g e acc =
      case e of
        Def s l -> f l acc \\ [s]

test :: IO ()
test =
  do
    print $ fv   $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv   $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))

    print $ fv   $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv   $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))

    print $ ssFv $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ ssFv $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))

    print $ ssFv $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ ssFv $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))
