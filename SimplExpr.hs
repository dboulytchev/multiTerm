{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE ExistentialQuantification  #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}


module SimplExpr where

import Prelude hiding (foldl)
import IntrospectionWorkout
import Data.List ((\\), nub)

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving Show
data Def  = Def String Expr deriving Show

class Term t where
  type Var t :: *
  type Sub t :: *

  var      :: t -> Maybe (Var t)
  binder   :: t -> Maybe (Var t)
  subterms :: t -> AppList (Sub t) c
  makeFV   :: (Eq (Var t)) => t -> [Var t] -> [Var t]

  {-unifold :: ((AppList (Sub t) a -> a -> a) -> t -> a -> a ) -> t -> a -> a
  unifold fun term acc  = fun (unifold fun) term acc-}

  makeFV t a = case var t of
                 Just  v -> v : a
                 Nothing -> case binder t of
                              Just v  -> filter (/= v) a
                              Nothing -> a

fold'' f t acc = polyfoldr (fold'' f) (subterms t) (applyUniform f (t :: Sub t) acc)


fold :: (Sub t ~ U t, ApplyUniform f t (c -> c), Term t) =>
          Uniform f (c -> c) -> t -> c -> c
fold f t acc = polyfoldr (fold f) (subterms t) (applyUniform f t acc)

y :: ((Uniform f (c -> c) -> c -> c) -> Uniform f (c -> c) -> c -> c) -> Uniform f (c -> c) -> c -> c
y f = f (y f)

fold' f t acc = y (polyfoldl f (subterms t) (applyUniform f t acc)) t acc

{-toSub :: t -> Sub t
toSub = undefined

fold' f t acc = polyfoldr (fold f) (subterms t) (applyUniform f (toSub t) acc)
-}
instance Term Expr where
  type Var Expr = String
  type Sub Expr = Expr :|: U Def

  subterms (Var   _)   = Nil
  subterms (Const _)   = Nil
  subterms (Bop _ l r) = Cons l (Cons r Nil)
  subterms (Let d e)   = Cons d (Cons e Nil)

  var (Var x) = Just x
  var _ = Nothing

  binder _ = Nothing

instance Term Def where
  type Var Def = String
  type Sub Def = Expr :|: U Def {-U Expr-}

  subterms (Def _ e) = Cons e Nil

  var _ = Nothing

  binder (Def s _) = Just s

fv :: Expr -> [Var Expr]
fv expr = nub $ polyfoldr ((\(t :: Expr) -> makeFV t) :+: (\(t :: Def) -> makeFV t)) (Cons expr Nil) []
-- fv expr = nub $ foldl ((\(t :: Expr) -> makeFV t) :+: (\(t :: Def) -> makeFV t)) expr []

fv' :: Expr -> [String]
fv' expr = nub $ polyfoldr (f :+: g) (Cons expr Nil) []
  where
    f e acc =
      case e of
        Var   x -> x : acc
        _ -> polyfoldr (f :+: g) (subterms e) acc
    g e@(Def s _) acc = polyfoldr (f :+: g) (subterms e) acc \\ [s]

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
    print $ fv    $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv    $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))
    print $ fv    $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv    $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))


    print $ fv'   $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv'   $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))
    print $ fv'   $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ fv'   $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))
{-
    print $ ssFv $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ ssFv $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))

    print $ ssFv $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ ssFv $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))


    putStrLn "polyform functions"

    let renaming n = case n of
                       "a" -> "r"
                       "b" -> "z"
                       _   -> n

    let rename = (\(x :: Expr) r -> case x of Var y -> Var (r y) ; _ -> x) :+: (\(Def s b :: Def) r -> Def (r s) b)

    print $ applyPolyform rename (Var "x") renaming
    print $ applyPolyform rename (Var "a") renaming
    print $ applyPolyform rename (Def "b" (Var "a")) renaming

    putStrLn "mapPolyForm"
    print $ mapPolyForm rename (Cons (Var "a") (Cons (Def "b" (Var "a")) Nil)) renaming -}
