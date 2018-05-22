{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module SimplExpr where

import Prelude hiding (foldl)
import IntrospectionWorkout
import Data.List ((\\), nub, concat, delete)
import Data.Maybe
import Unsafe.Coerce

data Expr = Var String | Const Int | Bop String Expr Expr | Let Def Expr deriving Show
data Def  = Def String Expr deriving Show

class Term t where
  type Var t :: *
  type Sub t :: *

  var      :: t -> Maybe (Var t)
  binder   :: t -> Maybe (Var t)
  subterms :: t -> AppList (Sub t) c
  make     :: t -> AppList (Sub t) (Eithery (Sub t)) -> t
  makeFV   :: (Eq (Var t)) => t -> [Var t] -> [Var t]
{-  rename   :: t -> Var t -> t
-}
  {-unifold :: ((AppList (Sub t) a -> a -> a) -> t -> a -> a ) -> t -> a -> a
  unifold fun term acc  = fun (unifold fun) term acc-}

  makeFV t a = case var t of
                 Just  v -> v : a
                 Nothing -> case binder t of
                              Just v  -> filter (/= v) a
                              Nothing -> a

{-
fold'' f t acc = polyfoldr (fold'' f) (subterms t) (applyUniform f (t :: Sub t) acc)


fold :: (Sub t ~ U t, ApplyUniform f t (c -> c), Term t) =>
          Uniform f (c -> c) -> t -> c -> c
fold f t acc = polyfoldr (fold f) (subterms t) (applyUniform f t acc)

y :: ((Uniform f (c -> c) -> c -> c) -> Uniform f (c -> c) -> c -> c) -> Uniform f (c -> c) -> c -> c
y f = f (y f)

fold' f t acc = y (polyfoldl f (subterms t) (applyUniform f t acc)) t acc
-}
{-toSub :: t -> Sub t
toSub = undefined

fold' f t acc = polyfoldr (fold f) (subterms t) (applyUniform f (toSub t) acc)
-}

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

  make (Bop b _ _) subs@(Cons l (Cons r Nil)) = let ([l', r'] :+: [] :+: _) = reify subs in Bop b l' r' --(unsafeCoerce l) (unsafeCoerce r)
  make (Let _ _  ) subs@(Cons d (Cons e Nil)) = let ([e'] :+: [d'] :+: _)  = reify subs in Let d' e' --(unsafeCoerce d) (unsafeCoerce e)
  make t           _                     = t

instance ShallowRename Expr where
  rename (Var _) x = Var x
  rename x       _ = x

instance ShallowRewrite Expr where
  rewrite (Bop b l r) = Bop b r l
  rewrite t = t

instance (v ~ Var Expr) => ShallowFold Expr [v] where
  fold (Var v) a = v : a
  fold _       a = a

instance Term Def where
  type Var Def = String
  type Sub Def = Expr :|: Def :|: U

  subterms (Def _ e) = Cons e Nil

  var _ = Nothing

  binder (Def s _) = Just s

  make (Def s _) x@(Cons e Nil) = let ([e' :: Expr ] :+: [] :+: _) = reify x in Def s e' -- Def s (unsafeCoerce e)

instance ShallowRename Def where
  rename (Def _ e) x = Def x e

instance ShallowRewrite Def where
  rewrite = id

instance (v ~ Var Def) => ShallowFold Def [v] where
  fold (Def v e) a  = v `delete` a

class Term t => ShallowFold t c where
  fold :: t -> c -> c

class ShallowFold t c => Fold t c where
  gfold :: t -> c -> c

instance (Term t, ShallowFold t c, GeneralizedFold (Sub t) c) => Fold t c where
  gfold t acc =
    polyfoldr generalizedFold (subterms t) (fold t acc)

class GeneralizedFold sub c where
  generalizedFold :: Uniform sub (c -> c)

instance GeneralizedFold U c where
  generalizedFold = undefined

instance (Fold t c, GeneralizedFold a c) => GeneralizedFold (t :|: a) c where
  generalizedFold = gfold :+: generalizedFold

class Term t => ShallowRewrite t where
  rewrite :: t -> t

class ShallowRewrite t => Rewrite t where
  grewrite :: t -> t

instance (Term t, ShallowRewrite t, GeneralizedRewrite (Sub t)) => Rewrite t where
  grewrite t =
    let t' = rewrite t in
    make t' (mapTransform multiRewrite (subterms t'))

class GeneralizedRewrite sub where
  multiRewrite :: Transform sub

instance GeneralizedRewrite U where
  multiRewrite = undefined

instance (ShallowRewrite t, GeneralizedRewrite (Sub t), GeneralizedRewrite a) => GeneralizedRewrite (t :|: a) where
  multiRewrite = grewrite :+: multiRewrite


class Term t => ShallowRename t where
  rename :: t -> (Var t) -> t

class ShallowRename t => Rename t where
  grename :: t -> (Var t) -> t

instance (Term t, v ~ Var t, ShallowRename t, GeneralizedRename (Sub t) v) => Rename t where
  grename t v =
    make (rename t v) (mapPolyForm m (subterms t) v)

class GeneralizedRename sub var where
  m :: Polyform sub var

instance GeneralizedRename U v where
  m = undefined

instance (Rename t, v ~ Var t, GeneralizedRename a v) => GeneralizedRename (t :|: a) v where
  m = grename :+: m

class Term t => FV t where
  gfv :: t -> [Var t]

instance (Term t, v ~ Var t, Eq v, GeneralizedFv (Sub t) v) => FV t where
  gfv x =
    let sx = subterms x in
    nub $ (maybeToList (var x) ++ concat (polymap f sx)) \\ maybeToList (binder x)

class GeneralizedFv t v where
  f :: Uniform t [v]

instance (FV t, v ~ Var t , GeneralizedFv a v) => GeneralizedFv (t :|: a) v where
  f = gfv :+: f

instance GeneralizedFv U v where
  f = undefined

fv :: Expr -> [Var Expr]
fv expr = nub $ polyfoldr ((\(t :: Expr) -> makeFV t) :+: (\(t :: Def) -> makeFV t) :+: undefined) (Cons expr Nil) []
-- fv expr = nub $ foldl ((\(t :: Expr) -> makeFV t) :+: (\(t :: Def) -> makeFV t) :+: undefined) expr []

fv' :: Expr -> [String]
fv' expr = nub $ polyfoldr (f :+: g :+: undefined) (Cons expr Nil) []
  where
    f e acc =
      case e of
        Var   x -> x : acc
        _ -> polyfoldr (f :+: g :+: undefined) (subterms e) acc
    g e@(Def s _) acc = polyfoldr (f :+: g :+: undefined) (subterms e) acc \\ [s]

ssFv :: Expr -> [String]
ssFv expr = nub $ polyfoldr (f :+: g :+: undefined) (Cons expr Nil) []
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
    let t = Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print t
    putStrLn ""

    print $ grename t "c"
    putStrLn ""

    print $ grewrite t
    putStrLn ""

    print $ gfold t []
    putStrLn ""

    print $ gfv    $ Def "b" (Var "b")
    print $ gfv    $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ gfv    $ Bop "+" (Var "a") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))
    print $ gfv    $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "b")))
    print $ gfv    $ Bop "+" (Var "b") (Let (Def "b" (Bop "+" (Const 7) (Const 0))) (Bop "+" (Const 6) (Var "a")))

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
