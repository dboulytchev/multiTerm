{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE UndecidableInstances       #-}

module HeteroList where

infixr 6 :+:
infixr 6 :|:

-- Product
data a :+: b = a :+: b

-- Coproduct
data a :|: b

-- Singleton
data U

-- Heterogeneous list
data HeteroList f = Nil
                  | forall a . ( Show a,
                                 ApplyUniform   f a,
                                 ApplyPolyform  f a,
                                 ApplyTransform f a
                               ) => Cons a (HeteroList f)

-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c) -}
type family Uniform u c = r | r -> u c where
  Uniform (a :|: b) c = (a -> c) :+: Uniform b c

-- Type-discriminated application
class ApplyUniform f a where
  applyUniform :: Uniform f b -> a -> b

instance {-# OVERLAPPING #-} ApplyUniform (a :|: c) a where
  applyUniform (f :+: _) x = f x

instance  {-# OVERLAPPABLE #-} ApplyUniform y a => ApplyUniform (x :|: y) a where
  applyUniform (_ :+: g) x = applyUniform g x

-- Composition for a polyfunction with uniform codomain
class ComposeUniform f b c where
  composeUniform :: Uniform f b -> (b -> c) -> Uniform f c

instance ComposeUniform U b c where
  composeUniform _ _ = undefined

instance ComposeUniform fs b c => ComposeUniform (f :|: fs) b c where
  composeUniform (f :+: fs) g = g . f :+: composeUniform fs g

-- A simple transformation polyfunction
type family Transform u = r | r -> u where
  Transform (a :|: b) = (a -> a) :+: Transform b

class ApplyTransform u a where
  applyTransform :: Transform u -> a -> a

instance {-# OVERLAPPING #-} ApplyTransform (a :|: b) a where
  applyTransform (f :+: _) x = f x

instance {-# OVERLAPPABLE #-} ApplyTransform b c => ApplyTransform (a :|: b) c where
  applyTransform (_ :+: f) x = applyTransform f x

-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c -> t_i) -}
type family Polyform u c = r | r -> u c where
  Polyform (a :|: b) c = (a -> c -> a) :+: Polyform b c

-- Type-discriminated application
class ApplyPolyform f a where
  applyPolyform :: Polyform f b -> a -> b -> a

instance {-# OVERLAPPING #-} ApplyPolyform (a :|: c) a where
  applyPolyform (f :+: _) x b = f x b

instance  {-# OVERLAPPABLE #-} ApplyPolyform y a => ApplyPolyform (x :|: y) a where
  applyPolyform (_ :+: g) x b = applyPolyform g x b

instance Show (HeteroList f) where
  show Nil = "[]"
  show (Cons h t) = show h ++ " : " ++ show t

type family Eithery u = r | r -> u where
  Eithery (a :|: b) = Either a (Eithery b)

class Index u a where
  index :: a -> Eithery u

instance {-# OVERLAPPING #-} Index (a :|: b) a where
  index a = Left a

instance {-# OVERLAPPABLE #-} Index b c => Index (a :|: b) c where
  index a = Right (index a)

class MultiIndex u z where
  multiIndex :: Uniform u (Eithery z)

instance {-# OVERLAPPING #-} MultiIndex U U where
  multiIndex = undefined

instance {-# OVERLAPPING #-} (Index (a :|: b) a, MultiIndex b (a :|: b)) => MultiIndex (a :|: b) (a :|: b) where
  multiIndex = index :+: multiIndex

instance {-# OVERLAPPABLE #-} ( MultiIndex b b,
                                ComposeUniform b (Eithery b) (Eithery (a :|: b))
                              ) => MultiIndex b (a :|: b) where
  multiIndex = composeUniform multiIndex Right

type family Reify u = r | r -> u where
  Reify (a :|: b) = [a] :+: Reify b

class Default u where
  def :: Reify u

instance Default U where
  def = undefined

instance Default b => Default (a :|: b) where
  def = [] :+: def

class Default u => Product u where
  insert :: [Eithery u] -> Reify u
  insert = foldl insert' def

  insert' :: Reify u -> Eithery u -> Reify u

instance Product U where
  insert' = undefined

instance Product b => Product (a :|: b) where
  insert' (as :+: bs) (Left  a) = (as ++ [a]) :+: bs
  insert' (as :+: bs) (Right b) = as :+: (insert' bs b)

reify :: (Product u, MultiIndex u u) => HeteroList u -> Reify u
reify x = insert $ polymap multiIndex x

polymap :: Uniform f c -> HeteroList f -> [c]
polymap _ Nil = []
polymap f (Cons h t) = applyUniform f h : polymap f t

polyfoldl :: Uniform f (c -> c) -> HeteroList f -> c -> c
polyfoldl _  Nil       acc = acc
polyfoldl f (Cons h t) acc = polyfoldl f t (applyUniform f h acc)

polyfoldr :: Uniform f (c -> c) -> HeteroList f -> c -> c
polyfoldr _  Nil       acc = acc
polyfoldr f (Cons h t) acc = applyUniform f h (polyfoldr f t acc)

mapPolyForm :: Polyform f c -> HeteroList f -> c -> HeteroList f
mapPolyForm _ Nil _ = Nil
mapPolyForm f (Cons h t) c = Cons (applyPolyform f h c) (mapPolyForm f t c)

mapTransform :: Transform f -> HeteroList f -> HeteroList f
mapTransform _ Nil = Nil
mapTransform f (Cons h t) = Cons (applyTransform f h) (mapTransform f t)

main :: IO ()
main = do
  let (ints :+: _) = reify (Cons (42 :: Int) (Cons (13 :: Int) Nil)) :: Reify (Int :|: U)
  print $ ints


  let (ints :+: strings :+: _) = reify (Cons (42 :: Int)
                                       (Cons "c"
                                       (Cons (13 :: Int)
                                       (Cons "abc" Nil)))) :: Reify (Int :|: String :|: U)
  print $ ints
  print $ strings

