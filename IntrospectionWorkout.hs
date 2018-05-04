{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE TypeFamilyDependencies     #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE ScopedTypeVariables        #-}

module IntrospectionWorkout where

infixr 6 :+:
infixr 6 :|:

-- Product
data a :+: b = a :+: b

-- Coproduct
data a :|: b

-- Singleton
data U a

-- Membership
class Member x u

instance Member a (U a)
instance Member a (a :|: b)
instance Member a c => Member a (b :|: c)

-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c) -}
type family Uniform u c = r | r -> u c where
  Uniform (a :|: b) c = (a -> c) :+: Uniform b c
  Uniform (U a)     c = a -> c

-- Type-discriminated application

class ApplyUniform f a b where
  applyUniform :: Uniform f b -> a -> b

instance {-# OVERLAPPING #-} ApplyUniform (a :|: c) a b where
  applyUniform (f :+: _) x = f x

instance  {-# OVERLAPPABLE #-} ApplyUniform y a b => ApplyUniform (x :|: y) a b where
  applyUniform (_ :+: g) x = applyUniform g x

instance ApplyUniform (U a) a b where
  applyUniform f x = f x

-- End of application

-- Polyfunction with uniform codomain
{- (u = \Sigma t_i) -> \Pi (t_i -> c -> t_i) -}
type family Polyform u c = r | r -> u c where
  Polyform (a :|: b) c = (a -> c -> a) :+: Polyform b c
  Polyform (U a)     c = a -> c -> a

-- Type-discriminated application

class ApplyPolyform f a b where
  applyPolyform :: Polyform f b -> a -> b -> a

instance {-# OVERLAPPING #-} ApplyPolyform (a :|: c) a b where
  applyPolyform (f :+: _) x b = f x b

instance  {-# OVERLAPPABLE #-} ApplyPolyform y a b => ApplyPolyform (x :|: y) a b where
  applyPolyform (_ :+: g) x b = applyPolyform g x b

instance ApplyPolyform (U a) a b where
  applyPolyform f x b = f x b

-- End of application

data AppList f c = Nil | forall a . (Show a, ApplyUniform f a c, ApplyPolyform f a c) => Cons a (AppList f c)

instance Show (AppList f c) where
  show Nil = "[]"
  show (Cons h t) = show h ++ " : " ++ show t

polymap :: Uniform f c -> AppList f c -> [c]
polymap _ Nil = []
polymap f (Cons h t) = applyUniform f h : polymap f t

polyfoldl :: Uniform f (c -> c) -> AppList f (c -> c) -> c -> c
polyfoldl _  Nil       acc = acc
polyfoldl f (Cons h t) acc = polyfoldl f t (applyUniform f h acc)

polyfoldr :: Uniform f (c -> c) -> AppList f (c -> c) -> c -> c
polyfoldr _  Nil       acc = acc
polyfoldr f (Cons h t) acc = applyUniform f h (polyfoldr f t acc)



mapPolyForm :: Polyform f c -> AppList f c -> c -> AppList f c
mapPolyForm _ Nil _ = Nil
mapPolyForm f (Cons h t) c = Cons (applyPolyform f h c) (mapPolyForm f t c)


main :: IO ()
main = do
  print $ polyfoldl ((\(x :: Int) acc -> x * acc :: Int) :+: (\x acc -> acc + length (x :: String) :: Int)) (Cons "b" (Cons (2 :: Int) (Cons "twitter" Nil))) 0
  print $ polyfoldr ((\(x :: Int) acc -> x * acc :: Int) :+: (\x acc -> acc + length (x :: String) :: Int)) (Cons "b" (Cons (2 :: Int) (Cons "twitter" Nil))) 0

--p :: ExList -> String
--p Nil        = ""
--p (Cons h t) = show h ++ p t

--class List l a where
 -- polymap :: Uniform a c -> l -> [c]

--instance (ApplyUniformUniform b a b, List l b) => List (a :+: l) b where
  --polymap f (a :+: b) = applyUniform f a : polymap f b

