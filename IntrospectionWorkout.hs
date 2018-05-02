{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
--{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE TypeFamilyDependencies #-}

infixr 6 :+:
infixr 6 :|:
  
data a :+: b = a :+: b
data a :|: b
data U a 

-- Union of types

class Member x u

instance Member a (U a)
instance Member a (a :|: b)  
instance Member a c => Member a (b :|: c)

-- End of union
-- Type of polyfunction

type family PolyFun u c = r | r -> u c where
  PolyFun (a :|: b) c = (a -> c) :+: PolyFun b c
  PolyFun (U a)     c = a -> c

-- End of polyfunction

-- Type-discriminated apply

class Apply f a b where
  apply :: PolyFun f b -> a -> b

instance {-# OVERLAPPING #-} Apply (a :|: c) a b where
  apply (f :+: _) x = f x

instance  {-# OVERLAPPABLE #-} Apply y a b => Apply (x :|: y) a b where
  apply (_ :+: g) x = apply g x

instance Apply (U a) a b where
  apply f x = f x 
  
-- End of apply

class List l a where
  polymap :: PolyFun a c -> l -> [c]

--instance (Apply b a b, List l b) => List (a :+: l) b where
  --polymap f (a :+: b) = apply f a : polymap f b
  
