import Data.List
  
data Expr =
   Lambda String Expr
 | Var    String
 | App    Expr Expr
 deriving Show

subterms (Lambda _ e) = [e]
subterms (App    x y) = [x, y]
subterms  _           = []

make (Lambda s _) [e]    = Lambda s e
make (App    _ _) [l, r] = App l r
make  t            _     = t

gfold :: ((a -> Expr -> b) -> a -> Expr -> b) -> a -> Expr -> b
gfold f a e = f (gfold f) a e

f self (ss, i) (Lambda s e) = let j = show i in
                              Lambda j (self ((s, j):ss, i+1) e)
f self (ss, i) (App    x y) = App (self (ss, i) x) (self (ss, i) y)
f self (ss, i) (Var x     ) = case lookup x ss of
                                Nothing -> Var x
                                Just y  -> Var y

names = (\ l -> l ++ [x ++ name | name <- names, x <- l]) $ map (:[]) ['a'..'z']
update f x a y = if x == y then a else f y

f' cas' (dom, f, _  ) (Var    x  ) = if elem x dom then f x else Var x
f' cas' s             (App    x y) = App (cas' s x) (cas' s y) 
f' cas' (dom, f, fvs) (Lambda s e) =
  if elem s dom
  then (Lambda s $ cas' (dom \\ [s], f, fvs) e)
  else if elem s fvs
       then let s' = head $ names \\ (s:fvs) in
            Lambda s' $ cas' (s:dom, update f s (Var s'), s':fvs) e
       else Lambda s $ cas' (dom, f, fvs) e
  
cas t x a = gfold f' ([x], update (\ _ -> undefined) x a, fv a) t 

index = gfold f ([], 0)

fold :: (Expr -> [a] -> a) -> Expr -> a
fold f s  = f s (map (fold f) $ subterms s) 

fv = fold (\ s ss -> case (s, ss) of
                       (Lambda s  _, [fvs] ) -> fvs \\ [s]
                       (Var    s   , _     ) -> [s]
                       (App    _  _, [x, y]) -> x ++ y
          )

swap = fold (\ s ss -> case s of
                         App _ _ -> make s $ reverse ss
                         _       -> make s ss
            )

rename q = fold (\s ss -> case s of
                            Var    s   -> Var $ q s
                            Lambda s e -> make (Lambda (q s) e) ss
                            _          -> make s ss
              )
