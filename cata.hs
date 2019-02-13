--From :  https://www.schoolofhaskell.com/user/bartosz/understanding-algebras

{-# LANGUAGE DeriveFunctor #-}

data ExprF a = Num Int | Add a a | Mul a a deriving (Show, Functor)

data Fix f = Fx ( f (Fix f ))

type Expr = Fix ExprF

type Algebra f a = f a -> a

-- example F-Algebra

alg :: Algebra ExprF Int
alg (Num x) = x
alg (Add x y) = x + y
alg (Mul x y ) = x * y

type Expr_Init_Alg = Algebra ExprF (Fix ExprF)

ini :: Expr_Init_Alg -- ExprF (Fix Exprf) -> (Fix Exprf)
ini = Fx

unFix :: Fix f -> f (Fix f)
unFix (Fx x) = x

cata' :: Functor f => (f a -> a) -> (Fix f -> a)
cata' alg = alg . fmap (cata' alg) . unFix

eval = cata' alg

val = eval (Fx (Add (Fx (Num 7)) (Fx (Num 3))))
-- val = 10




-- how to define functions  on nat in this framework?
data NatF a = Z  | Suc a deriving (Functor,Show)

type Nat = Fix NatF

-- calculates  value  neval : Nat -> Int
nalg :: Algebra NatF Int
nalg (Z) = 0
nalg (Suc x) = 1 + x

neval = cata' nalg

-- f : Nat -> Int
-- f (x) = 2* x

nalg' :: Algebra NatF Int
nalg' (Z) = 0
nalg' (Suc x) = 2 + x

neval' = cata' nalg'

-- f : Nat -> Int
-- f (x) = 1 if even
-- f (x) = -1 if odd

eoalg :: Algebra NatF Int
eoalg (Z) = 1
eoalg (Suc x) = 0 - x

eoeval = cata' eoalg

-- 3 is odd so results in -1
val' = eoeval (Fx $ Suc (Fx $ Suc (Fx $ Suc (Fx Z))))



--Plus
plus :: Nat -> Nat -> Nat
plus n = cata' phi where
  phi Z = n
  phi (Suc m) = Suc n



