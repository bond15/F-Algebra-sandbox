{-# LANGUAGE DeriveFunctor #-}

-- from wiki.haskell.org/catamorphims

type Algebra f a = f a -> a

data Mu f = InF { outF :: f (Mu f)}

cata :: Functor f => Algebra f a -> Mu f -> a
cata f = f . fmap (cata f) . outF


----------Examples----------

-- functor for a string

data StrF x = Nil | Cons Char x deriving (Show,Functor)

type Str = Mu StrF

-- length of string

length' :: Str -> Int
length' = cata phi where
  phi (Cons a b ) = 1 + b
  phi (Nil) = 0

-- ex
val = length' (InF (Cons 'd' (InF (Cons 'a' (InF Nil ))))) -- = 2

-------------------------------------------------

-- functor for Nat

data NatF a = S a | Z deriving (Eq, Show, Functor)

type Nat = Mu NatF

three = (InF $ S (InF $ S (InF $ S (InF Z))))

five = (InF $ S (InF $ S (InF $ S (InF $ S (InF $ S (InF Z))))))

-- plus

plus :: Nat -> Nat -> Nat
plus n = cata phi where
  phi Z = n
  phi (S m) = s m


-- multiplication

times :: Nat -> Nat -> Nat
times n = cata phi where
  phi Z = z
  phi (S m) = plus n m


s :: Nat -> Nat
s = InF . S

z ::Nat
z = InF Z
  
-- to Int (for printing reasons)
toInt :: Nat -> Int
toInt  = cata phi where
  phi Z = 0
  phi (S n) = 1 + n
  

resultplus = toInt (plus three five)
resultmult = toInt( times three five)
