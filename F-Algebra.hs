-- Allow derivation of Functor for data types
{-# LANGUAGE DeriveFunctor #-}



-- Functor

class Functor' f  where
    fmap' :: ( a -> b) -> f a -> f b

-- usage of Funtor on various data types

data Maybe' a = None | Some a deriving Show

instance Functor' Maybe' where
    fmap' f None = None
    fmap' f (Some x) = Some (f x)

-- given f: A -> B,   can construct a function from (Maybe' A) to (Maybe' B)

-- ex
{- dummy function

     f : Int -> Bool

      f _ = False
      f 7 = True

          concretely "let { g 7 = True ; g _ = False }

      then


      f'' : Maybe' A -> Maybe' B

     f'' = fmap' f


     such that


      f'' None => None
      f'' (Some 7) => (Some True)
      f'' (Some 9) => (Some False

-}


-- Another type, deriving Functor instead of hand tailoring definition

data T2 a = Nope | That a deriving (Functor,  Show)


-- Deriving a Functor for a Polymorphic Tree type

data Tre a = Leaf a | Node a (Tre a) (Tre a) deriving (Functor, Show)

{-  ex usage

     let { f 7 = True ;  f _  = False }

     f' = fmap f     // Tre type is an Instance of Functor and fmap is automatically derived

     f' (Node 9 (Leaf 7 ) (Leaf 8))  = >    (Node False (Leaf True ) (Leaf False))

-}




-- Using a simple expression tree

data ExprF a = Num a | Add a a | Mul a a deriving Show --(Functor, Show)


-- Essence of Evaluation / Understanding F Algebras tutorial

{-
   Claim:  split recursion scheme into 'top level evaluator'  = alg
                                                       and 'recursive evaluator' = eval

            both return values of type a
-}

--instance Functor ExprF where
 -- fmap eval (Num x) = (Num x)  -- Why identity here? instead of (Num (eval x))
  --fmap eval (Add left right) = (Add (eval left) (eval right))
  --fmap eval (Mul left right) = (Mul (eval left) (eval right))


f :: Int -> Bool
f 7 = True
f _ = False

--f' = fmap f  -- Functor from (f a) -> (f b)  where (a b : Type)


type Algebra f a = f a -> a

-- F-algebra with Expression Functor and Carrier Type Int

alg :: Algebra ExprF Int
--alg :: ExprF Int -> Int

alg (Num x)  = x
alg (Add x y ) = x + y
alg (Mul x y ) = x * y

 -- F-algebra with Expression Functor and Carrier Type String

--alg' :: Algebra ExprF String
--alg' :: ExprF String -> String

--alg' (Num x) = [chr (ord 'a' + x)]
--alg' (Add x y) = x ++ y
--alg' (Mul x y) = concat [[a,b] | a <- x, b <- y]


-- How to get the 'eval' function that computes the recursive terms?

-- Answer: Initial Algebras
