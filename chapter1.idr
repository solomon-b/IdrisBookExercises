module Main

{-
import Data.Vect

f : Integer -> Integer -> Integer
f x y = x + y

main : IO ()
main = putStrLn "foo"

zip' : List a -> List b -> List (a, b)
zip' [] [] = []
zip' [] (x :: xs) = []
zip' (x :: xs) [] = []
zip' (x :: xs) (y :: ys) = (x, y) :: zip' xs ys

zip'' : Vect n a -> Vect n b -> Vect n (a,b)
zip'' [] ys = []
zip'' (x :: xs) (y :: ys) = ?zip''_rhs_1
-}


data List' a = Nil' | Con' a (List' a)

data List'' : Type -> Type where
  Nil'' : List'' a
  Cons'' : a -> List'' a -> List'' a

data Vect : Nat -> Type -> Type where
  Nill : Vect Z a
  Conss : a -> Vect n a -> Vect (S n) a

ourVect : Vect 0 Integer
ourVect = Nill

ourVect' : Vect 1 Integer
ourVect' = Conss 1 Nill

ourVect'' : Vect 2 Integer
ourVect'' = Conss 1 (Conss 2 Nill)

zip' : Vect n a -> Vect n b -> Vect n (a, b)
zip' Nill y = Nill
zip' (Conss x z) (Conss y w) = Conss (x, y) (zip' z w)
