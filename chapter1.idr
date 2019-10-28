module Main


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
