module Chapter2
  
import Data.Vect
  
--------------
--- Warmup ---
--------------

allLengths : List String -> List Nat
allLengths [] = []
allLengths (x :: xs) = length x :: allLengths xs
  
xor : Bool -> Bool -> Bool
xor False y = y
xor True y = not y

mutual
  isEven : Nat -> Bool
  isEven Z = True
  isEven (S k) = isOdd k
  
  isOdd : Nat -> Bool
  isOdd Z = False
  isOdd (S k) = isEven k
  
  
fourInts : Vect 4 Int
fourInts = [0,1,2,3]

sixInts : Vect 6 Int
sixInts = [4,5,6,7,8,9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts
  
allLengths' : Vect n String -> Vect n Nat
allLengths' [] = []
allLengths' (x :: xs) = length x :: allLengths' xs

insert : Ord elem => (x : elem) -> (xsSorted : Vect len elem) -> Vect (S len) elem
insert x [] = pure x
insert x (y :: xs) = 
  case x < y of
    False => y :: insert x xs
    True => x :: y :: xs

insSort : Ord elem => Vect n elem -> Vect n elem
insSort [] = []
insSort (x :: xs) =
  let xsSorted = insSort xs
  in insert x xsSorted
  
  
length' : List a -> Nat
length' [] = 0
length' (x :: xs) = 1 + length' xs

reverse' : List a -> List a
reverse' [] = []
reverse' (x :: xs) = reverse' xs ++ pure x

map' : (a -> b) -> List a -> List b
map' f [] = []
map' f (x :: xs) = f x :: map' f xs

mapV' : (a -> b) -> Vect n a -> Vect n b
mapV' f [] = []
mapV' f (x :: xs) = f x :: mapV' f xs
  
-------------------------
--- Matrix Operations ---
-------------------------

createEmpties : Vect n (Vect 0 elem)
createEmpties = replicate _ []

transposeHelper : (x : Vect n elem) -> (xsTrans : Vect n (Vect k elem)) -> Vect n (Vect (S k) elem)
transposeHelper [] [] = []
transposeHelper (x :: xs) (y :: ys) = (x :: y) :: transposeHelper xs ys

transposeMatrix : Vect m (Vect n elem) -> Vect n (Vect m elem)
transposeMatrix [] = createEmpties
transposeMatrix (x :: xs) =
  let transposed = transposeMatrix xs
  in (zipWith (::) x transposed)


addVects : Num numType => Vect len numType -> Vect len numType -> Vect len numType
addVects [] _ = []
addVects (x :: xs) (y :: ys) = x + y :: addVects xs ys

addMatrix : Num numType =>
  Vect rows (Vect cols numType) -> 
  Vect rows (Vect cols numType) -> 
  Vect rows (Vect cols numType)
addMatrix [] [] = []
addMatrix (x :: xs) (y :: ys) =
  let summed = addMatrix xs ys
  in addVects x y :: summed
  -- zipWith (+) x y :: summed

infixr 7 ..  
(..) : (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(..) f g x y = f (g x y)

dotProduct : Num numType => Vect n numType -> Vect n numType -> numType
dotProduct = foldr (+) 0 .. zipWith (*)

multMatrix : Num numType => 
  Vect n (Vect m numType) ->
  Vect m (Vect p numType) -> 
  Vect n (Vect p numType)
multMatrix xs ys = 
  let ys' = transposeMatrix ys
  in map (\x => map (dotProduct x) ys') xs

a : Vect 2 (Vect 3 Integer)
a = [[1,2,3], [4,5,6]]

b : Vect 3 ( Vect 2 Integer)
b = [[7, 8], [9, 10], [11,12]]

b' : Vect 2 (Vect 3 Integer)
b' = [[7,9,11], [8,10,12]]

append' : Vect n elem -> Vect m elem -> Vect (n + m) elem
append' [] ys = ys
append' (x :: xs) ys = x :: append' xs ys 

--append' : (elem : Type) -> (n : Nat) -> (m : Nat) ->  Vect n elem -> Vect m elem -> Vect (n + m) elem
--append' elem Z m [] ys = ys
--append' elem (S k) m (x :: xs) ys = x :: append' elem k m xs ys 

len : Vect n elem -> Nat
len {n} xs = n

  
