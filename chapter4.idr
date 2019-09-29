module Chapter4
  
import Data.Vect

------------------------
--- Enumerated Types --- 
------------------------

data Direction = North | South | East | West
  
turnClockWise : Direction -> Direction
turnClockWise North = East
turnClockWise South = West
turnClockWise East = North
turnClockWise West = South


-------------------
--- Union Types ---
-------------------

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

area : Shape -> Double
area (Triangle x y) = 0.5 * x * y
area (Rectangle x y) = x * y
area (Circle x) = pi * x * x

  
-----------------------
--- Recursive Types ---
-----------------------

data Picture = Primitive Shape
             | Combine Picture Picture
             | Rotate Double Picture
             | Translate Double Double Picture
  
%name Shape shape, shape1, shape2
%name Picture pic, pic1, pic

rectangle : Picture
rectangle = Primitive $ Rectangle 20 10

circle : Picture
circle = Primitive $ Triangle 10 10

triangle : Picture
triangle = Primitive $ Circle 5

testPicture : Picture
testPicture = Combine (Translate 5 5 rectangle)
                      (Combine (Translate 35 5 circle)
                      (Translate 15 25 triangle))
                      
pictureArea : Picture -> Double
pictureArea (Primitive shape) = area shape
pictureArea (Combine pic pic1) = pictureArea pic + pictureArea pic1
pictureArea (Rotate x pic) = pictureArea pic
pictureArea (Translate x y pic) = pictureArea pic


---------------------
--- Generic Types ---
---------------------
  
data Maybe' a = Nothing' | Just' a

safeDivide : Double -> Double -> Maybe Double
safeDivide x y = if y == 0 then Nothing else Just (x / y)

data Tree elem = Empty | Node (Tree elem) elem (Tree elem)
  
%name Tree tree, tree1, tree2

insert : Ord elem => elem -> Tree elem -> Tree elem
insert x Empty = Node Empty x Empty
insert x (Node left val right) =
  case compare x val of
    LT => Node (insert x left) val right
    EQ => Node left val right
    GT => Node left val (insert x right)

data BSTree : Type -> Type where
  Empty' : Ord elem => BSTree elem
  Node'  : Ord elem => (left : BSTree elem) -> (val : elem) -> (right : BSTree elem) -> BSTree elem

insert' : elem -> BSTree elem -> BSTree elem
insert' x Empty' = Node' Empty' x Empty'
insert' x (Node' left val right) =
  case compare x val of
    LT => Node' (insert' x left) val right
    EQ => Node' left val right
    GT => Node' left val (insert' x right)


listToTree : Ord a => List a -> Tree a
listToTree = foldr insert Empty

treeFold : (a -> b -> b) -> b -> Tree a -> b
treeFold f b Empty = b
treeFold f b (Node left val right) =
  let b' = f val (treeFold f b right)
  in treeFold f b' left

treeToList : Ord a => Tree a -> List a
treeToList = treeFold (::) []

testCase : List Integer
testCase = [4,1,8,7,2,3,9,5,6]

data Expr = Lit Integer
          | Add Expr Expr
          | Sub Expr Expr
          | Mul Expr Expr
          | Div Expr Expr

eval : Expr -> Integer
eval (Lit x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y


maxMaybe : Ord a => Maybe a -> Maybe a -> Maybe a
maxMaybe Nothing Nothing = Nothing
maxMaybe Nothing (Just x) = Just x
maxMaybe (Just x) Nothing = Just x
maxMaybe (Just x) (Just y) = Just $ max x y

  
biggestTriangle : Picture -> Maybe Double
biggestTriangle (Primitive t@(Triangle _ _)) = Just (area t)
biggestTriangle (Primitive _) = Nothing
biggestTriangle (Combine pic pic1) = maxMaybe (biggestTriangle pic) (biggestTriangle pic1)
biggestTriangle (Rotate _ pic) = biggestTriangle pic
biggestTriangle (Translate _ _ pic) = biggestTriangle pic

testPic1 : Picture
testPic1 = Combine (Primitive (Triangle 2 3)) (Primitive (Triangle 2 4))

testPic2 : Picture
testPic2 = Combine (Primitive (Rectangle 1 3)) (Primitive (Circle 4))


-----------------------
--- Dependent Types ---
-----------------------

data PowerSource = Petrol | Pedal | Electric

data Vehicle : PowerSource -> Type where
  Bicycle : Vehicle Pedal
  Car : (fuel : Nat) -> Vehicle Petrol
  Bus : (fuel : Nat) -> Vehicle Petrol
  Motorcycle : (fuel : Nat) -> Vehicle Petrol
  Unicycle :  Vehicle Pedal
  ElectricCar : (fuel : Nat) -> Vehicle Electric

wheels : Vehicle power -> Nat
wheels Bicycle = 2
wheels (Car fuel) = 4
wheels (Bus fuel) = 4
wheels (Motorcycle fuel) = 2
wheels Unicycle = 1
wheels (ElectricCar fuel) = 4

refuel : Vehicle Petrol -> Vehicle Petrol
refuel (Car fuel) = Car 100
refuel (Bus fuel) = Bus 200
refuel (Motorcycle fuel) = Motorcycle 50
  
data Tree' : Nat -> Type -> Type where
  Leaf'   : Ord elem => Tree' Z elem
  Branch' : Ord elem => (left : Tree' n elem) -> elem -> (right : Tree' m elem) -> Tree' (S (n+m)) elem

--insert'' : elem -> Tree' n elem -> Tree' (S n) elem
--insert'' x Leaf' = Branch' Leaf' x Leaf'
--insert'' x (Branch' left val right) =
--  case compare x val of
--    LT => Branch' (insert'' x left) val right
--    EQ => Branch' left val right
--    GT => Branch' left val (insert'' x right)



tree : Tree' 1 Integer
tree = Branch' Leaf' 1 Leaf'

data Vect' : Nat -> Type -> Type where
  Nil  : Vect' Z a
  (::) : (x : a) -> Vect' k a -> Vect' (S k) a

append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

zip' : Vect n a -> Vect n b -> Vect n (a, b)
zip' [] y = []
zip' (x :: z) (y :: w) = (x, y) :: zip' z w

tryIndex : Integer -> Vect n a -> Maybe a
tryIndex {n} i xs = case integerToFin i n of
                         Nothing => Nothing
                         (Just idx) => Just (index idx xs)
            
vectTake : (n : Nat) -> Vect (n + m) a -> Vect n a
vectTake Z [] = []
vectTake Z (x :: xs) = []
vectTake (S k) (x :: xs) = x :: vectTake k xs
  
vectDrop : (n : Nat) -> Vect (n + m) a -> Vect m a
vectDrop Z xs = xs
vectDrop (S k) (x :: xs) = vectDrop k xs

vectTest : Vect 5 Int
vectTest = [1,2,3,4,5]
 
sumEntries' : Num a => Integer -> Vect n a -> Vect n a -> Maybe a
sumEntries' _ [] _ = Nothing
sumEntries' 0 (x :: xs) (y :: ys) = Just (x + y)
sumEntries' i (x :: xs) (y :: ys) = sumEntries' (i - 1) xs ys
        
sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = integerToFin pos n >>= \_ => sumEntries' pos xs ys
 
sumEntries1 : Num a => Maybe a
sumEntries1 = sumEntries 2 [1,2,3,4] [5,6,7,8]

sumEntries2 : Num a => Maybe a
sumEntries2 = sumEntries 4 [1,2,3,4] [5,6,7,8]
