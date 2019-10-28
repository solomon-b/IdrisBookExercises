module Eq

occurences : Eq ty => (item : ty) -> (values : List ty) -> Nat
occurences item [] = 0
occurences item (value :: values) = 
  case value == item of
    False => occurences item values
    True  => 1 + occurences item values

data Matter = Solid | Liquid | Gas

Eq Matter where
  (==) Solid Liquid   = True
  (==) Liquid Liquid  = True
  (==) Gas Gas        = True
  (==) _ _            = False
  (/=) x y = not (x == y)

data Tree elem = Empty | Node (Tree elem) elem (Tree elem)

Eq a => Eq (Tree a) where
  (==) Empty Empty = True
  (==) (Node l x r) (Node l' y r') = l == l' && x == y && r == r'
  (==) _ _     = False

record Album where
  constructor MkAlbum
  artist : String
  title  : String
  year   : Integer

help : Album
help = MkAlbum "The Beatles" "Help" 1965

rubbersoul : Album
rubbersoul = MkAlbum "The Beatles" "Rubber Soul" 1965

clouds : Album
clouds = MkAlbum "Joni Mitchell" "Clouds" 1969

hunkydory : Album
hunkydory = MkAlbum "David Bowie" "Hunky Dory" 1973

heroes : Album
heroes = MkAlbum "David Bowie" "Heroes" 1977

collection : List Album
collection = [help, rubbersoul, clouds, hunkydory, heroes]

Show Album where
  show (MkAlbum artist title year)
  = title ++ " by " ++ artist ++ " (released " ++ show year ++ ")"
 
Eq Album where
  (==) (MkAlbum x y z) (MkAlbum x' y' z') = x == x' && y == y' && z == z'

Ord Album where
  compare (MkAlbum x y z) (MkAlbum x' y' z') = 
    case compare x x' of
      EQ => case compare z z' of
              EQ => compare y y'
              diff_year => diff_year
      diff_artist => diff_artist

data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

Eq Shape where
  (==) (Triangle x z) (Triangle x' z')   = x == x' && z == z'
  (==) (Rectangle x z) (Rectangle x' z') = x == x' && z == z'
  (==) (Circle x) (Circle x')            = x == x'
  (==) _ _                               = False

area : Shape -> Double
area (Triangle x y) = (x * y) / 2
area (Rectangle x y) = x * y
area (Circle r) = pi * r * r

Ord Shape where
  compare x y = compare (area x) (area y)

testShapes : List Shape
testShapes = [Circle 3, Triangle 3 9, Rectangle 2 6, Circle 4, Rectangle 2 7]

data Expr num = Val num
              | Add (Expr num) (Expr num)
              | Sub (Expr num) (Expr num)
              | Mul (Expr num) (Expr num)
              | Div (Expr num) (Expr num)
              | Abs (Expr num)
              | Mod (Expr num) (Expr num)

Num a => Num (Expr a) where
  (+) = Add
  (*) = Mul
  fromInteger = Val . fromInteger

Neg a => Neg (Expr a) where
  negate x = 0 - x
  (-) = Sub

Abs a => Abs (Expr a) where
  abs = Abs

Integral a => Integral (Expr a) where
  div = Div
  mod = Mod

Show a => Show (Expr a) where
  show (Val x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Abs x) = "|" ++ show x ++ "|"
  show (Mod x y) = "(" ++ show x ++ " % " ++ show y ++ ")"

eval : (Num a, Neg a, Integral a, Abs a) => Expr a -> a
eval (Val x) = x
eval (Add x y) = eval x + eval y
eval (Sub x y) = eval x - eval y
eval (Mul x y) = eval x * eval y
eval (Div x y) = eval x `div` eval y
eval (Mod x y) = eval x `mod` eval y
eval (Abs x)   = abs $ eval x

(Eq a, Abs a, Integral a, Neg a) => Eq (Expr a) where
  (==) x y = (eval x) == (eval y)

(Abs a, Integral a, Neg a) => Cast (Expr a) a where
  cast expr = eval expr

totalLen : Foldable t => t String -> Nat
totalLen xs = foldr (\str, acc => acc + length str) 0 xs

Functor Expr where
  map f (Val x) = Val (f x)
  map f (Add x y) = Add (map f x) (map f y)
  map f (Sub x y) = Sub (map f x) (map f y)
  map f (Mul x y) = Mul (map f x) (map f y)
  map f (Div x y) = Div (map f x) (map f y)
  map f (Abs x) = Abs (map f x)
  map f (Mod x y) =  Mod (map f x) (map f y)

data Vect : Nat -> Type -> Type where
  Nil : Vect Z type
  (::) : type -> Vect n type -> Vect (S n) type


Functor (Vect n) where
  map func [] = []
  map func (x :: xs) = func x :: map func xs

Foldable (Vect n) where
  foldr func init [] = init
  foldr func init (x :: xs) = x `func` foldr func init xs

zipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
zipWith f [] y = []
zipWith f (x :: xs) (y :: ys) = f x y :: zipWith f xs ys

Eq a => Eq (Vect n a) where
  (==) xs ys = let zs = zipWith (==) xs ys in foldr (\a, b => a && b) True zs
