module Chapter8

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a


data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

sameS : (x : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = Same (S k)

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = checkEqNat k j >>= pure . sameS

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = checkEqNat m len >>= \(Same x) => Just input


-----------------
--- Exercises ---
-------------------

same_cons : (xs : List a) -> (ys : List a) -> xs = ys -> x :: xs = x :: ys
same_cons xs ys prf = cong prf

same_lists : (xs : List a) -> (ys : List a) -> x = y -> xs = ys -> x :: xs = y :: ys
same_lists {x = x} {y = x} ys ys Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  --SameThree : x -> ThreeEq x x x
  SameThree : a = b -> b = c -> ThreeEq a b c

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS x x x (SameThree Refl Refl) = SameThree Refl Refl
