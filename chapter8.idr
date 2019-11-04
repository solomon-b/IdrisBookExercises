module Chapter8

  import Data.Vect


-------------------
--- Section 8.1 ---
-------------------

data EqNat : (num1 : Nat) -> (num2 : Nat) -> Type where
  Same : (num : Nat) -> EqNat num num

data EqAll : a -> b -> Type where
  SameAll : (x : _) -> EqAll x x

--data Nat = Z | S nat

checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (EqNat num1 num2)
checkEqNat Z Z = Just (Same Z)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              (Just (Same z)) => Just (Same (S z))

checkEq : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
checkEq Z Z = Just Refl
checkEq Z (S k) = Nothing
checkEq (S k) Z = Nothing
checkEq (S k) (S j) = checkEq k j >>= \Refl => pure Refl
--checkEq (S k) (S j) = checkEq k j >>= \prf => pure (cong prf)


--exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
--exactLength {m} len input = case checkEq m len of
--                                 Nothing => Nothing
--                                 (Just (Same len)) => Just input

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEq m len of
                                 Nothing => Nothing
                                 (Just Refl) => pure input


---------------------
--- Exercises 8.1 ---
---------------------

sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons Refl = Refl

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
-- sameLists {xs = ys} {ys = ys} Refl Refl = Refl
sameLists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  SameThree : (x : _) -> ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (SameThree z) = SameThree (S z)


-------------------
--- Section 8.2 ---
-------------------


myReverse : Vect n elem -> Vect n elem
myReverse {n = Z} [] = []
myReverse {n = (S k)} (x :: xs) =
  let result = myReverse xs ++ [x]
  in rewrite plusCommutative 1 k in result

reverseProof : Vect (len + 1) elem -> Vect (S len) elem
reverseProof {len} xs = rewrite plusCommutative 1 len in xs

myReverse' : Vect n elem -> Vect n elem
myReverse' [] = []
myReverse' (x :: xs) = reverseProof (myReverse' xs ++ [x])

consPrf : Vect (S (left + right)) elem -> Vect (plus left (S right)) elem
consPrf {left} {right} xs = rewrite sym (plusSuccRightSucc left right) in xs

nilProof : Vect m elem -> Vect (plus m 0) elem
nilProof {m} xs = rewrite plusZeroRightNeutral m in xs

append : Vect n elem -> Vect m elem -> Vect (m + n) elem
append {m} [] ys = nilProof ys
append (x :: xs) ys = consPrf (x :: append xs ys)


--------------------
--- Exercises 8.2 --
--------------------

prf : ((k + m) = (m + k)) -> S (plus k m) = plus m (S k)
prf {k} {m} prf = rewrite sym (plusSuccRightSucc m k) in cong prf

myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = rewrite plusZeroRightNeutral m in Refl
myPlusCommutes (S k) m = prf (myPlusCommutes k m)

reverseProof_nil : Vect n a -> Vect (plus n 0) a
reverseProof_nil {n} xs = rewrite plusZeroRightNeutral n in xs

reverseProof_xs : Vect ((S n) + len) a -> Vect (plus n (S len)) a
reverseProof_xs {n} {len} xs = rewrite sym (plusSuccRightSucc n len) in xs

myNewReverse : Vect n a -> Vect n a
myNewReverse xs = reverse' [] xs
  where
    reverse' : Vect n a -> Vect m a -> Vect (n+m) a
    reverse' acc [] = reverseProof_nil acc
    reverse' acc (x :: xs) = reverseProof_xs (reverse' (x :: acc) xs)


-------------------
--- Section 8.3 ---
-------------------

--data Void : Type where

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

valueNotSuc : (x : Nat) -> x = S x -> Void
valueNotSuc _ Refl impossible

sucNotZero : (S k = 0) -> Void
sucNotZero Refl impossible

zeroNotSuc : (0 = S k) -> Void
zeroNotSuc Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat' : (num1 : Nat) -> (num2 : Nat) -> Dec (num1 = num2)
checkEqNat' Z Z = Yes Refl
checkEqNat' Z (S k) = No zeroNotSuc
checkEqNat' (S k) Z = No sucNotZero
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               (Yes prf) => Yes (cong prf)
                               (No contra) => No (noRec contra)

-- Exercises


data Vect' : Nat -> Type -> Type where
  Nil : Vect' Z a
  (::) : a -> Vect' n a -> Vect' (S n) a

headUnequal : DecEq a => {xs : Vect' n a} -> {ys : Vect' n a}
           -> (contra : (x = y) -> Void) -> (x :: xs) = (y :: ys) -> Void
headUnequal contra Refl = contra Refl

tailUnequal : DecEq a => {xs : Vect' n a} -> {ys : Vect' n a}
           -> (contra : (xs = ys) -> Void) -> (x :: xs) = (y :: ys) -> Void
tailUnequal contra Refl = contra Refl

DecEq a => DecEq (Vect' n a) where
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) =
    case decEq x y of
      (No contra) => No (headUnequal contra)
      (Yes Refl) =>
        case decEq xs ys of
          (No contra) => No (tailUnequal contra)
          (Yes Refl) => Yes Refl

testVectEqual : DecEq a => (xs : Vect' n a) -> (ys : Vect' n a) -> Dec (xs = ys)
testVectEqual xs ys = decEq xs ys
--- Notes ---
{-
foo : {pf : Nat} -> Nat
foo {pf} = pf

example' : (x : Nat) -> x = x
example' rf  = Refl {x=foo}

--example : Nat -> Nat
--example pf  = foo


--example'' : (x : Nat) -> (y : Nat) -> x = y
--example'' r1 r2 = Refl {x=foo}


 So in:
```example' : (x : Nat) -> x = x
example' pf  = Refl {x=foo}```
we are given `pf : Nat` and we need a proof that `pf = pf`
We further tell the type-checker to use Refl, and pass in `foo` as argument, so this means that
the type of `Refl {x=foo}`, which is `foo = foo` should match that type `pf = pf`.
This means that (`foo`, `pf`) are the same _and_ have the same type.
Because `foo` has an implicit argument, we have two cases:
(a) `foo` is not applied. But then its type `{qf : Nat} -> Nat` should be the same type as `Nat`, and that's just not true.
(b) `foo` is applied to some implicit argument, let's say `foo {pf=qf}`.
Now this means that `foo {pf=qf}` and `pf` are the same (and have the same type).
Since `foo {pf=qf}` is something the type-checker can reduce, it does so, and reduces `foo {pf=qf}` to `qf`.
So we now know that `qf` and `pf` are the same, which means that we worked out which argument we need to pass to `foo`: it is `pf`, i.e., we pass to `foo` the argument `pf=pf`, and so we pass to `Refl` the argument `x = foo {pf=pf}` (edited) 

(let me know when you've worked your way through this, or if you're stuck --- I know it's a mouthful)
 
-}
 
