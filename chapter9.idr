module Chapter9

import Data.Vect

-------------------
--- Section 9.1 ---
-------------------

data Elem' : a -> Vect k a -> Type where
  Here' : Elem' x (x :: xs)
  There' : (later : Elem' x xs) -> Elem' x (y :: xs)

oneInVector : Elem 1 [1,2,3]
oneInVector = Here

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

--removeElemBroke : DecEq a => (value : a) -> (xs : Vect (S n) a) -> Vect n a
--removeElemBroke value (x :: xs) = case decEq value x of
--                                       (Yes prf) => xs
--                                       (No contra) => x :: removeElemBroke value xs

removeElem : (value : a) -> (xs : Vect (S n) a) -> (cert : Elem value xs) -> Vect n a
removeElem value (value :: xs) Here = xs
removeElem {n = Z} value (x :: []) (There later) = absurd later
removeElem {n = (S k)} value (x :: xs) (There later) = x :: removeElem value xs later


removeElemAuto : (value : a) -> (xs : Vect (S n) a) -> {auto prf : Elem value xs} -> Vect n a
removeElemAuto x (x :: xs) {prf = Here} = xs
removeElemAuto {n = Z} value (x :: []) {prf = (There later)} = absurd later
removeElemAuto {n = (S k)} value (x :: xs) {prf = (There later)} = x :: removeElem value xs later


notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (x = value) -> Void) -> (notThere : Elem value xs -> Void) -> Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem' : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem' value [] = No notInNil
isElem' value (x :: xs) = case decEq x value of
                               (Yes Refl) => Yes Here
                               (No notHere) => case isElem value xs of
                                                    (Yes prf) => Yes (There prf)
                                                    (No notThere) => No (notInTail notHere notThere)

elem' : Eq ty => (value : ty) -> (xs : Vect n ty) -> Bool
elem' value [] = False
elem' value (x :: xs) = case x == value of
                            False => elem' value xs
                            True => True

---------------------
--- 9.1 Exercises ---
---------------------

data ListElem : a -> List a -> Type where
  ListHere : ListElem a (a :: xs)
  ListThere : (listLater : ListElem x xs) -> ListElem x (y :: xs)

maryInList : ListElem "Mary" ["Peter", "Paul", "Mary"]
maryInList = ListThere (ListThere ListHere)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (x :: xs) value

notInHead' : Last [] value -> Void
notInHead' LastOne impossible
notInHead' (LastCons _) impossible

notLast : (contra : (x = value) -> Void) -> Last [x] value -> Void
notLast contra LastOne = contra Refl
notLast _ (LastCons LastOne) impossible
notLast _ (LastCons (LastCons _)) impossible

notInnTail : (contra1 : Last xs value -> Void) -> (contra : (xs = []) -> Void) -> Last (x :: xs) value -> Void
notInnTail contra1 contra LastOne = contra Refl
notInnTail contra1 contra (LastCons prf) = contra1 prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInHead'
isLast (x :: xs) value = case decEq xs [] of
                              (Yes Refl) => case decEq x value of
                                                  (Yes Refl) => Yes LastOne
                                                  (No contra) => No (notLast contra)
                              (No contra) => case isLast xs value of
                                                   (Yes prf) => Yes (LastCons prf)
                                                   (No contra1) => No (notInnTail contra1 contra)



-------------------
--- Section 9.2 ---
-------------------


