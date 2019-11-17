module Chapter10

--------------------
--- Section 10.1 ---
--------------------

data ListLast : List a -> Type where
  Empty : ListLast []
  NonEmpty : (xs : List a) -> (x : a) -> ListLast (xs ++ [x])

describeHelper : (input : List Int) -> (form : ListLast input) -> String
describeHelper [] Empty = "Empty"
describeHelper (xs ++ [x]) (NonEmpty xs x) = "Non-empty, initial portion = " ++ show xs

listLast : (xs : List a) -> ListLast xs
listLast [] = Empty
listLast (x :: xs) = case listLast xs of
                          Empty => NonEmpty [] x
                          (NonEmpty xs' x') => NonEmpty (x :: xs') x'

describeListEnd : List Int -> String
describeListEnd xs = describeHelper xs (listLast xs)

describeListEnd' : List Int -> String
describeListEnd' input with (listLast input)
  describeListEnd' [] | Empty = "Empty"
  describeListEnd' (xs ++ [x]) | (NonEmpty xs x) = "Non-Empty, intial portion = " ++ show xs

myReverse : List a -> List a
myReverse xs with (listLast xs)
  myReverse [] | Empty = []
  myReverse (ys ++ [x]) | (NonEmpty ys x) = x :: myReverse ys

data SplitList : List a -> Type where
  SplitNil  : SplitList []
  SplitOne : SplitList [x]
  SplitPair   : (lefts : List a) -> (rights : List a) -> SplitList (lefts ++ rights)

total
splitList : (input : List a) -> SplitList input
splitList input = splitListHelp input input
  where
    splitListHelp : List a -> (input : List a) -> SplitList input
    splitListHelp _ [] = SplitNil
    splitListHelp _ [x] = SplitOne
    splitListHelp (_ :: _ :: counter) (item :: items) =
      case splitListHelp counter items of
        SplitNil => SplitOne
        SplitOne {x} => SplitPair [item] [x]
        SplitPair lefts rights => SplitPair (item :: lefts) rights
    splitListHelp _ items = SplitPair [] items

mergeSort : Ord a => List a -> List a
mergeSort xs with (splitList xs)
  mergeSort [] | SplitNil = []
  mergeSort [x] | SplitOne = [x]
  mergeSort (lefts ++ rights) | (SplitPair lefts rights) = merge (mergeSort lefts) (mergeSort rights)

--data SplitList' : List a -> Type where
--  EmptyL  : SplitList' []
--  SingleL : (x : a) -> SplitList' [x]
--  FullL   : (lefts : List a) -> (rights : List a) -> SplitList' (lefts ++ rights)
--
--splitList' : (xs : List a) -> SplitList' xs
--splitList' [] = EmptyL
--splitList' [x] = SingleL x
--splitList' (x :: xs) =
--  let half = length (x :: xs) `div` 2
--      (ys, zs) = splitAt half (x :: xs)
--  in FullL ys zs

----------------------
--- 10.1 Exercises ---
----------------------

data TakeN : List a -> Type where
  FewerN : TakeN xs
  ExactN : (n_xs : List a) -> TakeN (n_xs ++ rest)

takeN : (n : Nat) -> (xs : List a) -> TakeN xs
takeN Z xs = ExactN []
takeN (S k) [] = FewerN
takeN (S k) (x :: xs) =
  case takeN k xs of
    FewerN => FewerN
    (ExactN n_xs) => ExactN (x :: n_xs)

groupByN : (n : Nat) -> (xs : List a) -> List (List a)
groupByN n xs with (takeN n xs)
  groupByN n xs | FewerN = [xs]
  groupByN n (n_xs ++ rest) | (ExactN n_xs) = n_xs :: groupByN n rest

halves : List a -> (List a, List a)
halves xs = halvesHelper half xs
  where
    half = length xs `div` 2
    halvesHelper : (n : Nat) -> (ys : List a) -> (List a, List a)
    halvesHelper n ys with (takeN n ys)
      halvesHelper n ys | FewerN = ([], ys)
      halvesHelper n (n_xs ++ rest) | (ExactN n_xs) = (n_xs, rest)


--------------------
--- Section 10.2 ---
--------------------
