module TheDreamOfIdrisPartOne


--associative : (a : List Char) -> (b : List Char) -> (c : List Char) -> (a ++ b) ++ c = a ++ (b ++ c)
--associative [] b c = Refl
--associative (x :: xs) b c = cong (associative xs b c)

  --identityL : (a : Integer) -> 0 + a = a
  --identityL a = Refl


identityL : (a : Nat) -> 0 + a = a
identityL a = Refl

identityR : (a : Nat) -> a + 0 = a
identityR Z = Refl
identityR (S k) = cong (identityR k)

associative : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = (a + b) + c
associative Z b c = Refl
associative (S k) b c = cong (associative k b c)





--record Preorder where
--  constructor MkPreorder
--  set : Type
--  (<=) : set -> set -> Type
--  reflexivity : (a : set) -> a <= a
--  transitivity : (a, b, c : set) -> a <= b -> b <= c -> a <= c

data NatRel : (j : Nat) -> (k : Nat) -> Type where
  Zero : NatRel Z k
  Induct : NatRel j k -> NatRel (S j) (S k)


set : Type
set = Nat

test : NatRel 0 4
test = Zero

checkRel : (j : Nat) -> (k : Nat) -> NatRel j k
checkRel Z k = Zero
checkRel (S j) k = case checkRel j k of
                     Zero => ?zeroCase
                     (Induct x) => ?inductCase

--natPreorder : Preorder
--natPreorder = MkPreorder Nat rel ref trans
--  where
--    rel = ?rel
--    ref = ?ref
--    trans = ?trans

