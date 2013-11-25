open import ttlite

-- an example of possible translation from TT Lite to Agda
-- we turn TT Lite assumed variables into module parameters
module proof ($x : Nat) where

plus = elimNat (\ x -> Nat -> Nat) (\ x -> x) (\ x r y → succ (r y) )

p1 : Id Nat $x (plus zero $x) 
p1 = refl Nat $x

p2 : Id Nat $x (plus $x zero)
p2 = elimNat 
      (\ x -> Id Nat x (plus x zero)) 
      (refl Nat zero)
      ( \ x p -> cong1 Nat Nat succ x (plus x zero) p)
      $x
