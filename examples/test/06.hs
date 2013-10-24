$n : Nat;

t = \ (m : Set) -> elim Nat (\ (_ : Nat) -> Nat) Zero (\ (_ : Nat) (rec : m) ->  Zero) $n;