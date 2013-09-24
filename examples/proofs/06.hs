
f : forall (_ : Truth) . Bool;
f = \ (x : Truth) -> elim Truth (\ (_ : Truth) -> Bool) False x;

boolToNat : forall (_ : Bool) . Nat;
boolToNat =
    \ (n : Bool) ->
        elim Bool (\ (_ : Bool) -> Nat) Zero (Succ Zero) n;

$u : Truth;

e1 = boolToNat (f $u);
(r1, proof1) = sc e1;
