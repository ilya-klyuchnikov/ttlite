import "examples/id.hs";

-- Succ x = Succ x

$x : Nat;
$y : Nat;
$z : Nat;

e1 = (Succ $x);
e2 = (Succ $x);
(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
eq_res1_res2 : Id Nat res1 res2;
eq_res1_res2 = Refl Nat res1;
-- deriving equality
eq_e1_e2 : Id Nat e1 e2;
eq_e1_e2 =
    proof_by_sc Nat e1 e2 res1 proof1 proof2;
