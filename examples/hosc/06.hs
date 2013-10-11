import "examples/id.hs";
import "examples/hosc/defs.hs";

$A : Set;

$xs : List $A;
$ys : List $A;
$zs : List $A;

e1 = rep $A (append $A $xs $ys) $zs;
e2 = compose (List $A) (List $A) (List $A) (rep $A $xs) (rep $A $ys) $zs;

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
eq_res1_res2 : Id (List $A) res1 res2;
eq_res1_res2 = Refl (List $A) res1;

eq_e1_e2 : Id (List $A) e1 e2;
eq_e1_e2 = proof_by_sc (List $A) e1 e2 res1 proof1 proof2;
