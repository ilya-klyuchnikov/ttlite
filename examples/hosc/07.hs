import "examples/id.hs";
import "examples/hosc/defs.hs";

$A : Set;
$xs : List $A;

e1 = compose (List $A) (forall (_ : List $A) . List $A) (List $A) (abs $A (List $A)) (rep $A) $xs;
e2 = list_id $A $xs;

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

eq_res1_res2 : Id (List $A) res1 res2;
eq_res1_res2 = Refl (List $A) res1;

eq_e1_e2 : Id (List $A) e1 e2;
eq_e1_e2 = proof_by_sc (List $A) e1 e2 res1 proof1 proof2;
