import "examples/id.hs";
import "examples/hosc/defs.hs";

$A : Set;
$B : Set;
$f : forall (_ : $A). $B;
$xs : List (List $A);

e1 = compose (List (List $A)) (List $A) (List $B) (map $A $B $f) (join $A) $xs;
e2 = compose (List (List $A)) (List (List $B)) (List $B) (join $B) (map (List $A) (List $B) (map $A $B $f)) $xs;

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

eq_res1_res2 : Id (List $B) res1 res2;
eq_res1_res2 = Refl (List $B) res1;

eq_e1_e2 : Id (List $B) e1 e2;
eq_e1_e2 = proof_by_sc (List $B) e1 e2 res1 proof1 proof2;
