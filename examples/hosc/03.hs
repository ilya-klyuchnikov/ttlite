import examples/id;
import examples/hosc/defs;

$A : Set;
$B : Set;
$f : forall (_ : $A). $B;
$xs : List $A;
$ys : List $A;

e1 = map $A $B $f (append $A $xs $ys);
e2 = append $B (map $A $B $f $xs) (map $A $B $f $ys);

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

eq_res1_res2 : Id (List $B) res1 res2;
eq_res1_res2 = Refl (List $B) res1;

eq_e1_e2 : Id (List $B) e1 e2;
eq_e1_e2 = proof_by_sc (List $B) e1 e2 res1 proof1 proof2;
