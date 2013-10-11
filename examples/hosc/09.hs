import "examples/id.hs";
import "examples/hosc/defs.hs";

$A : Set;
$r : List $A;
$x:  $A;
$p: $A;
$ps : List $A;

e1 = append $A $r (cons $A $p $ps);
e2 =
    elim (List $A)
        (\(_: List $A) -> List $A)
        $ps
        (\(v : $A) (vs : List $A) (r : List $A) -> cons $A v r)
        (append $A $r (cons $A $p (nil $A)));

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

eq_res1_res2 : Id (List $A) res1 res2;
eq_res1_res2 = Refl (List $A) res1;

eq_e1_e2 : Id (List $A) e1 e2;
eq_e1_e2 = proof_by_sc (List $A) e1 e2 res1 proof1 proof2;
