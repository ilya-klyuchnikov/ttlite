import "examples/id.hs";
import "examples/list.hs";

-- map f (append xs ys) = append (map f xs) (map f ys)

$A :: Set;
$B :: Set;
$f :: forall (_ :: $A). $B;
$xs :: List $A;
$ys :: List $A;

e1 = map $A $B $f (append $A $xs $ys);
e2 = append $B (map $A $B $f $xs) (map $A $B $f $ys);

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
eq_res1_res2 :: Id (List $B) res1 res2;
eq_res1_res2 = Refl (List $B) res1;
-- deriving equality
eq_e1_e2 :: Id (List $B) e1 e2;
eq_e1_e2 =
    proof_by_sc (List $B) e1 e2 res1 proof1 proof2;
