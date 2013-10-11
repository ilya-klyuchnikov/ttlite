import "examples/id.hs";
import "examples/hosc/defs.hs";

-- `filter p (map f xs) = map f (filter (compose p f) xs)`

$A : Set;
$f : forall (_ : $A). $A;
$p : forall (_ : $A). Bool;
$xs : List $A;
$ys : List $A;

-- we need a generalization here!
e1 = filter $A $p (map $A $A $f $xs);
e2 = map $A $A $f (filter $A (compose $A $A Bool $p $f) $xs);

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
--eq_res1_res2 : Id (List $A) res1 res2;
--eq_res1_res2 = Refl (List $A) res1;
-- deriving equality
--eq_e1_e2 : Id (List $A) e1 e2;
--eq_e1_e2 =
--    proof_by_sc (List $A) e1 e2 res1 proof1 proof2;
