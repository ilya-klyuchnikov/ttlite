import "examples/core.hs";
import "examples/id.hs";
import "examples/list.hs";

-- map (comp f g) xs = (comp (map f)(map g)) xs
-- http://hosc.appspot.com/test?key=agRob3NjcjELEgZBdXRob3IiGmlseWEua2x5dWNobmlrb3ZAZ21haWwuY29tDAsSBFRlc3QYvhcM
$A : Set;
$B : Set;
$C : Set;
$f : forall (_ : $B). $C;
$g : forall (_ : $A). $B;
$xs : List $A;

e1 = map $A $C (comp $A $B $C $f $g) $xs;
e2 = comp (List $A) (List $B) (List $C) (map $B $C $f) (map $A $B $g) $xs;

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
eq_res1_res2 : Id (List $C) res1 res2;
eq_res1_res2 = Refl (List $C) res1;
-- deriving equality
eq_e1_e2 : Id (List $C) e1 e2;
eq_e1_e2 =
    proof_by_sc (List $C) e1 e2 res1 proof1 proof2;

