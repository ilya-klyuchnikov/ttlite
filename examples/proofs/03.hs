import "examples/list.hs";
import "examples/eq.hs";

-- http://hosc.appspot.com/test?key=agRob3NjcjELEgZBdXRob3IiGmlseWEua2x5dWNobmlrb3ZAZ21haWwuY29tDAsSBFRlc3QYuRcM
-- Associativity of list concatenation

$A :: Set;
$x :: List $A;
$y :: List $A;
$z :: List $A;

e1 = (append $A $x (append $A $y $z));
e2 = (append $A (append $A $x $y) $z);

(res1, proof1) = sc e1;
(res2, proof2) = sc e2;

-- check that t1 and t2 are supercompiled into the same expression
eq_res1_res2 :: Eq (List $A) res1 res2;
eq_res1_res2 = Refl (List $A) res1;
-- deriving equality
eq_e1_e2 :: Eq (List $A) e1 e2;
eq_e1_e2 =
    proof_by_sc (List $A) e1 e2 res1 proof1 proof2;
