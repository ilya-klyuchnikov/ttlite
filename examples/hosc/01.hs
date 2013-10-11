import "examples/id.hs";
import "examples/hosc/defs.hs";

-- compose (map f) unit = compose unit f
-- http://hosc.appspot.com/test?key=agRob3NjcjELEgZBdXRob3IiGmlseWEua2x5dWNobmlrb3ZAZ21haWwuY29tDAsSBFRlc3QYuxcM
-- we even do not need supercompilation here: normalization is enough

$A : Set;
$B : Set;
$f : forall (_ : $A). $B;
$x : $A;

e1 = compose $A $B (List $B) (unit $B) $f;
e2 = compose $A (List $A) (List $B) (map $A $B $f) (unit $A);

proof : Id (forall (_ : $A) . List $B) e1 e2;
proof = Refl (forall (_ : $A) . List $B) e1;
