import "examples/core.hs";
import "examples/list.hs";
import "examples/eq.hs";

-- compose (map f) unit = compose unit f
-- http://hosc.appspot.com/test?key=agRob3NjcjELEgZBdXRob3IiGmlseWEua2x5dWNobmlrb3ZAZ21haWwuY29tDAsSBFRlc3QYuxcM
-- we even do not need supercompilation here: normalization is enough

$A :: Set;
$B :: Set;
$f :: forall (_ :: $A). $B;
$x :: $A;

e1 = comp $A $B (List $B) (unit $B) $f;
e2 = comp $A (List $A) (List $B) (map $A $B $f) (unit $A);

proof :: Eq (forall (_ :: $A) . List $B) e1 e2;
proof = Refl (forall (_ :: $A) . List $B) e1;
