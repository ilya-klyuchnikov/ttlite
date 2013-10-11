import "examples/id.hs";
import "examples/hosc/defs.hs";

-- map (fp (P f g)) (zip (P x y)) = zip (fp (P (map f) (map g)) (P x y))

$A : Set;
$B : Set;
$C : Set;
$D : Set;

ft = forall (_ : $A). $C;
fts = forall (_ : List $A). List $C;
gt = forall (_ : $B). $D;
gts = forall (_ : List $B). List $D;

$f : ft;
$g : gt;

$x : $A;
$y : $B;
$xs : List $A;
$ys : List $B;

-- this is an interesting example, small modification is needed.
e1 = map (Product $A $B) (Product $C $D) (fp $A $B $C $D (pair ft gt $f $g)) (zipp $A $B (pair (List $A) (List $B) $xs $ys));
e2 = zipp $C $D (fp (List $A) (List $B) (List $C) (List $D) (pair fts gts (map $A $C $f) (map $B $D $g)) (pair (List $A) (List $B) $xs $ys));



