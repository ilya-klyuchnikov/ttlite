import "examples/list.hs";

nrev =
    \ (xs : List a) ->
        elim
            (List a)
            (\(_ : List a) -> List a)
            (Nil (List a))
            (\ (v : a) (vs : List a) (rec : List a) -> append a rec (Cons (List a) v (Nil (List a))))
            xs;

cps_rev : forall (a : Set) (_ : List a) (_ : List a) . List a;
cps_rev =
    \ (a : Set) (xs : List a) ->
        elim
            (List a)
            (\ (_ : List a) -> forall (_ : List a) . List a)
            (\ (ys : List a) ->  ys)
            (\ (v : a) (vs : List a) (rec : forall (_ : List a) . List a) ->
                \ (ys : List a) -> rec (Cons (List a) v ys))
            xs;

$A : Set;
$a : $A; $b : $A; $c : $A;

xs = Cons (List $A) $a (Cons (List $A) $b (Cons (List $A) $c (Nil (List $A))));

xs1 = nrev $A xs;
xs2 = cps_rev $A xs (Nil (List $A));

$ys1 : List $A;
$y1 : $A;
$y2 : $A;

ys2 = Cons (List $A) $y1 $ys1;

ys3 = Cons (List $A) $y2 ys2;

