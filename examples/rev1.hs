import "examples/list.hs";
import "examples/id.hs";

$A :: Set;
$a :: $A; $b :: $A; $c :: $A;

$ys1 :: List $A;
$y1 :: $A;
$y2 :: $A;

ys1 = $ys1;
ys2 = Cons (List $A) $y1 $ys1;
ys3 = Cons (List $A) $y2 ys2;

append =
    \ (xs :: List a) (ys :: List a) ->
        elim
            (List $A)
            (\(_ :: List $A) -> List $A)
            ys
            (\ (v :: $A) (vs :: List $A) (w :: List $A) -> Cons (List $A) v w)
            xs;

nrev =
    \ (xs :: List $A) ->
        elim
            (List $A)
            (\(_ :: List $A) -> List $A)
            (Nil (List $A))
            (\ (v :: $A) (vs :: List $A) (rec :: List $A) -> append $A rec (Cons (List $A) v (Nil (List $A))))
            xs;

conf1 = append (nrev ys1) $xs;
conf2 = append (nrev ys2) $xs;

-- conf1
elim
    (List $A)
    (\ (a :: List $A) -> List $A)
    $xs
    (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
    (elim (List $A)
        (\ (a :: List $A) -> List $A)
        (Nil (List $A))
        (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) ->
            elim (List $A)
                (\ (d :: List $A) -> List $A)
                (Cons (List $A) a (Nil (List $A)))
                (\ (d :: $A) -> \ (e :: List $A) -> \ (f :: List $A) -> Cons (List $A) d f)
                c)
    $ys1);

$abs1 :: List $A;

-- conf2
elim
    (List $A)
    (\ (a :: List $A) -> List $A)
    $xs
    (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
    (elim (List $A)
        (\ (a :: List $A) -> List $A)
        (Cons (List $A) $y1 (Nil (List $A)))
        (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
        (elim (List $A)
            (\ (a :: List $A) -> List $A)
            (Nil (List $A))
            (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) ->
                elim (List $A)
                    (\ (d :: List $A) -> List $A)
                    (Cons (List $A) a (Nil (List $A)))
                    (\ (d :: $A) -> \ (e :: List $A) -> \ (f :: List $A) -> Cons (List $A) d f)
                    c)
        $ys1));

-- extracting rev $ys1

c1 =
elim
    (List $A)
    (\ (a :: List $A) -> List $A)
    $xs
    (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
    $abs1;

c2 = elim
    (List $A)
    (\ (a :: List $A) -> List $A)
    $xs
    (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
    (elim (List $A)
        (\ (a :: List $A) -> List $A)
        (Cons (List $A) $y1 (Nil (List $A)))
        (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
        $abs1);

(c2_sc, _) = sc c2;

cc1 =
elim (List $A)
    (\ (a :: List $A) -> List $A)
    (Cons (List $A) $y1 $xs)
    (\ (a :: $A) -> \ (b :: List $A) -> \ (c :: List $A) -> Cons (List $A) a c)
    $abs1;

-- now we can see that c2_sc is an instance of cc1 -- folding can be performed
p :: Id (List $A) c2_sc cc1;
p = Refl (List $A) cc1;

