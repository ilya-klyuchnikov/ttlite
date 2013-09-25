import "examples/rules/arrays.hs";
import "examples/rules/sugar.hs";

$A : Set;
$f : forall (_ : $A) (_ : $A) . $A;

-- monoid properties
$z : $A;
$assoc : forall (x : $A) (y : $A) (z : $A) . Id $A ($f x ($f y z)) ($f ($f x y) z);
$lid : forall (x : $A) . Id $A ($f $z x) x;
$rid : forall (x : $A) . Id $A ($f x $z) x;

$ys : List $A;

conj =
    \ (xs : List $A) .
        Id $A (foldr $A $A $z $f (append $A xs $ys)) ($f (foldr $A $A $z $f xs) (foldr $A $A $z $f $ys));


-- base case xs == nil
-- note we use left identity to prove base case!
e1 = foldr $A $A $z $f (append $A (nil $A) $ys);
e2 = $f (foldr $A $A $z $f (nil $A)) (foldr $A $A $z $f $ys);

id_e2_e1 : Id $A e2 e1;
id_e2_e1 = $lid (foldr $A $A $z $f $ys);

id_e1_e2 : Id $A e1 e2;
id_e1_e2 = symm $A e2 e1 id_e2_e1;

baseCase : conj (nil $A);
baseCase = id_e1_e2;

-- now we need a lemma
-- note that use associativity property to prove it!
lemma =
    forall (x : $A) (xs : List $A) .
        Id $A
            ($f x ($f (foldr $A $A $z $f xs) (foldr $A $A $z $f $ys)))
            ($f (foldr $A $A $z $f (cons $A x xs)) (foldr $A $A $z $f $ys));

lemma_proof : lemma;
lemma_proof =
    \ (x : $A) (xs : List $A) ->
        $assoc x (foldr $A $A $z $f xs) (foldr $A $A $z $f $ys);


-- inductive case

indCase : forall (x : $A) (xs : List $A) (hyp : conj xs) . conj (cons $A x xs);
indCase =
    \ (x : $A) (xs : List $A) (hyp : conj xs) ->
        tran $A
            ($f x (foldr $A $A $z $f (append $A xs $ys)))
            ($f x ($f (foldr $A $A $z $f xs) (foldr $A $A $z $f $ys)))
            ($f (foldr $A $A $z $f (cons $A x xs)) (foldr $A $A $z $f $ys))
            (cong1 $A $A ($f x) (foldr $A $A $z $f (append $A xs $ys)) ($f (foldr $A $A $z $f xs) (foldr $A $A $z $f $ys)) hyp)
            (lemma_proof x xs);

proof : forall (xs : List $A) . conj xs;
proof = \ (xs : List $A) -> elim (List $A) conj baseCase indCase xs;
