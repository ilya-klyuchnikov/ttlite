import examples/rules/arrays;
import examples/rules/sugar;
import examples/rules/lte;
import examples/fin;
import examples/misc/logic;
import examples/product;

filter : forall (A : Set) (f : forall (_ : A) . Bool) (_ : List A) . List A;
filter = \ (A : Set) (f : forall (_ : A) . Bool) (xs : List A) ->
    elim (List A)
        (\ (_ : List A) -> List A)
        (nil A)
        (\ (v : A) (vs : List A) (rec : List A) -> elim Bool (\ (_ : Bool) -> List A) rec (cons A v rec) (f v) )
        xs;

gt = \ (x : Nat) ->
    elim Nat
        (\ (_ : Nat) -> forall (_ : Nat) . Bool)
        (\ (_ : Nat) -> False)
        (\ (x1 : Nat) (rec : forall (_ : Nat) . Bool) (y : Nat) ->
             elim Nat (\ (_ : Nat) -> Bool) True (\ (y1 : Nat) (_ : Bool) -> rec y1) y)
        x;


n0 = Zero;
n1 = Succ n0;
n2 = Succ n1;
n3 = Succ n2;

test_lte = \ (x : Nat) (y : Nat) (expected: Bool) (proof : Id Bool (lte x y) expected) -> Triv;
test_gt  = \ (x : Nat) (y : Nat) (expected: Bool) (proof : Id Bool (gt  x y) expected) -> Triv;

-- unit testing happens in compile time!
test_lte n0 n0 True (Refl Bool True);
test_gt n0 n0 False (Refl Bool False);
test_lte n1 n0 False (Refl Bool False);
test_gt n1 n0 True (Refl Bool True);

--lte_prop = \ (x : Nat) (y : Nat) -> bool_to_prop (lte x y);
gt_prop  = \ (x : Nat) (y : Nat) -> bool_to_prop (gt  x y);

--$qsort1 : (∀n:N).(∀l:[N]).((#l ≤ n) ⇒ [N])
$qsort1 : forall (n : Nat) (xs : List Nat) (_ : lte_prop (length Nat xs) n) . List Nat;

$v : Nat;
$vs : List Nat;
$p : forall (_ : Nat) . Bool;

$xs : List Nat;

e1 = filter Nat $p (cons Nat $v $vs);
e2 =
    elim Bool
        (\ (_ : Bool) -> List Nat)
        (filter Nat $p $vs)
        (cons Nat $v (filter Nat $p $vs))
        ($p $v);

test : Id (List Nat) e1 e2;
test = Refl (List Nat) e1;

f1 =
    \ (p : forall (_ : Nat) . Bool) (v : Nat) (vs : List Nat) (b : Bool) ->
        elim Bool
            (\ (_ : Bool) -> List Nat)
            (filter Nat p vs)
            (cons Nat v (filter Nat p vs))
            b;

x1 = filter Nat $p (cons Nat $v $vs);
x2 = f1 $p $v $vs ($p $v);

test1 : Id (List Nat) x1 x2;
test1 = Refl (List Nat) x1;

-- such an trivial lemma!
lte_refl : forall (x : Nat) . lte_prop x x;
lte_refl = \ (x : Nat) ->
    elim Nat
        (\ (x : Nat) -> lte_prop x x)
        Triv
        ( \ (x : Nat) (rec : lte_prop x x) -> rec)
        x;

filter_lemma1 : forall (p : forall (_ : Nat) . Bool) (v : Nat) (vs : List Nat) .
            lte_prop (length Nat (filter Nat p (cons Nat v vs))) (length Nat (cons Nat v (filter Nat p vs)));

filter_lemma1 =
    \ (p : forall (_ : Nat) . Bool) (v : Nat) (vs : List Nat) ->
        elim Bool
            (\ (b : Bool) -> lte_prop (length Nat (f1 p v vs b)) (length Nat (cons Nat v (filter Nat p vs))) )
            (lte_lemma5 (length Nat (filter Nat p vs)))
            (lte_refl (length Nat (filter Nat p vs)))
            (p v);

filter_lemma2 :
    forall (p : forall (_ : Nat) . Bool) (xs : List Nat) .
        lte_prop (length Nat (filter Nat p xs)) (length Nat xs);

filter_lemma2 =
    \ (p : forall (_ : Nat) . Bool) (xs : List Nat) ->
    elim (List Nat)
        (\ (xs : List Nat) -> lte_prop (length Nat (filter Nat p xs)) (length Nat xs))
        -- xs = []
        Triv
        -- xs = v:vs
        (\ (v : Nat) (vs : List Nat)
            (qq : lte_prop (length Nat (filter Nat p vs)) (length Nat vs)) ->
            elim Bool
                (\ (b : Bool) -> lte_prop (length Nat (f1 p v vs b)) (length Nat (cons Nat v vs)))
                (lte_tran
                    (length Nat (filter Nat p vs))
                    (length Nat vs)
                    (length Nat (cons Nat v vs))
                    qq
                    (lte_lemma5 (length Nat vs)))
                qq
                (p v))
        xs;

lte_p = \ (n : Nat) (m : Nat) -> lte m n;
gt_p = \ (n : Nat) (m : Nat) -> gt m n;

qsort_aux : forall (n : Nat) (xs : List Nat) (_ : lte_prop (length Nat xs) n) . List Nat;
qsort_aux =
    \ (n : Nat) ->
        elim Nat
            (\ (k : Nat) -> forall (xs : List Nat) (_ : lte_prop (length Nat xs) k) . List Nat )
            -- n = 0
            (\ (xs : List Nat) ->
                elim (List Nat)
                    (\ (xs : List Nat) -> forall (_ : lte_prop (length Nat xs) Zero) . List Nat)
                    -- xs == [] , the result is []
                    (\ (_ : lte_prop (length Nat (nil Nat)) Zero) -> nil Nat)
                    -- xs = v : vs , impossible case, the result is via abort
                    (\ (v : Nat) (vs : List Nat)
                        (_ : forall (_ : lte_prop (length Nat vs) Zero) . List Nat)
                        (prop : lte_prop (length Nat (cons Nat v vs)) Zero) -> abort (List Nat) prop)
                    xs
                )
            -- n = 1 + n1
            (\ (n1 : Nat)
               (rec : forall (xs : List Nat) (_ : lte_prop (length Nat xs) n1) . List Nat)
               (xs : List Nat) ->
                    elim (List Nat)
                        (\ (xs : List Nat) -> forall (_ : lte_prop (length Nat xs) (Succ n1)) . List Nat)
                        -- xs == [] , the result is []
                        (\ (_ : lte_prop (length Nat (nil Nat)) (Succ n1)) -> nil Nat)
                        -- xs = v : vs
                        (\ (v : Nat)
                            (vs : List Nat)
                            (_ : forall (_ : lte_prop (length Nat vs) (Succ n1)) . List Nat)
                            (len_prop : lte_prop (length Nat (cons Nat v vs)) (Succ n1)) ->

                                append Nat
                                    -- qsort n (filter (lesseq a) x)
                                    (rec
                                        (filter Nat (lte_p v) vs)
                                        (lte_tran
                                            (length Nat (filter Nat (lte_p v) vs))
                                            (length Nat vs)
                                            n1
                                            (filter_lemma2 (lte_p v) vs)
                                            len_prop))

                                    (cons Nat v

                                    -- qsort n (filter (greater a) x) p2
                                    (rec
                                        (filter Nat (gt_p v) vs)
                                        (lte_tran
                                            (length Nat (filter Nat (gt_p v) vs))
                                            (length Nat vs)
                                            n1
                                            (filter_lemma2 (gt_p v) vs)
                                            len_prop))

                                    ))
                        xs)
            n;

qsort : forall (_ : List Nat) . List Nat;
qsort = \ (xs : List Nat) -> qsort_aux (length Nat xs) xs (lte_refl (length Nat xs));


t10     = qsort (cons Nat n3 (cons Nat n2 (cons Nat n1 (nil Nat))));
t10_ans = (cons Nat n1 (cons Nat n2 (cons Nat n3 (nil Nat))));

qsort_test10 : Id (List Nat) t10 t10_ans;
qsort_test10 = Refl (List Nat) t10_ans;

t20 = qsort (cons Nat n3 (cons Nat n2 (cons Nat n3 (nil Nat))));
t20_ans = (cons Nat n2 (cons Nat n3 (cons Nat n3 (nil Nat))));

qsort_test2 : Id (List Nat) t20 t20_ans;
qsort_test2 = Refl (List Nat) t20_ans;

---- AND NOW THE PROOF ----
-- if List is sorted then
-- sorted = Product Truth (Product Truth ...)
-- otherwise sorted has at least one Falsity.
sorted : forall (_ : List Nat) . Set;
sorted =
    \ (xs : List Nat) ->
        elim (List Nat)
            (\ (_ : List Nat) -> Set)
            Truth
            (\ (v : Nat) (vs : List Nat) (rec : Set) ->
                elim (List Nat)
                    (\ (_ : List Nat) -> Set)
                    Truth
                    (\ (v1 : Nat) (vs1 : List Nat) (_ : Set) -> Product (lte_prop v v1) rec)
                    vs)
            xs;

-- equality over natural numbers
eqn : forall (_ : Nat) (_ : Nat) . Bool;
eqn =
    \ (x : Nat) ->
        elim Nat (\ (_ : Nat) -> forall (_ : Nat) . Bool)
            -- x == 0
            (\ (y : Nat) ->
                elim Nat (\ (_ : Nat) -> Bool) True (\ (_ : Nat) (_ : Bool) -> False) y )
            -- x == S x1
            ( \ (x1 : Nat) (rec : forall (_ : Nat) . Bool) (y : Nat) ->
                elim Nat (\ (_ : Nat) -> Bool) False (\ (y1 : Nat) (_ : Bool) -> rec y1) y )
            x;

eqn_test1 : Id Bool True (eqn n1 n1);
eqn_test1 = Refl Bool True;

eqn_test2 : Id Bool False (eqn n1 n0);
eqn_test2 = Refl Bool False;

eqn_test3 : Id Bool False (eqn n0 n1);
eqn_test3 = Refl Bool False;

-- bool2n False = 0
-- bool2n True  = 1
bool2n = \ (b : Bool) -> elim Bool (\ (_ : Bool) -> Nat) n0 n1 b;

-- counts the occurrences of element in a given list
occs : forall (a : Nat) (xs : List Nat) . Nat;
occs =
    \ (a : Nat) (xs : List Nat) ->
        elim (List Nat)
            (\ (_ : List Nat) -> Nat)
            n0
            (\ (v : Nat) (_ : List Nat) (rec : Nat) -> plus (bool2n (eqn a v) ) rec )
            xs;

occs_test1 : Id Nat n0 (occs n0 (nil Nat));
occs_test1 = Refl Nat n0;

occs_test2 : Id Nat n1 (occs n0 (cons Nat n0 (nil Nat)));
occs_test2 = Refl Nat n1;

occs_test3 : Id Nat n2 (occs n0 (cons Nat n0 (cons Nat n0 (nil Nat))));
occs_test3 = Refl Nat n2;

occs_test4 : Id Nat n1 (occs n0 (cons Nat n1 (cons Nat n0 (nil Nat))));
occs_test4 = Refl Nat n1;

-- intensional member
mem : forall (_ : Nat) (xs : List Nat) . Set;
mem =
    \ (a : Nat) (xs : List Nat) ->
        elim (List Nat)
            (\ (_ : List Nat) -> Set)
            Falsity
            (\ (v : Nat) (_ : List Nat) (rec : Set) -> Sum (Id Nat a v) rec)
            xs;



perm : forall (_ : List Nat) (_ : List Nat) . Set;
perm = \ (xs : List Nat) (ys : List Nat) -> forall (a : Nat) . Id Nat (occs a xs) (occs a ys);


--
prop1 : forall (x : Nat) (y : Nat) (_ : Id Bool (lte x y) True) . lte_prop x y;
prop1 =
    \ (x : Nat) (y : Nat) ->
        elim Bool
            ( \ (b : Bool) -> forall (_ : Id Bool b True) . (bool_to_prop b))
            neq_f_t
            (\ (z : Id Bool True True) -> Triv)
            (lte x y);


prop2 : forall (x : Nat) (y : Nat) . Sum (Id Bool (lte x y) True) (Id Bool (gt x y) True);
prop2 =
    \ (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> forall (y : Nat) . Sum (Id Bool (lte x y) True) (Id Bool (gt x y) True) )
            -- x == 0
            (\ (y : Nat) ->
                InL
                    (Sum (Id Bool (lte n0 y) True) (Id Bool (gt n0 y) True))
                    (Refl Bool True) )
            -- x == S x1
            (\ (x1 : Nat)
               (rec : forall (y : Nat) . Sum (Id Bool (lte x1 y) True) (Id Bool (gt x1 y) True))
               (y : Nat) ->
                    elim Nat
                        ( \ (y: Nat) -> Sum (Id Bool (lte (Succ x1) y) True) (Id Bool (gt (Succ x1) y) True) )
                        -- y = 0
                        (InR
                            (Sum (Id Bool (lte (Succ x1) n0) True) (Id Bool (gt (Succ x1) n0) True))
                            (Refl Bool True) )
                        -- y == S y1
                        (\ (y1 : Nat) (_ : Sum (Id Bool (lte (Succ x1) y1) True) (Id Bool (gt (Succ x1) y1) True)) ->
                            rec y1)
                        y)
            x;


$prop3 : forall (x : Nat) (y : Nat) .
    NOT (
        Product
            (Id Bool (lte x y) True)
            (Id Bool (gt  x y) True));

{-
prop3 =
    \ (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> forall (y : Nat) . NOT (Product (Id Bool (lte x y) True) (Id Bool (gt  x y) True)) )
            -- x == 0
            (\ (y : Nat)
               (a : Product (Id Bool (lte n0 y) True) (Id Bool False True)) ->
                  neq_f_t (snd (Id Bool (lte n0 y) True) (Id Bool False True) a))
            -- x == S x1
            (\ (x1 : Nat)
               (rec : forall (y : Nat) . NOT (Product (Id Bool (lte x1 y) True) (Id Bool (gt x1 y) True)))
               (y : Nat) ->
                    elim Nat
                        (\ (y : Nat) -> NOT (Product (Id Bool (lte x1 y) True) (Id Bool (gt x1 y) True)))
                        -- y == 0
                        ( \ (a : Product (Id Bool (lte x1 n0) True) (Id Bool (gt x1 n0) True)) ->

                            )

            )



            x;
-}


