import "examples/rules/arrays.hs";
import "examples/rules/sugar.hs";
import "examples/rules/lte.hs";
import "examples/fin.hs";

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

bool_to_prop = \ (x : Bool) -> elim Bool (\ (_ : Bool) -> Set) Falsity Truth x;

lte_prop = \ (x : Nat) (y : Nat) -> bool_to_prop (lte x y);
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

f =
    \ (p : forall (_ : Nat) . Bool) (v : Nat) (vs : List Nat) (b : Bool) ->
        elim Bool
            (\ (_ : Bool) -> List Nat)
            (filter Nat p vs)
            (cons Nat v (filter Nat p vs))
            b;

x1 = filter Nat $p (cons Nat $v $vs);
x2 = f $p $v $vs ($p $v);

test1 : Id (List Nat) x1 x2;
test1 = Refl (List Nat) x1;

-- such an trivial lemma!
lte1 : forall (x : Nat) . lte_prop x x;
lte1 = \ (x : Nat) ->
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
            (\ (b : Bool) -> lte_prop (length Nat (f p v vs b)) (length Nat (cons Nat v (filter Nat p vs))) )
            (lte_lemma5 (length Nat (filter Nat p vs)))
            (lte1 (length Nat (filter Nat p vs)))
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
                (\ (b : Bool) -> lte_prop (length Nat (f p v vs b)) (length Nat (cons Nat v vs)))
                (lte_tran
                    (length Nat (filter Nat p vs))
                    (length Nat vs)
                    (length Nat (cons Nat v vs))
                    qq
                    (lte_lemma5 (length Nat vs)))
                qq
                (p v))
        xs;

qsort1 =
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
                            -- len_prop : lte_prop (length Nat vs) n1
                            (len_prop : lte_prop (length Nat (cons Nat v vs)) (Succ n1)) ->
                                rec
                                    (filter Nat $p vs)
                                    (lte_tran
                                        (length Nat (filter Nat $p vs))
                                        (length Nat vs)
                                        n1
                                        (filter_lemma2 $p vs)
                                        len_prop))
                        xs)
            n;
