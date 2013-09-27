import "examples/rules/arrays.hs";
import "examples/rules/sugar.hs";
import "examples/fin.hs";

filter : forall (A : Set) (f : forall (_ : A) . Bool) (_ : List A) . List A;
filter = \ (A : Set) (f : forall (_ : A) . Bool) (xs : List A) ->
    elim (List A)
        (\ (_ : List A) -> List A)
        (nil A)
        (\ (v : A) (vs : List A) (rec : List A) -> elim Bool (\ (_ : Bool) -> List A) rec (cons A v rec) (f v) )
        xs;

lte = \ (x : Nat) ->
    elim Nat
        (\ (_ : Nat) -> forall (_ : Nat) . Bool)
        (\ (_ : Nat) -> True)
        (\ (x1 : Nat) (rec : forall (_ : Nat) . Bool) (y : Nat) ->
             elim Nat (\ (_ : Nat) -> Bool) False (\ (y1 : Nat) (_ : Bool) -> rec y1) y)
        x;

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

qsort1 =
    \ (n : Nat) ->
        elim Nat
            (\ (k : Nat) -> forall (xs : List Nat) (_ : lte_prop (length Nat xs) k) . List Nat )
            (\ (xs : List Nat) ->
                elim (List Nat)
                    (\ (xs : List Nat) -> forall (_ : lte_prop (length Nat xs) Zero) . List Nat)
                    (\ (_ : lte_prop (length Nat (nil Nat)) Zero) -> nil Nat)
                    (\ (v : Nat) (vs : List Nat)
                        (_ : forall (_ : lte_prop (length Nat vs) Zero) . List Nat)
                        (prop : lte_prop (length Nat (cons Nat v vs)) Zero) ->
                            abort (List Nat) prop)
                    xs
                )
            (\ (n1 : Nat)
               (rec : forall (xs : List Nat) (_ : lte_prop (length Nat xs) n1) . List Nat)
               (xs : List Nat) ->
                    elim (List Nat)
                        (\ (xs : List Nat) -> forall (_ : lte_prop (length Nat xs) (Succ n1)) . List Nat)
                        (\ (_ : lte_prop (length Nat (nil Nat)) (Succ n1)) -> nil Nat)
                        (\ (v : Nat)
                            (vs : List Nat)
                            (_ : forall (_ : lte_prop (length Nat vs) (Succ n1)) . List Nat)
                            (prop : lte_prop (length Nat (cons Nat v vs)) (Succ n1)) ->
                                           nil Nat
                                           )
                        xs)
            n;
