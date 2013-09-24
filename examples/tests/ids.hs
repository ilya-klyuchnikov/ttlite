import "examples/core.hs";
import "examples/dproduct.hs";
import "examples/id.hs";
import "examples/fin.hs";
import "examples/list.hs";
import "examples/nat.hs";
import "examples/product.hs";
import "examples/sum.hs";

$A : Set;
$B : Set;
$F : forall (_ : $A) . Set;
$dp : exists (x : $A) . $F x;
$x : $A; $y : $A; $eq_x_y : Id $A $x $y;
$f1 : Truth; $f2 : Bool;
$xs : List $A;
$n1 : Nat; $n2 : Nat; $n3 : Nat;
$p : Product $A $B;
$s : Sum $A $B;

-- BUG??
(dp_sc, dp_proof) = sc (dproduct_id $A $F $dp);

eep = dpair (exists (x : Nat) . Id Nat x Zero) Zero (Refl Nat Zero);

(dpair_sc, dpair_proof) = sc (eep);

(_, _) = sc (eq_id $A $x $y $eq_x_y);


(refl_sc, refl_proof) = sc (Refl $A $x);


(_, _) = sc (unit_id $f1);

(_, _) = sc (bool_id $f2);

(_, _) = sc (list_id $A $xs);

(_, _) = sc (nat_id $n1);

(_, _) = sc (product_id $A $B $p);

(_, _) = sc (sum_id $A $B $s);

list_id_1 =
    \ (A : Set1) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List A)
            (Nil (List A))
            (\ (h : A) (t : List A) (rec : List A) -> Cons (List A) h rec)
            xs;

$A1 : Set1;
$xs1 : List $A1;

(_, _) = sc (list_id_1 $A1 $xs1);


(sum_sc, sum_proof) = sc (Sum (Sum Nat Nat) Nat);

(eq_sc, eq_proof) = sc (Id Nat (plus (plus $n1 $n2) $n3) (plus $n1 (plus $n2 $n3)));

(list_sc, list_proof) =
    sc (List (List Set));

(pr_sc, pr_proof) = sc (Product (Product Set Nat) Set);
