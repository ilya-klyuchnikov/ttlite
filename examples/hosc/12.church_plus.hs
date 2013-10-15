import "examples/nat.hs";
import "examples/id.hs";

-- unchurch (churchPlus (church x) (church y)) = nat_id (plus x y)

fn = forall (_ : Nat) . Nat;
churchNat = forall (_ : fn) (_ : Nat) . Nat;

church : forall (_ : Nat) . churchNat;
church = \(n : Nat) ->
    elim Nat
        (\ (_: Nat) -> churchNat)
        (\ (f : fn ) (n : Nat) -> n )
        (\ (_ : Nat) (rec : churchNat) (f : fn ) (n : Nat) -> f (rec f n))
        n;

unchurch : forall (_ : churchNat) . Nat;
unchurch = \ (cn : churchNat) -> cn (\ (x : Nat) -> Succ x) Zero;

churchPlus : forall (_ : churchNat) (_ : churchNat) . churchNat;
churchPlus = \(m: churchNat) (n : churchNat) (f : fn) (x : Nat) -> m f (n f x);

$x : Nat;
$y : Nat;

e1 = unchurch (churchPlus (church $x) (church $y));
e2 = nat_id (plus $x $y);

(r1, pr1) = sc e1;
(r2, pr2) = sc e2;

eq_r1_r2 : Id Nat r1 r2;
eq_r1_r2 = Refl Nat r1;

eq_e1_e2 : Id Nat e1 e2;
eq_e1_e2 = proof_by_sc Nat e1 e2 r1 pr1 pr2;
