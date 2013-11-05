import examples/nat;
import examples/fin;

-- general structural recursion for natural numbers

n0 = Zero;
n1 = Succ n0;
n2 = Succ n1;
n3 = Succ n2;
n4 = Succ n3;
n5 = Succ n4;

fst =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> a) (\(x : a) (y : b) -> x) p;

snd =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> b) (\(x : a) (y : b) -> y) p;

-- type of the course of values
-- belowT A Z        = Truth;
-- belowT A (Succ n) = Product (belowNat p xs) (p xs);
belowT : forall (A: Set) (n: Nat) . Set;
belowT = \ (A: Set) (n: Nat) ->
  elim Nat (\ (_: Nat) -> Set) Truth (\ (_: Nat) (rec: Set) -> Product rec A) n;

-- value of the course of values
-- h p below Z       = Triv;
-- h p below (S n)  = Pair (h p xs) (below xs (h p xs))
belowV : forall
        (A: Set)
        (f: forall (n: Nat) (_: belowT A n) . A)
        (n: Nat) . belowT A n;
belowV = \ (A: Set) (f: forall (n: Nat) (_: belowT A n) . A) (n : Nat) ->
  elim Nat (belowT A)
    Triv
    (\ (n: Nat) (rec: belowT A n) -> Pair (Product (belowT A n) A) rec (f n rec))
    n;

natRec : forall
    (A: Set)
    (f: forall (n: Nat) (_: belowT A n) . A)
    (n: Nat) . A;
natRec = \ (A: Set) (f: forall (n: Nat) (_: belowT A n) . A) (n : Nat) ->
  f n (belowV A f n);

-- generic extractor of previous values
get : forall (A : Set) (i : Nat) (n : Nat) (bv : belowT A (plus (Succ i) n)) . A;
get = \ (A : Set) (i : Nat) (n : Nat) ->
        elim Nat (\ (i : Nat) -> forall (bv : belowT A (plus (Succ i) n)) . A)
            (\ (bv : belowT A (Succ n)) -> snd (belowT A n) A bv )
            (\ (i : Nat)
               (rec : forall (_ : belowT A (plus (Succ i) n)) . A)
               (bv : belowT A (plus (Succ (Succ i)) n)) ->
                    rec (fst (belowT A (plus (Succ i) n)) A bv))
            i;

evenF : forall (n: Nat) (_: belowT Bool n) . Bool;
evenF = \ (n : Nat) ->
        elim Nat (\ (n : Nat) -> forall (_: belowT Bool n) . Bool)
        (\ (_ : Truth) -> True)
        (\ (n : Nat) (_ : forall (_: belowT Bool n) . Bool) ->
            elim Nat (\ (n : Nat) -> forall (_: belowT Bool (plus n1 n)) . Bool)
                (\ (_ : belowT Bool (Succ Zero)) -> False)
                (\ (n : Nat) (_ : forall (_: belowT Bool (Succ n)) . Bool) (bv2 : belowT Bool (plus n2 n)) -> get Bool n1 n bv2)
                n)
        n;

oddF : forall (n: Nat) (_: belowT Bool n) . Bool;
oddF = \ (n : Nat) ->
        elim Nat (\ (n : Nat) -> forall (_: belowT Bool n) . Bool)
        (\ (_ : Truth) -> False)
        (\ (n : Nat) (_ : forall (_: belowT Bool n) . Bool) ->
            elim Nat (\ (n : Nat) -> forall (_: belowT Bool (plus n1 n)) . Bool)
                (\ (_ : belowT Bool (Succ Zero)) -> True)
                (\ (n : Nat) (_ : forall (_: belowT Bool (Succ n)) . Bool) (bv2 : belowT Bool (plus n2 n)) -> get Bool n1 n bv2)
                n)
        n;

even = natRec Bool evenF;
odd  = natRec Bool oddF;

$n : Nat;

ez = or (even n0) (odd n0);
es = or (even n1) (odd n1);

e0 = or (even $n) (odd $n);
e1 = or (even (Succ (Succ $n))) (odd (Succ (Succ $n)));

-- it is proved just by normalization!
d : Id Bool e0 e1;
d = Refl Bool e0;

-- rec0
-- rec0 z f 0     = z
-- rec0 z f (S n) = f n (rec0 z f n)

--
-- rec1
-- rec1 z0 z1 f 0         = z0
-- rec1 z0 z1 f 1         = z1
-- rec1 z0 z1 f (S (S n)) = f n (rec1 z0 z1 f (S n)) (rec1 z0 z1 f (S n))