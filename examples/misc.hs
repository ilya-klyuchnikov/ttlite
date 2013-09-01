import "examples/product.hs";
import "examples/nat.hs";
import "examples/fin.hs";

pr1 :: forall (A :: Set) (B :: Set) (_ :: Product A B) . Product B A;
pr1 = (\ (A :: Set) (B :: Set) (p :: Product A B) -> Pair (Product B A) (snd A B p) (fst A B p));

-- Exercise 4.1
-- (A /\ B) /\ C => A /\ (B /\ C)
th2 =
    forall
        (A :: Set)
        (B :: Set)
        (C :: Set)
        ( _ :: Product (Product A B) C) .
            Product A (Product B C);

-- p1 = fst (Product A B) C p
-- a = fst A B p1 = fst A B (fst (Product A B) C p)
-- b = snd A B p1 = snd A B (fst (Product A B) C p)
-- c = snd (Product A B) C p
-- (b, c) = Pair B C b c = Pair B C (snd A B (fst (Product A B) C p)) (snd (Product A B) C p)
-- (a, (b, c)) = Pair A (Product B C) a (b, c) =
--   =  Pair A (Product B C) (fst A B (fst (Product A B) C p)) (Pair B C (snd A B (fst (Product A B) C p)) (snd (Product A B) C p))
pr2 :: th2;
pr2 =
    (\(A :: Set) (B :: Set) (C :: Set) (p :: Product (Product A B) C) ->
        Pair (Product A (Product B C))
            (fst A B (fst (Product A B) C p))
            (Pair (Product B C) (snd A B (fst (Product A B) C p)) (snd (Product A B) C p)));


even    = natFold Bool true not;
odd     = natFold Bool false not;
isZero  = natFold Bool true (\  (_ :: Bool) -> false);
isSucc  = natFold Bool false (\ (_ :: Bool) -> true);

length :: forall (A :: Set) (xs :: List A). Nat;
length =
    \ (A :: Set) (xs :: List A) ->
        elim (List A)
            (\ (xs :: List A) -> Nat)
            Zero
            (\ (x :: A) (xs :: List A) (len_xs :: Nat) -> Succ len_xs)
            xs;

isTrue :: forall (b :: Bool). Set;
isTrue =
    \ (b :: Bool) ->
        elim Bool (\ (_ :: Bool) -> Set) Void Unit b;


--less :: forall (x :: Nat) (y :: Nat) . Bool;
less =
    \ (x :: Nat) ->
        elim
            Nat
            ( \ (_ :: Nat) -> forall (_ :: Nat) . Bool)
            (\ (y:: Nat) ->
                elim
                    Nat
                    ( \ (_ :: Nat) -> Bool)
                    false
                    (\ (_ :: Nat) (_ :: Bool) -> true )
                    y)
            (\ (x1 :: Nat) (rec :: forall (_ :: Nat) . Bool) ->
                (\ (y:: Nat) ->
                    elim
                        Nat
                        ( \ (_ :: Nat) -> Bool)
                        false
                        (\ (y1 :: Nat) (_ :: Bool) -> rec y1)
                        y))
            x;

n1 = Succ Zero;
n2 = Succ n1;

p1 :: Eq Bool (less n1 n2) true;
p1 = Refl Bool true;

p2 :: Eq Bool (less n2 n1) false;
p2 = Refl Bool false;

--$lookup :: forall (A :: Set) (xs :: List A) (n :: Nat) (_ :: isTrue (less n (length A xs))) . A;

abort :: forall (A :: Set) (v :: Void) . A;
abort =
    \ (A :: Set) (v :: Void) ->
        elim Void (\ (_ :: Void) -> A) v;


nonEmpty :: forall (A :: Set) (xs :: List A). Set;
nonEmpty = \ (A :: Set) (xs :: List A) -> isTrue (less Zero (length A xs));

first :: forall (A :: Set) (xs :: List A) (contract :: nonEmpty A xs) . A;
first =
    \ (A :: Set) (xs :: List A) (contract :: nonEmpty A xs) ->
        elim
            (List A)
            (\ (xs :: List A) -> forall (_ :: nonEmpty A xs) . A)
            (\ (v :: Void) -> abort A v)
            (\ (h :: A) (t :: List A) (_ :: forall (_ :: nonEmpty A t) . A) (_ :: Unit) -> h)
            xs
            contract;

first Nat (Cons (List Nat) Zero (Nil (List Nat))) U;

