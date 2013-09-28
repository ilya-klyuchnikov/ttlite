plus : forall (x : Nat) (y : Nat). Nat;
plus =
    \ (x : Nat) (y : Nat) ->
        elim Nat
            (\ (_ : Nat) -> Nat )
            y
            ( \(x1 : Nat) (rec : Nat) -> Succ rec ) x;


lte = \ (x : Nat) ->
    elim Nat
        (\ (_ : Nat) -> forall (_ : Nat) . Bool)
        (\ (_ : Nat) -> True)
        (\ (x1 : Nat) (rec : forall (_ : Nat) . Bool) (y : Nat) ->
             elim Nat (\ (_ : Nat) -> Bool) False (\ (y1 : Nat) (_ : Bool) -> rec y1) y)
        x;

bool_to_prop = \ (x : Bool) -> elim Bool (\ (_ : Bool) -> Set) Falsity Truth x;

lte_prop = \ (x : Nat) (y : Nat) -> bool_to_prop (lte x y);

--    y <= 0  x <= y
-- --------------------
--        x <= 0
lemma1 :
    forall (y : Nat) (_ : lte_prop y Zero)
           (x : Nat) (_ : lte_prop x y) .
                lte_prop x Zero;
lemma1 =
    \ (y : Nat) ->
        elim Nat
            (\ (y : Nat) -> forall (_ : lte_prop y Zero) (x : Nat) (_ : lte_prop x y)  . lte_prop x Zero)
            (\ (_ : lte_prop Zero Zero) (x : Nat) (lte1 : lte_prop x Zero)  -> lte1)
            (\ (y1 : Nat)
               (rec : forall (_ : lte_prop y1 Zero) (x : Nat) (_ : lte_prop x y1) . lte_prop x Zero)
               (lte2 : lte_prop (Succ y1) Zero)
               (x : Nat)
               (lte1 : lte_prop x (Succ y1)) ->
                    elim Nat
                        (\ (x : Nat) -> lte_prop x Zero)
                        Triv
                        (\ (x : Nat) (_ : lte_prop x Zero) -> lte2)
                        x)
            y;


lemma2 : forall (x : Nat) (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero);
lemma2 =
    \ (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> forall (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero))
            (\ (_ : lte_prop (Succ Zero) Zero) -> Triv)
            (\ (x : Nat)
               (rec : forall (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero))
               (k : lte_prop (Succ (Succ x)) Zero) ->
                    k)
            x;


lemma3 : forall (y : Nat) (x : Nat) (_ : lte_prop x y) . lte_prop x (Succ y);
lemma3 =
    \ (y : Nat) ->
        elim Nat
            (\ (y : Nat) -> forall (x : Nat) (_ : lte_prop x y) . lte_prop x (Succ y))
            (\ (x : Nat)  ->
                elim Nat
                    (\ (x : Nat) -> forall (_ : lte_prop x Zero) . lte_prop x (Succ Zero))
                    (\ (_ : lte_prop Zero Zero) -> Triv)
                    ( \ (x : Nat)
                        (rec : forall (_ : lte_prop x Zero) . lte_prop x (Succ Zero))
                        (p : lte_prop (Succ x) Zero) ->
                            -- (?? : lte_prop (Succ x) (Succ Zero))
                            lemma2 x p)
                    x)
            ( \ (y : Nat)
                (rec : forall (x : Nat) (_ : lte_prop x y) . lte_prop x (Succ y))
                (x : Nat) ->
                    elim Nat
                        (\ (x : Nat) -> forall (_ : lte_prop x (Succ y)). lte_prop x (Succ (Succ y)))
                        (\ (_ : lte_prop Zero (Succ y)) -> Triv )
                        (\ (x : Nat)
                           (rec1 : forall (_ : lte_prop x (Succ y)). lte_prop x (Succ (Succ y)))
                           (p : lte_prop (Succ x) (Succ y)) ->
                              rec x p
                           )
                        x)
            y;

--    y <= z     x <= y    x <= z
-- ---------------------------------
--          x <=
$lemma4 :
    forall (z : Nat) (rec : forall (y : Nat) (_ : lte_prop y z) (x : Nat) (_ : lte_prop x y) . lte_prop x z)
           (y : Nat) (_ : lte_prop y (Succ z))
           (x : Nat) (_ : lte_prop x y) .
                lte_prop x (Succ z);

{-
$theorem :
    forall (z : Nat)
           (y : Nat) (_ : lte_prop y z)
           (x : Nat) (_ : lte_prop x y) . lte_prop x z;

$theorem :
    forall (x : Nat) (y : Nat) (z : Nat) (lte1 : lte_prop x y) (lte1 : lte_prop y z) . lte_prop x z;
-}
