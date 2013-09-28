import "examples/fin.hs";

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

-- used in lemma3;
lemma2 : forall (x : Nat) (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero);
lemma2 =
    \ (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> forall (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero))
            (\ (_ : lte_prop (Succ Zero) Zero) -> Triv)
            (\ (x : Nat)
               (rec : forall (_ : lte_prop (Succ x) Zero) . lte_prop (Succ x) (Succ Zero))
               (bot : lte_prop (Succ (Succ x)) Zero) -> bot)
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
                        (p : lte_prop (Succ x) Zero) -> lemma2 x p)
                            -- (?? : lte_prop (Succ x) (Succ Zero))
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

lemma4 :
    forall (z : Nat) (x : Nat) (l2 : lte_prop x Zero) . lte_prop x (Succ z);
lemma4 =
    \ (z : Nat) (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> forall (l2 : lte_prop x Zero) . lte_prop x (Succ z) )
            (\ (l2 : lte_prop Zero Zero) . Triv)
            (\ (x : Nat)
               (rec : forall (l2 : lte_prop x Zero) . lte_prop x (Succ z))
               (l2 : lte_prop (Succ x) Zero) -> abort (lte_prop (Succ x) (Succ z)) l2)
            x;

lte_tran_aux :
    forall (z : Nat)
           (y : Nat) (_ : lte_prop y z)
           (x : Nat) (_ : lte_prop x y) . lte_prop x z;
lte_tran_aux =
    \ (z : Nat) ->
        elim Nat
            (\ (z : Nat) -> forall (y : Nat) (_ : lte_prop y z) (x : Nat) (_ : lte_prop x y) . lte_prop x z)
            -- z = Zero
            lemma1
            -- z = S z1
            (\ (z1 : Nat)
               (recZ : forall (y : Nat) (_ : lte_prop y z1) (x : Nat) (_ : lte_prop x y) . lte_prop x z1)
               (y : Nat) ->
                    elim Nat
                        (\ (y : Nat) -> forall (_ : lte_prop y (Succ z1)) (x : Nat) (_ : lte_prop x y) . lte_prop x (Succ z1))
                        -- y = Z
                        (\ (l1 : lte_prop Zero (Succ z1)) -> lemma4 z1)
                        -- y = S y1
                        (\ (y1 : Nat)
                           (recY : forall (_ : lte_prop y1 (Succ z1)) (x : Nat) (_ : lte_prop x y1) . lte_prop x (Succ z1))
                           (lte_y1_z1 : lte_prop (Succ y1) (Succ z1))
                           (x : Nat) ->
                                elim Nat
                                    (\ (x : Nat) -> forall (_ : lte_prop x (Succ y1)) . lte_prop x (Succ z1) )
                                    -- x == Z
                                    (\ (_ : lte_prop Zero (Succ y1)) -> Triv )
                                    -- x == S x1
                                    ( \ (x1 : Nat)
                                        (_ : forall (_ : lte_prop x1 (Succ y1)) . lte_prop x1 (Succ z1))
                                        (lte_x1_y1 : lte_prop (Succ x1) (Succ y1)) -> recZ y1 lte_y1_z1 x1 lte_x1_y1)
                                    x
                           )
                        y
               )
            z;

lte_tran :
    forall (x : Nat) (y : Nat) (z : Nat) (_ : lte_prop x y) (_ : lte_prop y z) . lte_prop x z;
lte_tran =
    \ (x : Nat) (y : Nat) (z : Nat) (lte_xy : lte_prop x y) (lte_yz : lte_prop y z) ->
        lte_tran_aux z y lte_yz x lte_xy;

lte_lemma5 : forall (x : Nat) . lte_prop x (Succ x);
lte_lemma5 =
    \ (x : Nat) ->
        elim Nat
            (\ (x : Nat) -> lte_prop x (Succ x))
            Triv
            ( \ (x1 : Nat) (rec : lte_prop x1 (Succ x1)) -> rec)
            x;
