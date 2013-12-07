$y  : Nat;
$c0 : Nat;
$c1 : Nat;

e1 = elim Nat (\ (_ : Nat) -> Nat) $c0 (\ (_ : Nat) (_ : Nat) -> $c1) $y;

e2 = elim Nat
        (\ (_ : Nat) -> Nat)
        (elim Nat (\ (_ : Nat) -> Nat) $c0 (\ (_ : Nat) (_ : Nat) -> $c1) $y)
        (\ (_ : Nat) (_ : Nat) -> $c1)
        $y;

(r1, p1) = sc e1;
(r2, p2) = sc e2;

-- this is an improvement lemma
-- case y of {Z -> case y of {Z -> g x2; S _ -> Z}; S _ -> Z} ==
-- case y of {Z -> g x2; S _ -> Z }
eq_r1_r2 : Id Nat r1 r2;
eq_r1_r2 = Refl Nat r1;

-- this is a simple function `g` which is quadratic that we would like to linear
-- f x = case x of {Z -> Z ; S x1 -> f x1;}
-- g x = case x of {Z -> Z ; S x1 -> case (f x1) of {Z -> g x1; S _ -> Z}}
-- this is possible if we apply following lemma during supercompilation
-- case (f x2) of {Z -> case (f x2) of {Z -> g x2; S _ -> Z}; S _ -> Z} ==
-- case (f x2) of {Z -> g x2; S _ -> Z}
-- the instance of this lemma was proved above by means of supercompilation

-- in order to perform such supercompilation (n^2 -> n) we need to apply lemmas during supercompilation

f = \ (n : Nat) ->
    elim Nat
        (\ (_ : Nat) -> Nat)
        Zero
        (\ (n1 : Nat) (pred : Nat) -> pred )
        n;

g = \ (n : Nat) ->
    elim Nat
        (\ (_ : Nat) -> Nat)
        Zero
        (\ (n1 : Nat) (pred : Nat) ->
            elim Nat
                (\ (_ : Nat) -> Nat)
                pred
                (\ (_ : Nat) (_ : Nat) -> Zero)
                (f n1))
        n;
