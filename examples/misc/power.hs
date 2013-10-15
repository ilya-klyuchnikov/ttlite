-- this examples shows that normalization of terms with free
-- variables can be seen as partial evaluation

$mult : forall (_ : Nat)(_ : Nat). Nat;

power = \(n : Nat) (x : Nat) ->
    elim Nat
    (\ (_ : Nat) -> Nat)
    (Succ Zero)
    (\(n : Nat) (x_pow_n : Nat) -> $mult x x_pow_n)
    n;

-- power 3 as specialized by hand
power_3 = \ (x : Nat) -> $mult x ($mult x ($mult x (Succ Zero)));

norm_is_pe : Id   (forall (_ : Nat) . Nat) power_3 (power (Succ (Succ (Succ Zero))));
norm_is_pe = Refl (forall (_ : Nat) . Nat) power_3;
