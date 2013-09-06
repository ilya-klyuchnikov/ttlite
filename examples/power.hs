$mult :: forall (_ :: Nat)(_ :: Nat). Nat;

power = \(n :: Nat) (x :: Nat) ->
    elim Nat
    (\ (_ :: Nat) -> Nat)
    (Succ Zero)
    (\(n :: Nat) (x_pow_n :: Nat) -> $mult x x_pow_n)
    n;

power_3 = power (Succ (Succ (Succ Zero)));