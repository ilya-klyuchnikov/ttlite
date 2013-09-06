import "examples/eq.hs";

m :: forall (_ :: Nat). Set;
m =
  \(n :: Nat).
      elim Nat
        (\(n:: Nat). Set) (Eq Nat Zero Zero) (\(_:: Nat)(_:: Set). Nat) n;

predOrRefl :: forall (n :: Nat). m n;
predOrRefl =
  \(n :: Nat).
      elim Nat m (Refl Nat Zero) (\(n1 :: Nat)(_ :: m n1). n1) n;




plus :: forall (x :: Nat) (y :: Nat). Nat;
plus =
    \ (x :: Nat) (y :: Nat) ->
        elim Nat
            (\ (_ :: Nat) -> Nat )
            y
            ( \(x1 :: Nat) (rec :: Nat) -> Succ rec ) x;

proof :: forall (n :: Nat) . Eq Nat (plus n Zero) (plus Zero n);
proof = \(n :: Nat) ->
    elim Nat
        (\(n :: Nat) -> Eq Nat (plus n Zero) (plus Zero n))
        (Refl Nat Zero)
        (\(n :: Nat)(r :: Eq Nat (plus n Zero) (plus Zero n)) ->
            cong1
                Nat
                Nat
                (\(n :: Nat) -> Succ n)
                (plus n Zero)
                (plus Zero n)
                r) n;
