import "examples/nat.hs";
import "examples/id.hs";

iter =
    \(f : forall (_ : Nat). Nat) (n : Nat) ->
        elim Nat (\(n: Nat) -> Nat)
            (f (Succ Zero))
            (\(p : Nat)(q: Nat) -> f q)
            n;

ack = \(n : Nat) ->
    elim Nat
        (\ (m: Nat) -> forall (n : Nat) . Nat)
        (\ (m : Nat) -> Succ m )
        (\ (n : Nat) -> iter)
        n;

e1 = ack Zero Zero;
e2 = ack (Succ (Succ Zero)) Zero;
e3 = ack Zero (Succ (Succ Zero));

$n : Nat;

t1 = ack Zero $n;
t2 = ack (Succ Zero) $n;
t3 = ack (Succ (Succ Zero)) $n;