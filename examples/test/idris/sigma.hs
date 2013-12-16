import examples/dproduct;

$x : Nat;

t = exists (x : Nat) . Id Nat x $x;
t1 = exists (x : Nat) (y : Nat) . Id Nat x y;

exportToIdris sigma;