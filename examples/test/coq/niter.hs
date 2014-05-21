$a : Set0;
$seed : $a;
$f : forall (_ : $a) . $a;

niter = \ (n : Nat) ->
    elim Nat (\ (_ : Nat) -> $a)
        $seed
        (\ (_ : Nat) (prev : $a) -> $f prev)
        n;

exportToCoq niter;