$A : Set0;
$seed : $A;
$f : forall (_ : $A) . $A;

niter = \ (n : Nat) ->
    elim Nat (\ (_ : Nat) -> $A)
        $seed
        (\ (_ : Nat) (prev : $A) -> $f prev)
        n;

exportToIdris niter;
