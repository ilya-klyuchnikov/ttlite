-- generate a vector of given length from a specified element (replicate)
replicate :: forall (n :: Nat) . forall (a :: Set) (_ :: a) . Vec a n;
replicate =
    \ (n :: Nat) ->
        elim Nat
            (\ (n :: Nat) -> forall (a :: Set) (_ :: a) . Vec a n )
            (\ (a :: Set) (_ :: a) -> VNil a )
            (\ (n :: Nat) (rec :: forall (a :: Set) (_ :: a) . Vec a n) (a :: Set) (x :: a) -> VCons a n x (rec a x) )
             n;


-- generate a vector of given length n, containing the natural numbers smaller than n
fromto =
    \ (n :: Nat) ->
        elim Nat
            ( \ (n :: Nat) -> Vec Nat n )
            ( VNil Nat )
            ( \ (n :: Nat) (rec :: Vec Nat n) -> VCons Nat n n rec )
            n;
