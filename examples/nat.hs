
-- addition of natural numbers
plus : forall (x : Nat) (y : Nat). Nat;
plus =
    \ (x : Nat) (y : Nat) ->
        elim Nat
            (\ (_ : Nat) -> Nat )
            y
            ( \(x1 : Nat) (rec : Nat) -> Succ rec ) x;

-- predecessor, mapping 0 to 0
pred =
    \ (n : Nat) .
        elim Nat
            ( \ (_ : Nat) . Nat )
            Zero
            ( \ (n1 : Nat) (rec : Nat) . n1 )
            n;

-- a simpler elimination scheme for natural numbers:
-- a result type doesn't depend on n
natFold : forall (m : Set) (_ : m) (_ : forall (_ : m) . m) (_ : Nat) . m;
natFold =
    \ (m : Set) (mz : m) (ms : forall (_ : m) . m) (n : Nat) ->
        elim Nat
            (\ (_ : Nat) -> m )
             mz
             (\ (n1 : Nat) (rec : m) -> ms rec )
             n;


nat_id =
    \ (n : Nat) ->
        elim Nat
            (\ (_ : Nat) -> Nat )
            Zero
            (\ (n1 : Nat) (rec : Nat) -> Succ rec)
            n;
