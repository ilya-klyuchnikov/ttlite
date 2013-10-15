import examples/rules/arrays;

-- checking the following rule
-- case NestedArraySegments(Def(RepArray(l, vs))) =>
--   val lens = replicate(l, vs.length)
--   createSegmentsFromLens(lens)

lhs : forall (A : Set) (_ : List A) (_ : Nat) -> List Nat;
lhs = \ (A : Set) (xs : List A) (n : Nat) -> segLengths A (rep (List A) n xs);

rhs : forall (A : Set) (_ : List A) (_ : Nat) -> List Nat;
rhs = \ (A : Set) (xs : List A) (n : Nat) -> rep Nat n (length A xs);

-- segLengths A (rep (List A) n xs) = rep Nat n (length A xs);
conj =
    \ (A : Set) (xs : List A) (n : Nat) ->
        Id (List Nat) (lhs A xs n) (rhs A xs n);

--
--    ---------------------------------------------------------------------
--        segLengths A (rep (List A) 0 xs) = rep Nat 0 (length A xs)
zeroCase : forall (A : Set) (xs : List A) . conj A xs Zero;
zeroCase = \ (A : Set) (xs : List A) -> Refl (List Nat) (lhs A xs Zero);


--         segLengths A (rep (List A) n xs) = rep Nat n (length A xs)
--    ---------------------------------------------------------------------
--    segLengths A (rep (List A) (1 + n) xs) = rep Nat (1 + n) (length A xs)
succCase : forall (A : Set) (xs : List A) (n : Nat) (ln : conj A xs n) . (conj A xs (Succ n));
succCase =
    \ (A : Set) (xs : List A) (n : Nat) (ln : conj A xs n) ->
        cong1
            (List Nat)
            (List Nat)
            (\ (vs : List Nat) -> Cons (List Nat) (length A xs) vs)
            (lhs A xs n)
            (rhs A xs n)
            ln;


proof : forall (A : Set) (xs : List A) (n : Nat) . conj A xs n;
proof =
    \ (A : Set) (xs : List A) (n : Nat) ->
        elim Nat (conj A xs) (zeroCase A xs) (succCase A xs) n;
