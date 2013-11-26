sum_id =
    (\ (A : Set) (B : Set) (s : Sum A B) ->
        elim (Sum A B)
            (\ (_ : Sum A B) -> Sum A B)
            (\ (a : A) . InL (Sum A B) a)
            (\ (b : B) . InR (Sum A A) x) -- exception here
            s);
