map =
    \ (A : Set) (B : Set) (f : forall (_ : A). B) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List B)
            (Nil (List B))
            (\ (h : A) (t : List A) (rec : List B) -> Cons (List B) (f h) rec )
            xs;

exportToCoq map;