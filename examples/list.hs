map =
    \ (A : Set) (B : Set) (f : forall (_ : A). B) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List B)
            (Nil (List B))
            (\ (h : A) (t : List A) (rec : List B) -> Cons (List B) (f h) rec )
            xs;

append =
    \ (a : Set) (xs : List a) (ys : List a) ->
        elim
            (List a)
            (\(_ : List a) -> List a)
            ys
            (\ (v : a) (vs : List a) (w : List a) -> Cons (List a) v w)
            xs;

unit =
    \ (A : Set) (x : A) -> Cons (List A) x (Nil (List A));

list_id =
    \ (A : Set) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List A)
            (Nil (List A))
            (\ (h : A) (t : List A) (rec : List A) -> Cons (List A) h rec)
            xs;
