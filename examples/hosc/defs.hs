nil = \ (A : Set) -> Nil (List A);
cons = \ (A : Set) (x : A) (xs : List A) -> Cons (List A) x xs;
pair = \ (A : Set) (B : Set) (a : A) (b : B) -> Pair (Product A B) a b;

compose =
    \ (A : Set) (B : Set) (C : Set)
      (f : forall (_ : B). C)
      (g : forall (_ : A). B) (x : A) ->
        f (g x);

unit =
    \ (A : Set) (x : A) -> cons A x (nil A);

append =
    \ (A : Set) (xs : List A) (ys : List A) ->
        elim
            (List A)
            (\(_ : List A) -> List A)
            ys
            (\ (v : A) (_ : List A) (r : List A) -> cons A v r)
            xs;

rep = append;

abs = \ (A : Set) (B : Set) (f : forall (_ : List A) . B) -> f (nil A);

map =
    \ (A : Set) (B : Set) (f : forall (_ : A). B) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List B)
            (nil B)
            (\ (h : A) (t : List A) (rec : List B) -> cons B (f h) rec)
            xs;

list_id =
    \ (A : Set) (xs : List A) ->
        elim
            (List A)
            (\ (_ : List A) -> List A)
            (nil A)
            (\ (h : A) (t : List A) (rec : List A) -> cons A h rec)
            xs;

join =
    \ (A : Set) (xs : List (List A)) ->
        elim (List (List A))
            (\ (_ : List (List A)) -> List A)
            (nil A)
            (\ (v : List A) (_ : List (List A)) (r : List A) -> append A v r)
            xs;

filter = \ (A : Set) (f : forall (_ : A) . Bool) (xs : List A) ->
    elim (List A)
        (\ (_ : List A) -> List A)
        (nil A)
        (\ (v : A) (vs : List A) (rec : List A) -> elim Bool (\ (_ : Bool) -> List A) rec (cons A v rec) (f v) )
        xs;

fst =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> a) (\(x : a) (y : b) -> x) p;

snd =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> b) (\(x : a) (y : b) -> y) p;

zip =
    \ (A : Set) (B : Set) (xs : List A) ->
        elim (List A)
            (\ (_ : List A) -> forall (_ : List B) . List (Product A B) )
            (\ (ys : List B) -> nil (Product A B))
            (\ (x : A)
               (_ : List A)
               (r : forall (_ : List B) . List (Product A B))
               (ys: List B) ->
                    elim (List B)
                        (\ (_ : List B) -> List (Product A B))
                        (nil (Product A B))
                        (\ (y : B) (ys : List B) (_ : List (Product A B)) ->
                            (cons (Product A B) (pair A B x y) (r ys)))
                        ys)
            xs;

zipp = \ (A : Set) (B : Set) (ps : Product (List A) (List B)) ->
    elim (Product (List A) (List B)) (\ (_ : Product (List A) (List B)) -> List (Product A B)) (zip A B) ps;

fp = \ (A : Set) (B : Set) (C : Set) (D : Set)
    (fs : Product (forall (_ : A) . C) (forall (_ : B) . D))
    (p : Product A B) ->
    elim (Product (forall (_ : A) . C) (forall (_ : B) . D))
        (\ (_ : Product (forall (_ : A) . C) (forall (_ : B) . D)) -> Product C D)
            (\ (f : forall (_ : A) . C) (g: forall (_ : B) . D) ->
                elim (Product A B)
                    (\ (_ : Product A B) -> Product C D)
                    (\ (a : A) (b : B) -> pair C D (f a) (g b) )
                    p)
        fs;

--e1 = zip Bool Bool (nil Bool) (cons Bool True (nil Bool));
--e2 = zip Bool Bool (cons Bool True (nil Bool)) (nil Bool);
--e3 = zip Bool Bool (cons Bool True (nil Bool)) (cons Bool False (nil Bool));
--e4 = zip Bool Bool (cons Bool True (cons Bool True (nil Bool))) (cons Bool False (cons Bool True (nil Bool)));
--e5 = zip Bool Bool (cons Bool True (cons Bool True (nil Bool))) (cons Bool False (nil Bool));