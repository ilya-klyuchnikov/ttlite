module examples where

import ttlite
open ttlite

compose =
    \ (A : Set) (B : Set) (C : Set)
      (f : forall (_ : B) -> C)
      (g : forall (_ : A) -> B) (x : A) ->
        f (g x)


unit = \ (A : Set) (x : A) -> cons A x (nil A)

append =
    \ (A : Set) (xs : List A) (ys : List A) ->
        elimList A
            (\ (_ : List A) -> List A)
            ys
            (\ (v : A) (_ : List A) (r : List A) -> cons A v r)
            xs

rep = append

abs = \ (A : Set) (B : Set) (f : forall (_ : List A) -> B) -> f (nil A)

map =
    \ (A : Set) (B : Set) (f : forall (_ : A) -> B) (xs : List A) ->
        elimList A
            (\ (_ : List A) -> List B)
            (nil B)
            (\ (h : A) (t : List A) (rec : List B) -> cons B (f h) rec)
            xs

list_id =
    \ (A : Set) (xs : List A) ->
        elimList A
            (\ (_ : List A) -> List A)
            (nil A)
            (\ (h : A) (t : List A) (rec : List A) -> cons A h rec)
            xs

join =
    \ (A : Set) (xs : List (List A)) ->
        elimList (List A)
            (\ (_ : List (List A)) -> List A)
            (nil A)
            (\ (v : List A) (_ : List (List A)) (r : List A) -> append A v r)
            xs

filter = \ (A : Set) (f : forall (_ : A) -> Bool) (xs : List A) ->
    elimList A
        (\ (_ : List A) -> List A)
        (nil A)
        (\ (v : A) (vs : List A) (rec : List A) -> elimBool (\ (_ : Bool) -> List A) rec (cons A v rec) (f v) )
        xs
