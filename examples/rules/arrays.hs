import examples/nat;
import examples/list;
import examples/id;

-- monomorphic eliminator of an array
-- = list recursor
listRec =
    \ (A : Set) (B : Set) (z : B) (f : forall (_ : A) (_ : List A) (rec : B) . B) (xs : List A) ->
        elim (List A) (\ (_ : List A) -> B) z f xs;

foldr : forall (A : Set) (B : Set) (z : B) (f : forall (_ : A) (rec : B) . B) (xs : List A) . B;
foldr =
    \ (A : Set) (B : Set) (z : B) (f : forall (_ : A) (rec : B) . B) ->
        listRec A B z (\ (x : A) (_ : List A) (rec : B) -> f x rec);

rep = \ (A : Set) (size : Nat) (el : A) ->
    natFold (List A) (Nil (List A)) (\ (rec : List A) -> Cons (List A) el rec) size;

length =
    \ (A : Set ) -> foldr A Nat Zero (\ (_ : A) (l : Nat) -> Succ l);

-- length of segments
segLengths =
    \ (A : Set) -> map (List A) Nat (length A);

flatten : forall (A : Set) (_ : List (List A)) . List A;
flatten =
    \ (A : Set) -> foldr (List A) (List A) (Nil (List A)) (append A);


