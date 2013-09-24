
id : forall (a : Set) (x : a) . a;
id =  (\ (a : Set) (x : a) . x );

const : forall (a : Set) (b : Set) (_ : a) (_ : b) . a;
const =  (\ (a : Set) (b : Set) (x : a) (y : b) -> x);

const1 : forall (a : Set) (_ : a) (b : Set) (_ : b) . a;
const1 = (\ (a : Set) (x : a) (b : Set) (y : b) -> x);

comp =
    \ (A : Set) (B : Set) (C : Set) (f : forall (_ : B). C) (g : forall (_ : A). B) (x : A) ->
        f (g x);
