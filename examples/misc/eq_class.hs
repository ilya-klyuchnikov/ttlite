-- it was an attempt to make some interesting example with type classes

import "examples/fin.hs";
import "examples/product.hs";
import "examples/dproduct.hs";

eq = \ (A : Set) . forall (x : A) (y : A) . Bool;
neq = \ (A : Set) . forall (x : A) (y : A) . Bool;

eq_class = \ (A : Set) . Product (eq A) (neq A);

dict = \ (A : Set) . eq_class A;

eq_list_type = forall (A : Set) (eqa : eq A) . eq (List A);

eq_f = \ (A : Set) (eqa : eq_class A) ->
    fst (eq A) (neq A) eqa;

-- this is a good function - it doesnt' construct/deconstruct values
eq_list = \ (A : Set) (eqa : eq_class A) (xs : List A) ->
    elim
        (List A)
        (\ (_ : List A) -> forall (_ : List A) . Bool )
        (\ (ys : List A) ->
            elim
                (List A)
                (\ (_ : List A) -> Bool)
                True
                (\ (_ : A) (_ : List A) (_ : Bool) -> False)
                ys)
        (\ (x : A) (xs : List A) (rec : forall (_ : List A) . Bool) ->
            (\ (ys : List A) ->
                elim (List A) (\ (_ : List A) -> Bool) False (\ (y : A) (ys : List A) (b : Bool) ->
                    and ((eq_f A eqa) x y) b) ys))
        xs;
--
fstD1 = \ (a : Set1) (b : (forall (_ : a). Set)) (p : (exists (x : a) . b x)) ->
            elim
                (exists (x : a) . b x)
                (\ (_ : exists (x : a) . b x) -> a)
                (\(x : a) (y : b x) -> x)
                p;

sndD1 = \ (a : Set1) (b : (forall (_ : a). Set)) (p : (exists (x : a) . b x)) ->
            elim
                (exists (x : a) . b x)
                (\ (p : (exists (x : a) . b x)) -> b (fstD1 a b p))
                (\(x : a) (y : b x) -> y)
                p;



eq_class_2 = exists (A : Set) . eq_class A;

-- extracts a type from an Eq Class
eq_class_param = \ (cl : eq_class_2) . fstD1 Set eq_class cl;
-- extracts an implementation from an Eq Class
eq_class_impl = \ (cl : eq_class_2) . sndD1 Set eq_class cl;


$bool_eq : forall (_ : Bool) (_ : Bool) . Bool;
$bool_neq : forall (_ : Bool) (_ : Bool) . Bool;

bool_impl = Pair (Product (eq Bool) (neq Bool)) $bool_eq $bool_neq;
eq_bool_class = dpair (exists (A : Set) . eq_class A) Bool bool_impl;

$eq_list2 : forall (class : eq_class_2). eq_class (List (eq_class_param class));

eq1 = \ (A : Set) . forall (y : A) . Bool;
neq1 = \ (A : Set) . forall (y : A) . Bool;

eq_class1 = \ (A : Set) . Product (eq1 A) (neq1 A);

$comb : forall (A : Set) (_ : forall (_ : A) . eq_class1 A) . eq_class A;

--eq_list3 :
eq_list3 = \ (A : Set) (eqa : eq_class A) (xs : List A) ->
    elim
        (List A)
        (\ (_ : List A) -> eq_class1 (List A) )

        (Pair (Product (eq1 (List A)) (neq1 (List A)))
            (\ (ys : List A) ->
                elim
                    (List A)
                    (\ (_ : List A) -> Bool)
                    True
                    (\ (_ : A) (_ : List A) (_ : Bool) -> False)
                    ys)
            (\ (ys : List A) -> False))

        (\ (x : A) (xs : List A) (bb : eq_class1 (List A)) ->
            (Pair (Product (eq1 (List A)) (neq1 (List A)))
                (\ (ys : List A) ->
                                elim
                                    (List A)
                                    (\ (_ : List A) -> Bool)
                                    False
                                    (\ (y : A) (ys : List A) (_ : Bool) -> fst (eq1 (List A)) (eq1 (List A)) bb ys)
                                    ys)
                            (\ (ys : List A) -> False)
            ))
        xs;
