import examples/fin;

-- generate a vector of given length from a specified element (replicate)
replicate : forall (n : Nat) . forall (a : Set) (_ : a) . Vec a n;
replicate =
    \ (n : Nat) ->
        elim Nat
            (\ (n : Nat) -> forall (a : Set) (_ : a) . Vec a n )
            (\ (a : Set) (_ : a) -> VNil a )
            (\ (n : Nat) (rec : forall (a : Set) (_ : a) . Vec a n) (a : Set) (x : a) -> VCons a n x (rec a x) )
             n;

-- generate a vector of given length n, containing the natural numbers smaller than n
fromto =
    \ (n : Nat) ->
        elim Nat
            ( \ (n : Nat) -> Vec Nat n )
            ( VNil Nat )
            ( \ (n : Nat) (rec : Vec Nat n) -> VCons Nat n n rec )
            n;

bool_to_prop = \ (x : Bool) -> elim Bool (\ (_ : Bool) -> Set) Falsity Truth x;

-- Zero > _x = False
-- Succ x > Zero = True
-- Succ x > Succ y = x > y
gt = \ (x : Nat) ->
    elim Nat
        (\ (_ : Nat) -> forall (_ : Nat) . Bool)
        (\ (_ : Nat) -> False)
        (\ (x1 : Nat) (rec : forall (_ : Nat) . Bool) (y : Nat) ->
             elim Nat (\ (_ : Nat) -> Bool) True (\ (y1 : Nat) (_ : Bool) -> rec y1) y)
        x;

test1 : Id Bool (gt Zero Zero) False;
test1 = Refl Bool False;

test2 : Id Bool (gt (Succ Zero) Zero) True;
test2 = Refl Bool True;

test3 : Id Bool (gt (Succ (Succ Zero)) (Succ Zero)) True;
test3 = Refl Bool True;

gt_prop = \ (x : Nat) (y : Nat) -> bool_to_prop (gt x y);

--at : forall (A : Set) (i : Nat) (v : )

isEmpty : forall (A : Set) (n : Nat) (v : Vec A n) -> Bool;
isEmpty = \ (A : Set) (n : Nat) (v : Vec A n) ->
    vecElim A (\ (n : Nat) (v : Vec A n) -> Bool)
        True
        (\ (n : Nat) (v : A) (vs : Vec A n) (rec : Bool) -> False )
        n
        v;

$A : Set;
A = $A;

$a : A;

head_aux : forall (n : Nat) (v : Vec A n) (contr: gt_prop n Zero) . A;
head_aux = \ (n : Nat) (v : Vec A n) ->
    vecElim A
        (\ (n : Nat) (_ : Vec A n) -> forall (contr: gt_prop n Zero) . A)
        ( \ (contr : gt_prop Zero Zero) -> abort A contr)
        (\ (n : Nat)
           (v : A)
           (vs : Vec A n)
           (r : forall (contr: gt_prop n Zero) . A)
           (_ : gt_prop (Succ n) Zero) ->
                v)
        n
        v;


head : forall (n : Nat) (v : Vec A (Succ n)) . A;
head = \ (n : Nat) (v : Vec A (Succ n)) -> head_aux (Succ n) v Triv;

at : forall (n : Nat) (v : Vec A n) (i : Nat) (contr: gt_prop n i) . A;
at = \ (n : Nat) (v : Vec A n) ->
    vecElim A
        (\ (n : Nat) (_ : Vec A n) -> forall (i : Nat) (contr: gt_prop n i) . A)
        (\ (i : Nat) (contr : gt_prop Zero i) -> abort A contr)
        (\ (n : Nat)
           (v : A)
           (vs : Vec A n)
           (rvec : forall (i : Nat) (contr: gt_prop n i) . A)
           (i : Nat) ->
                elim Nat
                    (\ (i : Nat) -> forall (contr : gt_prop (Succ n) i) . A)
                    (\ (_ : gt_prop (Succ n) Zero) -> v)
                    (\ (i : Nat)
                       (_ : forall (contr : gt_prop (Succ n) i) . A)
                       -- see the trick that contr is reused here!!!
                       (contr : gt_prop (Succ n) (Succ i)) ->
                            rvec i contr)
                    i)
        n
        v;

head1 : forall (n : Nat) (v : Vec A (Succ n)) . A;
head1 = \ (n : Nat) (v : Vec A (Succ n)) -> at (Succ n) v Zero Triv;
