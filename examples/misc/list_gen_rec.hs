fst =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> a) (\(x : a) (y : b) -> x) p;

snd =
    \ (a : Set) (b : Set) (p : Product a b) ->
        elim (Product a b) (\ (_ : Product a b) -> b) (\(x : a) (y : b) -> y) p;

nil = \(A: Set) -> Nil (List A);
cons = \(A: Set)(x: A)(xs: List A) -> Cons (List A) x xs;

n0 = Zero;
n1 = Succ n0;
n2 = Succ n1;
n3 = Succ n2;
n4 = Succ n3;
n5 = Succ n4;

seq1 = \(start: Nat)(len: Nat) ->
  elim Nat (\(_: Nat) -> forall (_: Nat) . List Nat)
    (\(_: Nat) -> nil Nat)
    (\(len: Nat)(recRes: forall (_: Nat) . List Nat)(start: Nat) ->
      cons Nat start (recRes (Succ start)))
    len start;

seq2 = \(start: Nat)(len: Nat) ->
  elim Nat (\(_: Nat) -> forall (_: Nat) . List Nat)
    (\(_: Nat) -> nil Nat)
    (\(len: Nat)(recRes: forall (_: Nat) . List Nat)(start: Nat) ->
      cons Nat start (recRes (Succ (Succ start))))
    len start;


-- type for rec helper
-- belowList p b Nil      = Truth;
-- belowList p b (x : xs) = Product (belowList p xs) (p xs);
belowList : forall
    (A: Set)
    (p: forall (_: List A) . Set)
    (xs: List A) . Set;
belowList = \(A: Set)(p: forall (_: List A) . Set)(xs: List A) ->
  elim (List A) (\(_: List A) -> Set)
    Truth
    (\(x: A)(xs: List A)(rec: Set) -> Product rec (p xs))
    xs;

bl = belowList;

-- h p below Nil       = Triv;
-- h p below (x : xs)  = Pair (h p xs) (below xs (h p xs))
h : forall
    (A: Set)
    (p: forall (_: List A) . Set)
    (below: forall (xs: List A)(_: bl A p xs) . p xs)
    (xs: List A) . bl A p xs;
h = \(A: Set) (p: forall (_: List A) . Set) (below: forall (xs: List A)(_: bl A p xs) . p xs) (xs: List A) ->
  elim (List A) (bl A p)
    Triv
    (\(x: A)(xs: List A)(recRes: bl A p xs) ->
      Pair (Product (bl A p xs) (p xs)) recRes (below xs recRes))
    xs;

-- list => type
-- just motive
m1 = (\ (_ : List Nat) -> Bool);
tt = h Nat m1;

l0 = seq1 n0 n0;
l1 = seq1 n0 n1;
l2 = seq1 n0 n2;
l3 = seq1 n0 n3;

-- Truth
bl0 = bl Nat m1 l0;
-- Product Truth Truth
bl1 = bl Nat m1 l1;
-- Product (Product Truth Truth) Truth
bl2 = bl Nat m1 l2;
-- Product (Product (Product Truth Truth) Truth) Truth
bl3 = bl Nat m1 l3;

{- general structural recursion on lists: -}
listRec : forall
    (A: Set)
    (p: forall (_: List A) . Set)
    (below: forall (xs: List A)(_: belowList A p xs) . p xs)
    (xs: List A) . p xs;
listRec = \(A: Set) (p: forall (_: List A) . Set) (below: forall (xs: List A)(_: belowList A p xs) . p xs) (xs: List A) ->
  below xs (h A p below xs);

-- trivial function
-- it doesn't use `g`
below1 : forall (xs: List Nat)(g: belowList Nat m1 xs) . m1 xs;
below1 = \ (xs : List Nat) (g : belowList Nat m1 xs) -> False;

-- less trivial, but still quite trivial
-- it performs only pattern patching
below2 : forall (xs: List Nat)(g: belowList Nat m1 xs) . m1 xs;
below2 =
    \ (xs : List Nat) ->
        elim (List Nat) ( \ (xs : List Nat) -> forall (_ : belowList Nat m1 xs) . m1 xs)
            (\ (g :  belowList Nat m1 (nil Nat)) -> False)
            (\ (v : Nat)
               (vs : List Nat)
               (rec : forall (_ : belowList Nat m1 vs) . m1 vs)
               (g : belowList Nat m1 (cons Nat v vs)) ->
                    False
               )
            xs;

$n : Nat;
$l : List Nat;

below3 : forall (xs: List Nat)(g: belowList Nat m1 xs) . m1 xs;
below3 =
    \ (xs : List Nat) ->
        elim (List Nat) ( \ (xs : List Nat) -> forall (_ : bl Nat m1 xs) . m1 xs)
            (\ (g :  bl Nat m1 (nil Nat)) -> False)
            (\ (v : Nat)
               (vs : List Nat)
               (rec : forall (_ : bl Nat m1 vs) . m1 vs)
               (g : bl Nat m1 (cons Nat v vs)) ->
                    -- here we try to get the previous iteration!!!
                    snd (bl Nat m1 vs) (m1 vs) g
               )
            xs;

modd = \ (_ : List Nat) -> List Nat;


bo0 : forall (xs: List Nat)(g: belowList Nat modd xs) . modd xs;
bo0 =
    \ (xs : List Nat) ->
        elim (List Nat) ( \ (xs : List Nat) -> forall (_ : bl Nat modd xs) . modd xs)
            (\ (g :  bl Nat modd (nil Nat)) -> (nil Nat))
            (\ (v : Nat)
               (vs : List Nat)
               (_ : forall (_ : bl Nat modd vs) . modd vs)
               (g : bl Nat modd (cons Nat v vs)) ->
                    snd (bl Nat modd vs) (modd vs) g
               )
            xs;

bo1 : forall (xs: List Nat)(g: belowList Nat modd xs) . modd xs;
bo1 =
    \ (xs : List Nat) ->
        elim (List Nat) ( \ (xs : List Nat) -> forall (_ : bl Nat modd xs) . modd xs)
            (\ (g :  bl Nat modd (nil Nat)) -> (nil Nat))
            (\ (v : Nat)
               (vs : List Nat)
               (_ : forall (_ : bl Nat modd vs) . modd vs) ->
                    elim (List Nat) ( \ (vs : List Nat) -> forall (v : Nat) (_ : bl Nat modd (cons Nat v vs)) . modd (cons Nat v vs) )
                         (\ (v0 : Nat) (g :  bl Nat modd (cons Nat v0 (nil Nat))) -> cons Nat v0 (nil Nat))
                         (\
                            (v1 : Nat)
                            (vs : List Nat)
                            (_ : forall (v : Nat) (_ : bl Nat modd (cons Nat v vs)) . modd (cons Nat v vs))
                            (v0 : Nat)
                            (g : bl Nat modd (cons Nat v0 (cons Nat v vs))) ->
                                cons Nat v0 (snd (bl Nat modd vs) (modd vs) (fst (bl Nat modd (cons Nat v vs)) (modd (cons Nat v vs)) g))
                         )
                         vs
                         v
               )
            xs;

odd = listRec Nat modd bo1;

-- the same, so the second element is the previous iteration!!
k = belowList Nat m1 (cons Nat $n $l);
z = Product (belowList Nat m1 $l) (m1 $l);

f1 : forall (_ : List Nat) . Bool;
f1 = listRec Nat m1 below1;

f3 : forall (_ : List Nat) . Bool;
f3 = listRec Nat m1 below3;

test0 : Id (List Nat) (odd (seq1 n0 n0)) (seq2 n0 n0);
test0 = Refl (List Nat) (seq2 n0 n0);

test1 : Id (List Nat) (odd (seq1 n0 n1)) (seq2 n0 n1);
test1 = Refl (List Nat) (seq2 n0 n1);

test2 : Id (List Nat) (odd (seq1 n0 n2)) (seq2 n0 n1);
test2 = Refl (List Nat) (seq2 n0 n1);

test3 : Id (List Nat) (odd (seq1 n0 n3)) (seq2 n0 n2);
test3 = Refl (List Nat) (seq2 n0 n2);

test4 : Id (List Nat) (odd (seq1 n0 n4)) (seq2 n0 n2);
test4 = Refl (List Nat) (seq2 n0 n2);

test5 : Id (List Nat) (odd (seq1 n0 n5)) (seq2 n0 n3);
test5 = Refl (List Nat) (seq2 n0 n3);
