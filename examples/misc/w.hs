-- examples of well founded types

-- data Nat = Zero | Succ Nat

zero = False;
succ = True;
z_or_succ = Bool;

z_children = Falsity;

pred = Triv;
pred_children = Truth;

abort =
    \(m : Set) (v : Falsity) -> elim Falsity ( \(_ : Falsity) -> m) v;

zzNat = \ (x : z_or_succ) . elim Bool (\ (x : z_or_succ) -> Set) z_children pred_children x;
WNat =
    W (x : z_or_succ) . zzNat x;

zeroCon : WNat;
zeroCon =
    Sup (W (x : z_or_succ) . elim Bool (\ (x : z_or_succ) -> Set) z_children pred_children x)
        zero
        (abort WNat);

succCon : forall (_ : WNat) . WNat;
succCon = \ (a : WNat) ->
    Sup WNat succ (\ (v : pred_children) -> a );


two : WNat;
two = succCon (succCon zeroCon);

-- datatype BinTree = leaf | node of BinTree * BinTree
leaf = False;
node = True;

leaf_node_enum = Bool;

left = False;
right = True;

-- {}
no_children = Falsity;
-- {left, right}
l_r_children = Bool;

zzz = \ (x : leaf_node_enum) . elim Bool (\ (x : leaf_node_enum) -> Set) no_children l_r_children x;

BinTree =
    W (x : leaf_node_enum) . zzz x;

-- leaf
leafCon : BinTree;
leafCon =
    Sup BinTree
        leaf
        (abort BinTree);

nodeCon : forall (l : BinTree) (r : BinTree) . BinTree;
nodeCon = \ (l : BinTree) (r : BinTree) ->
    Sup BinTree
        node
        (\ (c : l_r_children) -> elim Bool (\ (_ : Bool) -> BinTree) l r c);


tree1 : BinTree;
tree1 = nodeCon leafCon leafCon;


--nrofnodes(x) = wrec(x, (y, z, u)case(y, 1, u(left) + u(right)))
import "examples/nat.hs";

nofNodes = \ (t : BinTree) ->
    Rec BinTree
        (\ (_ : BinTree) -> Nat)
        (\ (y : leaf_node_enum) ->
           elim Bool
                (\ (y : leaf_node_enum) -> forall (_ : forall (_ : zzz y) . BinTree) (_ : forall (_ : zzz y) . Nat) . Nat )
                (\ (z : forall (_ : zzz leaf) . BinTree) (u : forall (_ : zzz leaf) . Nat) -> Succ Zero)
                (\ (z : forall (_ : zzz node) . BinTree) (u : forall (_ : zzz node) . Nat) -> plus (u left) (u right))
                y)
        t;

tt = nofNodes tree1;

-- the same, but zzz True, False are unfolded
nofNodes1 = \ (t : BinTree) ->
    Rec BinTree
        (\ (_ : BinTree) -> Nat)
        (\ (y : leaf_node_enum) ->
           elim Bool
                (\ (y : leaf_node_enum) -> forall (_ : forall (_ : zzz y) . BinTree) (_ : forall (_ : zzz y) . Nat) . Nat )
                (\ (z : forall (_ : Falsity) . BinTree) (u : forall (_ : Falsity) . Nat) -> Succ Zero)
                (\ (z : forall (_ : Bool) . BinTree) (u : forall (_ : Bool) . Nat) -> plus (u left) (u right))
                y)
        t;

wplus = \ (n1 : WNat) (n2 : WNat) ->
    Rec WNat
        (\ (_ : WNat) -> WNat)
        (\ (y : z_or_succ) ->
            elim Bool
                (\ (y : z_or_succ) -> forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . WNat) . WNat )
                (\ (z : forall (_ : zzNat zero) . WNat) (u : forall (_ : zzNat zero) . WNat) -> n2)
                (\ (z : forall (_ : zzNat succ) . WNat) (u : forall (_ : zzNat succ) . WNat) -> succCon (u pred))
                y)
        n1;

one_plus_one = wplus (succCon zeroCon) (succCon zeroCon);

check : Id WNat one_plus_one two;
check = Refl WNat two;

-- monomorphic simple nat fold
simpleNatFold =
    \ (A : Set) (zCase : A) (sCase : forall (_ : A) . A) (n : WNat) ->
        Rec WNat
        (\ (_ : WNat) -> A)
        (\ (y : z_or_succ) ->
            elim Bool
                (\ (y : z_or_succ) -> forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . A) . A)
                (\ (z : forall (_ : zzNat zero) . WNat) (u : forall (_ : zzNat zero) . A) -> zCase)
                (\ (z : forall (_ : zzNat succ) . WNat) (u : forall (_ : zzNat succ) . A) -> sCase (u pred))
                y)
                n;

-- monomorphic nat fold
natFold :
    forall (A : Set) (zCase : A) (sCase : forall (_ : WNat) (_ : A) . A) (n : WNat) . A;
natFold =
    \ (A : Set) (zCase : A) (sCase : forall (_ : WNat) (_ : A) . A) (n : WNat) ->
        Rec WNat
        (\ (_ : WNat) -> A)
        (\ (y : z_or_succ) ->
            elim Bool
                (\ (y : z_or_succ) -> forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . A) . A)
                (\ (z : forall (_ : zzNat zero) . WNat) (u : forall (_ : zzNat zero) . A) -> zCase)
                (\ (z : forall (_ : zzNat succ) . WNat) (u : forall (_ : zzNat succ) . A) -> sCase (z pred) (u pred))
                y)
                n;
---
f = False;
t = True;
f_or_t = Bool;

f_children = Falsity;
t_children = Falsity;

-- returns a type of labels
zzBool : forall (a : Bool) . Set0;
zzBool = \ (x : f_or_t) . elim Bool (\ (x : f_or_t) -> Set) f_children t_children x;
WBool =
    W (x : f_or_t) . zzBool x;

boolFold =
    \ (A : Set) (fCase : A) (tCase : A) (b : WBool) ->
        Rec WBool
        (\ (_ : WBool) -> A)
        (\ (y : f_or_t) ->
            elim Bool
                (\ (y : f_or_t) -> forall (_ : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . A) . A)
                (\ (z : forall (_ : zzBool f) . WBool) (u : forall (_ : zzBool f) . A) -> fCase)
                (\ (z : forall (_ : zzBool t) . WBool) (u : forall (_ : zzBool t) . A) -> tCase)
                y) b;

$A : Set;
vv = \ (y : f_or_t) -> forall (_ : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . $A) . $A;
vv1 = \ (y : z_or_succ) -> forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . $A) . $A;

-- just to gen Set
boolFold1 =
    \ (A : Set1) (fCase : A) (tCase : A) (b : WBool) ->
        Rec WBool
        (\ (_ : WBool) -> A)
        (\ (y : f_or_t) ->
            elim Bool
                (\ (y : f_or_t) -> forall (_ : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . A) . A)
                (\ (z : forall (_ : zzBool f) . WBool) (u : forall (_ : zzBool f) . A) -> fCase)
                (\ (z : forall (_ : zzBool t) . WBool) (u : forall (_ : zzBool t) . A) -> tCase)
                y)
                b;

fCon : WBool;
fCon = Sup WBool f (abort WBool);
tCon : WBool;
tCon = Sup WBool t (abort WBool);

wBoolId =
    \ (b : WBool) ->
        Rec WBool
        (\ (_ : WBool) -> WBool)
        (\ (y : f_or_t) ->
            elim Bool
                (\ (y : f_or_t) -> forall (_ : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . WBool) . WBool)
                (\ (z : forall (_ : zzBool f) . WBool) (u : forall (_ : zzBool f) . WBool) -> fCon)
                (\ (z : forall (_ : zzBool t) . WBool) (u : forall (_ : zzBool t) . WBool) -> tCon)
                y)
                b;

-- reconstructs wNat
wNatId =
    \ (n : WNat) ->
        Rec WNat
        (\ (_ : WNat) -> WNat)
        (\ (y : z_or_succ) ->
            elim Bool
                (\ (y : z_or_succ) -> forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . WNat) . WNat)
                (\ (z : forall (_ : zzNat zero) . WNat) (u : forall (_ : zzNat zero) . WNat) -> zeroCon)
                (\ (z : forall (_ : zzNat succ) . WNat) (u : forall (_ : zzNat succ) . WNat) -> succCon (u pred))
                y)
                n;

$m : forall (_ : WBool) . Set;
$fC : $m fCon;
$tC : $m tCon;
--$A : Set;
--ff = (\ (y : z_or_succ) -> {-- pattern matching here!!! --} forall (_ : forall (_ : zzNat y) . WNat) (_ : forall (_ : zzNat y) . $A) . $A);

wboolMotive = forall (m : forall (_ : WBool) . Set) (y : f_or_t) . Set;
wboolMotive = \ (m : forall (_ : WBool) . Set) (y : f_or_t) ->
    elim Bool (\ (b : Bool) -> Set )
        (forall (z : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . WBool) . m fCon)
        (forall (_ : forall (_ : zzBool y) . WBool) (_ : forall (_ : zzBool y) . WBool) . m tCon)
        y;

bool2WBool : forall (_ : Bool) . WBool;
bool2WBool = \ (b : Bool) -> elim Bool (\ (_ : Bool) -> WBool) fCon tCon b;


test = \ (y : f_or_t) ->
            elim Bool
                (\ (x : f_or_t) -> wboolMotive $m x)
                (\ (z : forall (_ : zzBool f) . WBool) (u : forall (_ : zzBool f) . WBool) -> $fC)
                (\ (z : forall (_ : zzBool t) . WBool) (u : forall (_ : zzBool t) . WBool) -> $tC)
                y;

$ss : forall (a : Bool) (z : forall (b : zzBool a) . WBool) (u : forall (c : zzBool a) . $m (z c)) . $m (Sup WBool a z);

{-
-- this is a general pattern recursion
-- it doesn't work without extensional equality
wboolCase = \ (b : WBool) ->
    Rec WBool
        (\ (b : WBool) -> $m b)
        (\ (y : f_or_t) ->
            elim Bool
                (\ (a : Bool) -> forall (z : forall (_ : zzBool a) . WBool) (u : forall (c : zzBool a) . $m (z c)) . $m (Sup WBool a z))
                (\ (z : forall (_ : zzBool f) . WBool) (u : forall (c : zzBool f) . $m (z c)) -> $fC)
                (\ (z : forall (_ : zzBool t) . WBool) (u : forall (c : zzBool t) . $m (z c)) -> $tC)
                y) b;
-}
