-- examples of well founded types

-- data Nat = Zero | Succ Nat

zero = False;
succ = True;
z_or_succ = Bool;

z_children = Falsity;

pred = Triv;
pred_children = Truth;

abort =
    \(m :: Set) (v :: Falsity) -> elim Falsity ( \(_ :: Falsity) -> m) v;

WNat =
    W (x :: z_or_succ) . elim Bool (\ (x :: z_or_succ) -> Set) z_children pred_children x;

zeroCon :: WNat;
zeroCon =
    Sup (W (x :: z_or_succ) . elim Bool (\ (x :: z_or_succ) -> Set) z_children pred_children x)
        zero
        (abort WNat);

succCon :: forall (_ :: WNat) . WNat;
succCon = \ (a :: WNat) ->
    Sup WNat succ (\ (v :: pred_children) -> a );


two :: WNat;
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

zzz = \ (x :: leaf_node_enum) . elim Bool (\ (x :: leaf_node_enum) -> Set) no_children l_r_children x;

BinTree =
    W (x :: leaf_node_enum) . zzz x;

-- leaf
leafCon :: BinTree;
leafCon =
    Sup BinTree
        leaf
        (abort BinTree);

nodeCon :: forall (l :: BinTree) (r :: BinTree) . BinTree;
nodeCon = \ (l :: BinTree) (r :: BinTree) ->
    Sup BinTree
        node
        (\ (c :: l_r_children) -> elim Bool (\ (_ :: Bool) -> BinTree) l r c);


tree1 :: BinTree;
tree1 = nodeCon leafCon leafCon;


--nrofnodes(leaf) = 1 | nrofnodes(node(t0, t00)) = nrofnodes(t0) + nrofnodes(t00)
--In type theory this function could be defined by
--nrofnodes(x) = wrec(x, (y, z, u)case(y, 1, u(left) + u(right)))

$y :: leaf_node_enum;
$u :: forall (_ :: zzz True) . Nat;

xx = $u left;


-- seems that we need to propagate y somehow!
-- it should be written in a bit different way!

import "examples/nat.hs";

nofNodes = \ (t :: BinTree) ->
    Rec BinTree
        (\ (_ :: BinTree) -> Nat)
        (\ (y :: leaf_node_enum) ->
           elim Bool
                (\ (y :: Bool) -> forall (_ :: forall (_ :: zzz y) . BinTree) (_ :: forall (_ :: zzz y) . Nat) . Nat )
                (\ (z :: forall (_ :: zzz False) . BinTree) (u :: forall (_ :: zzz False) . Nat) -> Succ Zero)
                (\ (z :: forall (_ :: zzz True) . BinTree) (u :: forall (_ :: zzz True) . Nat) -> plus (u left) (u right))
                y)
        t;

tt = nofNodes tree1;

{-
nofNodes = \ (t :: BinTree) ->
    Rec BinTree
        (\ (_ :: BinTree) -> Nat)
        (\ (y :: leaf_node_enum)
           (z :: forall (_ :: zzz y) . BinTree)
           (u :: forall (_ :: zzz y) . Nat) ->
              elim Bool (\ (_ :: Bool) -> Nat) (Succ Zero) (u left) y)
        t;
-}