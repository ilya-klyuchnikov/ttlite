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

BinTree =
    W (x :: leaf_node_enum) . elim Bool (\ (x :: leaf_node_enum) -> Set) no_children l_r_children x;

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
