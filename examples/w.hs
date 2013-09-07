-- examples of well founded types

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

-- datat

zero = False;
succ = True;
z_or_succ = Bool;

z_children = Falsity;

pred = Triv;
pred_children = Truth;

WNat =
    W (x :: z_or_succ) . elim Bool (\ (x :: z_or_succ) -> Set) z_children pred_children x;

abort =
    \(m :: Set) (v :: Falsity) -> elim Falsity ( \(_ :: Falsity) -> m) v;

-- leaf
l1 :: BinTree;
l1 =
    Sup
        (W (x :: leaf_node_enum) . elim Bool (\ (x :: leaf_node_enum) -> Set) no_children l_r_children x)
        leaf
        (\ (v :: no_children) -> abort BinTree v);
