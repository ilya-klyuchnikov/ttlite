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

zzNat = \ (x :: z_or_succ) . elim Bool (\ (x :: z_or_succ) -> Set) z_children pred_children x;
WNat =
    W (x :: z_or_succ) . zzNat x;

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


--nrofnodes(x) = wrec(x, (y, z, u)case(y, 1, u(left) + u(right)))
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

-- the same, but zzz True, False are unfolded
nofNodes1 = \ (t :: BinTree) ->
    Rec BinTree
        (\ (_ :: BinTree) -> Nat)
        (\ (y :: leaf_node_enum) ->
           elim Bool
                (\ (y :: leaf_node_enum) -> forall (_ :: forall (_ :: zzz y) . BinTree) (_ :: forall (_ :: zzz y) . Nat) . Nat )
                (\ (z :: forall (_ :: Falsity) . BinTree) (u :: forall (_ :: Falsity) . Nat) -> Succ Zero)
                (\ (z :: forall (_ :: Bool) . BinTree) (u :: forall (_ :: Bool) . Nat) -> plus (u left) (u right))
                y)
        t;

wplus = \ (n1 :: WNat) (n2 :: WNat) ->
    Rec WNat
        (\ (_ :: WNat) -> WNat)
        (\ (y :: z_or_succ) ->
            elim Bool
                (\ (y :: z_or_succ) -> forall (_ :: forall (_ :: zzNat y) . WNat) (_ :: forall (_ :: zzNat y) . WNat) . WNat )
                (\ (z :: forall (_ :: zzNat zero) . WNat) (u :: forall (_ :: zzNat zero) . WNat) -> n2)
                (\ (z :: forall (_ :: zzNat succ) . WNat) (u :: forall (_ :: zzNat succ) . WNat) -> succCon (u pred))
                y)
        n1;

one_plus_one = wplus (succCon zeroCon) (succCon zeroCon);

check :: Eq WNat one_plus_one two;
check = Refl WNat two;
