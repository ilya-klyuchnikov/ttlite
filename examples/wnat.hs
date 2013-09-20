abort =
    \(m :: Set) (v :: Falsity) -> elim Falsity ( \(_ :: Falsity) -> m) v;

-- data Nat = Zero | Succ Nat
-- modelling of natural numbers via W

-- there are two types of nodes: zero and succ;
nodes = Bool;
-- label of zero node
zero_node = False;
-- label of succ node
succ_node = True;


zero_children = Falsity;
succ_children = Truth;

pred_label = Triv;

-- a function which for a given node label returns a type of children labels;
node_to_labels =
    \ (x :: nodes) .
        elim Bool (\ (x :: nodes) -> Set) zero_children succ_children x;

WNat = W (x :: nodes) . node_to_labels x;

wzero :: WNat;
-- 'zero_node' is a label of the node
wzero = Sup WNat zero_node (abort WNat);

wsucc :: forall (_ :: WNat) . WNat;
wsucc = \ (a :: WNat) -> Sup WNat succ_node (\ (v :: succ_children) -> a );

-- 0, 1, 2, ...
w0 = wzero;
w1 = wsucc w0;
w2 = wsucc w1;

-- todo make a fold over wplus
wplus = \ (n1 :: WNat) (n2 :: WNat) ->
    Rec WNat
        (\ (_ :: WNat) -> WNat)
        (\ (y :: nodes) ->
            elim Bool
                (\ (y :: nodes) -> forall (_ :: forall (_ :: node_to_labels y) . WNat) (_ :: forall (_ :: node_to_labels y) . WNat) . WNat )
                (\ (z :: forall (_ :: node_to_labels zero_node) . WNat) (u :: forall (_ :: node_to_labels zero_node) . WNat) -> n2)
                (\ (z :: forall (_ :: node_to_labels succ_node) . WNat) (u :: forall (_ :: node_to_labels succ_node) . WNat) -> wsucc (u pred_label))
                y)
        n1;

wnat2nat = \ (n :: WNat) ->
    Rec WNat
        (\ (_ :: WNat) -> Nat)
        (\ (y :: nodes) ->
            elim Bool
                (\ (y :: nodes) -> forall (_ :: forall (_ :: node_to_labels y) . WNat) (_ :: forall (_ :: node_to_labels y) . Nat) . Nat )
                (\ (z :: forall (_ :: node_to_labels zero_node) . WNat) (u :: forall (_ :: node_to_labels zero_node) . Nat) -> Zero)
                (\ (z :: forall (_ :: node_to_labels succ_node) . WNat) (u :: forall (_ :: node_to_labels succ_node) . Nat) -> Succ (u pred_label))
                y)
        n;

-- more explicit coding
wnat2nat = \ (n :: WNat) ->
    Rec WNat
        (\ (_ :: WNat) -> Nat)
        (\ (y :: nodes) ->
            elim Bool
                (\ (y :: nodes) -> forall (_ :: forall (_ :: node_to_labels y) . WNat) (_ :: forall (_ :: node_to_labels y) . Nat) . Nat )
                (\ (z :: forall (_ :: zero_children) . WNat) (u :: forall (_ :: zero_children) . Nat) -> Zero)
                (\ (z :: forall (_ :: succ_children) . WNat) (u :: forall (_ :: succ_children) . Nat) -> Succ (u pred_label))
                y)
        n;

-- primitive recursion over nat
wnat_fold =
    forall (A :: Set) (fz :: A) (fs :: forall (_ :: WNat) (_ :: A) . A) (n :: WNat) . A;
wnat_fold =
    \ (A :: Set) (fz :: A) (fs :: forall (_ :: WNat) (_ :: A) . A) (n :: WNat) ->
        Rec WNat
            (\ (_ :: WNat) -> A)
            (\ (y :: nodes) ->
                elim Bool
                    (\ (y :: nodes) -> forall (_ :: forall (_ :: node_to_labels y) . WNat) (_ :: forall (_ :: node_to_labels y) . A) . A)
                    (\ (_ :: forall (_ :: zero_children) . WNat) (rec :: forall (_ :: zero_children) . A) -> fz)
                    (\ (n :: forall (_ :: succ_children) . WNat) (rec :: forall (_ :: succ_children) . A) -> fs (n pred_label) (rec pred_label))
                    y)
            n;
