abort =
    \(m :: Set) (v :: Falsity) -> elim Falsity ( \ (_ :: Falsity) -> m) v;

-- data Nat = Zero | Succ Nat
-- modelling of natural numbers via W

-- there are two types of nodes: nil and cons;
node = \ (A :: Set) -> Sum Truth A;
nil_node = \ (A :: Set) -> InL (Sum Truth A) Triv;
-- label of succ node
cons_node = \ (A :: Set) (x :: A) -> InR (Sum Truth A) x;


nil_children = Falsity;
cons_children = Truth;

node_to_label = \ (A :: Set) (n :: node A) .
    elim (Sum Truth A) (\ (n :: node A) -> Set) (\ (_ :: Truth) -> nil_children) (\ (_ :: A) -> cons_children) n;

WList = \ (A :: Set) -> W (x :: node A) . node_to_label A x;

wnil = \ (A :: Set) ->
    Sup (WList A) (nil_node A) (abort (WList A));
wcons = \ (A :: Set) (h :: A) (t :: WList A) ->
    Sup (WList A) (cons_node A h) (\ (x :: Truth) -> t);

l0 = wnil Nat;
l1 = wcons Nat Zero l0;
l2 = wcons Nat (Succ Zero) l1;
l3 = wcons Nat (Succ (Succ Zero)) l2;


$A :: Set;

-- always False
wempty0 = \ (xs :: WList $A) ->
    Rec (WList $A)
        (\ (_ :: WList $A) -> Bool)
        (\ (y :: node $A) -- label
           (z :: forall (_ :: node_to_label $A y) . WList $A) -- sub-tree
           (u :: forall (_ :: node_to_label $A y) . Bool) . -- sub-rec
                False
           ) xs;

tt :: forall (y :: node $A) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) . Bool;
tt = \ (y :: node $A) .
    elim (Sum Truth $A)
        (\ (_ :: Sum Truth $A) -> forall (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) . Bool)
        (\ (_ :: Truth) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) -> False)
        (\ (_ :: $A) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) -> True)
        y;

wnonempty = \ (xs :: WList $A) ->
    Rec (WList $A) (\ (_ :: WList $A) -> Bool) tt xs;
