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

tail = Triv;

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

nonempty_step :: forall (y :: node $A) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) . Bool;
nonempty_step = \ (y :: node $A) .
    elim (Sum Truth $A)
        (\ (_ :: Sum Truth $A) -> forall (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) . Bool)
        (\ (_ :: Truth) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) -> False)
        (\ (_ :: $A) (z :: forall (_ :: node_to_label $A y) . WList $A) (u :: forall (_ :: node_to_label $A y) . Bool) -> True)
        y;

wnonempty = \ (xs :: WList $A) ->
    Rec (WList $A) (\ (_ :: WList $A) -> Bool) nonempty_step xs;

-- length
l_step :: forall (A :: Set) (y :: node A) (z :: forall (_ :: node_to_label A y) . WList A) (u :: forall (_ :: node_to_label A y) . Nat) . Nat;
l_step = \ (A :: Set) (y :: node A) .
    elim (Sum Truth A)
        (\ (n :: Sum Truth A) -> forall (z :: forall (_ :: node_to_label A n) . WList A) (u :: forall (_ :: node_to_label A n) . Nat) . Nat)
        (\ (_ :: Truth)
           (z :: forall (_ :: node_to_label A (nil_node A)) . WList A)
           (rec :: forall (_ :: node_to_label A (nil_node A)) . Nat) ->
                Zero)
        (\ (a :: A)
           (z :: forall (_ :: node_to_label A (cons_node A a)) . WList A)
           (rec :: forall (_ :: node_to_label A (cons_node A a)) . Nat) ->
                Succ (rec tail) )
        y;

wlength = \ (A :: Set) (xs :: WList A) ->
    Rec (WList A) (\ (_ :: WList A) -> Nat) (l_step A) xs;

-- toList
toListStep :: forall (A :: Set) (y :: node A) (z :: forall (_ :: node_to_label A y) . WList A) (u :: forall (_ :: node_to_label A y) . List A) . List A;
toListStep = \ (A :: Set) (y :: node A) .
    elim (Sum Truth A)
        (\ (n :: Sum Truth A) -> forall (z :: forall (_ :: node_to_label A n) . WList A) (u :: forall (_ :: node_to_label A n) . List A) . List A)
        (\ (_ :: Truth)
           (z :: forall (_ :: node_to_label A (nil_node A)) . WList A)
           (rec :: forall (_ :: node_to_label A (nil_node A)) . List A) ->
                Nil (List A))
        (\ (a :: A)
           (z :: forall (_ :: node_to_label A (cons_node A a)) . WList A)
           (rec :: forall (_ :: node_to_label A (cons_node A a)) . List A) ->
                Cons (List A) a (rec tail) )
        y;

wlist2list :: forall (A :: Set) (xs :: WList A) . List A;
wlist2list = \ (A :: Set) (xs :: WList A) ->
    Rec (WList A) (\ (_ :: WList A) -> List A) (toListStep A) xs;


-- fold over lists
fold_step :: forall
        (A :: Set)
        (B :: Set)
        (fnil :: B)
        (fcons :: forall (_ :: A) (_ :: WList A) (rec :: B) . B )
        (y :: node A)
        (z :: forall (_ :: node_to_label A y) . WList A)
        (u :: forall (_ :: node_to_label A y) . B) .
            B;

fold_step = \ (A :: Set) (B :: Set) (fnil :: B) (fcons :: forall (_ :: A) (_ :: WList A) (rec :: B) . B ) (y :: node A).
    elim (Sum Truth A)
        (\ (n :: Sum Truth A) -> forall (z :: forall (_ :: node_to_label A n) . WList A) (u :: forall (_ :: node_to_label A n) . B) . B)
        (\ (_ :: Truth)
           (z :: forall (_ :: node_to_label A (nil_node A)) . WList A)
           (rec :: forall (_ :: node_to_label A (nil_node A)) . B) ->
                fnil)
        (\ (a :: A)
           (z :: forall (_ :: node_to_label A (cons_node A a)) . WList A)
           (rec :: forall (_ :: node_to_label A (cons_node A a)) . B) ->
                fcons a (z tail) (rec tail))
        y;


wlist_fold ::
    forall
        (A :: Set)
        (B :: Set)
        (fnil :: B)
        (fcons :: forall (_ :: A) (_ :: WList A) (rec :: B) . B )
        (ys :: WList A) . B;
wlist_fold = \
        (A :: Set)
        (B :: Set)
        (fnil :: B)
        (fcons :: forall (_ :: A) (_ :: WList A) (rec :: B) . B )
        (ys :: WList A) ->
            Rec (WList A) (\ (_ :: WList A) -> B) (fold_step A B fnil fcons) ys;

