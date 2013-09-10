import "examples/fin.hs";

-- The general form of these types is that each node is built from a certain collection of predecessors of the same type.

-- the constructor set, represents the different ways to form an element in W(A,B)
unit_ctrs :: Set;
unit_ctrs = Truth;
-- there is a single node kind
u = Triv;
-- there are no selectors for unit element, so we have empty set
u_parts = Falsity;

-- selector family, represents the parts of a tree formed by ctr.
unit_sels :: forall (ctr :: unit_ctrs) . Set;
unit_sels = \ (ctr :: unit_ctrs) . elim Truth (\ (_ :: unit_ctrs) . Set) u_parts ctr;

WUnit = W (x :: unit_ctrs) . unit_sels x;

-- the only constructor for unit
--$xx :: forall (a :: Falsity) . WUnit;
fU :: WUnit;
fU = Sup WUnit u (abort WUnit);

$A :: Set;
$a :: $A;

$rec0 ::
    forall
        (ctr :: unit_ctrs)
        (b :: forall (b :: unit_sels ctr) . WUnit)
        (c :: forall (c :: unit_sels ctr) . $A) .
        $A;

wunitCase0Dummy :: forall (x :: WUnit) . $A;
wunitCase0Dummy = \ (x :: WUnit) ->
    Rec WUnit
        (\ (x :: WUnit) -> $A)
        $rec0
        x;

-- this is easy to construct !!
wunitCase0 :: forall (x :: WUnit) . $A;
wunitCase0 = \ (x :: WUnit) ->
    Rec WUnit
        (\ (x :: WUnit) -> $A)
        (\ (ctr :: unit_ctrs) (b :: forall (b :: unit_sels ctr) . WUnit) (c :: forall (c :: unit_sels ctr) . $A) -> $a)
        x;

$m :: forall (_ :: WUnit) . Set;
$mu :: $m fU;

recType =
    forall (ctr :: unit_ctrs) (sel :: forall (_ :: unit_sels ctr) . WUnit) (rec :: forall (c :: unit_sels ctr) . $m (sel c)) . $m (Sup WUnit ctr sel);

$rec1 ::
    forall
        -- label of a node
        (ctr :: unit_ctrs)
        -- decomposing
        (sel :: forall (_ :: unit_sels ctr) . WUnit)
        (rec :: forall (c :: unit_sels ctr) . $m (sel c)) .
        $m (Sup WUnit ctr sel);

-- naive pattern matching
wunitCase1Dummy :: forall (x :: WUnit) . $m x;
wunitCase1Dummy = \ (x :: WUnit) ->
    Rec WUnit
        (\ (x :: WUnit) -> $m x)
        $rec1
        x;

--wunitCase1 :: forall (x :: WUnit) . $m x;
wunitCase1 = \ (x :: WUnit) ->
    Rec WUnit
        (\ (x :: WUnit) -> $m x)
        (\ (y :: unit_ctrs) ->
            elim Truth
                (\ (_ :: unit_ctrs) ->
                    forall
                        (sel :: forall (part :: unit_sels u) . WUnit)
                        (rec :: forall (part :: unit_sels u) . $m (sel part)) .
                        $m (Sup WUnit u sel)
                )
                (\  (sel :: forall (part :: unit_sels u) . WUnit)
                    (rec :: forall (part :: unit_sels u) . $m (sel part)) -> $mu)
                y
        )
        x;
