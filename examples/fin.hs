import "examples/core.hs";

abort =
    \(m :: Set) (v :: Void) -> elim Void ( \(_ :: Void) -> m) v;

boolElim =
    \ (m :: forall (_ :: Bool) . Set) (c1 :: m False) (c2 :: m True) (b :: Bool) . elim Bool m c1 c2 b;

--Prop = boolElim (\ (_ :: Bool) -> Set) Void Unit;

not = boolElim (\ (_ :: Bool) -> Bool) True False;
and = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (\ (_ :: Bool) -> False) (id Bool);

or  = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (id Bool) (\ (_ :: Bool) -> True);
xor = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (id Bool) not;
if  = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) not (id Bool);


unit_id =
    \ (e :: Unit) ->
        elim Unit (\ (_ :: Unit) -> Unit) U e;

bool_id =
    \ (e :: Bool) ->
        elim Bool (\ (_ :: Bool) -> Bool) False True e;

t1 :: Eq Unit (unit_id U) U;
t1 = Refl Unit U;

t2 :: Eq Bool (bool_id False) False;
t2 = Refl Bool False;

t3 :: Eq Bool (bool_id True) True;
t3 = Refl Bool True;


