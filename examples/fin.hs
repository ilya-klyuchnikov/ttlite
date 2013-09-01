import "examples/core.hs";

abort =
    \(m :: Set) (v :: Void) -> elim Void ( \(_ :: Void) -> m) v;

boolElim =
    \ (m :: forall (_ :: Bool) . Set) (c1 :: m false) (c2 :: m true) (b :: Bool) . elim Bool m c1 c2 b;

--Prop = boolElim (\ (_ :: Bool) -> Set) Void Unit;

not = boolElim (\ (_ :: Bool) -> Bool) true false;
and = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (\ (_ :: Bool) -> false) (id Bool);

or  = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (id Bool) (\ (_ :: Bool) -> true);
xor = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) (id Bool) not;
if  = boolElim (\ (_ :: Bool) -> forall (_ :: Bool) . Bool) not (id Bool);


unit_id =
    \ (e :: Unit) ->
        elim Unit (\ (_ :: Unit) -> Unit) U e;

bool_id =
    \ (e :: Bool) ->
        elim Bool (\ (_ :: Bool) -> Bool) false true e;

t1 :: Eq Unit (unit_id U) U;
t1 = Refl Unit U;

t2 :: Eq Bool (bool_id false) false;
t2 = Refl Bool false;

t3 :: Eq Bool (bool_id true) true;
t3 = Refl Bool true;


