import examples/core;

abort =
    \(m : Set) (v : Falsity) -> elim Falsity ( \(_ : Falsity) -> m) v;

boolElim =
    \ (m : forall (_ : Bool) . Set) (c1 : m False) (c2 : m True) (b : Bool) . elim Bool m c1 c2 b;

--Prop = boolElim (\ (_ : Bool) -> Set) Falsity Truth;

not = boolElim (\ (_ : Bool) -> Bool) True False;
and = boolElim (\ (_ : Bool) -> forall (_ : Bool) . Bool) (\ (_ : Bool) -> False) (id Bool);

or  = boolElim (\ (_ : Bool) -> forall (_ : Bool) . Bool) (id Bool) (\ (_ : Bool) -> True);
xor = boolElim (\ (_ : Bool) -> forall (_ : Bool) . Bool) (id Bool) not;
if  = boolElim (\ (_ : Bool) -> forall (_ : Bool) . Bool) not (id Bool);


unit_id =
    \ (e : Truth) ->
        elim Truth (\ (_ : Truth) -> Truth) Triv e;

bool_id =
    \ (e : Bool) ->
        elim Bool (\ (_ : Bool) -> Bool) False True e;

t1 : Id Truth (unit_id Triv) Triv;
t1 = Refl Truth Triv;

t2 : Id Bool (bool_id False) False;
t2 = Refl Bool False;

t3 : Id Bool (bool_id True) True;
t3 = Refl Bool True;


