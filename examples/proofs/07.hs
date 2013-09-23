-- this is very interesting example!!
-- it shows that we are able to proof commutativity of and operation!
$b1 :: Bool;
$b2 :: Bool;

-- handling bottoms!
and1 :: forall (b1 :: Bool) (b2 :: Bool) . Bool;
and1 =
    \ (b1 :: Bool) (b2 :: Bool) ->
        elim
            Bool
            (\ (_ :: Bool) -> Bool)
            (elim Bool (\ (_ :: Bool) -> Bool) False False b2)
            (elim Bool (\ (_ :: Bool) -> Bool) False True b2)
            b1;

t1 = and1 $b1 $b2;
t2 = and1 $b2 $b1;

t1_sc = mrsc t1;
t2_sc = mrsc t2;

-- this a point where t1 and t2 are normalized to the same term!!
proof1 :: Id Bool t1_sc_1 t2_sc_2;
proof1 = Refl Bool t1_sc_1;

-- non-bottom case
and :: forall (b1 :: Bool) (b2 :: Bool) . Bool;
and =
    \ (b1 :: Bool) (b2 :: Bool) ->
        elim Bool (\ (_ :: Bool) -> Bool) False b2 b1;

e1 = and $b1 $b2;
e2 = and $b2 $b1;

(r, proof) = sc e1;

e1_sc1 = mrsc e1;
e2_sc2 = mrsc e2;

e1_sc2 = mrsc e1_sc1_4;
e2_sc2 = mrsc e1_sc2_4;

e1_sc2_9;
e2_sc2_2;

proof :: Id Bool e1_sc2_9 e2_sc2_2;
proof = Refl Bool e1_sc2_9;
