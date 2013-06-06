//assume (zz :: forall (a :: *) . a -> a);
let id    = (\ a x -> x) :: forall (a :: *) . a -> a;
let const = (\ a b x y -> x) :: forall (a :: *). forall (b :: *) . a -> b -> a;

//let const1 = (\a x b y -> x) :: forall (a :: *). a -> forall (b :: *) . b -> a;
let const2 = (\a -> a) :: forall (a :: *) . *;
let const3 = (\a x -> a) :: forall (a :: *) . forall (b :: *) . *;

assume (Bool :: *);
assume (False :: Bool);

let boolId = id Bool;
let False1 = boolId False;

assume (n :: *);
//-- zero element
assume (z :: n);
//-- successor element
assume (s :: n -> n);
let numeral = forall (A :: *) . (A -> A) -> (A -> A);
let zero = (\f x -> x) :: (n -> n) -> (n -> n);
let zero1 = (\A f x -> x) :: forall (A :: *). (A -> A) -> A -> A;
let zero2 = (\A f x -> x) :: numeral;
zero1 Bool;
let plus = (\m n A f x -> m A f (n A f x)) :: numeral -> numeral -> numeral;


