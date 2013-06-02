//putStrLn "natural numbers"
//-- natural numbers
assume (n :: *);
//-- zero element
assume (z :: n);
//-- successor element
assume (s :: n -> n);

let id = z :: n;
//-- churn numerals
let zero = (\f x -> x)    :: (n -> n) -> (n -> n);
let one = (\f x -> (f x)) :: (n -> n) -> (n -> n);
let two = (\f x -> (f (f x))) :: (n -> n) -> (n -> n);
//-- just numbers
let n0 = zero s z;
let n1 = one s z;
let n2 = two s z;
//-- church addition
let add = (\m n -> ((\f x -> m f (n f x)) :: (n -> n) -> (n -> n)))
	:: ((n -> n) -> (n -> n)) -> ((n -> n) -> (n -> n)) -> ((n -> n) -> (n -> n));

let three = add one two;
let n3 = three s z;
zero;
let n4 = three s z;