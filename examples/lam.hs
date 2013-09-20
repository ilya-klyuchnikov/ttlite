-- using TT as a LF.
-- implementation of a simply-typed lambda calculus
-- This example is taken from:
-- David Aspinall and Martin Hofmann. Dependent Types
-- (ch. 2 in the "Advanced Topics in Types and Programming Languages").

$Ty :: Set;
$Tm :: forall (_ :: $Ty) . Set;
$arrow :: forall (_ :: $Ty) (_ :: $Ty) . $Ty;
$app :: forall (A :: $Ty) (B :: $Ty) (lam :: $Tm ($arrow A B)) (x :: $Tm A) . $Tm B;
-- f is like a proof here
$lam :: forall (A :: $Ty) (B :: $Ty) (f :: forall (_ :: $Tm A) . $Tm B) . $Tm ($arrow A B);

$A :: $Ty;

idA = $lam $A $A (\ (x :: $Tm $A) -> x);

-- church numerals in type theory directly
$B :: Set;

-- there are two variants to get numerals: "left" and "right"
-- the only distinction is the order of arguments
-- "left numeral" is when function is the first argument
lChurhNum = forall (_ :: forall (_ :: $B) . $B ) (_ :: $B) -> $B;
lzero :: lChurhNum;
lzero = \ (f :: forall (_ :: $B) . $B ) (x :: $B) -> x;

lone :: lChurhNum;
lone =  \ (f :: forall (_ :: $B) . $B ) (x :: $B) -> f x;

ltwo :: lChurhNum;
ltwo =  \ (f :: forall (_ :: $B) . $B ) (x :: $B) -> f (f x);

-- just a bit different way
rChurhNum = forall (_ :: $B) (_ :: forall (_ :: $B) . $B ) -> $B;
rzero :: rChurhNum;
rzero = \ (x :: $B) (f :: forall (_ :: $B) . $B ) -> x;

rone :: rChurhNum;
rone  = \ (x :: $B) (f :: forall (_ :: $B) . $B ) -> f x;

rtwo :: rChurhNum;
rtwo  = \ (x :: $B) (f :: forall (_ :: $B) . $B ) -> f (f x);



-- church numerals in "Logical Framework";
lChurchNum1 = $Tm ($arrow ($arrow $A $A) ($arrow $A $A));

lzero1 :: lChurchNum1;
lzero1 = $lam ($arrow $A $A) ($arrow $A $A)
        ( \ (f :: $Tm ($arrow $A $A)) ->
                $lam $A $A (\ (x :: $Tm $A) -> x));

lone1 :: lChurchNum1;
lone1 = $lam ($arrow $A $A) ($arrow $A $A)
        ( \ (f :: $Tm ($arrow $A $A)) ->
                $lam $A $A (\ (x :: $Tm $A) -> $app $A $A f x));

ltwo1 :: lChurchNum1;
ltwo1 = $lam ($arrow $A $A) ($arrow $A $A)
        ( \ (f :: $Tm ($arrow $A $A)) ->
                $lam $A $A (\ (x :: $Tm $A) -> $app $A $A f ($app $A $A f x)));


rChurchNum1 = $Tm ($arrow $A ($arrow ($arrow $A $A) $A));
rzero1 :: rChurchNum1;
rzero1 = $lam $A ($arrow ($arrow $A $A) $A)
        ( \ (x :: $Tm $A) ->
                $lam ($arrow $A $A) $A (\ (f :: $Tm ($arrow $A $A)) ->
                    x));

rone1 :: rChurchNum1;
rone1 = $lam $A ($arrow ($arrow $A $A) $A)
        ( \ (x :: $Tm $A) ->
                $lam ($arrow $A $A) $A (\ (f :: $Tm ($arrow $A $A)) ->
                    $app $A $A f x));

rtwo1 :: rChurchNum1;
rtwo1 = $lam $A ($arrow ($arrow $A $A) $A)
        ( \ (x :: $Tm $A) ->
                $lam ($arrow $A $A) $A (\ (f :: $Tm ($arrow $A $A)) ->
                    $app $A $A f ($app $A $A f x)));

