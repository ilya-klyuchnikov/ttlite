import "examples/eq.hs";

apply :: forall (A :: Set) (B :: Set) (eq :: Eq Set A B) (_ :: B) . A;
apply =
    \ (A :: Set) (B :: Set) (eq :: Eq Set A B) .
        elim
            (Eq Set A B)
            (\ (A :: Set) (B :: Set) (eq :: Eq Set A B) -> forall (_ :: B) . A)
            (\ (A :: Set) -> \ (x :: A) -> x)
            eq;

cong11 :: forall
              (a :: Set)
              (b :: Set1)
              (f :: forall (_ :: a) . b)
              (x :: a)
              (y :: a)
              (_ :: Eq a x y) .
                  Eq b (f x) (f y);
cong11 =
  ( \ (a :: Set) (b :: Set1) (f :: forall (_ :: a) . b) (x :: a) (y :: a) (eq :: Eq a x y) ->
        elim
            (Eq a x y)
            (\ (x :: a) (y :: a) (eq_x_y :: Eq a x y) -> Eq b (f x) (f y))
            (\ (x :: a) -> Refl b (f x))
            eq);



NOT = \ (A :: Set) -> forall (a :: A) . Falsity;

$a :: Eq Bool False True;
f = \(x:: Bool) ->
    elim Bool (\(b :: Bool) -> Set) Falsity Truth x;


proof :: Eq Set Falsity Truth;
proof = cong11 Bool Set0 f False True $a;

top2bot = forall (_ :: Truth) . Falsity;
top2bot = apply Falsity Truth proof;

bot = top2bot Triv;

neq_f_t :: NOT (Eq Bool False True);
neq_f_t = \ (eq :: Eq Bool False True) ->
    apply Falsity Truth (cong11 Bool Set0 f False True eq) Triv;




