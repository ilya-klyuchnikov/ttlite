import "examples/id.hs";

apply :: forall (A :: Set) (B :: Set) (eq :: Id Set A B) (_ :: B) . A;
apply =
    \ (A :: Set) (B :: Set) (eq :: Id Set A B) .
        elim
            (Id Set A B)
            (\ (A :: Set) (B :: Set) (eq :: Id Set A B) -> forall (_ :: B) . A)
            (\ (A :: Set) -> \ (x :: A) -> x)
            eq;

cong11 :: forall
              (a :: Set)
              (b :: Set1)
              (f :: forall (_ :: a) . b)
              (x :: a)
              (y :: a)
              (_ :: Id a x y) .
                  Id b (f x) (f y);
cong11 =
  ( \ (a :: Set) (b :: Set1) (f :: forall (_ :: a) . b) (x :: a) (y :: a) (eq :: Id a x y) ->
        elim
            (Id a x y)
            (\ (x :: a) (y :: a) (eq_x_y :: Id a x y) -> Id b (f x) (f y))
            (\ (x :: a) -> Refl b (f x))
            eq);



NOT = \ (A :: Set) -> forall (a :: A) . Falsity;

$a :: Id Bool False True;
f = \(x:: Bool) ->
    elim Bool (\(b :: Bool) -> Set) Falsity Truth x;


proof :: Id Set Falsity Truth;
proof = cong11 Bool Set0 f False True $a;

top2bot = forall (_ :: Truth) . Falsity;
top2bot = apply Falsity Truth proof;

bot = top2bot Triv;

neq_f_t :: NOT (Id Bool False True);
neq_f_t = \ (eq :: Id Bool False True) ->
    apply Falsity Truth (cong11 Bool Set0 f False True eq) Triv;




