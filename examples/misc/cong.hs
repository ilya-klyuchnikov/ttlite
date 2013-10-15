-- cong2' is a fused version of cong2
-- cong2' is cited in the preprint

import "examples/id.hs";

cong2_type =
    forall
        (A : Set) (B : Set) (C : Set)
        (f : forall (_ : A) (_ : B) . C)
        (x1 : A) (x2 : A) (_ : Id A x1 x2)
        (y1 : B) (y2 : B) (_ : Id B y1 y2) .
            Id C (f x1 y1) (f x2 y2);

cong2' : cong2_type;
cong2' = \ (A : Set0) (B : Set0) (C : Set0)
  (f : forall (_ : A) (_ : B) . C)
  (x1 : A) (x2 : A) (ix : Id A x1 x2)
  (y1 : B) (y2 : B) (iy : Id B y1 y2) ->
    elim (Id (forall (_ : B) . C) (f x1) (f x2))
        (\ (g1 : forall (_ : B) . C)
           (g2 : forall (_ : B) . C)
           (_ : Id (forall (_ : B) . C) g1 g2) -> Id C (g1 y1) (g2 y2))
        (\ (g : forall (_ : B) . C) -> cong1 B C g y1 y2 iy)
        (cong1 A (forall (_ : B) . C) f x1 x2 ix);

eq : Id cong2_type cong2' cong2;
eq = Refl cong2_type cong2';