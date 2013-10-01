import "examples/ids.hs";

comb2_type = forall
                                  (a : Set)
                                  (b : Set)
                                  (c : Set)
                                  (f : forall (_ : a) (_ : b) . c)
                                  (x1 : a)
                                  (x2 : a)
                                  (eq_xs : Id a x1 x2)
                                  (y1 : b)
                                  (y2 : b)
                                  (eq_ys : Id b y1 y2) .
                                  Id c (f x1 y1) (f x2 y2);


comb2 : comb2_type;
comb2 = \ (a : Set0) (b : Set0) (c : Set0)
  (d : forall (_ : a) (_ : b) . c)
  (e : a) (f : a) (g : Id a e f)
  (h : b) (i : b) (j : Id b h i) ->
    elim (Id (forall (_ : b) . c) (d e) (d f))
        (\ (k : forall (_ : b) . c)
           (l : forall (_ : b) . c)
           (_ : Id (forall (_ : b) . c) k l) -> Id c (k h) (l i))
        (\ (k : forall (_ : b) . c) -> cong1 b c k h i j)
        (cong1 a (forall (n : b) . c) d e f g);

eq : Id comb2_type comb2 cong2;
eq = Refl comb2_type comb2;