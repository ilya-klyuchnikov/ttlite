import "examples/core.hs";

-- basic combinators for constructing
-- equality proofs from equality proofs

--   symmetry
--    a = b
--   -------
--    b = a
symm : forall (a : Set) (x : a) (y : a) (_ : Id a x y) . Id a y x;
symm = (\ (a : Set) (x : a) (y : a) (eq : Id a x y) ->
        elim (Id a x y)
            (\ (x : a) (y : a) (eq_x_y : Id a x y) -> Id a y x)
            (\ (x : a) -> Refl a x)
            eq);


--   transitivity
--    x = y   y = z
--   ---------------
--        x = z
tran : forall
             (a : Set)
             (x : a)
             (y : a)
             (z : a)
             (_ : Id a x y)
             (_ : Id a y z) .
                 Id a x z;
tran =
  ( \ (a : Set)
      (x : a)
      (y : a)
      (z : a)
      (eq_x_y : Id a x y) ->
        elim
            (Id a x y)
            (\ (x : a) (y : a) (eq_x_y : Id a x y) -> forall (z : a) (_ : Id a y z) . Id a x z)
            (\ (x : a) (z : a) (eq_x_z : Id a x z) -> eq_x_z)
             eq_x_y
             z);


--   congruence of operands
--         e1 = e2
--   -------------------
--       f e1 = f e2
cong1 : forall
              (a : Set)
              (b : Set)
              (f : forall (_ : a) . b)
              (x : a)
              (y : a)
              (_ : Id a x y) .
                  Id b (f x) (f y);
cong1 =
  ( \ (a : Set) (b : Set) (f : forall (_ : a) . b) (x : a) (y : a) (eq : Id a x y) ->
        elim
            (Id a x y)
            (\ (x : a) (y : a) (eq_x_y : Id a x y) -> Id b (f x) (f y))
            (\ (x : a) -> Refl b (f x))
            eq);



--   congruence of operators
--         f1 = f2
--   -------------------
--       f1 e = f1 e
fcong1 : forall
               (a : Set)
               (b : Set)
               (x : a)
               (f : forall (_ : a) . b)
               (g : forall (_ : a) . b)
               (_ : Id (forall (_ : a) . b) f g) .
               Id b (f x) (g x);
fcong1 =
  ( \ (a : Set) (b : Set) (x : a) (f : forall (_ : a) . b) (g : forall (_ : a) . b) (eq : Id (forall (_ : a) . b) f g) ->
        elim
            (Id (forall (_ : a) . b) f g)
            (\ (f : forall (_ : a) . b) (g : forall (_ : a) . b) (eq_f_g : Id (forall (_ : a) . b) f g) -> Id b (f x) (g x))
            (\ (f : forall (_ : a) . b) -> Refl b (f x))
            eq);


--   congruence of operators and operands
--     f1 = f2   e1 = e2
--   -------------------
--       f1 e1 = f2 e2
fargCong : forall
                 (a : Set)
                 (b : Set)
                 (x : a)
                 (y : a)
                 (f : forall (_ : a) . b)
                 (g : forall (_ : a) . b)
                 (_ : Id a x y)
                 (_ : Id (forall (_ : a) . b) f g) .
                 Id b (f x) (g y);

fargCong =
    ( \
        (a : Set)
        (b : Set)
        (x : a)
        (y : a)
        (f : forall (_ : a) . b)
        (g : forall (_ : a) . b)
        (eq_x_y : Id a x y)
        (eq_f_g : Id (forall (_ : a) . b) f g)  ->
            elim
                (Id (forall (_ : a) . b) f g)
                (\ (f : forall (_ : a) . b) (g : forall (_ : a) . b) (eq_f_g : Id (forall (_ : a) . b) f g) ->  Id b (f x) (g y))
                (\ (f : forall (_ : a) . b) -> cong1 a b f x y eq_x_y)
                eq_f_g);


--   congruence of two operands
--     x1 = x2   y1 = y2
--   ---------------------
--     f x1 y1 = f x2 y2
cong2 : forall
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
cong2 =
    (\
        (a : Set)
        (b : Set)
        (c : Set)
        (f : forall (_ : a) (_ : b) . c)
        (x1 : a)
        (x2 : a)
        (eq_xs : Id a x1 x2)
        (y1 : b)
        (y2 : b)
        (eq_ys : Id b y1 y2) ->
            fargCong b c y1 y2 (f x1) (f x2) eq_ys (cong1 a (forall (_ : b) . c) f x1 x2 eq_xs)
    );

--     e1 = res   e2 = res
--   ---------------------
--          e1 = e2
proof_by_sc :
    forall
        (A : Set)
        (e1 : A)
        (e2 : A)
        (res : A)
        (eq_e1_res : Id A e1 res)
        (eq_e2_res : Id A e2 res) .
        Id A e1 e2;
proof_by_sc =
    \ (A : Set)
      (e1 : A)
      (e2 : A)
      (res : A)
      (eq_e1_res : Id A e1 res)
      (eq_e2_res : Id A e2 res) ->
        tran A e1 res e2 eq_e1_res (symm A e2 res eq_e2_res);

eq_id =
    \ (A : Set) (x : A) (y : A) (eq_x_y : Id A x y) ->
        elim
            (Id A x y)
            (\ (x : A) (y : A) (eq_x_y : Id A x y) -> Id A x y)
            (\ (x : A) -> Refl A x)
            eq_x_y;
