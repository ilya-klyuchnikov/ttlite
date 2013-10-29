------------------------------------------
-- Sigma
------------------------------------------

Sigma :
    forall
    (A : Set)
    (B : forall (_ : A) . Set) .
        Set;
Sigma =
    \
    (A : Set)
    (B : forall (_ : A) . Set) .
        exists (x : A) . B x;

sigma :
    forall
    (A : Set)
    (B : forall (_ : A) . Set)
    (a : A)
    (b : B a) .
        exists (x : A) . B x;
sigma =
    \
    (A : Set)
    (B : forall (_ : A) . Set)
    (a : A)
    (b : B a) .
        dpair (exists (x : A) . B x) a b;

elimSigma :
    forall
    (A : Set)
    (B : forall (_ : A) . Set)
    (m : forall (_ : Sigma A B) . Set)
    (f : forall (a : A) (b : B a) . m (sigma A B a b))
    (e : Sigma A B) .
        m e;
elimSigma =
    \
    (A : Set)
    (B : forall (_ : A) . Set)
    (m : forall (_ : Sigma A B) . Set)
    (f : forall (a : A) (b : B a) . m (sigma A B a b))
    (e : Sigma A B) .
        elim (exists (x : A) . B x) m f e;

------------------------------------------
-- Sigma
------------------------------------------
inl :
    forall
    (A : Set)
    (B : Set)
    (a : A) .
        Sum A B;
inl =
    \
    (A : Set)
    (B : Set)
    (a : A) ->
        InL (Sum A B) a;

inr : forall (A : Set) (B : Set) (b : B) . Sum A B;
inr = \ (A : Set) (B : Set) (b : B) -> InR (Sum A B) b;

elimSum :
    forall
    (A : Set)
    (B : Set)
    (m : forall (_ : Sum A B) . Set)
    (f1 : forall (a : A) . m (inl A B a))
    (f2 : forall (b : B) . m (inr A B b))
    (e : Sum A B) .
        m e;
elimSum =
    \
    (A : Set)
    (B : Set)
    (m : forall (_ : Sum A B) . Set)
    (f1 : forall (a : A) . m (inl A B a))
    (f2 : forall (b : B) . m (inr A B b))
    (e : Sum A B) .
        elim (Sum A B) m f1 f2 e;

------------------------------------------
-- Falsity
------------------------------------------

elimFalsity :
    forall
    (m : forall (_ : Falsity) . Set)
    (e : Falsity) .
        m e;
elimFalsity =
    \
    (m : forall (_ : Falsity) . Set)
    (e : Falsity) .
        elim Falsity m e;

------------------------------------------
-- Truth
------------------------------------------

triv = Triv;

elimTruth :
    forall
    (m : forall (_ : Truth) . Set)
    (f1 : m triv)
    (e : Truth) .
        m e;
elimTruth =
    \
    (m : forall (_ : Truth) . Set)
    (f1 : m triv)
    (e : Truth) .
        elim Truth m f1 e;

------------------------------------------
-- Nat
------------------------------------------

zero = Zero;
succ = \ (n : Nat) -> Succ n;

elimNat :
    forall
    (m : forall (n : Nat) . Set)
    (f1 : m zero)
    (f2 : forall (n : Nat) (_ : m n) . m (succ n))
    (e : Nat) .
        m e;
elimNat =
    \
    (m : forall (n : Nat) . Set)
    (f1 : m zero)
    (f2 : forall (n : Nat) (_ : m n) . m (succ n))
    (e : Nat) .
        elim Nat m f1 f2 e;

------------------------------------------
-- List
------------------------------------------

nil :
    forall
    (A : Set) .
        List A;
nil =
    \
    (A : Set) .
        Nil (List A);

cons :
    forall
    (A : Set)
    (a : A)
    (as : List A) .
        List A;
cons =
    \
    (A : Set)
    (a : A)
    (as : List A) .
        Cons (List A) a as;

elimList :
    forall
    (A : Set)
    (m : forall (_ : List A) . Set)
    (f1 : m (nil A))
    (f2 : forall (a : A) (as : List A) (_ : m as) . m (cons A a as))
    (e : List A) .
        m e;
elimList =
    \
    (A : Set)
    (m : forall (_ : List A) . Set)
    (f1 : m (nil A))
    (f2 : forall (a : A) (as : List A) (_ : m as) . m (cons A a as))
    (e : List A) .
        elim (List A) m f1 f2 e;

------------------------------------------
-- Identity
------------------------------------------

refl = \ (A : Set) (a : A) . Refl A a;

elimId :
    forall
    (A : Set)
    (a1 : A)
    (a2 : A)
    (m : forall (a1 : A) (a2 : A) (id : Id A a1 a2) . Set)
    (f1 : forall (a : A) . m a a (refl A a))
    (e : Id A a1 a2) .
        m a1 a2 e;

elimId =
    \
    (A : Set)
    (a1 : A)
    (a2 : A)
    (m : forall (a1 : A) (a2 : A) (id : Id A a1 a2) . Set)
    (f1 : forall (a : A) . m a a (refl A a))
    (e : Id A a1 a2) .
        elim (Id A a1 a2) m f1 e;

------------------------------------------
-- Bool
------------------------------------------

false = False;
true = True;

elimBool :
    forall
    (m : forall (_ : Bool) . Set)
    (f1 : m false)
    (f2 : m true)
    (e : Bool) .
        m e;

elimBool =
    \
    (m : forall (_ : Bool) . Set)
    (f1 : m false)
    (f2 : m true)
    (e : Bool) .
        elim Bool m f1 f2 e;
