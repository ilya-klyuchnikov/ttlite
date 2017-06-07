module ttlite

%default total

------------------------------------------
-- Sigma (aka Σ)
------------------------------------------

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    Sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

elimSigma : (A : Type) ->
            (B : A -> Type) ->
            (m : TTSigma A B -> Type) ->
            (f : (a : A) -> (b : B a) -> m (Sigma A B a b)) ->
            (e : TTSigma A B) ->
            m e
elimSigma A B m f (Sigma _ _ a b) = f a b

------------------------------------------
-- Sum (aka +)
------------------------------------------

data Sum : (A : Type) -> (B : Type) -> Type where
    Inl : (A : Type) -> (B : Type) -> A -> Sum A B
    Inr : (A : Type) -> (B : Type) -> B -> Sum A B

elimSum : (A : Type) ->
          (B : Type) ->
          (m : Sum A B -> Type) ->
          (fl : (a : A) -> m (Inl A B a)) ->
          (fr : (b : B) -> m (Inr A B b)) ->
          (e : Sum A B) -> m e
elimSum _ _ _ fl fr (Inl _ _ a) = fl a
elimSum _ _ _ fl fr (Inr _ _ b) = fr b

------------------------------------------
-- Falsity (aka ⊥)
------------------------------------------
-- forwarding to Idris built-in Void and void

Falsity : Type
Falsity = Void

elimFalsity : (m : Falsity -> Type) -> (e : Falsity) -> m e
elimFalsity m e = void e {a = m e}

------------------------------------------
-- Truth (aka ⊤)
------------------------------------------

data Truth = Triv

elimTruth : (m : Truth -> Type) -> (f : m Triv) -> (e : Truth) -> m e
elimTruth m f Triv = f

------------------------------------------
-- Nat
------------------------------------------

data Nat = Zero | Succ Nat

elimNat : (m : Nat -> Type) ->
          (f1 : m Zero) ->
          (f2 : (n : Nat) -> m n -> m (Succ n)) ->
          (e : Nat) ->
          m e
elimNat m f1 f2 Zero     = f1
elimNat m f1 f2 (Succ n) = f2 n (elimNat m f1 f2 n)

------------------------------------------
-- List
------------------------------------------

data List : (A : Type) -> Type where
    Nil : (A : Type) -> List A
    Cons : (A : Type) -> A -> List A -> List A

elimList : (A : Type) ->
           (m : List A -> Type) ->
           (f1 : m (Nil A)) ->
           (f2 : (a : A) -> (as : List A) -> m as -> m (Cons A a as)) ->
           (e : List A) ->
           m e
elimList A m f1 f2 (Nil A) = f1
elimList A m f1 f2 (Cons A a as) = f2 a as (elimList A m f1 f2 as)

------------------------------------------
-- Identity
------------------------------------------
Id : (A : Type) -> A -> A -> Type
Id A = (=) {A = A} {B = A}

TTRefl : (A : Type) -> (a : A) -> Id A a a
TTRefl A a = Refl


elimId : (a : Type) ->
         (a1 : a) ->
         (a2 : a) ->
         (m : (x : a) -> (y : a) -> Id a x y -> Type) ->
         (f : (x : a) -> m x x (TTRefl a x)) ->
         (id : Id a a1 a2) ->
         m a1 a2 id
elimId _ x _ _ f Refl = f x

------------------------------------------
-- Bool
------------------------------------------

data Bool = False | True

elimBool : (m : Bool -> Type) ->
           m False ->
           m True ->
           (e : Bool) ->
           m e
elimBool m f1 f2 False = f1
elimBool m f1 f2 True = f2

------------------------------------------
-- Pair
------------------------------------------

data TTPair : (A : Type) -> (B : Type) -> Type where
    Pair : (A : Type) -> (B : Type) -> A -> B -> TTPair A B

elimPair : (A : Type) ->
           (B : Type) ->
           (m : TTPair A B -> Type) ->
           (f : (a : A) -> (b : B) -> m (Pair A B a b)) ->
           (e : TTPair A B) ->
           m e
elimPair A B m f (Pair A B a b) = f a b
