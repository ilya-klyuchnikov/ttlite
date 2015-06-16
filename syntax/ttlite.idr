module ttlite

%default total

------------------------------------------
-- Sigma (aka Σ)
------------------------------------------

data TTSigma : (A : Type) -> (B : A -> Type) -> Type where
    sigma : (A : Type) -> (B : A -> Type) -> (a : A) -> B a -> TTSigma A B

elimSigma : (A : Type) ->
            (B : A -> Type) ->
            (m : TTSigma A B -> Type) ->
            (f : (a : A) -> (b : B a) -> m (sigma A B a b)) ->
            (e : TTSigma A B) ->
            m e
elimSigma A B m f (sigma _ _ a b) = f a b

------------------------------------------
-- Sum (aka +)
------------------------------------------

data Sum : (A : Type) -> (B : Type) -> Type where
    inl : (A : Type) -> (B : Type) -> A -> Sum A B
    inr : (A : Type) -> (B : Type) -> B -> Sum A B

elimSum : (A : Type) ->
          (B : Type) ->
          (m : Sum A B -> Type) ->
          (fl : (a : A) -> m (inl A B a)) ->
          (fr : (b : B) -> m (inr A B b)) ->
          (e : Sum A B) -> m e
elimSum _ _ _ fl fr (inl _ _ a) = fl a
elimSum _ _ _ fl fr (inr _ _ b) = fr b

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

data Truth = triv

elimTruth : (m : Truth -> Type) -> (f : m triv) -> (e : Truth) -> m e
elimTruth m f triv = f

------------------------------------------
-- Nat
------------------------------------------

data Nat = zero | succ Nat

elimNat : (m : Nat -> Type) ->
          (f1 : m zero) ->
          (f2 : (n : Nat) -> m n -> m (succ n)) ->
          (e : Nat) ->
          m e
elimNat m f1 f2 zero     = f1
elimNat m f1 f2 (succ n) = f2 n (elimNat m f1 f2 n)

------------------------------------------
-- List
------------------------------------------

data List : (A : Type) -> Type where
    nil : (A : Type) -> List A
    cons : (A : Type) -> A -> List A -> List A

elimList : (A : Type) ->
           (m : List A -> Type) ->
           (f1 : m (nil A)) ->
           (f2 : (a : A) -> (as : List A) -> m as -> m (cons A a as)) ->
           (e : List A) ->
           m e
elimList A m f1 f2 (nil A) = f1
elimList A m f1 f2 (cons A a as) = f2 a as (elimList A m f1 f2 as)

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

data Bool = false | true

elimBool : (m : Bool -> Type) ->
           m false ->
           m true ->
           (e : Bool) ->
           m e
elimBool m f1 f2 false = f1
elimBool m f1 f2 true = f2

------------------------------------------
-- Pair
------------------------------------------

data TTPair : (A : Type) -> (B : Type) -> Type where
    pair : (A : Type) -> (B : Type) -> A -> B -> TTPair A B

elimPair : (A : Type) ->
           (B : Type) ->
           (m : TTPair A B -> Type) ->
           (f : (a : A) -> (b : B) -> m (pair A B a b)) ->
           (e : TTPair A B) ->
           m e
elimPair A B m f (pair A B a b) = f a b
