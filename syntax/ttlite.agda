module ttlite where

open import Agda.Primitive

------------------------------------------
-- Dep prod (aka Π)
------------------------------------------

-- Π = forall, λ is λ 
Π : ∀ {i j : Level} (A : Set i) (P : A → Set j) → Set (i ⊔ j)
Π A P = ∀ (x : A) → P x

------------------------------------------
-- Sigma (aka Σ)
------------------------------------------

-- usually in books Σ is implemented via records, but here I would like to try data
-- Indexes are inferred
data Sigma {i j} (A : Set i) (B : A → Set j) : Set (i ⊔ j) where
  sigma₀ : (a : A) -> (_ : B a) → Sigma A B

-- using local let in order to pass indices explicitly
sigma : ∀ {i j} (A : Set i) (B : A → Set j) (a : A) (_ : B a) → Sigma A B
sigma A B a b =
  let r : Sigma A B
      r = sigma₀ a b
  in r

elimSigma : ∀ {i j k}
              (A : Set i) 
              (B : A → Set j)
              (m : Sigma A B → Set k)
              (f : (a : A) (b : B a) → m (sigma A B a b))
              (e : Sigma A B) → m e
elimSigma A B m f (sigma₀ a b) = f a b

------------------------------------------
-- Sum (aka +)
------------------------------------------

data Sum {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  inl₀ : A → Sum A B
  inr₀ : B → Sum A B

inl : ∀ {i j} (A : Set i) (B : Set j) (a : A) → Sum A B
inl A B a = inl₀ a

inr : ∀ {i j} (A : Set i) (B : Set j) (b : B) → Sum A B
inr A B b = inr₀ b

elimSum : ∀ {i j k} 
            (A : Set i) 
            (B : Set j) 
            (m : Sum A B → Set k) 
            (fₗ : ∀ (a : A) → m (inl A B a))
            (fᵣ : ∀ (b : B) → m (inr A B b))
            (e : Sum A B) → m e
elimSum A B m fₗ fᵣ (inl₀ a) = fₗ a
elimSum A B m fₗ fᵣ (inr₀ b) = fᵣ b

------------------------------------------
-- Falsity (aka ⊥)
------------------------------------------

data Falsity : Set lzero where

elimFalsity : ∀ {i} 
                (m : Falsity → Set i) 
                (e : Falsity) → m e
elimFalsity m ()

------------------------------------------
-- Truth (aka ⊤)
------------------------------------------

data Truth : Set lzero where
  triv : Truth

elimTruth : ∀ {i} 
              (m : Truth → Set i) 
              (f₁ : m triv) 
              (e : Truth) → m e
elimTruth m f₁ triv = f₁

------------------------------------------
-- Nat
------------------------------------------

data Nat : Set lzero where
  zero : Nat
  succ : Nat → Nat

elimNat : ∀ {i} 
            (m : Nat → Set i) 
            (f₁ : m zero) 
            (f₂ : (n : Nat) → (_ : m n) → m (succ n))
            (e : Nat) → m e
elimNat m f₁ f₂ zero     = f₁
elimNat m f₁ f₂ (succ n) = f₂ n (elimNat m f₁ f₂ n)

------------------------------------------
-- List
------------------------------------------

data List {i} (A : Set i) : Set i where
  nil₀  : List A
  cons₀ : A → List A → List A

nil : ∀ {i} (A : Set i) → List A
nil A = nil₀

cons : ∀ {i} (A : Set i) (a : A) (as : List A) → List A
cons A a as = cons₀ a as

elimList : ∀ {i j}
             (A : Set i)
             (m : List A → Set j)
             (f₁ : m (nil A))
             (f₂ : (a : A) (as : List A) (_ : m as) → m (cons A a as))
             (e : List A) → m e
elimList A m f₁ f₂ nil₀         = f₁
elimList A m f₁ f₂ (cons₀ a as) = f₂ a as (elimList A m f₁ f₂ as)

------------------------------------------
-- Identity
------------------------------------------

data Id {i} (A : Set i) (a : A) : A → Set i where
  refl₀ : Id A a a

refl : ∀ {i} (A : Set i) (a : A) → Id A a a
refl A a = refl₀

elimId : ∀ {i k}
           (A : Set i)
           (a₁ a₂ : A)
           (m : (a₁ a₂ : A) (id : Id A a₁ a₂) → Set k)
           (f₁ : (a : A) → m a a (refl A a))
           (e : Id A a₁ a₂) → m a₁ a₂ e
elimId A a .a m f refl₀ = f a

------------------------------------------
-- Extra stuff (missed in preprint)
------------------------------------------

------------------------------------------
-- Bool
------------------------------------------

data Bool : Set lzero where
  false : Bool
  true  : Bool

elimBool : ∀ {i} 
             (m : Bool → Set i)
             (f₁ : m false)
             (f₂ : m true)
             (e : Bool) → m e
elimBool m f₁ f₂ false = f₁
elimBool m f₁ f₂ true  = f₂

------------------------------------------
-- Pair
------------------------------------------

data Pair {i j} (A : Set i) (B : Set j) : Set (i ⊔ j) where
  pair₀ : A → B → Pair A B

pair : ∀ {i j} (A : Set i) (B : Set j) (a : A) (b : B) → Pair A B
pair A B a b = pair₀ a b

elimPair : ∀ {i j k}
             (A : Set i)
             (B : Set j)
             (m : Pair A B → Set k)
             (f : (a : A) (b : B) → m (pair A B a b))
             (e : Pair A B) → m e
elimPair _ _ m f (pair₀ a b) = f a b

------------------------------------------
-- Vector
------------------------------------------

data Vec {i} (A : Set i) : (n : Nat) -> Set i where
  vnil₀ : Vec A zero
  vcons₀ : A -> (n : Nat) -> Vec A n -> Vec A (succ n)

vnil : ∀ {i} (A : Set i) → Vec A zero
vnil A = vnil₀

vcons : ∀ {i} (A : Set i) (n : Nat) (a : A) (as : Vec A n) → Vec A (succ n)
vcons A n a as = vcons₀ a n as

elimVec : ∀ {i j}
            (A : Set i)
            (m : (n : Nat) (_ : Vec A n) → Set j)
            (f₁ : m zero (vnil A))
            (f₂ : (n : Nat) (a : A) (as : Vec A n) (_ : m n as) → m (succ n) (vcons A n a as))
            (n : Nat)
            (v : Vec A n)
            → m n v

elimVec A m f₁ f₂ zero vnil₀  = f₁
elimVec A m f₁ f₂ (succ n) (vcons₀ a _ as) = f₂ n a as (elimVec A m f₁ f₂ n as)

------------------------------------------
-- TODO: W
------------------------------------------