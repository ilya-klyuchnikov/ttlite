module TTLite where

postulate
  Level : Set
  zero : Level
  suc : Level → Level
  max : Level → Level → Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO zero #-}
{-# BUILTIN LEVELSUC suc #-}
{-# BUILTIN LEVELMAX max #-}

------------------------------------------
-- Dep prod (aka Π)
------------------------------------------

-- Π = forall, λ is λ 
Π : ∀ {i j : Level} (A : Set i) (P : A → Set j) → Set (max i j)
Π A P = ∀ (x : A) → P x

------------------------------------------
-- Sigma (aka Σ)
------------------------------------------

-- usually in books Σ is implemented via records, but here I would like to try data
-- Indexes are inferred
data Sigma {i j} (A : Set i) (f : A → Set j) : Set (max i j) where
  sigma₀ : (a : A) -> (_ : f a) → Sigma A f 

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

data Sum {i j} (A : Set i) (B : Set j) : Set (max i j) where
  InL₀ : A → Sum A B
  InR₀ : B → Sum A B

InL : ∀ {i j} (A : Set i) (B : Set j) (a : A) → Sum A B
InL A B a = InL₀ a

InR : ∀ {i j} (A : Set i) (B : Set j) (b : B) → Sum A B
InR A B b = InR₀ b

elimSum : ∀ {i j k} 
            (A : Set i) 
            (B : Set j) 
            (m : Sum A B → Set k) 
            (fₗ : ∀ (a : A) → m (InL A B a))
            (fᵣ : ∀ (b : B) → m (InR A B b))
            (e : Sum A B) → m e
elimSum A B m fₗ fᵣ (InL₀ a) = fₗ a
elimSum A B m fₗ fᵣ (InR₀ b) = fᵣ b

------------------------------------------
-- Falsity (aka ⊥)
------------------------------------------

data Falsity : Set zero where

elimFalsity : ∀ {i} 
                (m : Falsity → Set i) 
                (e : Falsity) → m e
elimFalsity m ()

------------------------------------------
-- Truth (aka ⊤)
------------------------------------------

data Truth : Set zero where
  Triv : Truth

elimTruth : ∀ {i} 
              (m : Truth → Set i) 
              (f₁ : m Triv) 
              (e : Truth) → m e
elimTruth m f₁ Triv = f₁

------------------------------------------
-- Nat
------------------------------------------

data Nat : Set zero where
  Zero : Nat
  Succ : Nat → Nat

elimNat : ∀ {i} 
            (m : Nat → Set i) 
            (f₁ : m Zero) 
            (f₂ : (n : Nat) → (_ : m n) → m (Succ n))
            (e : Nat) → m e
elimNat m f₁ f₂ Zero     = f₁
elimNat m f₁ f₂ (Succ n) = f₂ n (elimNat m f₁ f₂ n)

------------------------------------------
-- List
------------------------------------------

data List {i} (A : Set i) : Set i where
  Nil₀  : List A
  Cons₀ : A → List A → List A

Nil : ∀ {i} (A : Set i) → List A
Nil A = Nil₀

Cons : ∀ {i} (A : Set i) (a : A) (as : List A) → List A
Cons A a as = Cons₀ a as

elimList : ∀ {i j}
             (A : Set i)
             (m : List A → Set j)
             (f₁ : m (Nil A))
             (f₂ : (a : A) (as : List A) (_ : m as) → m (Cons A a as))
             (e : List A) → m e
elimList A m f₁ f₂ Nil₀         = f₁
elimList A m f₁ f₂ (Cons₀ a as) = f₂ a as (elimList A m f₁ f₂ as)

------------------------------------------
-- Identity
------------------------------------------

data Id {i} (A : Set i) : A → A → Set i where
  refl₀ : (a : A) -> Id A a a

refl : ∀ {i} (A : Set i) (a : A) → Id A a a
refl A a = refl₀ a

elimId : ∀ {i k}
           (A : Set i)
           (a₁ a₂ : A)
           (m : (a₁ a₂ : A) (id : Id A a₁ a₂) → Set k)
           (f₁ : (a : A) → m a a (refl A a))
           (e : Id A a₁ a₂) → m a₁ a₂ e
elimId A .a .a m f (refl₀ a) = f a

------------------------------------------
-- Extra stuff (missed in preprint)
------------------------------------------

------------------------------------------
-- Bool
------------------------------------------

data Bool : Set zero where
  False : Bool
  True  : Bool

elimBool : ∀ {i} 
             (m : Bool → Set i)
             (f₁ : m False)
             (f₂ : m True)
             (e : Bool) → m e
elimBool m f₁ f₂ False = f₁
elimBool m f₁ f₂ True  = f₂
