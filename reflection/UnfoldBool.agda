module UnfoldBool where

open import Reflection
open import Data.List using (List ; [] ; _∷_ ; map)
open import Data.Nat hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open import Syntax

data Bool : Set where
  false : Bool
  true  : Bool

elimBool : (m : Bool → Set)
           (f₁ : m false)
           (f₂ : m true)
           (e : Bool) → m e
elimBool m f₁ f₂ false = f₁
elimBool m f₁ f₂ true  = f₂

-- not1 and not2 shoud be the same after 1-step unfolding

not1 : Bool → Bool
not1 = λ b → elimBool (λ _ → Bool) true false b

not2 : Bool → Bool
not2 = λ b → elimBool (λ _ → Bool) (not1 b) (not1 b) b

`elimBool = quote elimBool
`false = quoteTerm false
`true  = quoteTerm true

-- extreamly simple unfolding
-- it unfolds only top-level lambda in the form
-- λ v → elimBool m b1 b2 v
unfold : Term → Term
unfold (lam v₀ (def n (m ∷ (arg v₁ r₁ b₁) ∷ (arg v₂ r₂ b₂) ∷ (arg v r (var i [])) ∷ []))) = f (`elimBool ≟-Name n)
  where
    body = (def n (m ∷ (arg v₁ r₁ b₁) ∷ (arg v₂ r₂ b₂) ∷ (arg v r (var i [])) ∷ []))
    lam₀ = lam v₀ body
    nv = (arg v r (var i []))
    -- TAPL, p.81
    b₁' = shift-term pred 0 (subst-term (0 ↦ (shift-term suc 0 `false)) body)
    b₂' = shift-term pred 0 (subst-term (0 ↦ (shift-term suc 0 `true)) body)
    f : Dec (`elimBool ≡ n) → Term
    f (no _ )  = lam₀
    f (yes  _) = lam v₀ (def n (m ∷ (arg v₁ r₁ b₁') ∷ (arg v₂ r₂ b₂') ∷ (arg v r (var i [])) ∷ []))
unfold t = t

not2-unfolded = unquote (unfold (quoteTerm not2))

-- smoke-check:
-- unfolded not2 is the same as not1
proof : not1 ≡ not2-unfolded
proof = refl
