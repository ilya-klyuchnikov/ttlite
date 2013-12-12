module Syntax where

open import Reflection hiding ( _≟_ )
open import Data.List using (List ; [] ; _∷_)
open import Data.Nat
open import Relation.Nullary

-- see TAPL, ch. 6
-- The shift of a term `t` above cutoff `c` via shifter
-- We use shifter instead of explicit delta just because
-- in β-reduction we need to decrement index, but index is ℕ,
-- so in β-reduction we use `pred` as shifter.
shift-term : (ℕ → ℕ) → ℕ → Term → Term
shift-term shifter cutoff t = s-term cutoff t 
  where
    mutual
      s-term : ℕ → Term → Term
      s-term c (var k args) with c ≤? k
      ...          | yes _ = var (shifter k) (s-args c args) 
      ...          | no  _ = var k args
      s-term c (con n args) = con n (s-args c args)
      s-term c (def n args) = def n (s-args c args)
      s-term c (lam v t)    = lam v (s-term (c + 1) t)
      s-term c (pi t1 t2)   = pi (s-arg-type c t1) (s-type (c + 1) t2)
      s-term c (sort s)     = sort (s-sort c s)
      s-term c unknown      = unknown

      s-arg-term : ℕ → Arg Term → Arg Term
      s-arg-term c (arg v r x) = arg v r (s-term c x)

      s-arg-type : ℕ → Arg Type → Arg Type
      s-arg-type c (arg v r x) = arg v r (s-type c x)
  
      s-args : ℕ → List (Arg Term) → List (Arg Term)
      s-args c [] = []
      s-args c (x ∷ xs) = (s-arg-term c x) ∷ (s-args c xs)

      s-type : ℕ → Type → Type
      s-type c (el s t) = el (s-sort c s) (s-term c t)
    
      s-sort : ℕ → Sort → Sort
      s-sort c (set t) = set (s-term c t)
      s-sort c (lit n) = lit n
      s-sort c unknown = unknown

infix 4 _↦_ 
data Subst : Set where
  _↦_ : ℕ → Term → Subst

-- The restriction: we do not substitute for var which is a head of application.
-- (var k args) where args is not empty.
-- We assume that "interesting" variable is not in the head of application.
-- Why? - There is no (simple) means to make an application out of the thin air.
-- Also during supercompilation, we split (= case analysis)
-- only data variable 
mutual
  subst-term : Subst → Term → Term
  subst-term (j ↦ s) (var k []) with j ≟ k
  ... | yes _ = s
  ... | no _  = (var k [])
  subst-term subst (var k args) = var k (subst-args subst args)
  subst-term subst (con n args) = con n (subst-args subst args)
  subst-term subst (def n args) = def n (subst-args subst args)
  subst-term (j ↦ s) (lam v t) = lam v (subst-term (j + 1 ↦ (shift-term suc 0 s)) t)
  subst-term (j ↦ s) (pi t₁ t₂) = pi (subst-arg-type (j ↦ s) t₁) (subst-type (j + 1 ↦ (shift-term suc 0 s)) t₂)
  subst-term subst (sort s)     = sort (subst-sort subst s)
  subst-term subst unknown      = unknown
  
  subst-arg-term : Subst → Arg Term → Arg Term
  subst-arg-term subst (arg v r x) = arg v r (subst-term subst x)

  subst-arg-type : Subst → Arg Type → Arg Type
  subst-arg-type subst (arg v r x) = arg v r (subst-type subst x)
  
  subst-args : Subst → List (Arg Term) → List (Arg Term)
  subst-args subst [] = []
  subst-args subst (x ∷ xs) = (subst-arg-term subst x) ∷ (subst-args subst xs)

  subst-type : Subst → Type → Type
  subst-type subst (el s t) = el (subst-sort subst s) (subst-term subst t)
    
  subst-sort : Subst → Sort → Sort
  subst-sort subst (set t) = set (subst-term subst t)
  subst-sort subst (lit n) = lit n
  subst-sort subst unknown = unknown
