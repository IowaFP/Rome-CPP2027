module Rome.Metatheory.NBE.Normalization where

open import Rome.Prelude
open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Equivalence
open import Rome.NormalTypes
open import Rome.NormalTypes.NBE
open import Rome.Metatheory.NBE.Consistency
open import Rome.Metatheory.NBE.Stability

--------------------------------------------------------------------------------
-- An alias for _≡ₜ_ to emphasize that it's viewed as a step relation.

_—→ₜ*_ : Type Δ κ → Type Δ κ → Set
_—→ₜ*_  = _≡ₜ_

--------------------------------------------------------------------------------
-- It's tricky to define normal forms simply as types which do not step, e.g.:
--   ¬ Σ[ υ ∈ (Type Δ κ) ] (τ —→ₜ υ)
-- Because we would have to define _—→ₜ_ as the recursive restriction of _≡ₜ_
-- to just derivations not containing any eq-refl, eq-sym, or eq-trans subtrees.
-- This gets messy.

-- Alternatively, we'll say a type τ : Type Δ κ is "in normal form" if it's a
-- fixed-point of normalization (⇑ ∘ ⇓). In other words, the normalization procedure
--  has no effect on the type.

NormalForm  : Type Δ κ → Set _ 
NormalForm τ = (⇑ ∘ ⇓) τ ≡ τ

-- All normal types are in normal form
allNormal : (τ : NormalType Δ κ) → NormalForm (⇑ τ)
allNormal τ = cong ⇑ (stability τ) 

--------------------------------------------------------------------------------
-- (Weak) Normalization: every type τ steps to a normal form ⇑ υ.
-- This follows directly from consistency.

normalization : ∀ (τ : Type Δ κ) → Σ[ υ ∈ Type Δ κ ] (τ —→ₜ* υ × NormalForm υ)
normalization τ = ⇑ (⇓ τ) , consistency τ , allNormal (⇓ τ)

