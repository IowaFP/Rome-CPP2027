module Rome.Metatheory.Decidability where 

open import Rome.Prelude
open import Rome.Kinds
open import Rome.Kinds.Properties

open import Rome.Types
open import Rome.Types.Equivalence

open import Rome.NormalTypes
open import Rome.NormalTypes.Properties
open import Rome.NBE

open import Rome.Metatheory.NBE

--------------------------------------------------------------------------------
-- -- Type equivalence is decidable

_≡ₜ?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡ₜ τ₂)
τ₁ ≡ₜ? τ₂  with (⇓ₜ τ₁) ≡? (⇓ₜ τ₂)
... | yes p = yes (completeness p)
... | no  p = no (p ∘ soundness)
 
