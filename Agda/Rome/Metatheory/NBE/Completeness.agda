-- 
module Rome.Metatheory.NBE.Completeness where

open import Rome.Prelude

open import Rome.Kinds
open import Rome.Types
open import Rome.Types.Equivalence
open import Rome.NormalTypes
open import Rome.NormalTypes.NBE
open import Rome.Metatheory.NBE.Consistency
open ≡ₜ-Reasoning

--------------------------------------------------------------------------------
-- Consistency implies completeness.

completeness : ∀ {τ υ : Type Δ κ} →
                ⇓ₜ τ ≡ ⇓ₜ υ → τ ≡ₜ υ 
completeness {τ = τ} {υ} e = 
   τ        ≡ₜ⟨ consistency τ ⟩ 
   ⇑ (⇓ₜ τ)  ≡ₜ⟨ inst (cong ⇑ e) ⟩ 
   ⇑ (⇓ₜ υ)  ≡ₜ⟨ consistency υ ⁻¹ ⟩ 
   υ ∎ 