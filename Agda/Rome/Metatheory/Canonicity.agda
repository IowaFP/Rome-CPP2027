module Rome.Metatheory.Canonicity where 

open import Rome.Prelude
open import Rome.Kinds
open import Rome.Types
open import Rome.NormalTypes.Syntax 

--------------------------------------------------------------------------------
-- Canonical forms of rows

row-canonicity : (ρ : NormalType Δ R[ κ ]) →  ⊤
row-canonicity (⦅ x ⦆ ω) = tt
row-canonicity (ne x) = tt
row-canonicity (x ▹ₙ ρ) = tt
row-canonicity ((φ $ ρ)) = tt
row-canonicity (ρ₂ ∖ ρ₁) = tt

row-canonicity-∅ : (ρ : NormalType ∅ R[ κ ]) → 
                    ∃[ xs ] Σ[ oxs ∈ True (ordered? xs) ] 
                    (ρ ≡ ⦅ xs ⦆ oxs)
row-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
row-canonicity-∅ (⦅ ρ ⦆ ω) = ρ , ω , refl
row-canonicity-∅ ((ρ ∖ ρ₁) {nrl}) = ⊥-elim (noComplements nrl refl)
row-canonicity-∅ (l ▹ₙ ρ) = ⊥-elim (noNeutrals l)
row-canonicity-∅ (φ $ ρ) = ⊥-elim (noNeutrals ρ)

--------------------------------------------------------------------------------
-- arrow-canonicity

arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → ∃[ τ ] (f ≡ `λ τ)
arrow-canonicity (`λ f) = f , refl

--------------------------------------------------------------------------------
-- label canonicity

label-canonicity : (l : NormalType Δ L) → ⊤ 
label-canonicity (ne x) = tt
label-canonicity (lab l) = tt

label-canonicity-∅ : ∀ (l : NormalType ∅ L) → ∃[ s ] (l ≡ lab s)
label-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
label-canonicity-∅ (lab s) = s , refl