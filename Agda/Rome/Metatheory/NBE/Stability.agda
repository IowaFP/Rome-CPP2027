-- 
module Rome.Metatheory.NBE.Stability where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Renaming
open import Rome.Types.Equivalence

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Substitution
open import Rome.NormalTypes.Properties.Renaming

open import Rome.NormalTypes.NBE.Syntax
open import Rome.NormalTypes.NBE.Renaming
open import Rome.NormalTypes.NBE.Normalization

open import Rome.Metatheory.NBE.Soundness

--------------------------------------------------------------------------------
-- - stability : ⇑ is right-inverse to ⇓ₜ 
--     or, ⇓ₜ is a split-monomorphism/section.
-- - stabilityNE : ⟦ ∘ ⟧ₜ ⇑ₙₑ  = reflect
--   or, round trips from neutral semantic terms to semantic terms are preserved.

stability   : ∀ (τ : NormalType Δ κ) → ⇓ₜ (⇑ τ) ≡ τ
stabilityNE : ∀ (n : NeutralType Δ κ) → ⟦ ⇑ₙₑ n ⟧ₜ (idEnv {Δ}) ≡ reflect n

stabilityPred : ∀ (π : Pred (NormalType Δ R[ κ ])) → ⇓ₚ (⇑ₚ π) ≡ π
stabilityRow : ∀ (ρ : RowLiteral (NormalType Δ κ)) → 
              ⇓ᵣ (⇑ᵣ ρ) ≡ ρ 

stabilityNE {κ = κ} (` x) = refl
stabilityNE {Δ} {κ} (τ₁ · τ₂) rewrite stabilityNE τ₁ | stability τ₂ = ap reflect (cong₂ _·_ (renₜNE-id τ₁) refl) 

stability-β : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} 
                (τ : NormalType (Δ , κ₁) κ₂) → 
              reify (⟦ ⇑ τ ⟧ₜ (extende (renSem S ∘ idEnv) (idEnv Z))) ≡ τ
stability-β {Δ = Δ} τ = 
    trans (reify-≈ (idext η (⇑ τ))) (stability τ)
    where
        η : (extende (λ {κ} v' → renSem S (idEnv v')) (reflect (` Z))) ≈ₑ idEnv
        η Z = reflect-≈ refl
        η (S x) = ↻-ren-reflect S (` x)
  
stability {κ = ★} (ne x) = stabilityNE x
stability {κ = L} (ne x) = stabilityNE x
stability {κ = κ `→ κ₁} (ne x {()})
stability {κ = R[ κ ]} (ne x {()})
stability {κ   = κ₁ `→ κ₂} (`λ τ) = ap `λ (stability-β τ)
stability (`∀ τ) = ap (`∀) (stability-β τ)
stability (μ φ) = cong μ (stability φ) 
stability (τ₁ `→ τ₂) 
    rewrite stability τ₁ | stability τ₂ = refl
stability (π ⇒ τ) rewrite stabilityPred π | stability τ = refl    
stability (Π x)  rewrite stability x = refl
stability (Σ x)  rewrite stability x = refl
stability (⦅ ρ ⦆ ω)  = cong-⦅ stabilityRow ρ ⦆nf 
stability (lab l) = refl
stability ((ρ₂ ∖ ρ₁) {nrl}) with ⟦ (⇑ ρ₂) ⟧ₜ idEnv | ⟦ (⇑ ρ₁) ⟧ₜ idEnv | stability ρ₂ | stability ρ₁
... | φ₁ $ n₁ | _ | refl | refl = refl 
... | x₁ ▹ x₂ | x₃ ▹ x₄ | refl | refl = refl
... | x₁ ▹ x₂ | row ρ x₃ | refl | refl = refl
... | x₁ ▹ x₂ | d ∖ d₁ | refl | refl = refl
... | x₁ ▹ x₂ | φ $ n | refl | refl = refl
... | row ρ x₁ | x₂ ▹ x₃ | refl | refl = refl
... | row ρ x₁ | d ∖ d₁ | refl | refl = refl
... | row ρ x₁ | φ $ n | refl | refl = refl
... | c ∖ c₁ | x₁ ▹ x₂ | refl | refl = refl
... | c ∖ c₁ | row ρ x₁ | refl | refl = refl 
... | c ∖ c₁ | d ∖ d₁ | refl | refl = refl 
... | c ∖ c₁ | φ $ n | refl | refl = refl
stability (l ▹ₙ τ) with ⟦ (⇑ₙₑ l) ⟧ₜ idEnv | isNeutral? (⟦ (⇑ₙₑ l) ⟧ₜ idEnv) | stabilityNE l
... | ne x₁ | yes p | refl = ap (l ▹ₙ_) (stability τ)
... | .(ne l) | no q | refl = ⊥-elim (q tt)
stability ((φ $ n)) rewrite stabilityNE n = ap₂ _$_ (stability φ) refl

stabilityRow [] = refl
stabilityRow ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (stability τ)) (stabilityRow ρ)

stabilityPred (ρ₁ · ρ₂ ~ ρ₃) 
    rewrite stability ρ₁ | stability ρ₂ | stability ρ₃ = refl
stabilityPred (ρ₁ ≲ ρ₂) 
    rewrite stability ρ₁ | stability ρ₂ = refl

--------------------------------------------------------------------------------
-- idempotency

idempotency : ∀ (τ : Type Δ κ) → (⇑ ∘ ⇓ₜ ∘ ⇑ ∘ ⇓) τ ≡  (⇑ ∘ ⇓)  τ
idempotency τ = ap ⇑ (stability (⇓ₜ τ))

--------------------------------------------------------------------------------
-- surjectivity
--   
 
surjectivity : ∀ (τ : NormalType Δ κ) → ∃[ υ ] (⇓ₜ υ ≡ τ)
surjectivity τ = ( ⇑ τ , stability τ ) 

--------------------------------------------------------------------------------
-- stabilization is injective

stability-inj : ∀ {τ₁ τ₂ : NormalType Δ κ} → ⇓ₜ (⇑ τ₁) ≡ ⇓ₜ (⇑ τ₂) → τ₁ ≡ τ₂ 
stability-inj {τ₁ = τ₁} {τ₂} eq = stability τ₁ ⁻¹ ○ eq ○ stability τ₂ 

--------------------------------------------------------------------------------
-- Embedding is injective
 
⇑-inj : ∀ (τ₁ τ₂ : NormalType Δ κ) → ⇑ τ₁ ≡ ⇑ τ₂ → τ₁ ≡ τ₂                   
⇑-inj τ₁ τ₂ eq = trans (sym (stability τ₁)) (trans (ap ⇓ₜ eq) (stability τ₂))
