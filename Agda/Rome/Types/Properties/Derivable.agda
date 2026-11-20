module Rome.Types.Properties.Derivable where

open import Rome.Prelude
open import Rome.Kinds

open import Rome.Types.Syntax
open import Rome.Types.Equivalence
open import Rome.Types.Renaming
open import Rome.Types.Substitution

open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution

-------------------------------------------------------------------------------
-- Derivable rules: Π and Σ commute over binders

-- Nested rows have Π/Σ pushed inwards
eq-Π▹ : ∀ {l} {τ : Type Δ R[ κ ]}{nl : NotLabel κ} → 

        ----------------------------
        (Π {notLabel = nl} · (l ▹ τ)) ≡ₜ (l ▹ (Π {notLabel = nl} · τ))
eq-Π▹ = eq-Π ○ eq-▹$

--------------------------------------------------------------------------------
-- Type identity needed in eq-Πλ to reduce 
--   Π (weaken l ▹ □) 
-- to 
--   Π (weaken l ▹ τ)
-- where □ is the LHS below.

module _ where
  open ≡-Reasoning
  subₜ-weaken-over-lift² : (τ : Type (Δ₁ , κ₁) κ₂)  → 
                           (((renₜ (liftₜ S) (renₜ (liftₜ S) τ)) 
                               [ (liftsₜ (extendₜ ` (` Z))) ]ₛ)
                               βₜ[ ` Z ])
                           ≡ τ 
  subₜ-weaken-over-lift² τ = begin

    (((renₜ (liftₜ S) (renₜ (liftₜ S) τ)) 
         [ (liftsₜ (extendₜ ` (` Z))) ]ₛ)
         βₜ[ ` Z ])
      ≡⟨ subₜ-comp (renₜ (liftₜ S) (renₜ (liftₜ S) τ)) ⁻¹  ⟩ 
    (renₜ (liftₜ S) (renₜ (liftₜ S) τ)) 
      [   sub (extendₜ ` (` Z)) 
        ∘ liftsₜ (extendₜ ` (` Z)) ]ₛ
      ≡⟨ ↻-subₜ-renₜ (renₜ (liftₜ S) τ) ⁻¹ ⟩ 
    ((ren (liftₜ S) τ)
      [   (sub (extendₜ ` (` Z)) 
        ∘ (liftsₜ (extendₜ ` (` Z)) ∘ (liftₜ S))) ]ₛ)
      ≡⟨ ↻-subₜ-renₜ τ ⁻¹  ⟩ 
    τ [ (sub (extendₜ ` (` Z)) 
        ∘ (liftsₜ (extendₜ ` (` Z)) ∘ (liftₜ S))) 
        ∘ liftₜ S ]ₛ 
      ≡⟨ subₜ-cong (λ { Z → refl ; (S x) → refl }) τ ⟩ 
    sub ` τ 
      ≡⟨ sub-id τ ⟩ 
    τ ∎ 
    
    

--------------------------------------------------------------------------------
-- η-expansion is lifted over binders
-- N.b. I can maybe prove this in the row literal case through a general lemma:
--  Π (l ▹ τ) ≡ υ → Π ... 
-- not sure, but the idea is simply that: an equality on row singletons
-- can be mapped across row literals.
module _ where 
  
  open ≡ₜ-Reasoning
  eq-Πλ : ∀ l → 
          (τ : Type (Δ , κ₁) κ₂) (nl : NotLabel κ₂) → 
          Π {notLabel = nl} · (l ▹ `λ τ) ≡ₜ `λ (Π {notLabel = nl} · (weakenₜ l ▹ τ))
  eq-Πλ {κ₁ = κ₁} {κ₂} l τ nl = 
    Π · (l ▹ `λ τ)                       
      ≡ₜ⟨ eq-η ⟩ 
    `λ (weakenₜ (Π · (l ▹ `λ τ)) · ` Z)  
      ≡ₜ⟨ eq-λ eq-Π-assoc ⟩ 
    `λ (Π · (weakenₜ (l ▹ `λ τ) ?? ` Z)) 
      ≡ₜ⟨ eq-λ (eq-· eq-refl (eq-· eq-β eq-refl)) ⟩
    `λ
     (Π ·
      ((`λ (`λ (` Z · ` (S Z)) $ ` (S Z)) 
        βₜ[ weakenₜ (l ▹ `λ τ) ]) · ` Z)) 
      ≡ₜ⟨ (eq-λ ∘ eq-· eq-refl) eq-β ⟩ 
    `λ
     (Π ·
      (subₜ (liftsₜ (extendₜ ` (weakenₜ (l ▹ `λ τ))))
       (`λ (` Z · ` (S Z)) $ ` (S Z))
       βₜ[ ` Z ]))                        
      ≡ₜ⟨ (eq-λ ∘ eq-· eq-refl) eq-▹$ ⟩
    `λ
     (Π ·
      (subₜ (extendₜ ` (` Z)) (renₜ S (renₜ S l)) ▹
       (subₜ (extendₜ ` (` Z))
        (subₜ (liftsₜ (extendₜ ` (weakenₜ (l ▹ `λ τ))))
         (`λ (` Z · ` (S Z))))
        · subₜ (extendₜ ` (` Z)) 
              (renₜ S (renₜ S (`λ τ)))))) 
      ≡ₜ⟨ (eq-λ ∘ eq-· eq-refl) 
          (eq-▹ (inst (subₜ-weaken (weakenₜ l) (` Z))) eq-β) ⟩ 
    `λ
     (Π ·
      (weakenₜ l ▹
       (subₜ (liftsₜ (extendₜ ` (` Z)))
        (subₜ (liftsₜ (liftsₜ (extendₜ ` (weakenₜ (l ▹ `λ τ)))))
         (` Z · ` (S Z)))
        βₜ[ subₜ (extendₜ ` (` Z)) (renₜ S (renₜ S (`λ τ))) ]))) 
      ≡ₜ⟨ (eq-λ {κ₂ = κ₂} ∘ (eq-· {τ₁ = Π {notLabel = nl}} eq-refl) ∘ (eq-▹ eq-refl)) eq-β ⟩
    `λ
        (Π ·
         (weakenₜ l ▹
          (subₜ (liftsₜ (extendₜ ` (` Z)))
           (renₜ (liftₜ S) (renₜ (liftₜ S) τ))
           βₜ[ ` Z ])))
      ≡ₜ⟨ eq-λ (eq-· eq-refl (eq-▹ eq-refl (inst (subₜ-weaken-over-lift² τ)))) ⟩ 
    `λ (Π · (weakenₜ l ▹ τ)) ∎
