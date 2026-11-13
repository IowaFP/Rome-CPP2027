-- 
module Rome.NormalTypes.Properties.Renaming where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Properties.Renaming
open import Rome.Types.Renaming 

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming

open import Rome.NormalTypes.NBE
 


--------------------------------------------------------------------------------
-- Renaming respects congruence of Renamings

renₜNE-cong :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ∼ᵣ ρ₂ → 
                (τ : NeutralType Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ
renₜNF-cong    :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ∼ᵣ ρ₂ → 
                 (τ : NormalType Δ₁ κ) → ren ρ₁ τ ≡ ren ρ₂ τ
renₜNF-cong-row    :  ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ∼ᵣ ρ₂ → 
                (ρ : RowLiteral (NormalType Δ₁ κ)) → ren ρ₁ ρ ≡ ren ρ₂ ρ
renₜNF-cong-pred : ∀ {ρ₁ ρ₂ : Renaming Δ₁ Δ₂} →  ρ₁ ∼ᵣ ρ₂ → 
                (r : Pred (NormalType Δ₁ R[ κ ])) → ren ρ₁ r ≡ ren ρ₂ r

-- renₜNF-cong-row eq (l ▹ τ) rewrite renₜNF-cong eq l | renₜNF-cong eq τ = refl

renₜNE-cong eq (` x) rewrite eq x = refl
renₜNE-cong eq (ν · τ) rewrite
    renₜNE-cong eq ν
  | renₜNF-cong eq τ = refl

renₜNF-cong eq (ne ν) rewrite 
  renₜNE-cong eq ν = refl
renₜNF-cong eq (`λ τ) rewrite 
  renₜNF-cong (liftₜ-cong eq) τ = refl 
renₜNF-cong eq (τ₁ `→ τ₂) rewrite 
    renₜNF-cong eq τ₁ 
  | renₜNF-cong eq τ₂ = refl
renₜNF-cong eq (π ⇒ τ) rewrite 
    renₜNF-cong-pred eq π 
  | renₜNF-cong eq τ = refl  
renₜNF-cong eq (`∀ τ) rewrite 
  renₜNF-cong (liftₜ-cong eq) τ = refl 
renₜNF-cong eq (μ τ) rewrite renₜNF-cong eq τ = refl
renₜNF-cong eq (lab x) = refl
renₜNF-cong eq (Π x) rewrite renₜNF-cong eq x = refl
renₜNF-cong eq (Σ x) rewrite renₜNF-cong eq x = refl
renₜNF-cong eq (⦅ ρ ⦆ ω) = cong-⦅ renₜNF-cong-row eq ρ ⦆nf
renₜNF-cong eq (ρ₂ ∖ ρ₁) = cong-∖ (renₜNF-cong eq ρ₂) (renₜNF-cong eq ρ₁) 
renₜNF-cong eq (l ▹ₙ τ) = ap₂ _▹ₙ_ (renₜNE-cong eq l) (renₜNF-cong eq τ) 
renₜNF-cong eq ((x $ τ) ) = ap₂ _$_ (renₜNF-cong eq x) (renₜNE-cong eq τ)

renₜNF-cong-pred eq (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₜNF-cong eq ρ₁ | renₜNF-cong eq ρ₂ | renₜNF-cong eq ρ₃ = refl
renₜNF-cong-pred eq (ρ₁ ≲ ρ₂) 
  rewrite renₜNF-cong eq ρ₁ | renₜNF-cong eq ρ₂ = refl

renₜNF-cong-row eq [] = refl
renₜNF-cong-row eq ((l , τ) ∷ ρ) rewrite 
  renₜNF-cong eq τ | renₜNF-cong-row eq ρ = refl

--------------------------------------------------------------------------------
-- Renaming preserves identities (functor law #1)
renₜNF-id    : ∀ (τ : NormalType Δ κ) → ren id τ ≡ τ
renₜNE-id : ∀ (τ : NeutralType Δ κ) → ren id τ ≡ τ
renₜNF-id-row : ∀ (r : RowLiteral (NormalType Δ κ)) → ren id r ≡ r
renₜNF-id-pred : ∀ (τ : Pred (NormalType Δ R[ κ ])) → ren id τ ≡ τ

-- renₜNF-id-row (l ▹ τ) rewrite renₜNF-id l | renₜNF-id τ  = refl

renₜNE-id (` x) = refl
renₜNE-id (τ₁ · τ₂) rewrite
    renₜNE-id τ₁
  | renₜNF-id τ₂ = refl

renₜNF-id (ne ν) rewrite renₜNE-id ν = refl
renₜNF-id (`λ τ) rewrite 
    renₜNF-cong liftₜ-id τ 
  | renₜNF-id τ = refl 
renₜNF-id (τ₁ `→ τ₂) rewrite 
    renₜNF-id τ₁ 
  | renₜNF-id τ₂ = refl
renₜNF-id (π ⇒ τ) rewrite 
    renₜNF-id-pred π 
  | renₜNF-id τ = refl  
renₜNF-id (`∀ τ) rewrite 
    renₜNF-cong liftₜ-id τ 
  | renₜNF-id τ = refl
renₜNF-id (μ τ) rewrite renₜNF-id τ = refl
renₜNF-id (lab x) = refl
renₜNF-id (Π x)  rewrite renₜNF-id x  = refl 
renₜNF-id (Σ x)  rewrite renₜNF-id x  = refl 
renₜNF-id (⦅ ρ ⦆ ω) = cong-⦅ renₜNF-id-row ρ ⦆nf
renₜNF-id (ρ₂ ∖ ρ₁) = cong-∖ (renₜNF-id ρ₂) (renₜNF-id ρ₁)
renₜNF-id (l ▹ₙ τ) = ap₂ _▹ₙ_ (renₜNE-id l) (renₜNF-id τ)
renₜNF-id ((x $ τ) ) = ap₂ _$_ (renₜNF-id x) (renₜNE-id τ)

renₜNF-id-pred (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₜNF-id ρ₁ | renₜNF-id ρ₂ | renₜNF-id ρ₃ = refl
renₜNF-id-pred (ρ₁ ≲ ρ₂) 
  rewrite renₜNF-id ρ₁ | renₜNF-id ρ₂ = refl

renₜNF-id-row [] = refl
renₜNF-id-row ((l , τ) ∷ ρ) rewrite renₜNF-id τ | renₜNF-id-row ρ = refl

--------------------------------------------------------------------------------
-- Renaming preserves Composition (functor law #2)
renₜNF-comp     : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                  (τ : NormalType Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
renₜNE-comp  : ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                (τ : NeutralType Δ₁ κ) → ren (ρ₂ ∘ ρ₁) τ ≡ ren ρ₂ (ren ρ₁ τ)
renₜNF-comp-row :  ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                  (r : RowLiteral (NormalType Δ₁ κ)) → ren (ρ₂ ∘ ρ₁) r ≡ ren ρ₂ (ren ρ₁ r)
renₜNF-comp-pred :  ∀ (ρ₁ : Renaming Δ₁ Δ₂) (ρ₂ : Renaming Δ₂ Δ₃) → 
                  (π : Pred (NormalType Δ₁ R[ κ ])) → ren (ρ₂ ∘ ρ₁) π ≡ ren ρ₂ (ren ρ₁ π)

renₜNE-comp ρ₁ ρ₂ (` x) = refl
renₜNE-comp ρ₁ ρ₂ (ν · τ) rewrite
    renₜNE-comp ρ₁ ρ₂ ν
  | renₜNF-comp ρ₁ ρ₂ τ = refl

renₜNF-comp ρ₁ ρ₂ (ne ν) rewrite renₜNE-comp ρ₁ ρ₂ ν  = refl
renₜNF-comp ρ₁ ρ₂ (`λ τ)  rewrite
  trans (renₜNF-cong (liftₜ-comp ρ₁ ρ₂) τ) (renₜNF-comp (liftₜ ρ₁) (liftₜ ρ₂) τ) = refl
renₜNF-comp ρ₁ ρ₂ (τ₁ `→ τ₂) rewrite
    renₜNF-comp ρ₁ ρ₂ τ₁ 
  | renₜNF-comp ρ₁ ρ₂ τ₂ = refl
renₜNF-comp ρ₁ ρ₂ (π ⇒ τ) rewrite
    renₜNF-comp-pred ρ₁ ρ₂ π 
  | renₜNF-comp ρ₁ ρ₂ τ = refl  
renₜNF-comp ρ₁ ρ₂ (`∀ τ) rewrite
  (trans (renₜNF-cong (liftₜ-comp ρ₁ ρ₂) τ) (renₜNF-comp (liftₜ ρ₁) (liftₜ ρ₂) τ)) = refl
renₜNF-comp ρ₁ ρ₂ (μ τ) rewrite renₜNF-comp ρ₁ ρ₂ τ = refl
renₜNF-comp ρ₁ ρ₂ (lab x) = refl 
renₜNF-comp ρ₁ ρ₂ (Π x)  rewrite renₜNF-comp ρ₁ ρ₂ x = refl
renₜNF-comp ρ₁ ρ₂ (Σ x)  rewrite renₜNF-comp ρ₁ ρ₂ x = refl
renₜNF-comp ρ₁ ρ₂ (⦅ ρ ⦆ ω) = cong-⦅ renₜNF-comp-row ρ₁ ρ₂ ρ ⦆nf
renₜNF-comp r₁ r₂ (ρ₂ ∖ ρ₁) = cong-∖ (renₜNF-comp r₁ r₂ ρ₂) (renₜNF-comp r₁ r₂ ρ₁)
renₜNF-comp r₁ r₂ (l ▹ₙ τ) = ap₂ _▹ₙ_ (renₜNE-comp r₁ r₂ l) (renₜNF-comp r₁ r₂ τ)
renₜNF-comp ρ₁ ρ₂ ((x $ τ) ) = ap₂ _$_ (renₜNF-comp ρ₁ ρ₂ x) (renₜNE-comp ρ₁ ρ₂ τ)

renₜNF-comp-pred ρ ρ' (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₜNF-comp ρ ρ' ρ₁ | renₜNF-comp ρ ρ' ρ₂ | renₜNF-comp ρ ρ' ρ₃ = refl
renₜNF-comp-pred ρ ρ' (ρ₁ ≲ ρ₂) 
  rewrite renₜNF-comp ρ ρ' ρ₁ | renₜNF-comp ρ ρ' ρ₂ = refl

renₜNF-comp-row r₁ r₂ [] = refl
renₜNF-comp-row r₁ r₂ ((l , τ) ∷ ρ) rewrite renₜNF-comp r₁ r₂ τ | renₜNF-comp-row r₁ r₂ ρ = refl

--------------------------------------------------------------------------------
-- Weakening commutes with renaming

↻-weakenₜNF-ren  : ∀ {κ' : Kind} (ρ : Renaming Δ₁ Δ₂) (τ : NormalType Δ₁ κ) → 
                ren (liftₜ {κ = κ'} ρ) (ren S τ) ≡ ren S (ren ρ τ)
↻-weakenₜNF-ren  {κ' = κ'} ρ τ = 
  trans 
    (sym (renₜNF-comp (S {κ₂ = κ'}) (liftₜ ρ) τ)) 
    (renₜNF-comp ρ (S {κ₂ = κ'}) τ)

↻-weakenₜNE-ren  : ∀ {κ' : Kind} (ρ : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
                      ren (liftₜ {κ = κ'} ρ) (ren S τ) ≡ ren S (ren ρ τ)  
↻-weakenₜNE-ren ρ τ = trans (sym (renₜNE-comp S (liftₜ ρ) τ)) (renₜNE-comp ρ S τ)                        

↻-weakenPredₜNF-ren  : ∀ {κ' : Kind} (ρ : Renaming Δ₁ Δ₂) (π : Pred (NormalType Δ₁ R[ κ ])) → 
                ren (liftₜ {κ = κ'} ρ) (ren S π) ≡ ren S (ren ρ π)
↻-weakenPredₜNF-ren {κ' = κ'} ρ (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite 
    ↻-weakenₜNF-ren {κ' = κ'} ρ ρ₁ 
  | ↻-weakenₜNF-ren {κ' = κ'} ρ ρ₂ 
  | ↻-weakenₜNF-ren {κ' = κ'} ρ ρ₃ = refl
↻-weakenPredₜNF-ren {κ' = κ'} ρ (ρ₁ ≲ ρ₂)
  rewrite 
    ↻-weakenₜNF-ren {κ' = κ'} ρ ρ₁ 
  | ↻-weakenₜNF-ren {κ' = κ'} ρ ρ₂ = refl

--------------------------------------------------------------------------------
-- Renaming commutes with embedding

-- postulate 
↻-ren-⇑ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ κ) → 
          ⇑ (ren ρ τ) ≡ renₜ ρ (⇑ τ)
↻-ren-⇑ᵣ : ∀ (r : Renaming Δ₁ Δ₂) → (ρ : RowLiteral (NormalType Δ₁ κ)) → 
          ⇑ᵣ (ren r ρ) ≡ ren r (⇑ᵣ ρ)
↻-ren-⇑ₙₑ : ∀ (ρ : Renaming Δ₁ Δ₂) → (τ : NeutralType Δ₁ κ) → 
          ⇑ₙₑ (ren ρ τ) ≡ renₜ ρ (⇑ₙₑ τ)
↻-ren-⇑ₚ : ∀ (ρ : Renaming Δ₁ Δ₂) → (π : Pred (NormalType Δ₁ R[ κ ])) → 
            ⇑ₚ (ren ρ π) ≡ ren ρ (⇑ₚ π)      


↻-ren-⇑ ρ (ne x) = ↻-ren-⇑ₙₑ ρ x
↻-ren-⇑ ρ (`λ τ) = ap `λ (↻-ren-⇑ (liftₜ ρ) τ)
↻-ren-⇑ ρ (τ₁ `→ τ₂) = ap₂ _`→_ (↻-ren-⇑ ρ τ₁) (↻-ren-⇑ ρ τ₂) 
↻-ren-⇑ ρ (`∀ τ) = ap (`∀) (↻-ren-⇑ (liftₜ ρ) τ)
↻-ren-⇑ ρ (μ τ) = ap μ (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (π ⇒ τ) = ap₂ _⇒_ (↻-ren-⇑ₚ ρ π) (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (lab l) = refl
↻-ren-⇑ ρ (l ▹ₙ τ) = ap₂ _▹_ (↻-ren-⇑ₙₑ ρ l) (↻-ren-⇑ ρ τ)
↻-ren-⇑ ρ (Π r) = ap (λ x → Π · x) (↻-ren-⇑ ρ r) 
↻-ren-⇑ ρ (Σ r)  = ap (λ x → Σ · x) (↻-ren-⇑ ρ r)
↻-ren-⇑ r (⦅ ρ ⦆ ω) = cong-⦅ ↻-ren-⇑ᵣ r ρ ⦆
↻-ren-⇑ r (ρ₂ ∖ ρ₁) = ap₂ _∖_ (↻-ren-⇑ r ρ₂) (↻-ren-⇑ r ρ₁)
↻-ren-⇑ ρ ((φ $ τ) ) = ap₂ _$_ (↻-ren-⇑ ρ φ) (↻-ren-⇑ₙₑ ρ τ)

↻-ren-⇑ₙₑ ρ (` α) = refl
↻-ren-⇑ₙₑ ρ (τ₁ · τ₂) = ap₂ _·_ (↻-ren-⇑ₙₑ ρ τ₁) (↻-ren-⇑ ρ τ₂)

↻-ren-⇑ₚ ρ (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    ↻-ren-⇑ ρ ρ₁ 
  | ↻-ren-⇑ ρ ρ₂
  | ↻-ren-⇑ ρ ρ₃ = refl
↻-ren-⇑ₚ ρ (ρ₁ ≲ ρ₂) = ap₂ _≲_ (↻-ren-⇑ ρ ρ₁) (↻-ren-⇑ ρ ρ₂)

↻-ren-⇑ᵣ r [] = refl
↻-ren-⇑ᵣ r ((l , τ) ∷ ρ) rewrite ↻-ren-⇑ r τ | ↻-ren-⇑ᵣ r ρ = refl


--------------------------------------------------------------------------------
-- Membership is preserved by renaming, and vice-versa

∈-renₜNF : ∀ {l : Label} {τ : NormalType Δ₁ κ} {xs : RowLiteral (NormalType Δ₁ κ)} → 
             (r : Renaming Δ₁ Δ₂) → 
             (l , τ) ∈ xs → (l , ren r τ) ∈ ren r xs
∈-renₜNF r (here refl) = here refl
∈-renₜNF r (there i) = there (∈-renₜNF r i)

∈L-renₜNF : ∀ {l : Label} {xs : RowLiteral (NormalType Δ₁ κ)} → 
               (r : Renaming Δ₁ Δ₂) → 
               l ∈L xs → l ∈L ren r xs
∈L-renₜNF {xs = .((_ , _) ∷ _)} r Here = Here
∈L-renₜNF {xs = ((_ , τ) ∷ _)} r (There l∈xs) = There (∈L-renₜNF r l∈xs)

renRowₜNF-∈L : ∀ {l : Label} {xs : RowLiteral (NormalType Δ₁ κ)} → 
               (r : Renaming Δ₁ Δ₂) → 
               l ∈L ren r xs → l ∈L xs
renRowₜNF-∈L {xs = x ∷ xs} r Here = Here
renRowₜNF-∈L {xs = (l , τ) ∷ xs} r (There inn) = There (renRowₜNF-∈L r inn)

--------------------------------------------------------------------------------
-- Renaming commutes with η-norm 

↻-renₜNF-η-norm : ∀ (r : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
                    ren r (η-norm τ) ≡ η-norm (ren r τ) 
↻-renₜNF-η-norm {κ = ★} r τ = refl
↻-renₜNF-η-norm {κ = L} r τ = refl 
↻-renₜNF-η-norm {κ = κ `→ κ₁} r τ = ap `λ 
  (trans 
    (↻-renₜNF-η-norm (liftₜ r) (ren S τ · reify (reflect (` Z)))) 
    (ap η-norm (cong₂ _·_ (↻-weakenₜNE-ren r τ) (↻-renₜNF-η-norm (liftₜ r) (` Z)))))
↻-renₜNF-η-norm {κ = R[ κ ]} r τ = ap (_$ ren r τ) (ap `λ (↻-renₜNF-η-norm (liftₜ r) (` Z)))

--------------------------------------------------------------------------------
-- Renaming commutes over complement

↻-renRowₜNF-∖s : ∀ (r : Renaming Δ₁ Δ₂) → {ρ₂ ρ₁ : RowLiteral (NormalType Δ₁ κ)} → 
       ren r (ρ₂ ∖s ρ₁) ≡ ren r ρ₂ ∖s ren r ρ₁
↻-renRowₜNF-∖s r {[]} {ρ₁} = refl
↻-renRowₜNF-∖s r {(l , τ) ∷ ρ₂} {ρ₁} with l ∈L? ρ₁ | l ∈L? ren r ρ₁
... | yes p | yes q = ↻-renRowₜNF-∖s r {ρ₂} {ρ₁}
... | yes  p | no q = ⊥-elim (q (∈L-renₜNF r p))
... | no  p | yes q = ⊥-elim (p (renRowₜNF-∈L r q))
... | no  p | no q = ap ((l , ren r τ) ∷_) (↻-renRowₜNF-∖s r {ρ₂} {ρ₁})

