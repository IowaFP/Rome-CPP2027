module Rome.NormalTypes.Renaming where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax

--------------------------------------------------------------------------------
-- Normal Type renaming

renₜNE   : Renaming Δ₁ Δ₂ → NeutralType Δ₁ κ → NeutralType Δ₂ κ
renₜNF     : Renaming Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
renRowₜNF : Renaming Δ₁ Δ₂ → RowLiteral (NormalType Δ₁ κ) → RowLiteral (NormalType Δ₂ κ)
renPredₜNF : Renaming Δ₁ Δ₂ → Pred (NormalType Δ₁ R[ κ ]) → Pred (NormalType Δ₂ R[ κ ])

orderedRenRowₜNF : (r : Renaming Δ₁ Δ₂) → (xs : RowLiteral (NormalType Δ₁ κ)) → Ordered xs → 
                 Ordered (renRowₜNF r xs)

nrlRenₜNF : ∀ (r : Renaming Δ₁ Δ₂) (ρ₁ ρ₂ : NormalType Δ₁ R[ κ ]) → notRowLiteralNF ρ₂ or notRowLiteralNF ρ₁ → 
              notRowLiteralNF (renₜNF r ρ₂) or notRowLiteralNF (renₜNF r ρ₁)
nrlRenₜNF' : ∀ (r : Renaming Δ₁ Δ₂) (ρ : NormalType Δ₁ R[ κ ]) → notRowLiteralNF ρ → 
              notRowLiteralNF (renₜNF r ρ)

renₜNE r (` x) = ` (r x)
renₜNE ρ (τ₁ · τ₂) = renₜNE ρ τ₁ · renₜNF ρ τ₂

renₜNF ρ (ne τ {g}) = ne (renₜNE ρ τ) {g}
renₜNF ρ (`λ τ) = `λ (renₜNF (liftₜ ρ) τ)
renₜNF ρ (τ₁ `→ τ₂) = (renₜNF ρ τ₁) `→ (renₜNF ρ τ₂)
renₜNF ρ (π ⇒ τ) = renPredₜNF ρ π ⇒ renₜNF ρ τ
renₜNF ρ (`∀ τ) = `∀ (renₜNF (liftₜ ρ) τ)
renₜNF ρ (μ τ) = μ (renₜNF ρ τ)
renₜNF ρ (lab x) = lab x
renₜNF ρ (Π τ) = Π (renₜNF ρ τ)
renₜNF ρ (Σ τ) = Σ (renₜNF ρ τ)
renₜNF r (⦅ ρ ⦆ ω) = ⦅ renRowₜNF r ρ ⦆ (fromWitness (orderedRenRowₜNF r ρ (toWitness ω)))
renₜNF ρ (l ▹ₙ τ) = renₜNE ρ l ▹ₙ (renₜNF ρ τ)
renₜNF r ((ρ₂ ∖ ρ₁) {nrl}) = (renₜNF r ρ₂ ∖ renₜNF r ρ₁) {nrl = fromWitness (nrlRenₜNF r ρ₁ ρ₂ (toWitness nrl))}
renₜNF ρ ((φ $ x)) = (renₜNF ρ φ $ renₜNE ρ x) 

renPredₜNF ρ (ρ₁ · ρ₂ ~ ρ₃) = (renₜNF ρ ρ₁) · (renₜNF ρ ρ₂) ~ (renₜNF ρ ρ₃)
renPredₜNF ρ (ρ₁ ≲ ρ₂) = (renₜNF ρ ρ₁) ≲ (renₜNF ρ ρ₂)

renRowₜNF _ [] = []
renRowₜNF r ((l , τ) ∷ ρ) = (l , renₜNF r τ) ∷ renRowₜNF r ρ

nrlRenₜNF' r (ne x) nrl = tt
nrlRenₜNF' r (ρ ∖ ρ₁) nrl = tt
nrlRenₜNF' r (x ▹ₙ ρ) nrl = tt
nrlRenₜNF' r ((φ $ ρ)) nrl = tt

nrlRenₜNF r ρ₁ ρ₂ (left x) = left (nrlRenₜNF' r ρ₂ x)
nrlRenₜNF r ρ₁ ρ₂ (right y) = right (nrlRenₜNF' r ρ₁ y) 

orderedRenRowₜNF r [] oxs = tt
orderedRenRowₜNF r ((l , τ) ∷ []) oxs = tt
orderedRenRowₜNF r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₜNF r ((l₂ , υ) ∷ xs) oxs

renRowₜNF-isMap : ∀ (r : Renaming Δ₁ Δ₂) (xs : RowLiteral (NormalType Δ₁ κ)) → 
                  renRowₜNF r xs ≡ map (map₂ (renₜNF r)) xs 
renRowₜNF-isMap r [] = refl
renRowₜNF-isMap r (x ∷ xs) = ap₂ _∷_ refl (renRowₜNF-isMap r xs)

--------------------------------------------------------------------------------
-- Weakening

weakenₜNF : NormalType Δ κ₂ → NormalType (Δ , κ₁) κ₂
weakenₜNF = renₜNF S

weakenₜNE : NeutralType Δ κ₂ → NeutralType (Δ , κ₁) κ₂
weakenₜNE = renₜNE S 

weakenPredₜNF : Pred (NormalType Δ R[ κ₂ ]) → Pred (NormalType (Δ , κ₁) R[ κ₂ ])
weakenPredₜNF = renPredₜNF S

--------------------------------------------------------------------------------
-- Renaming instances

instance
  NormalTypeRenaming : RenamingTC NormalType
  NormalTypeRenaming = Ren renₜNF

  NeutralTypeRenaming : RenamingTC NeutralType
  NeutralTypeRenaming = Ren renₜNE

  NormalPredRenaming : RenamingTC (λ Δ κ → Pred (NormalType Δ R[ κ ]))
  NormalPredRenaming = Ren renPredₜNF

  NormalRowLitRenaming : RenamingTC (λ Δ κ → RowLiteral (NormalType Δ κ))
  NormalRowLitRenaming = Ren renRowₜNF


  




