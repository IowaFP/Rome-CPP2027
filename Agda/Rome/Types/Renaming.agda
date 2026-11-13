-- 
module Rome.Types.Renaming where

open import Rome.Prelude
open import Rome.Types.Syntax
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

--------------------------------------------------------------------------------
-- Type Renaming

Renaming : KEnv → KEnv → Set
Renaming Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → TVar Δ₂ κ

-- Renaming homotopies 
infix 5 _∼ᵣ_
_∼ᵣ_ : ∀ {Δ₁ : KEnv} (ρ₁ ρ₂ : Renaming Δ₁ Δ₂) → Set
_∼ᵣ_ {Δ₁ = Δ₁} ρ₁ ρ₂ = ∀ {κ : Kind} (x : TVar Δ₁ κ) → ρ₁ x ≡ ρ₂ x


-- lifting over binders.
liftₜ : Renaming Δ₁ Δ₂ → Renaming (Δ₁ , κ) (Δ₂ , κ)
liftₜ ρ Z = Z
liftₜ ρ (S x) = S (ρ x)

renₜ : Renaming Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
renPredₜ : Renaming Δ₁ Δ₂ → Pred (Type Δ₁ κ) → Pred (Type Δ₂ κ)
renRowₜ : Renaming Δ₁ Δ₂ → RowLiteral (Type Δ₁ κ) → RowLiteral (Type Δ₂ κ)
orderedRenRowₜ : (r : Renaming Δ₁ Δ₂) → 
                 (xs : RowLiteral (Type Δ₁ κ)) → 
                 Ordered xs → 
                 Ordered (renRowₜ r xs)

renₜ r (` x) = ` (r x)
renₜ r (`λ τ) = `λ (renₜ (liftₜ r) τ)
renₜ r (τ₁ · τ₂) = (renₜ r τ₁) · (renₜ r τ₂)
renₜ r (τ₁ `→ τ₂) = (renₜ r τ₁) `→ (renₜ r τ₂)
renₜ r (π ⇒ τ) = renPredₜ r π ⇒ renₜ r τ 
renₜ r (`∀ τ) = `∀ (renₜ (liftₜ r) τ)
-- renₜ r (μ F) = μ (renₜ r F)
renₜ r (Π {notLabel = nl}) = Π {notLabel = nl}
renₜ r (Σ {notLabel = nl}) = Σ {notLabel = nl}
renₜ r (lab x) = lab x
renₜ r (f $ m) = renₜ r f $ renₜ r m
renₜ r (⦅ xs ⦆ oxs) = ⦅ renRowₜ r xs ⦆ (fromWitness (orderedRenRowₜ r xs (toWitness oxs)))
renₜ r (ρ₂ ∖ ρ₁) = renₜ r ρ₂ ∖ renₜ r ρ₁
renₜ r (l ▹ τ) = renₜ r l ▹ renₜ r τ
renₜ r (μ φ) = μ (renₜ r φ)

renPredₜ ρ (ρ₁ · ρ₂ ~ ρ₃) = renₜ ρ ρ₁ · renₜ ρ ρ₂ ~ renₜ ρ ρ₃
renPredₜ ρ (ρ₁ ≲ ρ₂) = (renₜ ρ ρ₁) ≲ (renₜ ρ ρ₂) 

renRowₜ r [] = [] 
renRowₜ r ((l , τ) ∷ xs) = (l , renₜ r τ) ∷ renRowₜ r xs

orderedRenRowₜ r [] oxs = tt
orderedRenRowₜ r ((l , τ) ∷ []) oxs = tt
orderedRenRowₜ r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedRenRowₜ r ((l₂ , υ) ∷ xs) oxs

weakenₜ : Type Δ κ₂ → Type (Δ , κ₁) κ₂
weakenₜ = renₜ S

weakenPredₜ : Pred (Type Δ κ₂) → Pred (Type (Δ , κ₁) κ₂)
weakenPredₜ =  renPredₜ S

--------------------------------------------------------------------------------
-- Typeclass for renaming

record RenamingTC (T : KEnv → Kind → Set) : Set where
  constructor Ren
  field
    ren : Renaming Δ₁ Δ₂ → T Δ₁ κ → T Δ₂ κ
open RenamingTC {{...}} public

instance
  TypeRenaming : RenamingTC Type
  TypeRenaming = Ren renₜ

  PredRenaming : RenamingTC (λ Δ κ → Pred (Type Δ κ))
  PredRenaming = Ren renPredₜ

  RowRenaming : RenamingTC (λ Δ κ → RowLiteral (Type Δ κ))
  RowRenaming = Ren renRowₜ


  




