-- 
module Rome.Types.Substitution where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars
open import Rome.Types.Syntax
open import Rome.Types.Renaming

--------------------------------------------------------------------------------
-- Type-in-Type Substitution

Substitution : KEnv → KEnv → Set
Substitution Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → Type Δ₂ κ

-- lifting a substitution over binders.
liftsₜ :  Substitution Δ₁ Δ₂ → Substitution (Δ₁ , κ) (Δ₂ , κ)
liftsₜ σ Z = ` Z
liftsₜ σ (S x) = weakenₜ (σ x)

-- This is simultaneous substitution: Given tr σ and type τ, we replace *all*
-- variables in τ with the types mapped to by σ.
subₜ : Substitution Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
subPredₜ : Substitution Δ₁ Δ₂ → Pred (Type Δ₁ κ) → Pred (Type Δ₂ κ)
subRowₜ : Substitution Δ₁ Δ₂ → RowLiteral (Type Δ₁ κ) → RowLiteral (Type Δ₂ κ)
orderedSubRowₜ : (σ : Substitution Δ₁ Δ₂) → (xs : RowLiteral (Type Δ₁ κ)) → Ordered xs → 
                 Ordered (subRowₜ σ xs)

subₜ σ (` x) = σ x
subₜ σ (`λ τ) = `λ (subₜ (liftsₜ σ) τ)
subₜ σ (τ₁ · τ₂) = (subₜ σ τ₁) · (subₜ σ τ₂)
subₜ σ (τ₁ `→ τ₂) = (subₜ σ τ₁) `→ (subₜ σ τ₂)
subₜ σ (π ⇒ τ) = subPredₜ σ π ⇒ subₜ σ τ 
subₜ σ (`∀ τ) = `∀ (subₜ (liftsₜ σ) τ)
subₜ σ (μ F) = μ (subₜ σ F)
subₜ σ (Π {notLabel = nl}) = Π {notLabel = nl}
subₜ σ (Σ {notLabel = nl}) = Σ {notLabel = nl}
subₜ σ (lab x) = lab x
subₜ σ (f $ a) = subₜ σ f $ subₜ σ a
subₜ σ (ρ₂ ∖ ρ₁) = subₜ σ ρ₂ ∖ subₜ σ ρ₁
subₜ σ (⦅ xs ⦆ oxs) = ⦅ subRowₜ σ xs ⦆ (fromWitness (orderedSubRowₜ σ xs (toWitness oxs)))
subₜ σ (l ▹ τ) = (subₜ σ l) ▹ (subₜ σ τ)

subRowₜ σ [] = [] 
subRowₜ σ ((l , τ) ∷ xs) = (l , subₜ σ τ) ∷ subRowₜ σ xs

orderedSubRowₜ r [] oxs = tt
orderedSubRowₜ r ((l , τ) ∷ []) oxs = tt
orderedSubRowₜ r ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedSubRowₜ r ((l₂ , υ) ∷ xs) oxs

subRowₜ-isMap : ∀ (σ : Substitution Δ₁ Δ₂) (xs : RowLiteral (Type Δ₁ κ)) → 
                  subRowₜ σ xs ≡ map (map₂ (subₜ σ)) xs

subRowₜ-isMap σ [] = refl
subRowₜ-isMap σ (x ∷ xs) = ap₂ _∷_ refl (subRowₜ-isMap σ xs)

subPredₜ σ (ρ₁ · ρ₂ ~ ρ₃) = subₜ σ ρ₁ · subₜ σ ρ₂ ~ subₜ σ ρ₃
subPredₜ σ (ρ₁ ≲ ρ₂) = (subₜ σ ρ₁) ≲ (subₜ σ ρ₂) 

-- Extension of a substitution by A
extendₜ : Substitution Δ₁ Δ₂ → (A : Type Δ₂ κ) → Substitution (Δ₁ , κ) Δ₂
extendₜ σ A Z = A
extendₜ σ A (S x) = σ x

-- Single variable subₜstitution is a special case of simultaneous subₜstitution.
_βₜ[_] : Type (Δ , κ₁) κ₂ → Type Δ κ₁ → Type Δ κ₂
B βₜ[ A ] = subₜ (extendₜ ` A) B

--------------------------------------------------------------------------------
-- Typeclass for Substitution

record SubstitutionTC (T₁ T₂ T₃ : KEnv → Kind → Set) : Set where
  constructor Sub
  field
    sub : (∀ {κ : Kind} → TVar Δ₁ κ → T₁ Δ₂ κ) → T₂ Δ₁ κ → T₃ Δ₂ κ
  _[_]ₛ : T₂ Δ₁ κ → (∀ {κ : Kind} → TVar Δ₁ κ → T₁ Δ₂ κ) → T₃ Δ₂ κ
  τ [ σ ]ₛ = sub σ τ

open SubstitutionTC {{...}} public
{-# DISPLAY sub σ τ = τ [ σ ]ₛ #-}

instance
  TypeSubstitution : SubstitutionTC Type Type Type
  TypeSubstitution = Sub subₜ

  PredSubstitution : SubstitutionTC Type (λ Δ κ → Pred (Type Δ κ)) (λ Δ κ → Pred (Type Δ κ))
  PredSubstitution = Sub subPredₜ

  RowSubstitution : SubstitutionTC Type (λ Δ κ → RowLiteral (Type Δ κ)) (λ Δ κ → RowLiteral (Type Δ κ))
  RowSubstitution = Sub subRowₜ


  




