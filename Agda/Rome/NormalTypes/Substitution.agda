module Rome.NormalTypes.Substitution where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NBE.Normalization

open import Rome.Metatheory.Soundness
open import Rome.Types.Equivalence

--------------------------------------------------------------------------------
-- Normality preserving Type Substitution

SubstitutionₜNF : KEnv → KEnv → Set
SubstitutionₜNF Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → NormalType Δ₂ κ

-- lifting a substitution over binders.
liftsₜNF :  SubstitutionₜNF Δ₁ Δ₂ → SubstitutionₜNF (Δ₁ , κ) (Δ₂ , κ)
liftsₜNF {κ = κ} σ Z = η-norm (` Z)
liftsₜNF σ (S x) = weakenₜNF (σ x)

-- Identity substitution (s.t. substₜNF idSubst x = (idSubst x))
idSubst : SubstitutionₜNF Δ Δ
idSubst = η-norm ∘ `

-- Effectively: denormalize `n`, substitute, then normalize.
subₜNF : SubstitutionₜNF Δ₁ Δ₂ → NormalType Δ₁ κ → NormalType Δ₂ κ
subₜNF σ τ = ⇓ₜ (sub (⇑ ∘ σ) (⇑ τ))

subₜNE : SubstitutionₜNF Δ₁ Δ₂ → NeutralType Δ₁ κ → NormalType Δ₂ κ
subₜNE σ n = ⇓ₜ (sub (⇑ ∘ σ) (⇑ₙₑ n))

subRowₜNF : SubstitutionₜNF Δ₁ Δ₂ → RowLiteral (NormalType Δ₁ κ) → RowLiteral (NormalType Δ₂ κ)
subRowₜNF σ n = ⇓ᵣ (sub (⇑ ∘ σ) (⇑ᵣ n))

subPredₜNF : SubstitutionₜNF Δ₁ Δ₂ → Pred (NormalType Δ₁ R[ κ ]) → Pred (NormalType Δ₂ R[ κ ])
subPredₜNF σ π = ⇓ₚ (sub (⇑ ∘ σ) (⇑ₚ π))

-- Extend the substitution with a NormalType
extendₜNF : SubstitutionₜNF Δ₁ Δ₂ → (A : NormalType Δ₂ κ) → SubstitutionₜNF (Δ₁ , κ) Δ₂
extendₜNF σ A Z = A
extendₜNF σ A (S x) = σ x

-- Single variable substitution is a special case of simultaneous substitution.
_βₜNF[_] : NormalType (Δ , κ₁) κ₂ → NormalType Δ κ₁ → NormalType Δ κ₂
τ₁ βₜNF[ τ₂ ] = subₜNF (extendₜNF idSubst τ₂) τ₁

--------------------------------------------------------------------------------
-- Substitution preserves ordering of rows

orderedSubRowₜNF : (σ : SubstitutionₜNF Δ₁ Δ₂) → (xs : RowLiteral (NormalType Δ₁ κ)) → Ordered xs → 
                 Ordered (subRowₜNF σ xs)
orderedSubRowₜNF σ [] oxs = tt
orderedSubRowₜNF σ ((l , τ) ∷ []) oxs = tt
orderedSubRowₜNF σ ((l₁ , τ) ∷ (l₂ , υ) ∷ xs) (l₁<l₂ , oxs) = l₁<l₂ , orderedSubRowₜNF σ ((l₂ , υ) ∷ xs) oxs

--------------------------------------------------------------------------------
-- Application *is* β-substitution due to canonicity of arrow kinded types

_·′_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ κ₁ → NormalType Δ κ₂
`λ M ·′ v = M βₜNF[ v ]     


map-map₂-' : (ρ : RowLiteral (NormalType Δ κ₁)) (f : NormalType Δ (κ₁ `→ κ₂)) →
                Ordered ρ → Ordered ((map (map₂ (f ·′_)) ρ))
map-map₂-' [] f ω = tt
map-map₂-' (x₁ ∷ []) f ω = tt
map-map₂-' (x₁ ∷ x₂ ∷ ρ) f ω = ω .fst , map-map₂-' (x₂ ∷ ρ) f (ω .snd)


--------------------------------------------------------------------------------
-- Normality-preserving $ 


_$'_ : NormalType Δ (κ₁ `→ κ₂) → NormalType Δ R[ κ₁ ] → NormalType Δ R[ κ₂ ]
φ $' ρ = ⇓ₜ (⇑ φ $ ⇑ ρ)

-- This is just an alias for what happens to xs in:
--   φ $' ⦅ xs ⦆ oxs
_$′_ : NormalType Δ (κ₁ `→ κ₂) →
 RowLiteral (NormalType Δ κ₁) → 
 RowLiteral (NormalType Δ κ₂)
φ $′ xs =  reifyRow
             (⟦ (⇑ᵣ xs) ⟧ᵣ idEnv .fst ,
               (map₂ (⟦ (⇑ₜ φ) ⟧ₜ idEnv id)) ∘ (⟦ (⇑ᵣ xs) ⟧ᵣ idEnv .snd))

--------------------------------------------------------------------------------
-- Substitution instances

instance
  NormalTypeSubstitutionNF : SubstitutionTC NormalType NormalType NormalType
  NormalTypeSubstitutionNF = Sub (λ τ σ → subₜNF σ τ)

  NeutralTypeSubstitutionNF : SubstitutionTC NormalType NeutralType NormalType
  NeutralTypeSubstitutionNF = Sub (λ n σ → subₜNE σ n)

  NormalPredSubstitutionNF : SubstitutionTC NormalType (λ Δ κ → Pred (NormalType Δ R[ κ ])) (λ Δ κ → Pred (NormalType Δ R[ κ ]))
  NormalPredSubstitutionNF = Sub (λ π σ → subPredₜNF σ π)

  NormalRowLitSubstitutionNF : SubstitutionTC NormalType (λ Δ κ → RowLiteral (NormalType Δ κ)) (λ Δ κ → RowLiteral (NormalType Δ κ))
  NormalRowLitSubstitutionNF = Sub (λ ρ σ → subRowₜNF σ ρ)
