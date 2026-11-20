
module Rome.Kinds.Syntax where

open import Rome.Prelude


--------------------------------------------------------------------------------
-- 2.1 Kinds

data Kind : Set where
  ★ L     : Kind
  _`→_ : Kind → Kind → Kind
  R[_]  : Kind → Kind

infixr 5 _`→_

--------------------------------------------------------------------------------
-- Partitioning of kinds by labels and label-valued functions

NotLabel : Kind → Set 
NotLabel ★ = ⊤
NotLabel L = ⊥
NotLabel (κ₁ `→ κ₂) = NotLabel κ₂
NotLabel R[ κ ] = NotLabel κ

NotLabelIrrelevant : ∀ κ → Irrelevant (NotLabel κ)
NotLabelIrrelevant ★ nl₁ nl₂ = refl
NotLabelIrrelevant (κ `→ κ₁) nl₁ nl₂ = NotLabelIrrelevant κ₁ nl₁ nl₂
NotLabelIrrelevant R[ κ ] nl₁ nl₂ = NotLabelIrrelevant κ nl₁ nl₂

--------------------------------------------------------------------------------
-- Partitioning of kinds by row/arrow kind

Ground : Kind → Set 
Ground ★ = ⊤
Ground L = ⊤
Ground (κ `→ κ₁) = ⊥
Ground R[ κ ] = ⊥

ground? : ∀ (κ : Kind) → Dec (Ground κ)
ground? ★ = yes tt
ground? L = yes tt
ground? (_ `→ _) = no (λ ())
ground? R[ _ ] = no (λ ())

GroundIrrelevant : ∀ κ → Irrelevant (Ground κ) 
GroundIrrelevant ★ _ _ = refl 
GroundIrrelevant L _ _ = refl
GroundIrrelevant (κ `→ κ₁) () 
GroundIrrelevant R[ κ ] ()

--------------------------------------------------------------------------------
-- contexts Kind (ℓ|ι)(Δ|Δ₁|Δ₂)*(₁|₂|₃|₄|₅)*


data KEnv : Set where
  ∅ : KEnv 
  _,_ : KEnv → Kind → KEnv

--------------------------------------------------------------------------------
-- Type variables

private
  variable
    Δ Δ₁ Δ₂ Δ₃ : KEnv
    κ κ₁ κ₂ : Kind

data TVar : KEnv → Kind → Set where
  Z : TVar (Δ , κ) κ
  S : TVar Δ κ₁ → TVar (Δ , κ₂) κ₁
