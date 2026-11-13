module Rome.Prelude.Homotopies where

open import Rome.Prelude.Base
open import Rome.Prelude.GVars.Levels
open import Rome.Prelude.GVars.Sets

--------------------------------------------------------------------------------
-- Homotopies

private variable
    P : A → Set ℓ 
    f g h : (x : A) → P x

infix 4 _∼_
_∼_ : ((x : A) → P x) → ((x : A) → P x) → Set _
_∼_ {A = A} f g = (x : A) → f x ≡ g x

refl-∼ : f ∼ f
refl-∼ _ = refl

sym-∼ : f ∼ g → g ∼ f
sym-∼ f∼g = sym ∘ f∼g

trans-∼ : f ∼ g → g ∼ h → f ∼ h
trans-∼ f∼g g∼h x = trans (f∼g x) (g∼h x)

-- Left whiskering
infixl 25 _·ₗ_
_·ₗ_ : (h : B → C) → (H : f ∼ g) → (h ∘ f) ∼ (h ∘ g)
h ·ₗ H = ap h ∘ H

-- Right whiskering
infixl 25 _·ᵣ_
_·ᵣ_ : (H : g ∼ h) → (f : A → B) → (g ∘ f) ∼ (h ∘ f)
H ·ᵣ f = H ∘ f

-- _∼_ is an equivalence relation
∼-equiv : IsEquivalence (_∼_ {A = A} {P = P})
∼-equiv = record { refl = refl-∼ ; sym = sym-∼ ; trans = trans-∼ }

-- ((x : A) → B x , _∼_) is a setoid on any type A and family P.
∼-setoid : ∀ {A : Set ℓ₁} {P : A → Set ℓ₂} → Setoid (ℓ₁ ⊔ ℓ₂) _
∼-setoid {A = A} {P} .Setoid.Carrier = (x : A) → P x
∼-setoid {A = A} {P} .Setoid._≈_ = _∼_ {A = A} {P = P}
∼-setoid .Setoid.isEquivalence = ∼-equiv

-----------------------------------------------------------------------------
-- Reasoning syntax over homotopies

module HomReasoning {ℓ₁} {ℓ₂} {A : Set ℓ₁} {P : A → Set ℓ₂} where
  -- Open setoid reasoning syntax with carriers A and B. Usage:
  -- f : foo ∼ bar
  -- f = begin
  --   foo ∼⟨ ? ⟩
  --   ...
  --   ?   ∼⟨ ? ⟩
  --   bar ∎
  open import Relation.Binary.Reasoning.Base.Single (_∼_ {A = A} {P = P})
    refl-∼
    trans-∼ public
