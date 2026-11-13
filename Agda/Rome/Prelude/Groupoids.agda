module Rome.Prelude.Groupoids where

open import Rome.Prelude.Base 
open import Rome.Prelude.GVars.Levels
open import Rome.Prelude.GVars.Sets
open import Rome.Prelude.Homotopies

private variable
    P : A → Set ℓ 

--------------------------------------------------------------------------------
-- We'll separate pre-order syntax so that it can be used for things like containment

record OrderSyntax {ℓ₁} {ℓ₂} 
                      {A : Set ℓ₁} 
                      (_≤_ : A → A → Set ℓ₂)  : Set (ℓ₁ ⊔ lsuc ℓ₂)  where
  infixl 25 _○_
  field
    -- Getting rid of refl, actually, means I can use this syntax on PERs
    -- Refl : {x : A} →  x ≤ x
    _○_ : {x y z : A} → x ≤ y → y ≤ z → x ≤ z

--------------------------------------------------------------------------------
-- Paths and homotopies form **groupoids**. 

-----------------------------------------------------------------------------
-- Syntax for groupoids

record GroupoidSyntax {ℓ₁} {ℓ₂} {A : Set ℓ₁} 
  (_≈_ : A → A → Set ℓ₂) 
  (pre : OrderSyntax _≈_)  : Set (ℓ₁ ⊔ lsuc ℓ₂)  where
  infixl 30 _⁻¹
  open OrderSyntax pre

  field
    _⁻¹ : {x y : A} → x ≈ y → y ≈ x

    -- The type of paths between paths. This abstraction is
    -- unfortunately necessary if we want to also
    -- abstract over groupoid properties.
    _≋_ : ∀ {x y : A} → x ≈ y → x ≈ y → Set ℓ₂
    eqv : ∀ {x y} → IsEquivalence (_≋_ {x} {y})

    -- Congruence
    _⋆_ : ∀ {x y z : A} {p h : x ≈ y} {q k : y ≈ z} →
          (H : p ≋ h) → (K : q ≋ k) →
          p ○ q ≋ h ○ k

    -- properties
    Refl : {x : A} → x ≈ x
    left-inv : ∀ {x y : A} (p : x ≈ y) → p ⁻¹ ○ p ≋ Refl
    right-inv : ∀ {x y : A} (p : x ≈ y) → p ○ p ⁻¹ ≋ Refl
    involution : ∀ {x y : A} (p : x ≈ y) → (p ⁻¹) ⁻¹ ≋ p
    left-identity : {x y : A} (p : x ≈ y) → Refl ○ p ≋ p
    right-identity : {x y : A} (p : x ≈ y) → p ○ Refl ≋ p
    assoc : {x y z w : A} → 
            (p : x ≈ y) (q : y ≈ z) (r : z ≈ w) → 
            (p ○ q) ○ r ≋ p ○ (q ○ r)

  -- -- left congruence
  _⋆ₗ_ : ∀ {x y z : A} {p h : x ≈ y} →
          (H : p ≋ h) (q : y ≈ z) →
          p ○ q ≋ h ○ q
  H ⋆ₗ q = H ⋆ refl-≋
    where
      open IsEquivalence eqv renaming (refl to refl-≋)

  _⋆ᵣ_ : ∀ {x y z : A} {q h : y ≈ z} →
          (p : x ≈ y) (H : q ≋ h)  →
          p ○ q ≋ p ○ h
  p ⋆ᵣ H = refl-≋ ⋆ H
    where
      open IsEquivalence eqv renaming (refl to refl-≋)

--------------------------------------------------------------------------------
-- Export as typeclasses

open OrderSyntax {{...}} public
open GroupoidSyntax {{...}} hiding (_≋_) public


-------------------------------------------------------------------------------
-- The groupoidal structure of types (and paths)

instance
  PathOrder : OrderSyntax {A = A} (_≡_)
  PathOrder .OrderSyntax._○_ = trans

  PathGroupoid : GroupoidSyntax {A = A} (_≡_) PathOrder
  PathGroupoid .GroupoidSyntax._⁻¹ = sym
  PathGroupoid .GroupoidSyntax.Refl = refl
  PathGroupoid .GroupoidSyntax._≋_ = _≡_
  PathGroupoid .GroupoidSyntax.eqv = isEquivalence
  PathGroupoid .GroupoidSyntax._⋆_ refl refl = refl 
  PathGroupoid .GroupoidSyntax.left-inv refl = refl 
  PathGroupoid .GroupoidSyntax.right-inv refl = refl 
  PathGroupoid .GroupoidSyntax.involution refl = refl 
  PathGroupoid .GroupoidSyntax.left-identity refl = refl 
  PathGroupoid .GroupoidSyntax.right-identity refl = refl 
  PathGroupoid .GroupoidSyntax.assoc refl refl refl = refl 

-------------------------------------------------------------------------------
-- The groupoidal structure of homotopies

instance
  HtpyOrder : OrderSyntax {A = (x : A) → P x} (_∼_)
  HtpyOrder .OrderSyntax._○_ = trans-∼

  HtpyGroupoid : GroupoidSyntax {A = (x : A) → P x} (_∼_) HtpyOrder
  HtpyGroupoid .GroupoidSyntax.Refl = refl-∼
  HtpyGroupoid .GroupoidSyntax._⁻¹ = sym-∼
  HtpyGroupoid .GroupoidSyntax._≋_ = _∼_ 
  HtpyGroupoid .GroupoidSyntax.eqv = ∼-equiv 
  HtpyGroupoid .GroupoidSyntax._⋆_ p∼h q∼k x = _⋆_ {{PathGroupoid}}  (p∼h x) (q∼k x)
  HtpyGroupoid .GroupoidSyntax.left-inv H = left-inv  ∘ H
  HtpyGroupoid .GroupoidSyntax.right-inv H = right-inv  ∘ H 
  HtpyGroupoid .GroupoidSyntax.involution p =  involution ∘ p
  HtpyGroupoid .GroupoidSyntax.left-identity  _ = refl-∼ 
  HtpyGroupoid .GroupoidSyntax.right-identity H = right-identity ∘ H 
  HtpyGroupoid .GroupoidSyntax.assoc H K L x = assoc (H x) (K x) (L x)
    
