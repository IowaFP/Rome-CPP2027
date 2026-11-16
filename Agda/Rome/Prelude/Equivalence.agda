module Rome.Prelude.Equivalence where

open import Rome.Prelude.Base 
open import Rome.Prelude.GVars.Levels
open import Rome.Prelude.GVars.Sets
open import Rome.Prelude.Groupoids
open import Rome.Prelude.Homotopies

------------------------------------------------------------------------------
-- Sections and retractions

record section {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂)  where 
  constructor _,_ 
  field 
    `σ : B → A 
    sec : f ∘ `σ ∼ id     

id-section : section {A = A} {A} id 
id-section = id , refl-∼ 

record retraction {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor _,_ 
  field 
    `ρ : B → A 
    retr : `ρ ∘ f ∼ id 

id-retraction : retraction {A = A} {A} id 
id-retraction = id , refl-∼ 

record has-inverse {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor Inv 
  field 
    f⁻¹ : B → A 
    linv : f⁻¹ ∘ f ∼ id 
    rinv : f ∘ f⁻¹ ∼ id 

id-inv : has-inverse {A = A} {A} id 
id-inv = Inv id refl-∼ refl-∼ 


------------------------------------------------------------------------------
-- Equivalence

module _ where 
  open section ; open retraction ; open has-inverse 

  record is-equiv {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) : Set (ℓ₁ ⊔ ℓ₂) where
    constructor _,_ 
    field 
      sec : section f 
      retr : retraction f 
  open is-equiv

  -- smart destructors
  `sec `retr : {f : A → B} →  is-equiv f → B → A 
  `sec = `σ ∘ sec 
  `retr = `ρ ∘ retr 

  has-inverse⇒is-equiv : {f : A → B} → has-inverse f → is-equiv f
  has-inverse⇒is-equiv (Inv f⁻¹ linv rinv) = (f⁻¹ , rinv) , (f⁻¹ , linv)

  infixr 3 _≃_
  _≃_ : Set ℓ₁ → Set ℓ₂ → Set _ 
  A ≃ B = Σ[ f ∈ (A → B) ] (is-equiv f) 

  -- For lack of better notation, I'll write 
  -- - e ⁺ : A → B
  -- - e ⁻ : B → A 
  _⁺ : {A : Set ℓ₁} {B : Set ℓ₂} → A ≃ B → A → B 
  _⁺ = fst

  `inv _⁻ : {A : Set ℓ₁} {B : Set ℓ₂} → A ≃ B → B → A 
  `inv = `sec ∘ snd 
  _⁻ = `inv 

------------------------------------------------------------------------------
-- Given an equivalence e, its sections and retractions are equal. 

-- if f has a section g and retraction h then g ∼ h.
  is-equiv⇒equalSplits : ∀ {f : A → B} (p : is-equiv f) → `sec p ∼ `retr p
  is-equiv⇒equalSplits {f = f} ((g , G) , (h , H)) = begin
    g          ∼⟨ (H ·ᵣ g) ⁻¹ ⟩
    h ∘ f ∘ g  ∼⟨ h ·ₗ G ⟩
    h ∎
    where
      open HomReasoning

  is-equiv⇒has-inverse : {f : A → B} → is-equiv f → has-inverse f
  is-equiv⇒has-inverse {f = f} p@((g , G) , (h , H)) = Inv g L G 
    where
      open HomReasoning
      L : (g ∘ f) ∼ id
      L = begin
            g ∘ f ∼⟨ is-equiv⇒equalSplits p ·ᵣ f ⟩
            h ∘ f ∼⟨  H ⟩
            id ∎

------------------------------------------------------------------------------
-- Smart destructors for finding the linv and rinv properties 

  `linv : (e : A ≃ B) → e ⁻ ∘ e ⁺ ∼ id 
  `linv (f , e) = begin 
    `sec e ∘ f  ∼⟨ is-equiv⇒equalSplits e ·ᵣ f ⟩ 
    `retr e ∘ f ∼⟨ e .retr .retr ⟩ 
    id ∎
    where 
      open HomReasoning 

  `rinv : (e : A ≃ B) → e ⁺ ∘ e ⁻ ∼ id 
  `rinv (f , e) = e .sec .sec

------------------------------------------------------------------------------
-- _≃_ is an equivalence relation 

has-inverse-comp : {f : B → C} {g : A → B} → 
                   has-inverse f → has-inverse g → has-inverse (f ∘ g)
has-inverse-comp {f = f} {g = g} 
  (Inv f⁻¹ linv-f rinv-f) 
  (Inv g⁻¹ linv-g rinv-g) = Inv
    (g⁻¹ ∘ f⁻¹)
    (begin 
      g⁻¹ ∘ f⁻¹ ∘ f ∘ g ∼⟨ g⁻¹ ·ₗ linv-f ·ᵣ g ⟩ 
       g⁻¹ ∘ g ∼⟨ linv-g ⟩ 
      id ∎) 
    (begin 
      f ∘ g ∘ g⁻¹ ∘ f⁻¹ ∼⟨ f ·ₗ rinv-g ·ᵣ f⁻¹ ⟩ 
      f ∘ f⁻¹ ∼⟨ rinv-f ⟩ 
      id ∎)
  where open HomReasoning

is-equiv-comp : {f : B → C} {g : A → B} → 
                is-equiv f → 
                is-equiv g → 
                is-equiv (f ∘ g)
is-equiv-comp {f = f} {g = g} equiv-f equiv-g =
  has-inverse⇒is-equiv (has-inverse-comp has-inverse-f has-inverse-g)
  where
    has-inverse-f : has-inverse f
    has-inverse-f = is-equiv⇒has-inverse equiv-f

    has-inverse-g : has-inverse g
    has-inverse-g = is-equiv⇒has-inverse equiv-g

trans-≃ : A ≃ B → B ≃ C → A ≃ C
trans-≃ e1 e2 = (fst e2 ∘ fst e1) , (is-equiv-comp (snd e2) (snd e1))

sym-≃ : A ≃ B → B ≃ A
sym-≃ (f , eqv) with is-equiv⇒has-inverse eqv
... | Inv f⁻¹ linv-f rinv-f =  f⁻¹ , ((f , linv-f) , (f , rinv-f)) 

refl-≃ : A ≃ A
refl-≃ = id , (id , refl-∼) , (id , refl-∼)

-- _≃_ is an equivalence relation
≃-equiv : ∀ {A : Set ℓ₁} → IsEquivalence {A = Set ℓ₁} (_≃_)
≃-equiv = record { refl = refl-≃ ; sym = sym-≃ ; trans = trans-≃ }

--------------------------------------------------------------------------------
-- Equational reasoning over ≃ equivalence

module ≃-Reasoning where
  -- Usage:
  -- eq : A ≃ B
  -- eq = begin
  --   foo ≃⟨ ? ⟩
  --   ...
  --   ?   ≃⟨ ? ⟩
  --   bar ∎
  infixr 1 _≃⟨_⟩_
  _≃⟨_⟩_ : (A : Set ℓ₁) {B : Set ℓ₂} {C : Set ℓ₃} → A ≃ B → B ≃ C → A ≃ C
  _≃⟨_⟩_ A = trans-≃

  _∎ : ∀ (A : Set ℓ) → A ≃ A 
  _ ∎ = refl-≃


------------------------------------------------------------------------------
-- Injections 

is-inj : (f : A → B) → Set _ 
is-inj {A = A} f  = ∀ (x y : A) → f x ≡ f y → x ≡ y 

------------------------------------------------------------------------------
-- Embeddings are injections with an equivalence

is-emb : (f : A → B) → Set _ 
is-emb {A = A} f  = ∀ (x y : A) → is-equiv (ap f {x} {y})

_↪_ : Set ℓ₁ → Set ℓ₂ → Set _ 
A ↪ B = Σ[ f ∈ (A → B) ] (is-emb f) 

Emb : (f : A → B) → is-emb f → (x y : A) → (x ≡ y) ≃ (f x ≡ f y) 
Emb f e x y = ap f , e x y 

emb→inj : (f : A → B) → is-emb f → is-inj f 
emb→inj f emb x y = `sec (emb x y)

------------------------------------------------------------------------------
-- Fibers 

fib : (f : A → B) → (b : B) → Set _
fib {A = A} f b = Σ[ a ∈ A ] (f a ≡ b)
