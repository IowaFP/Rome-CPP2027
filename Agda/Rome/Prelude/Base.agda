module Rome.Prelude.Base where 

--------------------------------------------------------------------------------
-- =============================================================================
-- A bundle of commonly imported standard library modules
-- =============================================================================

--------------------------------------------------------------------------------
-- Agda level nonsense 

open import Agda.Primitive public

--------------------------------------------------------------------------------
-- Data

open import Data.Unit.Polymorphic 
  renaming (⊤ to ⊤ₚ ; tt to ttₚ) 
  hiding (_≟_) public 
open import Data.Unit hiding (_≟_) public 
open import Data.Empty public 

open import Data.Fin 
  using (Fin ; fromℕ ; inject₁ ; punchIn) 
  renaming (zero to fzero ; suc to fsuc ; _<_ to _≺_) public
import Data.Sum as Sum
  renaming (_⊎_ to _or_; inj₁ to left; inj₂ to right)

open import Data.Maybe using (Maybe ; just ; nothing) public
open import Data.Bool using (Bool ; true ; false ; not) public

open Sum using (_or_ ; left ; right) public
import Data.Product as Product
  renaming (proj₁ to fst ; proj₂ to snd) 
open Product 
  using (_×_ ; fst ; snd ; _,_ ; Σ-syntax ; ∃ ; ∃-syntax ; map₂) 
  public
open import Data.Product.Properties
open import Data.Product.Properties using (,-injectiveʳ ; ,-injectiveˡ ; Σ-≡,≡→≡) public

open import Data.Nat using (ℕ ; zero ; suc) public
open import Data.Nat.Properties using (suc-injective) public

open import Data.String hiding (_≈_ ; map ; length ; _++_) public
open import Relation.Binary.Structures using (IsStrictPartialOrder) public
open import Data.String.Properties renaming (<-isStrictPartialOrder-≈ to SPO) public

open import Data.List using (List ; [] ;  _∷_ ; [_] ; map ; length ; reverse ; _++_; lookup) public
open import Data.List.Relation.Unary.Any 
  using (Any ; here ; there) 
  renaming (map to map-any) public
open import Data.List.Relation.Unary.Any.Properties hiding (map-id ; map-cong ; map-∘) public
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ ) public

import Data.Vec as Vec using (Vec; tabulate)
open Vec public


--------------------------------------------------------------------------------
-- Function 

open import Function 
  using (_∘_ ; id ; const ; flip) public

--------------------------------------------------------------------------------
-- Relations

open import Relation.Binary.PropositionalEquality as Eq 
  renaming ([_] to [[_]]) public 
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality) public
open import Relation.Nullary using (¬_) public
open import Relation.Nullary.Negation using (contradiction; contraposition) public
open import Relation.Nullary using (Dec; yes; no ; map′ ; Irrelevant ; isYes ; isNo) public
open import Relation.Nullary.Decidable using (True ; toWitness ; fromWitness) public renaming (⌊_⌋ to ∥_∥)
open import Relation.Binary using (IsEquivalence ; Setoid) public

--------------------------------------------------------------------------------
-- Universe-polymorphic strings 

Label = String

--------------------------------------------------------------------------------
-- Bi-implication

infixr 1 _↔_
record _↔_  {ℓ₁ ℓ₂} (A : Set ℓ₁) (B : Set ℓ₂) : Set (ℓ₁ ⊔ ℓ₂) where 
  constructor _,_ 
  field 
    to : A → B 
    from : B → A 
open _↔_ public     

--------------------------------------------------------------------------------
-- Pair helpers

third : ∀ {A B C : Set} → A × B × C → C
third = snd ∘ snd

--------------------------------------------------------------------------------
-- congruence over a 3-ary function

cong₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
        (f : A → B → C → D) {x y u v l m} → 
        x ≡ y → u ≡ v → l ≡ m → f x u l ≡ f y v m
cong₃ f refl refl refl = refl

--------------------------------------------------------------------------------
-- HoTT ideas & notation 
-------------------------
-- Although we make heavy use of the UIP (thereby rejecting univalent
-- foundations), many homotopy TT concepts and notations are pleasant to work
-- with.

private variable 
  ℓ : Level 
  A B : Set ℓ 
  P : A → Set ℓ 

--------------------------------------------------------------------------------
-- The action on paths (or, cong)

-- HoTT-ists call it *the action on paths*, 
-- Agda stdlib calls it cong
ap : (f : A → B) → {x y : A} → x ≡ y → f x ≡ f y
ap = cong

ap₂ : {C : Set ℓ} → (f : A → B → C) → {x y : A} {a b : B} → 
      x ≡ y → a ≡ b → f x a ≡ f y b 
ap₂ = cong₂

ap₃ : ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d} 
        (f : A → B → C → D) {x y u v l m} → 
        x ≡ y → u ≡ v → l ≡ m → f x u l ≡ f y v m
ap₃ = cong₃    

-- identity functor law        
ap-id : {x y : A} → (p : x ≡ y) → p ≡ ap id p
ap-id refl = refl

-- composition functor law 
ap-comp : {C : Set ℓ} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) → 
          ap g (ap f p) ≡ ap (g ∘ f) p
ap-comp f g refl = refl

--------------------------------------------------------------------------------
-- Transports (or, subst)

-- HoTT-ists call it *transport*, Agda stdlib calls it subst
tr : ∀ (P : A → Set ℓ) → {x y : A} → x ≡ y → P x → P y
tr = subst

-- syntactic sugar for transports (\tb2)
infixr 5 _▸_ 
_▸_ : ∀ {P : A → Set ℓ} → {x y : A} → x ≡ y → P x → P y
p ▸ x = tr _ p x 

-- With explicit motive 
infixr 5 _⟨_⟩▸_
_⟨_⟩▸_ :  ∀ (P : A → Set ℓ) → {x y : A} → x ≡ y → P x → P y
_⟨_⟩▸_ = tr 

-- Dependent action on paths 
apd : {B : A → Set ℓ} (f : (x : A) → B x) → {x y : A} →
      (p : x ≡ y) → p ▸ (f x) ≡ f y
apd f refl = refl

--------------------------------------------------------------------------------
-- Sets observe the Uniqueness of Identity Principle (UIP). 
-- We work in Agda *with* Axiom K, so all types are sets.

UIP : (A : Set ℓ) → Set _ 
UIP A = ∀ {x y : A} → Irrelevant (x ≡ y) 

-- the UIP holds without --without-k
uip : UIP A 
uip refl refl = refl

------------------------------------------------------------------------------
-- Decidable types can be squashed into irrelevance

-- Decidable sets, when squashed, are irrelevant 
Dec→Irrelevant : ∀ {ℓ} (A : Set ℓ) → (d : Dec A) → Irrelevant (True d)
Dec→Irrelevant A (yes d) p₁ p₂ = refl
Dec→Irrelevant A (no  d) p₁ p₂ = refl


--------------------------------------------------------------------------------
-- Witness map: Dealing with witness of squashed evidence

-- When we use squashing to force irrelevance, we often still use that evidence
-- later. Since D is decidable (via d?), such evidence can be produced via
-- toWitness.  For example, when renaming the type (⦅ xs ⦆ ω), we have
--   ω : True (ordered? xs),
-- but we need evidence that 
--   True (ordered? (ren r xs)). 
-- So we have to write 
--   fromWitness (OrderedRenRowₜ r xs (toWitness ω)), 
-- which is ugly.  A cleaner way to view this is as a functor. I haven't given
-- more thought, particularly, on what the base categories are. That's not
-- terribly important.
wmap : ∀ {ℓ₁ ℓ₂} {A : Set ℓ₁} {D : A → Set ℓ₂} 
         {d? : (x : A) → Dec (D x)}
         {x y : A} → 
       (D x → D y) → True (d? x) → True (d? y)
wmap f d = fromWitness (f (toWitness d))