
module Rome.Prelude.Containment where

open import Rome.Prelude.Base
open import Rome.Prelude.GVars.Sets

------------------------------------------------------------------------------
-- Definition of containment and containment over a disjoint sum

_⊆_ : List A → List A → Set _ 
_⊆_ {A = A} xs ys = ∀ (x : A) → x ∈ xs → x ∈ ys

_⊆[_⊹_] : List A → List A → List A → Set _ 
_⊆[_⊹_] {A = A} xs ys zs = ∀ (x : A) → x ∈ xs → x ∈ ys or x ∈ zs

-- --------------------------------------------------------------------------------
-- List inclusion forms a pre-order

⊆-refl : ∀ {xs : List A} →
         xs ⊆ xs
⊆-refl x x∈xs = x∈xs

⊆-trans : ∀ {xs ys zs : List A} →
          xs ⊆ ys → ys ⊆ zs → xs ⊆ zs
⊆-trans i₁ i₂ = λ x → i₂ x ∘ i₁ x

-- --------------------------------------------------------------------------------
-- related elements are mapped together

map-∈ :  ∀ {xs : List A} {x : A} →
             (f : A → B) →
             x ∈ xs →
             f x ∈ map f xs
map-∈ f (here refl) = here refl
map-∈ f (there x∈xs) = there (map-∈ f x∈xs)

-- --------------------------------------------------------------------------------
-- Helper absurd eliminators

∈-elim : ∀ {x : A} →
          x ∈ [] → C
∈-elim ()

absurd-left-elim : ∀ {x : A} → x ∈ [] or B → B
absurd-left-elim (right y) = y

absurd-right-elim : ∀ {x : B} → A or x ∈ [] → A
absurd-right-elim (left x) = x

-- --------------------------------------------------------------------------------
-- map f is monotonic over _⊆_

⊆-map : ∀  {xs ys : List A} →
             (f : A → B) →
             xs ⊆ ys →
             map f xs ⊆ map f ys

⊆-map {xs = []} {[]} f i = λ { x () }
⊆-map {xs = []} {x ∷ ys} f i = λ { x () }
⊆-map {xs = x ∷ xs} {[]} f i = ∈-elim (i x (here refl))
⊆-map {xs = x ∷ xs} {y ∷ ys} f i z (here refl) = map-∈ f (i x (here refl))
⊆-map {xs = x ∷ xs} {y ∷ ys} f i z (there z∈fxs) = ⊆-map f (λ x₁ z₁ → i x₁ (there z₁)) z z∈fxs

-- --------------------------------------------------------------------------------
-- map f is monotonic over disjoint inclusion maps

⊆-map-or : ∀ {xs ys zs : List A} →
             (f : A → B) →
             xs ⊆[ ys ⊹ zs ] →
             map f xs ⊆[ map f ys ⊹ map f zs ]
⊆-map-or {xs = x ∷ xs} {[]} {zs} f i fx fx∈ with i x (here refl)
... | right y = right (⊆-map f (λ x x∈xs → absurd-left-elim (i x x∈xs)) fx fx∈)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {[]} f i fx fx∈ with i x (here refl)
... | left h = left (⊆-map f (λ x x∈xs → absurd-right-elim (i x x∈xs)) fx fx∈)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (here refl) with i x (here refl)
... | left x∈yys  = left (map-∈ f x∈yys)
... | right x∈zzs = right (map-∈ f x∈zzs)
⊆-map-or {xs = x ∷ xs} {y ∷ ys} {z ∷ zs} f i fx (there fx∈) = ⊆-map-or f (λ x₁ z₁ → i x₁ (there z₁)) fx fx∈

------------------------------------------------------------------------------
-- IsMap asserts that a function is extensionally equivalent to a map

IsMap : ∀ (f* : List A → List B) → (f : A → B) → Set _ 
IsMap {A = A} f* f = ∀ (xs : List A) → f* xs ≡ map f xs

-- --------------------------------------------------------------------------------
-- Containment is preserved by f* if f* is a map

⊆-cong : ∀ {xs ys : List A} →
            (f : A → B) (f* : List A → List B) →
            IsMap f* f →
            xs ⊆ ys →
            f* xs ⊆ f* ys
⊆-cong {xs = xs} {ys} f f* isMap i = 
  tr (λ X → X ⊆ f* ys) (sym (isMap xs)) (tr (λ X → map f xs ⊆ X) (sym (isMap ys)) (⊆-map f i))

⊆-cong-or : ∀ {xs ys zs : List A} →
            (f : A → B) (f* : List A → List B) →
            IsMap f* f →
            xs ⊆[ ys ⊹ zs ] →
            f* xs ⊆[ f* ys ⊹ f* zs ]
⊆-cong-or {xs = xs} {ys} {zs} f f* isMap i rewrite isMap xs | isMap ys | isMap zs = ⊆-map-or f i

-----------------------------------------------------------------------------------------
-- substitution of the membership relation

∈-subst₁ : ∀ {x y : A} {xs : List A} → x ∈ xs → x ≡ y → y ∈ xs
∈-subst₁ i refl = i

∈-subst₂ : ∀ {x : A} {xs ys : List A} → x ∈ xs → xs ≡ ys → x ∈ ys
∈-subst₂ i refl = i

-----------------------------------------------------------------------------------------
-- left truncation of an inclusion

truncate-⊆ : ∀ {x : A} → 
             {xs ys : List A } → 
             (x ∷ xs) ⊆ ys → 
             xs ⊆ ys 
truncate-⊆ {x = x} {xs} {ys} i = λ a → i a ∘ there 

truncate-⊆-or : ∀ {z : A} → 
             {xs ys zs : List A } → 
             (z ∷ zs) ⊆[ xs ⊹ ys ] → 
             zs ⊆[ xs ⊹ ys ] 
truncate-⊆-or {z = z} i = λ a → i a ∘ there

--------------------------------------------------------------------------------
-- A tail is contained by itself

tail-⊆ : ∀ {x : A} {xs : List A} → 
         xs ⊆ (x ∷ xs)
tail-⊆ {x} {xs} a a∈xs = there a∈xs 

--------------------------------------------------------------------------------
-- Label membership

infix 2 _∈L_

data _∈L_ {A : Set ℓ} : (l : Label) → List (Label × A) → Set ℓ  where
  Here : ∀ {τ : A} {xs : List (String × A)} {l : Label} → 
         l ∈L (l , τ) ∷ xs
  There : ∀ {τ : A} {xs : List (Label × A)} {l l' : Label} → 
          l ∈L xs → l ∈L (l' , τ) ∷ xs

-- Label membership is decidable
_∈L?_ : ∀ (l : Label) (xs : List (Label × A)) → Dec (l ∈L xs)
l ∈L? [] = no (λ { () })
l ∈L? ((l' , _) ∷ xs) with l ≟ l' 
... | yes refl = yes Here
... | no  p with l ∈L? xs 
...         | yes p = yes (There p)
...         | no  q = no λ { Here → p refl ; (There x) → q x }

--------------------------------------------------------------------------------
-- There is an obvious projection from _∈_ to _∈L_ 

∈-to-∈L : ∀ {l : Label} {a : A} {xs : List (Label × A)} → (l , a) ∈ xs → l ∈L xs
∈-to-∈L (here refl) = Here
∈-to-∈L (there inxs) = There (∈-to-∈L inxs)

--------------------------------------------------------------------------------
-- Containment relation on labels

_⊆L_ : List (Label × A) → List (Label × B) → Set _ 
xs ⊆L ys = ∀ (l : Label) → l ∈L xs → l ∈L ys

--------------------------------------------------------------------------------
-- Disjointedness predicate on labels

_＃_ : List (Label × A) → List (Label × A) → Set _ 
_＃_ {A = A} xs ys =  ∀ (l : Label) → l ∈L xs → ¬ (l ∈L ys)

--------------------------------------------------------------------------------
-- 

＃-sym : ∀ {xs ys : List (Label × A)} → xs ＃ ys → ys ＃ xs 
＃-sym dsj l l∈Lys l∈Lxs = dsj l l∈Lxs l∈Lys 

--------------------------------------------------------------------------------
-- Surjectivity predicate on transformations

SurjectiveOnLabels : ∀ (f* : List (Label × A) → List (Label × B)) → Set _ 
SurjectiveOnLabels {A = A} f* = ∀ (xs : List (Label × A)) → f* xs ⊆L xs

--------------------------------------------------------------------------------
-- Label preservation predicate

PreservesLabels : ∀ (f* : List (Label × A) → List (Label × B)) → Set _ 
PreservesLabels {A = A} f* = ∀ (xs : List (Label × A)) → xs ⊆L f* xs

--------------------------------------------------------------------------------
-- Mapping preserves labels and is surjective on labels

mapPreservesLabels : ∀ (f : A → B) → PreservesLabels (map (map₂ f))
mapPreservesLabels f (x ∷ xs) l Here = Here
mapPreservesLabels f (x ∷ xs) l (There l∈xs) = There (mapPreservesLabels f xs l l∈xs)

mapSurjective : ∀ (f : A → B) → SurjectiveOnLabels (map (map₂ f))
mapSurjective f (x ∷ xs) l Here = Here
mapSurjective f (x ∷ xs) l (There inn) = There (mapSurjective f xs l inn)

--------------------------------------------------------------------------------
-- disjointedness is preserved by transformations that are surjective on labels

Preserves＃ : ∀ (f* : List (Label × A) → List (Label × B)) → 
                               SurjectiveOnLabels f* → 
                               ∀ (xs ys : List (Label × A)) → 
                               xs ＃ ys → f* xs ＃ f* ys
Preserves＃ f* srj xs ys dsj l l∈Lf*xs l∈Lf*ys = dsj l (srj xs l l∈Lf*xs) (srj ys l l∈Lf*ys)

--------------------------------------------------------------------------------
-- Any transformation equivalent to a map preserves labels

mapPreserves＃ : ∀ (f* : List (Label × A) → List (Label × B)) → 
                   (f : A → B) → 
                   (∀ (xs : List (Label × A)) → f* xs ≡ map (map₂ f) xs) → 
                   ∀ (xs ys : List (Label × A)) → 
                   xs ＃ ys → f* xs ＃ f* ys
mapPreserves＃ f* f isMap xs ys dsj rewrite isMap xs | isMap ys = Preserves＃ (map (map₂ f)) (mapSurjective f) xs ys dsj
