-- 
module Rome.NormalTypes.Syntax where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming using (liftₜ ; Renaming)




--------------------------------------------------------------------------------
-- Normal & Neutral types 

data NormalType (Δ : KEnv) : Kind → Set

IsNeutral IsNormal : NormalType Δ κ → Set 
isNeutral? : ∀ (τ : NormalType Δ κ) → Dec (IsNeutral τ)
isNormal? : ∀ (τ : NormalType Δ κ) → Dec (IsNormal τ)

notRowLiteralNF : NormalType Δ R[ κ ] → Set 
notRowLiteralNFs? : ∀ (τ₁ τ₂ : NormalType Δ R[ κ ]) → Dec (notRowLiteralNF τ₁ or notRowLiteralNF τ₂)

data NeutralType (Δ : KEnv) : Kind → Set where
  ` : 
      (α : TVar Δ κ) → 
      ---------------------------
      NeutralType Δ κ

  _·_ : 
      
      (f : NeutralType Δ (κ₁ `→ κ)) → 
      (τ : NormalType Δ κ₁) → 
      ---------------------------
      NeutralType Δ κ

data NormalType Δ where

  ne : 

      (x : NeutralType Δ κ) → {ground : Ground κ} → 
      --------------
      NormalType Δ κ

  _$_ : (φ : NormalType Δ (κ₁ `→ κ₂)) → NeutralType Δ R[ κ₁ ] →
          --------------------------------------------------
          NormalType Δ R[ κ₂ ]

  `λ :

      (τ : NormalType (Δ , κ₁) κ₂) → 
      --------------------------
      NormalType Δ (κ₁ `→ κ₂)
  _`→_ : 

         (τ₁ : NormalType Δ ★) →
         (τ₂ : NormalType Δ ★) → 
         --------
         NormalType Δ ★

  `∀    :
      
         {κ : Kind} → (τ : NormalType (Δ , κ) ★) →
         -------------
         NormalType Δ ★

  μ     :
      
      (φ : NormalType Δ (★ `→ ★)) →
      -------------------------
      NormalType Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : ∀ {κ : Kind} → 

         (π : Pred (NormalType Δ R[ κ ])) → (τ : NormalType Δ ★) → 
         ---------------------
         NormalType Δ ★

  ------------------------------------------------------------------
  -- Rω business


  ⦅_⦆ : (ρ : RowLiteral (NormalType Δ κ)) → (ω : True (ordered? ρ)) →
        ----------------------
       NormalType Δ R[ κ ]

--   -- labels
  lab :
    
        (l : Label) → 
        --------
        NormalType Δ L

  Π  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ------------------
      NormalType Δ ★


  Σ  : 

      (ρ : NormalType Δ R[ ★ ]) →
      ---------------
      NormalType Δ ★

  _∖_ : (ρ₂ ρ₁ : NormalType Δ R[ κ ]) → 
        {nrl : True (notRowLiteralNFs? ρ₂ ρ₁)} → 
        NormalType Δ R[ κ ]

  _▹ₙ_ : (l : NeutralType Δ L) (τ : NormalType Δ κ) → 
         ------------------------------------
         NormalType Δ R[ κ ]

--------------------------------------------------------------------------------
-- IsNeutral and IsNormal predicates

IsNeutral (ne x) = ⊤ 
IsNeutral _ = ⊥

isNeutral? (ne x) = yes tt
isNeutral? (l ▹ₙ τ) = no λ ()
isNeutral? (`λ x) = no λ ()
isNeutral? (x `→ x₁) = no λ ()
isNeutral? (`∀ x) = no λ ()
isNeutral? (μ x) = no λ ()
isNeutral? (π ⇒ x) = no λ ()
isNeutral? (⦅ ρ ⦆ ω) = no λ ()
isNeutral? (lab l) = no λ ()
isNeutral? (Π x) = no λ ()
isNeutral? (Σ x) = no λ ()
isNeutral? (c ∖ c₁) = no λ ()
isNeutral? ((φ $ n)) = no λ ()

IsNormal (ne x)     = ⊥
IsNormal _     = ⊤

isNormal? (ne x) = no λ ()
isNormal? (l ▹ₙ τ) = yes tt
isNormal? (`λ x) = yes tt
isNormal? (x `→ x₁) = yes tt
isNormal? (`∀ x) = yes tt
isNormal? (μ x) = yes tt
isNormal? (π ⇒ x) = yes tt
isNormal? (⦅ ρ ⦆ ω) = yes tt
isNormal? (lab l) = yes tt
isNormal? (Π x) = yes tt
isNormal? (Σ x) = yes tt
isNormal? (ρ₂ ∖ ρ₁) = yes tt
isNormal? ((φ $ n)) = yes tt                

--------------------------------------------------------------------------------
-- Ordered predicate

cong-⦅_⦆nf : {ρ₁ ρ₂ : RowLiteral (NormalType Δ κ)} {ω₁ : True (ordered? ρ₁)} {ω₂ : True (ordered? ρ₂)} → 
                 ρ₁ ≡ ρ₂ → 
                _≡_ {A = NormalType Δ R[ κ ]} (⦅ ρ₁ ⦆ ω₁) (⦅ ρ₂ ⦆ ω₂)
cong-⦅_⦆nf {ρ₁ = ρ₁} {_} {ω₁} {ω₂} refl rewrite OrderedIrrelevant ρ₁ ω₁ ω₂ = refl


inj-⦅⦆ : {ρ₁ ρ₂ : RowLiteral (NormalType Δ κ)} 
         {ω₁ : True (ordered? ρ₁)} 
         {ω₂ : True (ordered? ρ₂)} → 
         _≡_ {A = NormalType Δ R[ κ ]} (⦅ ρ₁ ⦆ ω₁) (⦅ ρ₂ ⦆ ω₂) → 
         ρ₁ ≡ ρ₂
inj-⦅⦆ {ρ₁ = ρ₁} {_} {ω₁} {ω₂} refl rewrite OrderedIrrelevant ρ₁ ω₁ ω₂ = refl
                
--------------------------------------------------------------------------------
-- Defining notRowLiteralNFs? predicate

notRowLiteralNF (ne x) = ⊤
notRowLiteralNF ((φ $ τ)) = ⊤
notRowLiteralNF (⦅ ρ ⦆ ω) = ⊥
notRowLiteralNF (τ ∖ τ₁) = ⊤
notRowLiteralNF (x ▹ₙ τ) = ⊤

notRowLiteralNFs? (ne x) _ = yes (left tt)
notRowLiteralNFs? ((τ₁ $ ρ)) _ = yes (left tt)
notRowLiteralNFs? (⦅ ρ ⦆ ω) (ne x) = yes (right tt)
notRowLiteralNFs? (⦅ ρ ⦆ ω) (⦅ ρ₁ ⦆ ω₁) = no λ { (left ()) ; (right ()) }
notRowLiteralNFs? (⦅ ρ ⦆ ω) (ρ₁ ∖ ρ₂) = yes (right tt)
notRowLiteralNFs? (⦅ ρ ⦆ ω) (x ▹ₙ ρ₁) = yes (right tt)
notRowLiteralNFs? (⦅ ρ ⦆ ω) ((φ $ _)) = yes (right tt)
notRowLiteralNFs? (ρ₂ ∖ ρ₃) _ = yes (left tt)
notRowLiteralNFs? (x ▹ₙ ρ₂) _ = yes (left tt)


cong-∖ : {τ₂ υ₂ : NormalType Δ R[ κ ]}
          {τ₁ υ₁ : NormalType Δ R[ κ ]}
          {nrl₁ : True (notRowLiteralNFs? τ₂ τ₁)} 
          {nrl₂ : True (notRowLiteralNFs? υ₂ υ₁)} → 
                 τ₂ ≡ υ₂ → 
                 τ₁ ≡ υ₁ → 
                _≡_ {A = NormalType Δ R[ κ ]} ((τ₂ ∖ τ₁) {nrl₁}) ((υ₂ ∖ υ₁) {nrl₂})
cong-∖ {τ₂ = τ₂} {τ₁ = τ₁} {nrl₁ = x} {x₁} refl refl rewrite Dec→Irrelevant _ (notRowLiteralNFs? τ₂ τ₁) x x₁ = refl

--------------------------------------------------------------------------------
-- There are no neutral types in empty contexts

noNeutrals : NeutralType ∅ κ → ⊥

noNeutrals (n · τ) = noNeutrals n 

--------------------------------------------------------------------------------
-- There are no complements in empty contexts 

noComplements : ∀ {ρ₁ ρ₂ ρ₃ : NormalType ∅ R[ κ ]}
                  (nrl : True (notRowLiteralNFs? ρ₃ ρ₂)) → 
                  ρ₁ ≡ (ρ₃ ∖ ρ₂) {nrl} → 
                  ⊥
noComplements {ρ₁ = ne x₁ ∖ _} {_} {_} nrl refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ ω ∖ ne x₁} {_} {_} nrl refl = ⊥-elim (noNeutrals x₁)
noComplements {ρ₁ = ⦅ ρ ⦆ ω ∖ ((ρ₂ ∖ ρ₃) {nrl'})} {_} {_} nrl refl = noComplements {ρ₂ = ρ₃} {ρ₂} nrl' refl
noComplements {ρ₁ = ⦅ ρ ⦆ ω ∖ (l ▹ₙ ρ₂)} {_} {_} nrl refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ⦅ ρ ⦆ ω ∖ ((φ $ τ))} {_} {_} nrl refl = ⊥-elim (noNeutrals τ)
noComplements {ρ₁ = ((ρ₃ ∖ ρ₂) {nrl'}) ∖ _} {_} {_} nrl refl = noComplements {ρ₂ = ρ₂} {ρ₃} nrl' refl
noComplements {ρ₁ = (l ▹ₙ ρ₃) ∖ _} {_} {_} nrl refl = ⊥-elim (noNeutrals l)
noComplements {ρ₁ = ((φ $ τ)) ∖ _} nrl refl = ⊥-elim (noNeutrals τ)

--------------------------------------------------------------------------------
-- Mapping type definitions over predicates 


mapPred : ∀ (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
 Pred (NormalType Δ₁ R[ κ₁ ]) → Pred (NormalType Δ₂ R[ κ₂ ])
mapPred P (ρ₁ · ρ₂ ~ ρ₃) = P ρ₁ · P ρ₂ ~ P ρ₃
mapPred P (ρ₁ ≲ ρ₂)      = P ρ₁ ≲ P ρ₂

mapPredHO : ∀ 
            (P : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) (Q : NormalType Δ₁ R[ κ₁ ] → NormalType Δ₂ R[ κ₂ ]) → 
            (q : ∀ (τ : NormalType Δ₁ R[ κ₁ ]) → P τ ≡ Q τ) →
            (π : Pred (NormalType Δ₁ R[ κ₁ ])) → mapPred P π ≡ mapPred Q π
mapPredHO P Q q (ρ₁ · ρ₂ ~ ρ₃) rewrite 
  q ρ₁ | q ρ₂ | q ρ₃ = refl
mapPredHO P Q q (ρ₁ ≲ ρ₂) rewrite 
  q ρ₁ | q ρ₂ = refl

mapPred-id : ∀ (π : Pred (NormalType Δ R[ κ ])) → mapPred id π ≡ π
mapPred-id (ρ₁ · ρ₂ ~ ρ₃) = refl
mapPred-id (ρ₁ ≲ ρ₂) = refl

--------------------------------------------------------------------------------
-- Injectivity lemmas for all the NormalType syntax

inj-` : ∀ {α β : TVar Δ κ} → _≡_ {A = NeutralType Δ κ} (` α) (` β) → α ≡ β 
inj-` refl = refl

inj-· : ∀ {f₁ f₂ : NeutralType Δ (κ₁ `→ κ₂)} {τ₁ τ₂ : NormalType Δ κ₁} → 
         f₁ · τ₁ ≡ f₂ · τ₂ → 
         f₁ ≡ f₂ × τ₁ ≡ τ₂ 
inj-· refl = refl , refl

inj-`λ :  {τ₁ τ₂ : NormalType (Δ , κ₁) κ₂} → `λ τ₁ ≡ `λ τ₂ → τ₁ ≡ τ₂
inj-`λ refl = refl

inj-`→ : ∀ {τ₁ τ₂ υ₁ υ₂ : NormalType Δ ★} → 
            τ₁ `→ τ₂ ≡ υ₁ `→ υ₂ → 
            τ₁ ≡ υ₁ × τ₂ ≡ υ₂ 
inj-`→ refl = refl , refl

inj-`∀ : ∀ {τ₁ τ₂ : NormalType (Δ , κ) ★} → 
           `∀ τ₁ ≡ `∀ τ₂ → 
           τ₁ ≡ τ₂ 
inj-`∀ refl = refl

-- inj-μ : ∀ {F₁ F₂ : NormalType Δ (★ `→ ★)} →
--           μ F₁ ≡ μ F₂ → 
--           F₁ ≡ F₂ 
-- inj-μ refl = refl

inj-⇒ : ∀ {π₁ π₂ : Pred (NormalType Δ R[ κ₁ ])} {τ₁ τ₂ : NormalType Δ ★} → 
           π₁ ⇒ τ₁ ≡ π₂ ⇒ τ₂ → 
           π₁ ≡ π₂ × τ₁ ≡ τ₂ 
inj-⇒ refl = refl , refl

inj-lab : ∀ {l₁ l₂ : Label} → _≡_ {A = NormalType Δ L} (lab l₁) (lab l₂) → l₁ ≡ l₂
inj-lab refl = refl

inj-Π : ∀ {ρ₁ ρ₂ : NormalType Δ R[ ★ ]} → Π ρ₁ ≡ Π ρ₂ → ρ₁ ≡ ρ₂
inj-Π refl = refl

inj-Σ : ∀ {ρ₁ ρ₂ : NormalType Δ R[ ★ ]} → Σ ρ₁ ≡ Σ ρ₂ → ρ₁ ≡ ρ₂
inj-Σ refl = refl


--------------------------------------------------------------------------------
-- injectivity of ne constructor (erasing proofs)

inj-ne : ∀ {e₁ e₂ : NeutralType Δ κ} {g₁ g₂ : Ground κ} → ne e₁ {g₁} ≡ ne e₂ {ground = g₂} → e₁ ≡ e₂
inj-ne {κ = κ} {g₁ = g₁} {g₂ = g₂} refl rewrite GroundIrrelevant κ g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Congruene for ne constructor

cong-ne : ∀ {x y : NeutralType Δ κ} {g₁ g₂ : Ground κ} →
          x ≡ y → ne x {g₁} ≡ ne y {g₂}
cong-ne {κ = κ} {g₁ = g₁} {g₂} refl rewrite GroundIrrelevant κ g₁ g₂ = refl

--------------------------------------------------------------------------------
-- Embedding Normal/neutral types back to Types

⇑ₜ        : NormalType Δ κ → Type Δ κ
⇑ᵣ     : RowLiteral (NormalType Δ κ) → RowLiteral (Type Δ κ)
⇑ₙₑ      : NeutralType Δ κ → Type Δ κ
⇑ₚ    : Pred (NormalType Δ κ) → Pred (Type Δ κ)
⇑ₒ : ∀ (ρ : RowLiteral (NormalType Δ κ)) → Ordered ρ → 
             Ordered (⇑ᵣ ρ)
             

⇑ₜ (ne x)        = ⇑ₙₑ x
⇑ₜ (`λ τ)        = `λ (⇑ₜ τ)
⇑ₜ (τ₁ `→ τ₂)    = ⇑ₜ τ₁ `→ ⇑ₜ τ₂
⇑ₜ (`∀ τ)        = `∀ (⇑ₜ τ)
⇑ₜ (μ τ)      = μ (⇑ₜ τ)
⇑ₜ  (lab l)      = lab l
⇑ₜ  (Π x)        = Π · ⇑ₜ x
⇑ₜ  (Σ x)        = Σ · ⇑ₜ x
⇑ₜ  (π ⇒ τ)      = (⇑ₚ π) ⇒ (⇑ₜ τ)
⇑ₜ  (⦅ ρ ⦆ ω)   = ⦅ ⇑ᵣ ρ ⦆ (fromWitness (⇑ₒ ρ (toWitness ω)))
⇑ₜ  (ρ₂ ∖ ρ₁)    = ⇑ₜ ρ₂ ∖ ⇑ₜ ρ₁
⇑ₜ  (l ▹ₙ τ)     = (⇑ₙₑ l) ▹ (⇑ₜ τ)
⇑ₜ  ((F $ τ))  = (⇑ₜ F) $ (⇑ₙₑ τ)

⇑ᵣ []            = []
⇑ᵣ ((l , τ) ∷ ρ) = ((l , ⇑ₜ τ) ∷ ⇑ᵣ ρ)

⇑ₒ [] ω                                  = tt
⇑ₒ (x ∷ []) ω                            = tt
⇑ₒ ((l₁ , _) ∷ (l₂ , _) ∷ ρ) (l₁<l₂ , ω) = l₁<l₂ , ⇑ₒ ((l₂ , _) ∷ ρ) ω

⇑ᵣ-isMap : ∀ (xs : RowLiteral (NormalType Δ₁ κ)) →
               ⇑ᵣ xs ≡ map (λ { (l , τ) → l , ⇑ₜ τ }) xs
⇑ᵣ-isMap []       = refl
⇑ᵣ-isMap (x ∷ xs) = ap₂ _∷_ refl (⇑ᵣ-isMap xs)

⇑ₙₑ (` x) = ` x
⇑ₙₑ (τ₁ · τ₂) = (⇑ₙₑ τ₁) · (⇑ₜ τ₂)

⇑ₚ (ρ₁ · ρ₂ ~ ρ₃) = (⇑ₜ ρ₁) · (⇑ₜ ρ₂) ~ (⇑ₜ ρ₃)
⇑ₚ (ρ₁ ≲ ρ₂)      = (⇑ₜ ρ₁) ≲ (⇑ₜ ρ₂)

--------------------------------------------------------------------------------
-- Typeclass for embedding

record EmbedTC (𝒯 𝒱 : KEnv → Kind → Set) : Set where
  constructor Embed
  field
    ⇑ : 𝒯 Δ κ → 𝒱 Δ κ
open EmbedTC {{...}} public

instance
  embed : EmbedTC NormalType Type
  embed = Embed ⇑ₜ

  embedNE : EmbedTC NeutralType Type
  embedNE = Embed ⇑ₙₑ

  embedPred : EmbedTC 
              (λ Δ → Pred ∘ NormalType Δ)
              (λ Δ → Pred ∘ Type Δ) 
  embedPred = Embed ⇑ₚ

  embedRow : EmbedTC 
              (λ Δ → RowLiteral ∘ NormalType Δ)
              (λ Δ → RowLiteral ∘ Type Δ) 
  embedRow = Embed ⇑ᵣ 

--------------------------------------------------------------------------------
-- ⇑ᵣ commutes with ∖s 

⇑ᵣ-preserves-labels : ∀ (l : Label) (xs : RowLiteral (NormalType Δ₁ κ)) → 
                          l ∈L xs ↔ l ∈L ⇑ᵣ xs
⇑ᵣ-preserves-labels l []       = (λ ()), (λ ())
⇑ᵣ-preserves-labels l (x ∷ xs) = 
  (λ { Here → Here ; (There l∈xs) → There (⇑ᵣ-preserves-labels l xs .to l∈xs) }) , 
  λ { Here → Here ; (There l∈⇑ᵣxs) → There (⇑ᵣ-preserves-labels l xs .from l∈⇑ᵣxs) }

↻-⇑ᵣ-∖s : ∀ (ys xs : RowLiteral (NormalType Δ₁ κ)) → 
               ⇑ᵣ (ys ∖s xs) ≡ ⇑ᵣ ys ∖s ⇑ᵣ xs
↻-⇑ᵣ-∖s [] xs = refl
↻-⇑ᵣ-∖s ((l , τ) ∷ ys) xs with l ∈L? xs | l ∈L? ⇑ᵣ xs
... | yes p | yes q  = ↻-⇑ᵣ-∖s ys xs
... | no  p | yes q  = ⊥-elim (p (⇑ᵣ-preserves-labels l xs .from q)) 
... | yes p | no  q  = ⊥-elim (q (⇑ᵣ-preserves-labels l xs .to p)) 
... | no  p | no  q  = ap ((l , ⇑ τ) ∷_) (↻-⇑ᵣ-∖s ys xs)

--------------------------------------------------------------------------------
-- row "constructors"

εNF : NormalType Δ R[ κ ]
εNF = ⦅ [] ⦆ tt
_▹'_ : Label → NormalType Δ κ → NormalType Δ R[ κ ] 
x ▹' τ = ⦅ [ (x , τ) ] ⦆ tt

_▹′_ : NormalType Δ L → NormalType Δ κ → NormalType Δ R[ κ ]
ne n ▹′ τ =  n ▹ₙ τ
lab l ▹′ τ = l ▹' τ

--------------------------------------------------------------------------------
-- Admissable constants

UnitNF : NormalType Δ ★
UnitNF = Π (⦅ [] ⦆ tt)

