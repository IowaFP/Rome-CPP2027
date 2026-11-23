module Rome.NBE.Syntax where

open import Data.Product using (_×_ ; _,_)
open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming using (liftₜ ; Renaming)

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming


--------------------------------------------------------------------------------
-- Semantic types (definition)

module _ where 
  private 
    variable 
      A : Set
      n m : ℕ 

  infixr 5 _↪_
  _↪_ : ℕ → Set → Set 
  n ↪ A = Fin n → Label × A
  
  Row : Set → Set 
  Row A = ∃[ n ] (n ↪ A)

--------------------------------------------------------------------------------
-- Ordered predicate on finite maps

  OrderedRow′ : (n : ℕ) → (n ↪ A) → Set
  OrderedRow′ zero P          = ⊤
  OrderedRow′ (suc zero) P    = ⊤
  OrderedRow′ (suc (suc n)) P = 
    (P fzero .fst < P (fsuc fzero) .fst)  × OrderedRow′ (suc n) (P ∘ fsuc)

  OrderedRow : Row A → Set
  OrderedRow (n , P) = OrderedRow′ n P

--------------------------------------------------------------------------------
-- smart constructors

  -- extension
  _⨾⨾_ :  Label × A → Row A → Row A
  e ⨾⨾ (n , P) =  suc n , λ { fzero     → e 
                            ; (fsuc x) → P x }
  -- the empty row                                  
  ε : Row A
  ε = 0 , λ ()
  
  -- Singleton rows
  ⁅_⁆ : Label × A → Row A
  ⁅ e ⁆ = 1 , λ { fzero → e }

--------------------------------------------------------------------------------
-- some helpers
  
  substᵢₓ : n ≡ m → 
           (n ↪ A) → 
            m ↪ A 
  substᵢₓ {A = A} = tr (_↪ A)

--------------------------------------------------------------------------------
-- Semantic types (definition)

data SemRow (Δ : KEnv) (𝒯 : KEnv → Set) : Kind → Set 
NotRowLiteral : {Δ : KEnv} {𝒯 : KEnv → Set} → 
                SemRow Δ 𝒯 R[ κ ] → Set 
notRowLiterals? : {Δ : KEnv} {𝒯 : KEnv → Set} → 
                  (ρ₂ ρ₁ : SemRow Δ 𝒯 R[ κ ]) → 
                  Dec (NotRowLiteral ρ₂ or NotRowLiteral ρ₁)

data SemRow Δ 𝒯 where
  _$_ : (φ : ∀  {Δ' : KEnv} → Renaming Δ Δ' → NeutralType Δ' κ₁ → 𝒯 Δ') → 
          NeutralType Δ R[ κ₁ ] → 
          SemRow Δ 𝒯 R[ κ₂ ]
  _▹_ : ∀ {κ : Kind} → NeutralType Δ L → 𝒯 Δ → SemRow Δ 𝒯 R[ κ ]
  row : (ρ : Row (𝒯 Δ)) → OrderedRow ρ → SemRow Δ 𝒯 R[ κ ]
  _∖_ : (ρ₂ ρ₁ : SemRow Δ 𝒯 R[ κ ]) → 
        {nr : NotRowLiteral ρ₂ or NotRowLiteral ρ₁} →
        SemRow Δ 𝒯 R[ κ ]

NotRowLiteral (x ▹ x₁) = ⊤
NotRowLiteral (row ρ x) = ⊥
NotRowLiteral (ρ ∖ ρ₁) = ⊤
NotRowLiteral (φ $ ρ) = ⊤

notRowLiterals? (x ▹ x₁) ρ₁ = yes (left tt)
notRowLiterals? (ρ₂ ∖ ρ₃) ρ₁ = yes (left tt)
notRowLiterals? (φ $ ρ) ρ₁ = yes (left tt)
notRowLiterals? (row ρ x) (x₁ ▹ x₂) = yes (right tt)
notRowLiterals? (row ρ x) (row ρ₁ x₁) = no (λ { (left ()) ; (right ()) })
notRowLiterals? (row ρ x) (ρ₁ ∖ ρ₂) = yes (right tt)
notRowLiterals? (row ρ x) (φ $ τ) = yes (right tt)

--------------------------------------------------------------------------------
-- Defining Semantic types

SemType : KEnv → Kind → Set
SemType Δ ★          = NormalType Δ ★
SemType Δ L           = NormalType Δ L
SemType Δ₁ (κ₁ `→ κ₂) = 
  ∀ {Δ₂ : KEnv} → (r : Renaming Δ₁ Δ₂) (v : SemType Δ₂ κ₁) → SemType Δ₂ κ₂
SemType Δ₁ R[ κ ]      =  SemRow Δ₁ (λ Δ₂ → SemType Δ₂ κ) R[ κ ] 

--------------------------------------------------------------------------------
-- aliases

KripkeFunction : KEnv → Kind → Kind → Set
KripkeFunctionNE : KEnv → Kind → Kind → Set
KripkeFunction Δ₁ κ₁ κ₂ =  
  ∀ {Δ₂ : KEnv} → Renaming Δ₁ Δ₂ → SemType Δ₂ κ₁ → SemType Δ₂ κ₂
KripkeFunctionNE Δ₁ κ₁ κ₂ =  
  ∀ {Δ₂ : KEnv} → Renaming Δ₁ Δ₂ → NeutralType Δ₂ κ₁ → SemType Δ₂ κ₂

--------------------------------------------------------------------------------
-- Truncating a row preserves ordering

ordered-cut : ∀ {n : ℕ} → 
                {P : (suc n) ↪ SemType Δ κ} → 
              OrderedRow (suc n , P) → OrderedRow (n , P ∘ fsuc)
ordered-cut {n = zero} ω = tt
ordered-cut {n = suc n} ω = ω .snd


--------------------------------------------------------------------------------
-- Ordering is preserved by mapping

orderedMap₂ : ∀ {n} {P : n ↪ SemType Δ κ₁} → 
               (f : SemType Δ κ₁ → SemType Δ κ₂) → 
               OrderedRow (n , P) → 
               OrderedRow (n , map₂ f ∘ P)
orderedMap₂ {n = zero} {P} f ω = tt
orderedMap₂ {n = suc zero} {P} f ω = tt
orderedMap₂ {n = suc (suc n)} {P} f ω = (ω .fst) , (orderedMap₂ f (ω .snd))

--------------------------------------------------------------------------------
-- Semantic row operators


