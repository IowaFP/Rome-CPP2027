module Rome.Metatheory.Normalization where

open import Rome.Prelude
open import Rome.Kinds hiding (ℓ ; ℓ₁ ; ℓ₂ ; ℓ₃)
open import Rome.Types
open import Rome.Types.Equivalence
open import Rome.NormalTypes
open import Rome.NBE
open import Rome.Metatheory.Consistency
open import Rome.Metatheory.Stability

-------------------------------------------------------------------------------
-- Small step relation on types 
-- (_≡ₜ_ without eq-refl, eq-sym, and eq-trans)

infix 3 _—→ₜ_
infix 3 _—→ₚ_
data _—→ₚ_ : Pred (Type Δ R[ κ ]) → Pred (Type Δ R[ κ ]) → Set
data _—→ₜ_ : Type Δ κ → Type Δ κ → Set 

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Label
    l l₁ l₂ l₃ : Type Δ L
    ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
    π₁ π₂    : Pred (Type Δ R[ κ ])
    τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 

data _—→ᵣ_ : RowLiteral (Type Δ κ) → RowLiteral (Type Δ κ) → Set where 

  eq-[] : 
    
    _—→ᵣ_  {Δ = Δ} {κ = κ} [] []
    
  eq-cons : {xs ys : RowLiteral (Type Δ κ)} → 

            ℓ₁ ≡ ℓ₂ → τ₁ —→ₜ τ₂ → xs —→ᵣ ys → 
            -----------------------
            ((ℓ₁ , τ₁) ∷ xs) —→ᵣ ((ℓ₂ , τ₂) ∷ ys)

data _—→ₚ_ where

  _eq-≲_ : 

        τ₁ —→ₜ υ₁ → τ₂ —→ₜ υ₂ → 
        --------------------
        τ₁ ≲ τ₂ —→ₚ  υ₁ ≲ υ₂

  _eq-·_~_ : 

        τ₁ —→ₜ υ₁ → τ₂ —→ₜ υ₂ → τ₃ —→ₜ υ₃ → 
        -----------------------------------
        τ₁ · τ₂ ~ τ₃ —→ₚ  υ₁ · υ₂ ~ υ₃

data _—→ₜ_ where 

  -- -------------------------------------
  -- Congruence rules

    eq-→ : 

        τ₁ —→ₜ τ₂ → υ₁ —→ₜ υ₂ →
        -----------------------
        τ₁ `→ υ₁ —→ₜ τ₂ `→ υ₂

    eq-∀ : 

        τ —→ₜ υ →
        ----------------
        `∀ τ —→ₜ `∀ υ

    eq-μ : 

        τ —→ₜ υ →
        ----------------
        μ τ —→ₜ μ υ

    eq-λ : ∀ {τ υ : Type (Δ , κ₁) κ₂} → 

        τ —→ₜ υ →
        ----------------
        `λ τ —→ₜ `λ υ

    eq-· :

        τ₁ —→ₜ υ₁ → τ₂ —→ₜ υ₂ →
        ---------------------
        τ₁ · τ₂ —→ₜ υ₁ · υ₂

    eq-$ : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 

        τ₁ —→ₜ υ₁ → τ₂ —→ₜ υ₂ →
        ---------------------
        τ₁ $ τ₂ —→ₜ υ₁ $ υ₂        

    eq-⇒ :

         π₁ —→ₚ π₂ → τ₁ —→ₜ τ₂ →
        ------------------------
        (π₁ ⇒ τ₁) —→ₜ (π₂ ⇒ τ₂)

    eq-lab : 
           
           ℓ₁ ≡ ℓ₂ →
           -------------
           lab {Δ = Δ} ℓ₁ —→ₜ lab ℓ₂
    
    eq-row : 
        ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} {ω₁ : True (ordered? ρ₁)} 
          {ω₂ : True (ordered? ρ₂)} → 
  
        ρ₁ —→ᵣ ρ₂ → 
        -------------------------------------------
        ⦅ ρ₁ ⦆ ω₁ —→ₜ ⦅ ρ₂ ⦆ ω₂

    eq-▹ : ∀ {l₁ l₂ : Type Δ L} {τ₁ τ₂ : Type Δ κ} → 
         
           l₁ —→ₜ l₂   →    τ₁ —→ₜ τ₂ → 
           ------------------------------------
           (l₁ ▹ τ₁) —→ₜ (l₂ ▹ τ₂)

    eq-∖ : ∀ {ρ₂ ρ₁ υ₂ υ₁ : Type Δ R[ κ ]} → 
         
           ρ₂ —→ₜ υ₂   →    ρ₁ —→ₜ υ₁ → 
           ------------------------------------
           (ρ₂ ∖ ρ₁) —→ₜ (υ₂ ∖ υ₁)

  -- -------------------------------------
  -- η-laws  
         
    eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 


        ----------------------------
        f —→ₜ `λ (weakenₜ f · (` Z))

  -- -------------------------------------
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ , κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) —→ₜ (τ₁ βₜ[ τ₂ ])

    eq-labTy : 

        l —→ₜ lab ℓ → 
        -------------------------------------------
        (l ▹ τ) —→ₜ ⦅ [ (ℓ  , τ) ] ⦆ tt

    eq-▹$ : ∀ {κ₁ : Kind} {l : Type Δ L} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        ---------------------------------
        (F $ (l ▹ τ)) —→ₜ (l ▹ (F · τ))

    eq-$-∖ : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : Type Δ R[ κ₁ ]} → 

      
      ------------------------------------------
      F $ (ρ₂ ∖ ρ₁) —→ₜ (F $ ρ₂) ∖ (F $ ρ₁)

    eq-map : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ : RowLiteral (Type Δ κ₁)} {ω : True (ordered? ρ)} → 

         -------------------------------
         F $ (⦅ ρ ⦆ ω) —→ₜ ⦅ map (map₂ (F ·_)) ρ ⦆ (fromWitness (map-map₂ {Ty = Type} ρ (F ·_) (toWitness ω)))

    eq-map-id : ∀ {κ : Kind} {τ : Type Δ R[ κ ]} → 

        ---------------------------------------- 
        (`λ {κ₁ = κ} (` Z)) $ τ —→ₜ τ

    eq-map-∘ : ∀ {f : Type Δ (κ₂ `→ κ₃)} {g : Type Δ (κ₁ `→ κ₂)} {τ : Type Δ R[ κ₁ ]} → 

        ---------------------------------------- 
        (f $ (g $ τ))  —→ₜ (`λ (weakenₜ f · (weakenₜ g · (` Z)))) $ τ 
    
    eq-Π : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : NotLabel κ} → 

         ----------------------------
         Π {notLabel = nl} · ρ —→ₜ Π {notLabel = nl} $ ρ

    eq-Σ : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : NotLabel κ} → 

         ----------------------------
         Σ {notLabel = nl} · ρ —→ₜ Σ {notLabel = nl} $ ρ
        
    eq-Π-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : NotLabel κ₂} → 

        ----------------------------
        (Π {notLabel = nl} · ρ) · τ —→ₜ Π {notLabel = nl} · (ρ ?? τ)

    eq-Σ-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : NotLabel κ₂} → 

        ----------------------------
        (Σ {notLabel = nl} · ρ) · τ —→ₜ Σ {notLabel = nl} · (ρ ?? τ)

    eq-compl : ∀ {xs ys : RowLiteral (Type Δ κ)} 
                 {oxs : True (ordered? xs)} 
                 {oys : True (ordered? ys)} 
                 {ozs : True (ordered? (xs ∖s ys))} → 

                 --------------------------------------------
                 (⦅ xs ⦆ oxs) ∖ (⦅ ys ⦆ oys) —→ₜ ⦅ (xs ∖s ys) ⦆ ozs

--------------------------------------------------------------------------------
-- Promoting a step to an equivalence

steps : ∀ {τ υ : Type Δ κ} → τ —→ₜ υ → τ ≡ₜ υ 
stepsₚ : ∀ {π₁ π₂ : Pred (Type Δ R[ κ ])} → π₁ —→ₚ π₂ → π₁ ≡ₚ π₂
stepsᵣ : ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} → ρ₁ —→ᵣ ρ₂ → ρ₁ ≡ᵣ ρ₂

stepsₚ (x eq-≲ x₁) = (steps x) eq-≲ (steps x₁)
stepsₚ (x eq-· x₁ ~ x₂) = steps x eq-· steps x₁ ~ steps x₂
stepsᵣ eq-[] = eq-[]
stepsᵣ (eq-cons x x₁ s) = eq-cons x (steps x₁) (stepsᵣ s) 

steps (eq-→ s s₁) = eq-→ (steps s) (steps s₁)
steps (eq-∀ s) = eq-∀ (steps s)
steps (eq-μ s) = eq-μ (steps s)
steps (eq-λ s) = eq-λ (steps s)
steps (eq-· s s₁) = eq-· (steps s) (steps s₁)
steps (eq-$ s s₁) = eq-$ (steps s) (steps s₁)
steps (eq-⇒ x s) = eq-⇒ (stepsₚ x) (steps s)
steps (eq-lab x) = eq-lab x
steps (eq-row x) = eq-row (stepsᵣ x)
steps (eq-▹ s s₁) = eq-▹ (steps s) (steps s₁)
steps (eq-∖ s s₁) = eq-∖ (steps s) (steps s₁)
steps eq-η = eq-η
steps eq-β = eq-β
steps (eq-labTy s) = eq-labTy (steps s)
steps eq-▹$ = eq-▹$
steps eq-$-∖ = eq-$-∖
steps eq-map = eq-map
steps eq-map-id = eq-map-id
steps eq-map-∘ = eq-map-∘
steps eq-Π = eq-Π
steps eq-Σ = eq-Σ
steps eq-Π-assoc = eq-Π-assoc
steps eq-Σ-assoc = eq-Σ-assoc
steps eq-compl = eq-compl 

--------------------------------------------------------------------------------
-- By definition, _≡ₜ_ is the corresponding many-step relation 

_—→ₜ*_ : (τ υ : Type Δ κ) → Set
τ —→ₜ* υ = τ ≡ₜ υ

--------------------------------------------------------------------------------
-- We'll say a type τ : Type Δ κ is "in normal form" if it's a
-- fixed-point of normalization (⇑ ∘ ⇓). In other words, the normalization
-- procedure has no effect on the type.

NormalForm  : Type Δ κ → Set _ 
NormalForm τ = (⇑ ∘ ⇓) τ ≡ τ

-- All normal types are in normal form
allNormal : (τ : NormalType Δ κ) → NormalForm (⇑ τ)
allNormal τ = cong ⇑ (stability τ) 

-------------------------------------------------------------------------------
-- -- Types that are normal have a certain form 

-- NormalForm  : Type Δ κ → Set _ 
-- NormalFormₚ : Pred (Type Δ R[ κ ]) → Set _ 
-- NormalFormᵣ : RowLiteral (Type Δ κ) → Set _ 
-- NeutralForm : Type Δ κ → Set _ 

-- NormalForm (` α) = {!   !}
-- NormalForm (`λ τ) = NormalForm τ
-- NormalForm (τ · τ₁) = NeutralForm τ × NormalForm τ₁
-- NormalForm (τ `→ τ₁) = NormalForm τ × NormalForm τ₁
-- NormalForm (`∀ τ) = NormalForm τ
-- NormalForm (μ τ) = NormalForm τ
-- NormalForm (π ⇒ τ) = NormalFormₚ π × NormalForm τ
-- NormalForm (⦅ xs ⦆ ordered) = NormalFormᵣ xs
-- NormalForm (lab l) = ⊤
-- NormalForm (τ ▹ τ₁) = {!   !}
-- NormalForm (τ $ τ₁) = {!   !}
-- NormalForm Π = {!   !}
-- NormalForm Σ = {!   !}
-- NormalForm (τ ∖ τ₁) = {!   !} 
-- NeutralForm ν = {!   !} 

-- NormalFormₚ π = {!   !} 
-- NormalFormᵣ ρ = {!   !} 

-- allNormal : (τ : NormalType Δ κ) → NormalForm (⇑ τ)
-- allNormal = {!   !} 

--------------------------------------------------------------------------------
-- Normal forms indeed are normal w.r.t. type reduction:

_—↛ₜ  : Type Δ κ → Set 
_—↛ₜ {Δ = Δ} {κ = κ} τ  = ¬ (Σ[ υ ∈ (Type Δ κ) ] (τ —→ₜ υ))

doesntStep : (τ : Type Δ κ) → NormalForm τ → τ —↛ₜ 
doesntStep τ n (υ , eq-→ {τ₁ = τ₁} {τ₂} steps₁ steps₂) = {! doesntStep τ₁   !} -- doesntStep _ _ (_ , steps₁)
doesntStep τ n (υ , eq-∀ steps₁) = {!   !}
doesntStep τ n (υ , eq-μ steps₁) = {!   !}
doesntStep τ n (υ , eq-λ steps₁) = {!   !}
doesntStep τ n (υ , eq-· steps₁ steps₂) = {!   !}
doesntStep τ n (υ , eq-$ steps₁ steps₂) = {!   !}
doesntStep τ n (υ , eq-⇒ x steps₁) = {!   !}
doesntStep τ n (υ , eq-lab x) = {!   !}
doesntStep τ n (υ , eq-row x) = {!   !}
doesntStep τ n (υ , eq-▹ steps₁ steps₂) = {!   !}
doesntStep τ n (υ , eq-∖ steps₁ steps₂) = {!   !}
doesntStep τ n (υ , eq-η) = {!   !}
doesntStep τ n (υ , eq-β) = {!   !}
doesntStep τ n (υ , eq-labTy steps₁) = {!   !}
doesntStep τ n (υ , eq-▹$) = {!   !}
doesntStep τ n (υ , eq-$-∖) = {!   !}
doesntStep τ n (υ , eq-map-id) = {!   !}
doesntStep τ n (υ , eq-map-∘) = {!   !}
doesntStep τ n (υ , eq-Π) = {!   !}
doesntStep τ n (υ , eq-Σ) = {!   !}
doesntStep τ n (υ , eq-Π-assoc) = {!   !}
doesntStep τ n (υ , eq-Σ-assoc) = {!   !} 

--------------------------------------------------------------------------------
-- (Weak) Normalization: every type τ steps to a normal form ⇑ υ.
-- This follows directly from consistency.

normalization : ∀ (τ : Type Δ κ) → Σ[ υ ∈ Type Δ κ ] (τ —→ₜ* υ × NormalForm υ)
normalization τ = ⇑ (⇓ τ) , consistency τ , allNormal (⇓ τ)

