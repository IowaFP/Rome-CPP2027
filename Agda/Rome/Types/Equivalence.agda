module Rome.Types.Equivalence where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars hiding (ℓ ; ℓ₁ ; ℓ₂ ; ℓ₃ ; ℓ₄)

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NBE.Syntax
open import Rome.NBE.Normalization



-------------------------------------------------------------------------------
-- Small step relation on terms

infix 3 _≡ₜ_
infix 3 _≡ₚ_
data _≡ₚ_ : Pred (Type Δ R[ κ ]) → Pred (Type Δ R[ κ ]) → Set
data _≡ₜ_ : Type Δ κ → Type Δ κ → Set 

private
  variable
    ℓ ℓ₁ ℓ₂ ℓ₃ : Label
    l l₁ l₂ l₃ : Type Δ L
    ρ₁ ρ₂ ρ₃   : Type Δ R[ κ ]
    π₁ π₂    : Pred (Type Δ R[ κ ])
    τ τ₁ τ₂ τ₃ υ υ₁ υ₂ υ₃ : Type Δ κ 

data _≡ᵣ_ : RowLiteral (Type Δ κ) → RowLiteral (Type Δ κ) → Set where 

  eq-[] : 
    
    _≡ᵣ_  {Δ = Δ} {κ = κ} [] []
    
  eq-cons : {xs ys : RowLiteral (Type Δ κ)} → 

            ℓ₁ ≡ ℓ₂ → τ₁ ≡ₜ τ₂ → xs ≡ᵣ ys → 
            -----------------------
            ((ℓ₁ , τ₁) ∷ xs) ≡ᵣ ((ℓ₂ , τ₂) ∷ ys)

data _≡ₚ_ where

  _eq-≲_ : 

        τ₁ ≡ₜ υ₁ → τ₂ ≡ₜ υ₂ → 
        --------------------
        τ₁ ≲ τ₂ ≡ₚ  υ₁ ≲ υ₂

  _eq-·_~_ : 

        τ₁ ≡ₜ υ₁ → τ₂ ≡ₜ υ₂ → τ₃ ≡ₜ υ₃ → 
        -----------------------------------
        τ₁ · τ₂ ~ τ₃ ≡ₚ  υ₁ · υ₂ ~ υ₃

data _≡ₜ_ where 

  -- -------------------------------------
  -- Eq. relation
    
    eq-refl : 

        ------
        τ ≡ₜ τ 

    eq-sym : 
    
        τ₁ ≡ₜ τ₂ →
        ----------
        τ₂ ≡ₜ τ₁

    eq-trans : 
    
        τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → 
        ---------------------
        τ₁ ≡ₜ τ₃

  -- -------------------------------------
  -- Congruence rules

    eq-→ : 

        τ₁ ≡ₜ τ₂ → υ₁ ≡ₜ υ₂ →
        -----------------------
        τ₁ `→ υ₁ ≡ₜ τ₂ `→ υ₂

    eq-∀ : 

        τ ≡ₜ υ →
        ----------------
        `∀ τ ≡ₜ `∀ υ

    eq-μ : 

        τ ≡ₜ υ →
        ----------------
        μ τ ≡ₜ μ υ

    eq-λ : ∀ {τ υ : Type (Δ , κ₁) κ₂} → 

        τ ≡ₜ υ →
        ----------------
        `λ τ ≡ₜ `λ υ

    eq-· :

        τ₁ ≡ₜ υ₁ → τ₂ ≡ₜ υ₂ →
        ---------------------
        τ₁ · τ₂ ≡ₜ υ₁ · υ₂

    eq-$ : ∀ {τ₁ υ₁ : Type Δ (κ₁ `→ κ₂)} {τ₂ υ₂ : Type Δ R[ κ₁ ]} → 

        τ₁ ≡ₜ υ₁ → τ₂ ≡ₜ υ₂ →
        ---------------------
        τ₁ $ τ₂ ≡ₜ υ₁ $ υ₂        

    eq-⇒ :

         π₁ ≡ₚ π₂ → τ₁ ≡ₜ τ₂ →
        ------------------------
        (π₁ ⇒ τ₁) ≡ₜ (π₂ ⇒ τ₂)

    eq-lab : 
           
           ℓ₁ ≡ ℓ₂ →
           -------------
           lab {Δ = Δ} ℓ₁ ≡ₜ lab ℓ₂
    
    eq-row : 
        ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} {ω₁ : True (ordered? ρ₁)} 
          {ω₂ : True (ordered? ρ₂)} → 
  
        ρ₁ ≡ᵣ ρ₂ → 
        -------------------------------------------
        ⦅ ρ₁ ⦆ ω₁ ≡ₜ ⦅ ρ₂ ⦆ ω₂

    eq-▹ : ∀ {l₁ l₂ : Type Δ L} {τ₁ τ₂ : Type Δ κ} → 
         
           l₁ ≡ₜ l₂   →    τ₁ ≡ₜ τ₂ → 
           ------------------------------------
           (l₁ ▹ τ₁) ≡ₜ (l₂ ▹ τ₂)

    eq-∖ : ∀ {ρ₂ ρ₁ υ₂ υ₁ : Type Δ R[ κ ]} → 
         
           ρ₂ ≡ₜ υ₂   →    ρ₁ ≡ₜ υ₁ → 
           ------------------------------------
           (ρ₂ ∖ ρ₁) ≡ₜ (υ₂ ∖ υ₁)

  -- -------------------------------------
  -- η-laws  
         
    eq-η : ∀ {f : Type Δ (κ₁ `→ κ₂)} → 


        ----------------------------
        f ≡ₜ `λ (weakenₜ f · (` Z))

  -- -------------------------------------
  -- Computational laws

    eq-β : ∀ {τ₁ : Type (Δ , κ₁) κ₂} {τ₂ : Type Δ κ₁} → 


        ----------------------------
        ((`λ τ₁) · τ₂) ≡ₜ (τ₁ βₜ[ τ₂ ])

    eq-labTy : 

        l ≡ₜ lab ℓ → 
        -------------------------------------------
        (l ▹ τ) ≡ₜ ⦅ [ (ℓ  , τ) ] ⦆ tt

    eq-▹$ : ∀ {κ₁ : Kind} {l : Type Δ L} {τ : Type Δ κ₁} {F : Type Δ (κ₁ `→ κ₂)} → 

        ---------------------------------
        (F $ (l ▹ τ)) ≡ₜ (l ▹ (F · τ))

    eq-$-∖ : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : Type Δ R[ κ₁ ]} → 

      
      ------------------------------------------
      F $ (ρ₂ ∖ ρ₁) ≡ₜ (F $ ρ₂) ∖ (F $ ρ₁)

    eq-map : ∀ {F : Type Δ (κ₁ `→ κ₂)} {ρ : RowLiteral (Type Δ κ₁)} {ω : True (ordered? ρ)} → 

         -------------------------------
         F $ (⦅ ρ ⦆ ω) ≡ₜ ⦅ map (map₂ (F ·_)) ρ ⦆ (fromWitness (map-map₂ {Ty = Type} ρ (F ·_) (toWitness ω)))

    eq-map-id : ∀ {κ : Kind} {τ : Type Δ R[ κ ]} → 

        ---------------------------------------- 
        (`λ {κ₁ = κ} (` Z)) $ τ ≡ₜ τ

    eq-map-∘ : ∀ {f : Type Δ (κ₂ `→ κ₃)} {g : Type Δ (κ₁ `→ κ₂)} {τ : Type Δ R[ κ₁ ]} → 

        ---------------------------------------- 
        (f $ (g $ τ))  ≡ₜ (`λ (weakenₜ f · (weakenₜ g · (` Z)))) $ τ 
    
    eq-Π : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : NotLabel κ} → 

         ----------------------------
         Π {notLabel = nl} · ρ ≡ₜ Π {notLabel = nl} $ ρ

    eq-Σ : ∀ {ρ : Type Δ R[ R[ κ ] ]} {nl : NotLabel κ} → 

         ----------------------------
         Σ {notLabel = nl} · ρ ≡ₜ Σ {notLabel = nl} $ ρ
        
    eq-Π-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : NotLabel κ₂} → 

        ----------------------------
        (Π {notLabel = nl} · ρ) · τ ≡ₜ Π {notLabel = nl} · (ρ ?? τ)

    eq-Σ-assoc : ∀ {ρ : Type Δ (R[ κ₁ `→ κ₂ ])} {τ : Type Δ κ₁} {nl : NotLabel κ₂} → 

        ----------------------------
        (Σ {notLabel = nl} · ρ) · τ ≡ₜ Σ {notLabel = nl} · (ρ ?? τ)

    eq-compl : ∀ {xs ys : RowLiteral (Type Δ κ)} 
                 {oxs : True (ordered? xs)} 
                 {oys : True (ordered? ys)} 
                 {ozs : True (ordered? (xs ∖s ys))} → 

                 --------------------------------------------
                 (⦅ xs ⦆ oxs) ∖ (⦅ ys ⦆ oys) ≡ₜ ⦅ (xs ∖s ys) ⦆ ozs

-- -------------------------------------------------------------------------------
-- -- Lifting propositional equality to type equivalence

inst : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡ τ₂ → τ₁ ≡ₜ τ₂ 
inst refl = eq-refl

instᵣ :  ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} → ρ₁ ≡ ρ₂ → ρ₁ ≡ᵣ ρ₂
instᵣ {ρ₁ = []} refl = eq-[]
instᵣ {ρ₁ = x ∷ ρ₁} refl = eq-cons refl eq-refl (instᵣ refl)

-- -------------------------------------------------------------------------------
-- -- ≡ᵣ forms an equivalence relation

reflᵣ : ∀ {xs : RowLiteral (Type Δ κ)} → xs ≡ᵣ xs
reflᵣ {xs = []} = eq-[]
reflᵣ {xs = x ∷ xs} = eq-cons refl eq-refl reflᵣ

symᵣ : ∀ {xs ys : RowLiteral (Type Δ κ)} → xs ≡ᵣ ys → ys ≡ᵣ xs
symᵣ eq-[] = eq-[]
symᵣ (eq-cons l x eq) = eq-cons (sym l) (eq-sym x) (symᵣ eq)

transᵣ : ∀ {xs ys zs : RowLiteral (Type Δ κ)} → xs ≡ᵣ ys → ys ≡ᵣ zs → xs ≡ᵣ zs
transᵣ eq-[] eq-[] = eq-[]
transᵣ (eq-cons eq-l₁ eq-τ₁ eq-xs) (eq-cons eq-l₂ eq-τ₂ eq-ys) = eq-cons (trans eq-l₁ eq-l₂) (eq-trans eq-τ₁ eq-τ₂) (transᵣ eq-xs eq-ys)

∈L-≡ᵣ : ∀ {ℓ} {xs ys : RowLiteral (Type Δ κ)} → ℓ ∈L xs → xs ≡ᵣ ys → ℓ ∈L ys 
∈L-≡ᵣ Here (eq-cons refl x₂ eq) = Here
∈L-≡ᵣ (There l∈xs) (eq-cons refl x₂ eq) = There (∈L-≡ᵣ l∈xs eq)

cong-∖s : ∀ {xs₂ xs₁ ys₂ ys₁ : RowLiteral (Type Δ κ)} → xs₂ ≡ᵣ ys₂ → xs₁ ≡ᵣ ys₁ → (xs₂ ∖s xs₁) ≡ᵣ (ys₂ ∖s ys₁)
cong-∖s eq-[] eq₁ = eq-[]
cong-∖s {xs₁ = xs₁} {ys₁ = ys₁} (eq-cons {ℓ₁ = ℓ₁} refl eq-τ eq-xs) eq₁ with ℓ₁ ∈L? xs₁ | ℓ₁ ∈L? ys₁ 
... | yes p | yes q = cong-∖s eq-xs eq₁
... | no  p | no  q = eq-cons refl eq-τ (cong-∖s eq-xs eq₁)
... |  no p | yes q = ⊥-elim (p (∈L-≡ᵣ q (symᵣ eq₁)))
... | yes p | no  q = ⊥-elim (q (∈L-≡ᵣ p eq₁))


-------------------------------------------------------------------------------
-- Groupoid syntax for _≡ₜ_

instance
  ≡ₜ-Order : OrderSyntax {A = Type Δ κ} (_≡ₜ_)
  ≡ₜ-Order .OrderSyntax._○_ = eq-trans

  ≡ₜ-Groupoid : GroupoidSyntax {A = Type Δ κ} (_≡ₜ_) ≡ₜ-Order
  ≡ₜ-Groupoid .GroupoidSyntax._⁻¹ = eq-sym
  ≡ₜ-Groupoid .GroupoidSyntax.Refl = eq-refl
  -- We posit that the type  τ ≡ₜ υ is a **set** by mapping p ≋ q to ⊤. 
  -- That is, if p, q : τ ≡ₜ υ then p ≋ q : ⊤ is inhabited.  
  -- We are not really interested in reasoning over proofs of equivalence,
  -- since type equivalence denotes to _≡_, which is a set: 
  --   ⟦_⟧eq : τ ≡ₜ υ → ⟦ τ ⟧ ≡ ⟦ υ ⟧
  ≡ₜ-Groupoid .GroupoidSyntax._≋_  _ _ = ⊤ 
  ≡ₜ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.refl = tt
  ≡ₜ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.sym = const tt
  ≡ₜ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.trans = λ _ → const tt 
  ≡ₜ-Groupoid .GroupoidSyntax._⋆_ _ _ = tt 
  ≡ₜ-Groupoid .GroupoidSyntax.left-inv p = tt
  ≡ₜ-Groupoid .GroupoidSyntax.right-inv p = tt
  ≡ₜ-Groupoid .GroupoidSyntax.involution p = tt 
  ≡ₜ-Groupoid .GroupoidSyntax.left-identity p = tt
  ≡ₜ-Groupoid .GroupoidSyntax.right-identity p = tt
  ≡ₜ-Groupoid .GroupoidSyntax.assoc p q r = tt


-------------------------------------------------------------------------------
-- Groupoid syntax for _≡ₚ_

instance
  ≡ₚ-Order : OrderSyntax {A = Pred (Type Δ R[ κ ])} (_≡ₚ_)
  ≡ₚ-Order .OrderSyntax._○_
    (_eq-≲_ {τ₁ = τ₁} {υ₁ = υ₁} {τ₂ = τ₂} {υ₂ = υ₂} p  q) 
    (_eq-≲_ {τ₁ = _} {υ₁ = ν₁} {τ₂ = _} {υ₂ = ν₂} r s) = (p ○ r) eq-≲ (q ○ s)
  ≡ₚ-Order .OrderSyntax._○_ (p eq-· q ~ r) (s eq-· t ~ u) = (p ○ s) eq-· (q ○ t) ~ (r ○ u)

  ≡ₚ-Groupoid : GroupoidSyntax {A = Pred (Type Δ R[ κ ])} (_≡ₚ_) ≡ₚ-Order
  ≡ₚ-Groupoid .GroupoidSyntax._⁻¹ (p eq-≲ q) = (p ⁻¹) eq-≲ (q ⁻¹)
  ≡ₚ-Groupoid .GroupoidSyntax._⁻¹ (p eq-· q ~ r) = (p ⁻¹) eq-· q ⁻¹ ~ (r ⁻¹)
  ≡ₚ-Groupoid .GroupoidSyntax.Refl {ρ₁ · ρ₂ ~ ρ₃} = Refl eq-· Refl ~ Refl
  ≡ₚ-Groupoid .GroupoidSyntax.Refl {ρ₁ ≲ ρ₂} = Refl eq-≲ Refl
  ≡ₚ-Groupoid .GroupoidSyntax._≋_  _ _ = ⊤ 
  ≡ₚ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.refl = tt
  ≡ₚ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.sym = const tt
  ≡ₚ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.trans = λ _ → const tt 
  ≡ₚ-Groupoid .GroupoidSyntax._⋆_ _ _ = tt 
  ≡ₚ-Groupoid .GroupoidSyntax.left-inv p = tt
  ≡ₚ-Groupoid .GroupoidSyntax.right-inv p = tt
  ≡ₚ-Groupoid .GroupoidSyntax.involution p = tt 
  ≡ₚ-Groupoid .GroupoidSyntax.left-identity p = tt
  ≡ₚ-Groupoid .GroupoidSyntax.right-identity p = tt
  ≡ₚ-Groupoid .GroupoidSyntax.assoc p q r = tt

-------------------------------------------------------------------------------
-- Groupoid syntax for _≡ᵣ_

instance
  ≡ᵣ-Order : OrderSyntax {A = RowLiteral (Type Δ κ)} (_≡ᵣ_)
  ≡ᵣ-Order .OrderSyntax._○_ = transᵣ

  ≡ᵣ-Groupoid : GroupoidSyntax {A = RowLiteral (Type Δ κ)} (_≡ᵣ_) ≡ᵣ-Order
  (≡ᵣ-Groupoid GroupoidSyntax.⁻¹) = symᵣ
  ≡ᵣ-Groupoid .GroupoidSyntax.Refl = reflᵣ
  ≡ᵣ-Groupoid .GroupoidSyntax._≋_  _ _ = ⊤ 
  ≡ᵣ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.refl = tt
  ≡ᵣ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.sym = const tt
  ≡ᵣ-Groupoid .GroupoidSyntax.eqv .IsEquivalence.trans = λ _ → const tt 
  ≡ᵣ-Groupoid .GroupoidSyntax._⋆_ _ _ = tt 
  ≡ᵣ-Groupoid .GroupoidSyntax.left-inv p = tt
  ≡ᵣ-Groupoid .GroupoidSyntax.right-inv p = tt
  ≡ᵣ-Groupoid .GroupoidSyntax.involution p = tt 
  ≡ᵣ-Groupoid .GroupoidSyntax.left-identity p = tt
  ≡ᵣ-Groupoid .GroupoidSyntax.right-identity p = tt
  ≡ᵣ-Groupoid .GroupoidSyntax.assoc p q r = tt


--------------------------------------------------------------------------------
-- Equational Reasoning syntax for _≡ₜ_

module ≡ₜ-Reasoning where
  infixr 1 _≡ₜ⟨_⟩_
  _≡ₜ⟨_⟩_ : (τ₁ : Type Δ κ) 
            {τ₂ : Type Δ κ} 
            {τ₃ : Type Δ κ} → 
            τ₁ ≡ₜ τ₂ → τ₂ ≡ₜ τ₃ → τ₁ ≡ₜ τ₃
  _≡ₜ⟨_⟩_ _ = eq-trans

  _∎ : ∀ (τ : Type Δ κ) → τ ≡ₜ τ 
  _ ∎ = eq-refl
