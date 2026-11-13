-- 
module Rome.Types.Properties.Equivalence where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming
open import Rome.Types.Substitution
open import Rome.Types.Equivalence

open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution

--------------------------------------------------------------------------------
-- Renaming respects type equivalence

renₜ-≡ₜ : ∀ {τ υ : Type Δ₁ κ} (ρ : Renaming Δ₁ Δ₂) → 
                τ ≡ₜ υ → renₜ ρ τ ≡ₜ renₜ ρ υ 
renₜ-≡ₚ : ∀ {π₁ π₂ : Pred (Type Δ₁ R[ κ ])} (ρ : Renaming Δ₁ Δ₂) → 
                π₁ ≡ₚ π₂ → ren ρ π₁ ≡ₚ ren ρ π₂
renₜ-≡ᵣ : ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ₁ κ)} (r : Renaming Δ₁ Δ₂) → 
                ρ₁ ≡ᵣ ρ₂ → ren r ρ₁ ≡ᵣ ren r ρ₂

renₜ-≡ₜ {τ = τ} {υ} ρ eq-refl = eq-refl
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-sym e) = eq-sym (renₜ-≡ₜ ρ e)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-trans e e₁) = eq-trans (renₜ-≡ₜ ρ e) (renₜ-≡ₜ ρ e₁)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-→ e e₁) = eq-→ (renₜ-≡ₜ ρ e) (renₜ-≡ₜ ρ e₁)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-∀ e) = eq-∀ (renₜ-≡ₜ (liftₜ ρ) e)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-μ e) = eq-μ (renₜ-≡ₜ ρ e)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-λ e) = eq-λ (renₜ-≡ₜ (liftₜ ρ) e)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-· e e₁) = eq-· (renₜ-≡ₜ ρ e) (renₜ-≡ₜ ρ e₁)
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-⇒ x e) = eq-⇒ (renₜ-≡ₚ ρ x) (renₜ-≡ₜ ρ e)
renₜ-≡ₜ {τ = τ} {.(`λ (weakenₜ τ · ` Z))} ρ eq-η = 
    eq-trans 
        (eq-η {f = renₜ ρ τ}) 
        (eq-λ (eq-· 
            (inst (sym (↻-liftₜ-weaken ρ τ) )) 
            eq-refl))
renₜ-≡ₜ {τ = `λ τ₁ · τ₂} {.(τ₁ βₜ[ τ₂ ])} ρ (eq-β {τ₁ = τ₁} {τ₂}) = 
    eq-trans 
        (eq-β {τ₁ = renₜ (liftₜ ρ) τ₁} {renₜ ρ τ₂}) 
        (eq-sym (inst (↻-renₜ-β ρ τ₁ τ₂)))
renₜ-≡ₜ {τ = τ} {υ} ρ eq-Π-assoc = eq-Π-assoc
renₜ-≡ₜ {τ = τ} {υ} ρ eq-Σ-assoc = eq-Σ-assoc
renₜ-≡ₜ {τ = τ} {υ} ρ eq-Π = eq-Π
renₜ-≡ₜ {τ = τ} {υ} ρ eq-Σ = eq-Σ
renₜ-≡ₜ {τ = τ} {υ} ρ (eq-$ t u) = eq-$ (renₜ-≡ₜ ρ t) (renₜ-≡ₜ ρ u)
renₜ-≡ₜ {τ = τ} {υ} r (eq-row x) = eq-row (renₜ-≡ᵣ r x)
renₜ-≡ₜ {τ = τ} {υ} r (eq-map {F = F} {ρ = []}) = eq-map {F = renₜ r F} {ρ = []}
renₜ-≡ₜ {τ = τ} {υ} r (eq-map {F = F} {ρ = (l , τ') ∷ ρ}) =
    eq-trans 
        (eq-map) 
        (eq-row (eq-cons refl eq-refl (instᵣ (↻-ren-map r F ρ))))
renₜ-≡ₜ r (eq-lab refl) = eq-refl
renₜ-≡ₜ r (eq-▹ l τ) = eq-▹ (renₜ-≡ₜ r l) (renₜ-≡ₜ r τ)
renₜ-≡ₜ r (eq-∖ ρ υ) = eq-∖ (renₜ-≡ₜ r ρ) (renₜ-≡ₜ r υ)
renₜ-≡ₜ r eq-▹$ = eq-▹$
renₜ-≡ₜ r (eq-labTy eq) = eq-labTy (renₜ-≡ₜ r eq)
renₜ-≡ₜ r (eq-$-∖) = eq-$-∖
renₜ-≡ₜ r (eq-compl {xs = xs} {ys} {ozs = ozs}) = 
  eq-trans 
    (eq-compl  
      {ozs = fromWitness (tr Ordered (↻-renRowₜ-∖s r {xs} {ys}) ((orderedRenRowₜ r (xs ∖s ys) (toWitness ozs))))}) 
    (eq-row (instᵣ (sym (↻-renRowₜ-∖s r {xs} {ys}))))
renₜ-≡ₜ r (eq-map-id) = eq-map-id
renₜ-≡ₜ r (eq-map-∘ {f = f} {g = g} {τ = τ}) = 
  eq-trans (eq-map-∘ {f = renₜ r f} {g = renₜ r g} {τ = renₜ r τ}) 
  (eq-$ (eq-λ (eq-· (inst (sym (↻-liftₜ-weaken r f))) (eq-· (inst (sym (↻-liftₜ-weaken r g))) eq-refl))) eq-refl)

renₜ-≡ᵣ {ρ₁ = ρ₁} {ρ₂} r eq-[] = eq-[]
renₜ-≡ᵣ {ρ₁ = ρ₁} {ρ₂} r (eq-cons l x eq) = eq-cons l (renₜ-≡ₜ _ x) (renₜ-≡ᵣ r eq )

renₜ-≡ₚ {π₁} {π₂} ρ (eq₁ eq-≲ eq₂) = renₜ-≡ₜ ρ eq₁ eq-≲ renₜ-≡ₜ ρ eq₂
renₜ-≡ₚ {π₁} {π₂} ρ (eq₁ eq-· eq₂ ~ eq₃) = (renₜ-≡ₜ ρ eq₁) eq-· (renₜ-≡ₜ ρ eq₂) ~ (renₜ-≡ₜ ρ eq₃)

--------------------------------------------------------------------------------
-- Lifting of substitutions respects type equivalence

liftsₜ-cong-≡ₜ : ∀ {σ₁  σ₂ : Substitution Δ₁ Δ₂} → 
                (∀ {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ₜ σ₂ x) → 
                 ∀ {κ' : Kind} (x : TVar (Δ₁ , κ') κ) → liftsₜ σ₁ x ≡ₜ liftsₜ σ₂ x
liftsₜ-cong-≡ₜ c Z = eq-refl
liftsₜ-cong-≡ₜ c (S x) = renₜ-≡ₜ S (c x)                 

--------------------------------------------------------------------------------
-- Equivalent substitutions are congruent over types w.r.t. type equivalence

subₜ-cong-≡ₜ : ∀ {σ₁  σ₂ : Substitution Δ₁ Δ₂}  → 
                (∀  {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ₜ σ₂ x) → 
                 (τ : Type Δ₁ κ) → sub σ₁ τ ≡ₜ sub σ₂ τ
subRowₜ-cong-≡ₜ : ∀ {σ₁  σ₂ : Substitution Δ₁ Δ₂}  → 
                (∀  {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ₜ σ₂ x) → 
                 (ρ : RowLiteral (Type Δ₁ κ)) → sub σ₁ ρ ≡ᵣ sub σ₂ ρ
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (` α) = c α
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (`λ τ) = eq-λ (subₜ-cong-≡ₜ (liftsₜ-cong-≡ₜ c) τ)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (τ · τ₁) = eq-· (subₜ-cong-≡ₜ c τ) (subₜ-cong-≡ₜ c τ₁)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (τ `→ τ₁) = eq-→ (subₜ-cong-≡ₜ c τ) (subₜ-cong-≡ₜ c τ₁)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (`∀ τ)  = eq-∀ (subₜ-cong-≡ₜ (liftsₜ-cong-≡ₜ c) τ)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (μ τ)  = eq-μ (subₜ-cong-≡ₜ c τ)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) = 
    eq-⇒ 
        ((subₜ-cong-≡ₜ c ρ₁) eq-· (subₜ-cong-≡ₜ c ρ₂) ~ (subₜ-cong-≡ₜ c ρ₃))
        (subₜ-cong-≡ₜ c τ)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c ((ρ₁ ≲ ρ₂) ⇒ τ) = 
    eq-⇒ 
        ((subₜ-cong-≡ₜ c ρ₁) eq-≲ (subₜ-cong-≡ₜ c ρ₂))
        (subₜ-cong-≡ₜ c τ)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (lab l)  = eq-refl
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (τ ▹ τ₁) = eq-▹ (subₜ-cong-≡ₜ c τ) (subₜ-cong-≡ₜ c τ₁) 
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (τ $ τ₁) = eq-$ (subₜ-cong-≡ₜ c τ) (subₜ-cong-≡ₜ c τ₁)
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c Π  = eq-refl    
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c Σ  = eq-refl                
subₜ-cong-≡ₜ {σ₁ = σ₁} {σ₂} c (⦅ ρ ⦆ ω) = eq-row (subRowₜ-cong-≡ₜ c ρ)
subₜ-cong-≡ₜ c (ρ₂ ∖ ρ₁) = eq-∖ (subₜ-cong-≡ₜ c ρ₂) (subₜ-cong-≡ₜ c ρ₁)

subRowₜ-cong-≡ₜ c [] = eq-[]
subRowₜ-cong-≡ₜ c ((l , τ) ∷ ρ) = eq-cons refl (subₜ-cong-≡ₜ c τ) (subRowₜ-cong-≡ₜ c ρ)


--------------------------------------------------------------------------------
-- substitution respects type equivalence

subₜ-≡ₜ :  ∀ {σ : Substitution Δ₁ Δ₂} {τ₁ τ₂ : Type Δ₁ κ} → 
                  τ₁ ≡ₜ τ₂ → sub σ τ₁ ≡ₜ sub σ τ₂
subₜ-≡ᵣ :  ∀ {σ : Substitution Δ₁ Δ₂} {ρ₁ ρ₂ : RowLiteral (Type Δ₁ κ)} →
                  ρ₁ ≡ᵣ ρ₂ → sub σ ρ₁ ≡ᵣ sub σ ρ₂


subₜ-≡ₜ {σ} eq-refl = eq-refl 
subₜ-≡ₜ {σ} (eq-sym eq) = eq-sym (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ} (eq-trans eq eq₁) = eq-trans (subₜ-≡ₜ eq) (subₜ-≡ₜ eq₁)
subₜ-≡ₜ {σ} (eq-→ eq eq₁) = eq-→ (subₜ-≡ₜ eq) (subₜ-≡ₜ eq₁)
subₜ-≡ₜ {σ} (eq-∀ eq) = eq-∀ (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ} (eq-μ eq) = eq-μ (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ} (eq-λ eq) = eq-λ (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ} (eq-· eq eq₁) = eq-· (subₜ-≡ₜ eq) (subₜ-≡ₜ eq₁)
subₜ-≡ₜ {σ} (eq-$ eq eq₁) = eq-$ (subₜ-≡ₜ eq) (subₜ-≡ₜ eq₁)
subₜ-≡ₜ {σ} (eq-▹ eq eq₁) = eq-▹ (subₜ-≡ₜ eq) (subₜ-≡ₜ eq₁)
subₜ-≡ₜ {σ} (eq-⇒ (ρ₁ eq-≲ x₂) eq) = 
  eq-⇒ 
    (subₜ-≡ₜ ρ₁ eq-≲ subₜ-≡ₜ x₂) 
    (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ} (eq-⇒ (ρ₁ eq-· ρ₂ ~ ρ₃) eq) = 
  eq-⇒ 
    (subₜ-≡ₜ ρ₁ eq-· subₜ-≡ₜ ρ₂ ~ subₜ-≡ₜ ρ₃) 
    (subₜ-≡ₜ eq)
subₜ-≡ₜ {σ = σ} {τ₁ = τ₁} eq-η = 
    eq-trans 
        (eq-η {f = sub σ τ₁}) 
        (eq-λ (eq-· 
            (inst (sym (trans (sym (↻-subₜ-renₜ τ₁)) (↻-renₜ-sub {σ = σ} {S} τ₁)) )) 
            eq-refl))
subₜ-≡ₜ {σ = σ} {`λ τ₁ · τ₂} {.(τ₁ βₜ[ τ₂ ])} eq-β = 
    eq-trans 
        (eq-β {τ₁ = sub (liftsₜ σ) τ₁} {sub σ τ₂}) 
        (eq-sym (inst (sym (↻-subₜ-β σ τ₁ τ₂))))
subₜ-≡ₜ {σ} eq-Π = eq-Π
subₜ-≡ₜ {σ} eq-Σ = eq-Σ
subₜ-≡ₜ {σ} eq-Π-assoc = eq-Π-assoc
subₜ-≡ₜ {σ} eq-Σ-assoc = eq-Σ-assoc
subₜ-≡ₜ {σ} (eq-row x) =  eq-row (subₜ-≡ᵣ x)
subₜ-≡ₜ {σ = σ} (eq-map {F = F} {ρ = []}) = eq-map
subₜ-≡ₜ {σ = σ} (eq-map {F = F} {ρ = (l , τ) ∷ ρ}) =
    eq-trans 
        (eq-map {F = sub σ F} {ρ = (l , sub σ τ) ∷ sub σ ρ}) 
        (eq-row (eq-cons refl eq-refl (instᵣ (↻-sub-map σ F ρ))))

subₜ-≡ₜ {σ = σ} (eq-lab refl) = eq-refl
subₜ-≡ₜ {σ = σ} (eq-∖ eq₁ eq₂) = eq-∖ (subₜ-≡ₜ eq₁) (subₜ-≡ₜ eq₂)
subₜ-≡ₜ {σ = σ} eq-▹$ = eq-▹$
subₜ-≡ₜ {σ = σ} (eq-labTy eq) = eq-labTy (subₜ-≡ₜ {σ = σ} eq)
subₜ-≡ₜ {σ = σ} (eq-$-∖) = eq-$-∖
subₜ-≡ₜ {σ = σ} (eq-compl {xs = xs} {ys} {zs} {ozs = ozs}) = 
  eq-trans 
    (eq-compl  
      {ozs = fromWitness (tr Ordered (↻-subRowₜ-∖s σ {xs} {ys}) ((orderedSubRowₜ σ (xs ∖s ys) (toWitness ozs))))}) 
    (eq-row (instᵣ (sym (↻-subRowₜ-∖s σ {xs} {ys}))))
subₜ-≡ₜ {σ = σ} (eq-map-id) = eq-map-id
subₜ-≡ₜ {σ = σ} (eq-map-∘ {f = f} {g = g} {τ = τ}) = 
  eq-trans 
    (eq-map-∘ {f = sub σ f} {sub σ g} {sub σ τ}) 
    (eq-$ 
      (eq-λ (eq-· (inst (sym (↻-liftsₜ-weaken σ f))) (eq-· (inst (sym (↻-liftsₜ-weaken σ g))) eq-refl))) 
      eq-refl)

subₜ-≡ᵣ {ρ₁ = ρ₁} {ρ₂} eq-[] = eq-[]
subₜ-≡ᵣ {ρ₁ = ρ₁} {ρ₂} (eq-cons l x eq) = eq-cons l (subₜ-≡ₜ x) (subₜ-≡ᵣ eq )


-- --------------------------------------------------------------------------------
-- -- Properties of row equivalence

eq-reflᵣ : ∀ (xs : RowLiteral (Type Δ κ)) → xs ≡ᵣ xs 
eq-reflᵣ [] = eq-[]
eq-reflᵣ (x ∷ xs) = eq-cons refl eq-refl (eq-reflᵣ xs) 

eq-symᵣ : ∀ {xs ys : RowLiteral (Type Δ κ)} → xs ≡ᵣ ys → ys ≡ᵣ xs 
eq-symᵣ eq-[] = eq-[]
eq-symᵣ (eq-cons l x eq) = eq-cons (sym l) (eq-sym x) (eq-symᵣ eq) 

eq-transᵣ : ∀ {xs ys zs : RowLiteral (Type Δ κ)} → xs ≡ᵣ ys → ys ≡ᵣ zs → xs ≡ᵣ zs
eq-transᵣ eq-[] eq-[] = eq-[]
eq-transᵣ (eq-cons eq-l₁ eq-hd₁ eq-tl₁) (eq-cons eq-l₂ eq-hd₂ eq-tl₂) = eq-cons (trans eq-l₁ eq-l₂) (eq-trans eq-hd₁ eq-hd₂) (eq-transᵣ eq-tl₁ eq-tl₂)

