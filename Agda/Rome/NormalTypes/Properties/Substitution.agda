
module Rome.NormalTypes.Properties.Substitution where


open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Properties.Substitution
open import Rome.Types.Properties.Renaming
open import Rome.Types.Renaming
open import Rome.Types.Equivalence

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.Substitution

open import Rome.NormalTypes.Properties.Renaming
open import Rome.Types.Properties.Equivalence

open import Rome.NBE.Syntax
open import Rome.NBE.Normalization
open import Rome.NBE.Renaming

open import Rome.Metatheory.Soundness
open import Rome.Metatheory.Consistency

open import Rome.Metatheory.Stability



--------------------------------------------------------------------------------
-- Membership is preserved by substitution

∈-subₜNF : ∀ {l : Label} {τ : NormalType Δ₁ κ} {xs : RowLiteral (NormalType Δ₁ κ)} → 
             (σ : SubstitutionₜNF Δ₁ Δ₂) → 
             (l , τ) ∈ xs → (l , subₜNF σ τ) ∈ (subRowₜNF σ xs)
∈-subₜNF σ (here refl) = here refl
∈-subₜNF σ (there i) = there (∈-subₜNF σ i)

∈L-subₜNF : ∀ {l : Label} {xs : RowLiteral (NormalType Δ₁ κ)} → 
               (σ : SubstitutionₜNF Δ₁ Δ₂) → 
               l ∈L xs → l ∈L subRowₜNF σ xs
∈L-subₜNF {xs = .((_ , _) ∷ _)} σ Here = Here
∈L-subₜNF {xs = ((_ , τ) ∷ _)} σ (There l∈xs) = There (∈L-subₜNF σ l∈xs)

subRowₜNF-∈L : ∀ {l : Label} {xs : RowLiteral (NormalType Δ₁ κ)} → 
               (σ : SubstitutionₜNF Δ₁ Δ₂) → 
               l ∈L subRowₜNF σ xs → l ∈L xs
subRowₜNF-∈L {xs = x ∷ xs} σ Here = Here
subRowₜNF-∈L {xs = (l , τ) ∷ xs} σ (There inn) = There (subRowₜNF-∈L σ inn)

--------------------------------------------------------------------------------
-- Substitution and normalization commute

↻-⇓-sub : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) → 
             (τ : Type Δ₁ κ) → ⇓ₜ (sub (⇑ ∘ σ) τ) ≡ sub σ (⇓ₜ τ)
↻-⇓-sub σ τ = 
  trans 
    (reify-≈ (↻-subₜ-eval τ idEnv-≈ (⇑ ∘ σ))) 
    (sym (trans 
      (reify-≈ (↻-subₜ-eval (⇑ (⇓ₜ τ)) idEnv-≈ (⇑ ∘ σ))) 
      (reify-≈ (fund-≈ ((idext idEnv-≈) ∘ ⇑ ∘ σ) (eq-sym (consistency τ))))))

↻-⇓-subRow : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) → 
             (ρ : RowLiteral (Type Δ₁ κ)) →
             {ω : True (ordered? ρ)} → 
             ⇓ᵣ (sub (⇑ ∘ σ) ρ) ≡ sub σ (⇓ᵣ ρ)
↻-⇓-subRow σ ρ {ω} = inj-⦅⦆ (↻-⇓-sub σ (⦅ ρ ⦆ ω))

--------------------------------------------------------------------------------
-- Substitution respects the functor identity law

subₜNF-id          : ∀ (τ : NormalType Δ κ) → sub idSubst τ ≡ τ
subₜNF-id τ = 
  trans 
    (reify-≈ (↻-subₜ-eval (⇑ τ) idEnv-≈ (⇑ ∘ idSubst)))
  (trans 
    (reify-≈ 
      (idext {η₁ = λ x → ⟦ ⇑ (idSubst x) ⟧ₜ idEnv} {η₂ = idEnv} 
        (λ { x → fund-≈ {τ₁ = ⇑ (η-norm (` x))} {τ₂ = ` x} idEnv-≈ (η-norm-≡ₜ (` x)) }) (⇑ τ)))
    (stability τ))

subPredₜNF-id : ∀ (π : Pred (NormalType Δ R[ κ ])) → sub idSubst π ≡ π
subPredₜNF-id (ρ₁ · ρ₂ ~ ρ₃) = cong₃ _·_~_ (subₜNF-id ρ₁) (subₜNF-id ρ₂) (subₜNF-id ρ₃)
subPredₜNF-id (ρ₁ ≲ ρ₂) = ap₂ _≲_ (subₜNF-id ρ₁) (subₜNF-id ρ₂)

--------------------------------------------------------------------------------
-- Substitution respects the functor composition

subₜNF-comp :  ∀ (σ₁ : SubstitutionₜNF Δ₁ Δ₂) (σ₂ : SubstitutionₜNF Δ₂ Δ₃) → 
                (τ : NormalType Δ₁ κ) → sub (sub σ₂ ∘ σ₁) τ ≡ sub σ₂ (sub σ₁ τ)
subₜNF-comp σ₁ σ₂ τ = 
  trans 
    (trans 
      (trans 
        (reify-≈ 
          (↻-subₜ-eval (⇑ τ) idEnv-≈ (⇑ ∘ ⇓ₜ ∘ sub (⇑ ∘ σ₂) ∘ ⇑ ∘ σ₁)))
        (trans 
          (reify-≈ 
            (idext (λ x → fund-≈ idEnv-≈ (eq-sym (consistency (sub (⇑ ∘ σ₂) (⇑ (σ₁ x)))))) (⇑ τ)))
          (sym (reify-≈ (↻-subₜ-eval (⇑ τ) idEnv-≈ (sub (⇑ ∘ σ₂) ∘ ⇑ ∘ σ₁)))))) 
      (ap ⇓ₜ (subₜ-comp (⇑ τ)))) 
    (↻-⇓-sub σ₂ (sub (⇑ ∘ σ₁) (⇑ τ)))

--------------------------------------------------------------------------------
-- Lifting type equivalence over substitution by (⇑ ∘ σ)               

subₜ-≡ₜ⇑ :  ∀ {σ : SubstitutionₜNF Δ₁ Δ₂} {τ₁ τ₂ : Type Δ₁ κ} → 
                  τ₁ ≡ₜ τ₂ → sub (⇑ ∘ σ) τ₁ ≡ₜ sub (⇑ ∘ σ) τ₂
subₜ-≡ₜ⇑ {σ = σ} eq = subₜ-≡ₜ {σ = ⇑ ∘ σ} eq                  


subₜNF-cong-≡ₜ : ∀ {σ : SubstitutionₜNF Δ₁ Δ₂} {τ₁ τ₂ : NormalType Δ₁ κ} → 
                ⇑ τ₁ ≡ₜ ⇑ τ₂ → sub σ τ₁ ≡ sub σ τ₂
subₜNF-cong-≡ₜ {σ = σ} {τ₁} {τ₂} eq = 
  reify-≈ 
    (fund-≈ 
      {τ₁ = sub (⇑ ∘ σ) (⇑ τ₁)} 
      {τ₂ = sub (⇑ ∘ σ) (⇑ τ₂)} 
      idEnv-≈ (subₜ-≡ₜ⇑ {σ = σ} eq))

--------------------------------------------------------------------------------
-- Substitution over a variable substitutes the variable

subₜNF-var   : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂)(x : TVar Δ₁ κ) → 
              sub σ (idSubst x) ≡ σ x
subₜNF-var {κ = κ} σ x = trans
  (reify-≈ (fund-≈ {τ₁ = sub (⇑ ∘ σ) (⇑ (idSubst x))} {τ₂ = ⇑ (σ x)} idEnv-≈ 
    (eq-trans 
      (subₜ-≡ₜ⇑ {σ = σ}  (η-norm-≡ₜ (` x)))
      eq-refl)))
  (stability (σ x))

subₜNF-var-ground   : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂)(x : TVar Δ₁ κ) {g : Ground κ} → 
                      sub σ (ne (` x) {g}) ≡ σ x
subₜNF-var-ground σ x {g} = stability (σ x)                      

--------------------------------------------------------------------------------
-- Congruence of normality preserving substitution

subₜNF-cong : {σ₁ : SubstitutionₜNF Δ₁ Δ₂}{σ₂ : SubstitutionₜNF Δ₁ Δ₂} →
              (∀ {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : NormalType Δ₁ κ) → sub σ₁ τ ≡ sub σ₂ τ
subₜNF-cong {σ₁ = σ₁} {σ₂} peq τ = 
  ap ⇓ₜ (subₜ-cong (ap ⇑ ∘ peq) (⇑ τ))      

--------------------------------------------------------------------------------
-- Substitution commutes with renaming

↻-renₜNF-sub : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) (ρ : Renaming Δ₂ Δ₃)
                    (τ : NormalType Δ₁ κ) → sub (ren ρ ∘ σ) τ ≡ ren ρ (sub σ τ)           
↻-renₜNF-sub {Δ₁ = Δ₁} σ ρ τ = 
  trans 
    (reify-≈ 
      (trans-≈ 
        (trans-≈ 
          (↻-subₜ-eval (⇑ τ) idEnv-≈ (⇑ ∘ ren ρ ∘ σ)) 
          (trans-≈ 
            (idext 
              (λ x → trans-≈ 
                (tr 
                  (λ y →  ⟦ ⇑ (ren ρ (σ x)) ⟧ₜ  idEnv ≈ ⟦ y ⟧ₜ idEnv) 
                  (↻-ren-⇑ ρ (σ x)) 
                  (idext idEnv-≈ (⇑ (ren ρ (σ x)))))
                (trans-≈ 
                  (↻-renₜ-eval ρ  (⇑ (σ x)) idEnv-≈) 
                  (idext (sym-≈ ∘ ↻-ren-reflect ρ ∘ `) (⇑ (σ x))))) 
              (⇑ τ))
            ((sym-≈ (↻-subₜ-eval (⇑ τ) (ren-≈ ρ ∘ idEnv-≈) (⇑ ∘ σ)))))) 
        (sym-≈ (↻-renSem-eval ρ (sub (⇑ ∘ σ) (⇑ τ)) idEnv-≈))))
    (sym (↻-ren-reify {Δ₁ = Δ₁} ρ (idext idEnv-≈ (sub (⇑ ∘ σ) (⇑ τ)))))                  

↻-subₜNF-ren : ∀ (ρ : Renaming Δ₁ Δ₂)(σ : SubstitutionₜNF Δ₂ Δ₃)
                (τ : NormalType Δ₁ κ) → sub (σ ∘ ρ) τ ≡ sub σ (ren ρ τ)           
↻-subₜNF-ren ρ σ τ rewrite (sym (stability τ)) = 
  trans 
    (sym (↻-⇓-sub (σ ∘ ρ) (⇑ τ))) 
    (ap ⇓
       (trans 
        (↻-subₜ-renₜ {r = ρ} {σ = ⇑ ∘ σ} (⇑ τ)) 
        (ap 
          (sub (⇑ ∘ σ)) 
          (tr 
            (λ x → renₜ ρ (⇑ τ) ≡ ⇑ (ren ρ x)) 
            (sym (stability τ)) 
            (sym (↻-ren-⇑ ρ τ))))))

--------------------------------------------------------------------------------
-- weakening commutes with substitution.

↻-weakenₜNF-sub : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) (τ : NormalType Δ₁ κ) {κ' : Kind} → 
                  weakenₜNF {κ₁ = κ'} (sub σ τ) ≡ sub (liftsₜNF σ) (weakenₜNF τ)
↻-weakenₜNF-sub σ τ {κ} = trans 
  (sym (↻-renₜNF-sub σ S τ)) 
  ((↻-subₜNF-ren S (liftsₜNF σ) τ))

↻-weakenPredₜNF-sub : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) (τ : Pred (NormalType Δ₁ R[ κ ])) {κ' : Kind} → 
                  weakenPredₜNF {κ₁ = κ'} (sub σ τ) ≡ sub (liftsₜNF σ) (weakenPredₜNF τ)
↻-weakenPredₜNF-sub σ π {κ'} with mapPredHO  (weakenₜNF {κ₁ = κ'} ∘ sub σ) (sub (liftsₜNF σ) ∘ weakenₜNF) (λ τ → ↻-weakenₜNF-sub σ τ {κ'}) π 
↻-weakenPredₜNF-sub σ (ρ₁ · ρ₂ ~ ρ₃) {κ'} | c = c
↻-weakenPredₜNF-sub σ (ρ₁ ≲ ρ₂) {κ'} | c = c

--------------------------------------------------------------------------------
-- Substituting commutes over β reduction (first statement)

↻-subₜNF-β'      : {Δ₁ : KEnv} {κ : Kind} (σ : SubstitutionₜNF Δ₁ Δ₂) 
                   (τ₁ : NormalType (Δ₁ , κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    sub σ (τ₁ βₜNF[ τ₂ ])
                  ≡ 
                    (sub (liftsₜNF σ) τ₁)
                    βₜNF[ sub σ τ₂ ]
↻-subₜNF-β' σ τ₁ τ₂ =   trans 
    (sym (subₜNF-comp (extendₜNF (η-norm ∘ `) τ₂) σ τ₁)) 
    (trans 
      (subₜNF-cong 
        {σ₁ = sub σ ∘ extendₜNF (η-norm ∘ `) τ₂} 
        {sub (extendₜNF (η-norm ∘ `) (sub σ τ₂)) ∘ liftsₜNF σ} 
        (λ { Z     → sym (subₜNF-var (extendₜNF (η-norm ∘ `) (sub σ τ₂)) Z)
           ; (S x) → trans 
              (trans 
                (subₜNF-var σ x)
                (sym (subₜNF-id (σ x))))
              (↻-subₜNF-ren S (extendₜNF idSubst (sub σ τ₂)) (σ x)) })
        τ₁) 
      (subₜNF-comp (liftsₜNF σ) (extendₜNF (η-norm ∘ `) (sub σ τ₂)) τ₁))

--------------------------------------------------------------------------------
-- renaming commutes with beta-reduction

↻-renₜNF-β : (ρ : Renaming Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ , κ₁) κ₂) (τ₂ : NormalType Δ₁ κ₁) → 
                ren ρ (τ₁ βₜNF[ τ₂ ]) ≡ (ren (liftₜ ρ) τ₁) βₜNF[ (ren ρ τ₂) ]
↻-renₜNF-β {Δ₁ = Δ₁} ρ τ₁ τ₂ = 
  trans 
    (sym (↻-renₜNF-sub (extendₜNF idSubst τ₂) ρ τ₁)) 
    (trans 
      (subₜNF-cong 
        {σ₁ = ren ρ ∘ extendₜNF idSubst τ₂} 
        {σ₂ = extendₜNF idSubst (ren ρ τ₂) ∘ liftₜ ρ} 
        (λ { Z → refl
           ; (S x) → trans 
                (↻-ren-reify {Δ₁ = Δ₁}
                  ρ 
                  {reflect (` x)} 
                  {reflect (` x)} 
                  (reflect-≈ refl)) 
                (reify-≈ (↻-ren-reflect ρ (` x))) }) 
        τ₁) 
      (↻-subₜNF-ren (liftₜ ρ) (extendₜNF idSubst (ren ρ τ₂)) τ₁))

--------------------------------------------------------------------------------
-- Immediate application of a weakened type has no effect

extendₜNF-weakenₜNF-cancel : ∀ {κ' : Kind} 
                        (σ : SubstitutionₜNF Δ₁ Δ₂) → 
                        (τ₁ : NormalType Δ₁ κ) {τ₂ : NormalType Δ₂ κ'} → 
                        sub (extendₜNF σ τ₂) (weakenₜNF τ₁) ≡ sub σ τ₁
extendₜNF-weakenₜNF-cancel σ τ₁ {τ₂} = sym (↻-subₜNF-ren S (extendₜNF σ τ₂) τ₁)

extendPredₜNF-weakenPredₜNF-cancel : ∀ {κ' : Kind} 
                        (σ : SubstitutionₜNF Δ₁ Δ₂) → 
                        (π : Pred (NormalType Δ₁ R[ κ ])) {τ : NormalType Δ₂ κ'} → 
                        sub (extendₜNF σ τ) (weakenPredₜNF π) ≡ sub σ π
extendPredₜNF-weakenPredₜNF-cancel σ (ρ₁ · ρ₂ ~ ρ₃) {τ} = 
  cong₃ _·_~_ (extendₜNF-weakenₜNF-cancel σ ρ₁) (extendₜNF-weakenₜNF-cancel σ ρ₂) (extendₜNF-weakenₜNF-cancel σ ρ₃)
extendPredₜNF-weakenPredₜNF-cancel σ (ρ₁ ≲ ρ₂) {τ} = 
  ap₂ _≲_ (extendₜNF-weakenₜNF-cancel σ ρ₁) (extendₜNF-weakenₜNF-cancel σ ρ₂)

weakenₜNF-β-id   : ∀ {κ' : Kind} (τ : NormalType Δ κ) {τ₂ : NormalType Δ κ'} → τ ≡ (weakenₜNF τ) βₜNF[ τ₂ ]
weakenₜNF-β-id τ {τ₂} = 
  trans 
    (sym (subₜNF-id τ)) 
    (sym (extendₜNF-weakenₜNF-cancel idSubst τ {τ₂}))

weakenPredₜNF-Β-id : ∀ {κ' : Kind} (π : Pred (NormalType Δ R[ κ ])) {τ₂ : NormalType Δ κ'} → π ≡ sub (extendₜNF (λ x₁ → η-norm (` x₁)) τ₂) (weakenPredₜNF π)
weakenPredₜNF-Β-id π {τ₂} with mapPredHO id  (λ τ → (weakenₜNF τ) βₜNF[ τ₂ ]) (λ τ → weakenₜNF-β-id τ {τ₂}) π 
weakenPredₜNF-Β-id (ρ₁ · ρ₂ ~ ρ₃) {τ₂} | c = c
weakenPredₜNF-Β-id (ρ₁ ≲ ρ₂) {τ₂} | c = c

--------------------------------------------------------------------------------
-- Liftsₜ and liftsₜNF fusion under ≡ₜ

liftsₜ-liftsₜNF≡ₜ : ∀ {σ : SubstitutionₜNF Δ₁ Δ₂} → 
                   ∀ (x : TVar (Δ₁ , κ₁) κ) →
                    liftsₜ (⇑ ∘ σ) x ≡ₜ (⇑ ∘ liftsₜNF σ) x
liftsₜ-liftsₜNF≡ₜ Z = eq-sym ((η-norm-≡ₜ (` Z)))
liftsₜ-liftsₜNF≡ₜ {σ = σ} (S x) = inst (sym (↻-ren-⇑ S (σ x)))

--------------------------------------------------------------------------------
-- Substitution of a lifted substitution over τ is eqivalent under _≡ₜ_ to 
-- substitution of (⇑ ∘ liftsₜNF σ) over τ

subₜ-liftsₜ-≡ₜ : ∀ {Δ₁ : KEnv} {κ' : Kind} {κ : Kind} (σ : SubstitutionₜNF Δ₁ Δ₂) (τ : Type (Δ₁ , κ') κ) →
                    sub (liftsₜ (⇑ ∘ σ)) τ ≡ₜ sub (⇑ ∘ liftsₜNF σ) τ
subₜ-liftsₜ-≡ₜ σ τ = subₜ-cong-≡ₜ liftsₜ-liftsₜNF≡ₜ τ

-- The general idea:
--   idEnv maps ` x ↦ reflect x 
-- whereas (lifte η) maps
--   ` Z   ↦ reflect (` Z)
--   ` S x ↦ η (` S x)
-- hence (lifte idEnv) maps
--   ` Z ↦ reflect (` Z)
--   ` S x ↦ idEnv (` S x) ≡ reflect (` S x)
-- And so lifte idEnv ≈ idEnv.
lifte-idEnv : (lifte {Δ₁ = Δ₁} {κ = κ} idEnv) ≈ₑ idEnv
lifte-idEnv Z = idEnv-≈ Z
lifte-idEnv (S x) = ↻-ren-reflect S (` x)

lifte²-idEnv : (lifte {Δ₁ = Δ₁ , κ₁} {κ = κ₂} (lifte {Δ₁ = Δ₁} {κ = κ₁} idEnv)) ≈ₑ idEnv
lifte²-idEnv Z = idEnv-≈ Z
lifte²-idEnv (S x) = trans-≈ (ren-≈ S (lifte-idEnv x)) (↻-ren-reflect S (` x))

weaken-⇓ₜ : ∀ {κ' : Kind}(τ : Type (Δ₁ , κ') κ) → 
                  reify (⟦ τ ⟧ₜ (lifte idEnv)) ≡ ⇓ₜ τ
weaken-⇓ₜ τ = reify-≈ (idext lifte-idEnv τ)

-- Unfortunately we have to prove this theorem for each finite application
-- of lifte.
weaken-⇓² : ∀(τ : Type ((Δ₁ , κ₁) , κ₂) κ₃) → 
                  reify (⟦ τ ⟧ₜ (lifte (lifte idEnv))) ≡ ⇓ₜ τ
weaken-⇓² τ = reify-≈ (idext lifte²-idEnv τ)

--------------------------------------------------------------------------------
-- We often have the nuisance of trying to substitute over a variable 
-- that is stuck mid η-normalization.

↻-subₜ-η-norm : ∀ (x : TVar Δ₁ κ)
                  (σ : Substitution Δ₁ Δ₂) → 
                  ⇓ₜ (sub σ (⇑ (η-norm (` x)))) ≡ ⇓ₜ (σ x)
↻-subₜ-η-norm x σ = soundness (subₜ-≡ₜ (η-norm-≡ₜ (` x)))

--------------------------------------------------------------------------------
-- Substituting a lifted substitution is equivalent to evaluating a lifted environment

↻-lifted-subₜNF-eval      : ∀ {Δ₁ : KEnv} {κ : Kind} 
                            (σ : SubstitutionₜNF Δ₁ Δ₂) (τ : NormalType (Δ₁ , κ) ★) → 
                    sub (liftsₜNF σ) τ 
                  ≡ 
                    ⟦ (⇑ τ [ liftsₜ (⇑ ∘ σ) ]ₛ) ⟧ₜ  (lifte idEnv)
↻-lifted-subₜNF-eval  σ τ = 
  trans 
    (fund-≈ idEnv-≈ (eq-sym (subₜ-liftsₜ-≡ₜ σ (⇑ τ))))
    (sym (weaken-⇓ₜ (sub (liftsₜ (⇑ ∘ σ)) (⇑ τ))))

--------------------------------------------------------------------------------
-- Substitution commutes with β reduction (again, but actually useful declaration).

↻-subₜNF-β      : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) (τ₁ : NormalType (Δ₁ , κ) ★) (τ₂ : NormalType Δ₁ κ) → 
                    sub σ (τ₁ βₜNF[ τ₂ ])
                  ≡ 
                    ⟦ (⇑ τ₁ [ (liftsₜ (⇑ ∘ σ)) ]ₛ) ⟧ₜ (lifte idEnv)
                    βₜNF[ sub σ τ₂ ]
↻-subₜNF-β σ τ₁ τ₂ =  
  trans 
    (↻-subₜNF-β' σ τ₁ τ₂) 
    (ap (λ x → x βₜNF[ sub σ τ₂ ]) 
      (trans         
        (soundness (eq-sym (subₜ-liftsₜ-≡ₜ σ (⇑ τ₁))))
        (sym (weaken-⇓ₜ (sub (liftsₜ (⇑ ∘ σ)) (⇑ τ₁))))))


--------------------------------------------------------------------------------
-- Renaming and substitution commutes over _·′_

↻-renₜNF-·′ : ∀ (ρ : Renaming Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             ren ρ (f ·′ v) ≡ ren ρ f ·′ ren ρ v
↻-renₜNF-·′ ρ (`λ f) v = ↻-renₜNF-β ρ f v 

↻-subₜNF-·′ :  
           ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) 
             (f : NormalType Δ₁ (κ₁ `→ ★))
             (v : NormalType Δ₁ κ₁) → 
             sub σ (f ·′ v) ≡ sub σ f ·′ sub σ v
↻-subₜNF-·′ σ (`λ f) v = ↻-subₜNF-β σ f v

--------------------------------------------------------------------------------
-- Substitution commutes with embedding

↻-sub-⇑ : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) → (τ : NormalType Δ₁ κ) → 
          ⇑ (sub σ τ) ≡ₜ sub (⇑ ∘ σ) (⇑ τ)
↻-sub-⇑ σ τ = embed-≡ₜ (⇑-inj  (sub σ τ) (⇓ₜ (sub (⇑ ∘ σ) (⇑ τ))) refl)

--------------------------------------------------------------------------------
-- Substitution commutes with embedding (over rows)

↻-sub-⇑ᵣ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} (σ : SubstitutionₜNF Δ₁ Δ₂) (ys : RowLiteral (NormalType Δ₁ κ)) → 
        ⇑ᵣ (sub σ (⇓ᵣ (⇑ᵣ ys))) ≡ᵣ sub (⇑ ∘ σ) (⇑ᵣ ys)
↻-sub-⇑ᵣ σ [] = eq-[]
↻-sub-⇑ᵣ σ ((l , τ) ∷ ys) rewrite stability τ = eq-cons refl (↻-sub-⇑ σ τ) (↻-sub-⇑ᵣ σ ys)

--------------------------------------------------------------------------------
-- Embedding commutes with β-reduction

↻-idSubst-`-⇑ : ∀ (υ : NormalType Δ κ₁) {κ : Kind} (x : TVar (Δ , κ₁) κ)  → 
                (⇑ ∘ extendₜNF idSubst υ) x ≡ₜ extendₜ ` (⇑ υ) x
↻-idSubst-`-⇑ υ Z = eq-refl
↻-idSubst-`-⇑ υ (S x) = η-norm-≡ₜ (` x)

↻-β-⇑ : ∀ (τ₁ : NormalType (Δ , κ₁) κ₂) (τ₂ : NormalType Δ κ₁) → 
        ⇑ (τ₁ βₜNF[ τ₂ ]) ≡ₜ (⇑ τ₁) βₜ[ ⇑ τ₂ ]
↻-β-⇑ τ₁ τ₂ = 
  embed-≡ₜ {τ₁ = τ₁ βₜNF[ τ₂ ]} {⇑ τ₁ βₜ[ ⇑ τ₂ ]} 
  (reify-≈ 
  (fund-≈ {τ₁ = sub (λ x → ⇑ (extendₜNF idSubst τ₂ x)) (⇑ τ₁)}
         {⇑ τ₁ βₜ[ ⇑ τ₂ ]} 
         idEnv-≈ 
         (subₜ-cong-≡ₜ 
           (↻-idSubst-`-⇑ τ₂) 
           (⇑ τ₁))))


--------------------------------------------------------------------------------
-- Normalization commutes with β-reduction

↻-⇑-extend : (υ : Type Δ κ₁) → {κ : Kind} (x : TVar (Δ , κ₁) κ) →
                extendₜ ` υ x ≡ₜ ⇑ (extendₜNF idSubst (⇓ₜ υ) x)
↻-⇑-extend υ Z = consistency υ
↻-⇑-extend υ (S x) = eq-sym (η-norm-≡ₜ (` x))

↻-β-⇓ₜ : ∀ (τ₁ : Type (Δ , κ) ★) (τ₂ : Type Δ κ) → 
        ⇓ₜ (τ₁ βₜ[ τ₂ ]) ≡ (⇓ₜ τ₁) βₜNF[ ⇓ₜ τ₂ ]
↻-β-⇓ₜ τ₁ τ₂ = 
  reify-≈ 
  (fund-≈ 
    {τ₁ = sub (extendₜ ` τ₂) τ₁}
    {τ₂ = sub (λ x → ⇑ (extendₜNF idSubst (⇓ₜ τ₂) x)) (⇑ (⟦ τ₁ ⟧ₜ idEnv))}
    idEnv-≈ 
      (eq-trans 
        (subₜ-cong-≡ₜ (↻-⇑-extend τ₂) τ₁) 
        (subₜ-≡ₜ (consistency τ₁))))

--------------------------------------------------------------------------------
-- _·′_ commutes with embedding

↻-·′-⇑ : (f : NormalType Δ (κ₁ `→ κ₂)) → (N : NormalType Δ κ₁) → ⇑ (f ·′ N) ≡ₜ ⇑ f · ⇑ N
↻-·′-⇑ (`λ f) N = 
  eq-trans 
    (eq-trans 
      (↻-sub-⇑ (extendₜNF idSubst N) f) 
      (subₜ-cong-≡ₜ (↻-idSubst-`-⇑ N) (⇑ f))) 
    (eq-sym eq-β)

--------------------------------------------------------------------------------
-- _·′_ and mapping are stable (Denormalization followed by renormalization yields themselves)

stability-·′ : (f : NormalType Δ (κ₁ `→ κ₂)) → (N : NormalType Δ κ₁) → f ·′ N ≡ ⇓ₜ (⇑ₜ f · ⇑ₜ N)
stability-·′ f N = trans 
    (sym (stability (f ·′ N))) 
    (soundness {τ₁ = ⇑ (f ·′ N)} {τ₂ =  ⇑ f · ⇑ N} (↻-·′-⇑ f N))


stability-map : ∀ (f : NormalType Δ (κ₁ `→ κ₂)) → (xs : RowLiteral (NormalType Δ κ₁)) → 
                map (map₂ (_·′_ f)) xs ≡ f $′ xs
stability-map f [] = refl
stability-map f (x ∷ xs) = (cong₂ _∷_ (cong₂ _,_ refl (stability-·′ f (x .snd))) (stability-map f xs))

stability-map-⦅⦆ : ∀ (f : NormalType Δ (κ₁ `→ κ₂)) → (xs : RowLiteral (NormalType Δ κ₁)) (oxs : True (ordered? xs)) → 
                  f $' (⦅ xs ⦆ oxs) ≡ 
                  ⦅ map (map₂ (_·′_ f)) xs ⦆ (fromWitness (map-map₂ {Ty = NormalType} xs (_·′_ f) (toWitness oxs)))
stability-map-⦅⦆ f xs oxs = cong-⦅  (sym (stability-map f xs)) ⦆nf

--------------------------------------------------------------------------------
-- $' and $s are stable
 
-- stability-$ : ∀ (F : NormalType Δ (κ₁ `→ κ₂)) → (ρ : NormalType Δ R[ κ₁ ]) → 
--               F $' ρ ≡ F $s ρ 
-- stability-$ F ρ = {!!} 

--------------------------------------------------------------------------------
-- Normality preserving substitution commutes over $

↻-subₜNF-$' : ∀ (σ : SubstitutionₜNF Δ₁ Δ₂) → (f : NormalType Δ₁ (κ₁ `→ κ₂)) →
                  (ρ : NormalType Δ₁ R[ κ₁ ]) → 
                  sub σ (f $' ρ) ≡ sub σ f $' sub σ ρ
↻-subₜNF-$' σ F@(`λ M) ρ = sym (
  trans 
    (reify-≈
       {V₁ = (↑ (subₜNF σ F)) ⟨$⟩ ((↑ (subₜNF σ ρ)))} 
       {V₂ = (λ {Δ} → (⟦ ⇑ F [ ⇑ ∘ σ ]ₛ ⟧ₜ idEnv) {Δ}) ⟨$⟩ (⟦ ⇑ ρ [ ⇑ ∘ σ ]ₛ ⟧ₜ idEnv)}  
       (cong-$ 
       (fund-≈ idEnv-≈ (↻-sub-⇑ σ F)) 
        ((fund-≈ idEnv-≈ (↻-sub-⇑ σ ρ)))))
     (↻-⇓-sub σ (⇑ F $ ⇑ ρ)))

--------------------------------------------------------------------------------
-- Embedding commutes with mapping

-- ↻-⇑-$ : ∀ (φ : NormalType Δ (κ₁ `→ κ₂)) (ρ : NormalType Δ R[ κ₁ ]) → 
--             ⇑ φ $ ⇑ ρ ≡ₜ ⇑ (φ $' ρ)
-- ↻-⇑-$ φ (ρ $ x) = {!!}
-- ↻-⇑-$ φ (⦅ ρ ⦆ ω) = eq-trans eq-map (eq-row {!!})
-- ↻-⇑-$ φ (ρ ∖ ρ₁) = {!!} -- eq-trans {!eq-!} {!!}
-- ↻-⇑-$ φ (l ▹ₙ ρ) = {!!}

--------------------------------------------------------------------------------
-- Ordering is preserved by substitution and embedding

ordered-subRowₜ-⇑ :  (σ : SubstitutionₜNF Δ₁ Δ₂) → {ys : RowLiteral (NormalType Δ₁ κ)} → 
                      Ordered ys → 
                      Ordered (sub (⇑ ∘ σ) (⇑ᵣ ys))
ordered-subRowₜ-⇑ σ {[]} oys = tt
ordered-subRowₜ-⇑ σ {(l , τ) ∷ []} oys = tt
ordered-subRowₜ-⇑ σ {(l , τ) ∷ (l' , τ') ∷ ys} (l<l' , oys) = l<l' , ordered-subRowₜ-⇑ σ oys

