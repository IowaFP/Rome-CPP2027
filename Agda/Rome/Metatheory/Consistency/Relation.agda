-- 
module Rome.Metatheory.Consistency.Relation where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Renaming
open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution
open import Rome.Types.Properties.Equivalence

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming 
open import Rome.NormalTypes.Properties.Renaming

open import Rome.NBE.Syntax
open import Rome.NBE.Renaming
open import Rome.NBE.Normalization


open import Rome.Types.Equivalence
open import Rome.Types.Properties.Equivalence
open import Rome.Metatheory.Soundness
open import Rome.Metatheory.Stability

--------------------------------------------------------------------------------
-- Consistency of type normalization: 
--   All types are equivalent (under ≡ₜ) to their normal forms.

infix 0 ⟦_⟧≈_
⟦_⟧≈_ : ∀ {Δ : KEnv} {κ : Kind} → Type Δ κ → SemType Δ κ → Set
⟦_⟧≈ne_ : ∀ {Δ : KEnv} {κ : Kind} → Type Δ κ → NeutralType Δ κ → Set

⟦_⟧≈ᵣ_ : ∀ {Δ : KEnv} {κ : Kind} → RowLiteral (Type Δ κ) → Row (SemType Δ κ) → Set
⟦_⟧≈₂_ : ∀ {Δ : KEnv} {κ : Kind} → Label × Type Δ κ → Label × SemType Δ κ → Set
⟦ (l₁ , τ) ⟧≈₂ (l₂ , V) = (l₁ ≡ l₂) × (⟦ τ ⟧≈ V)

ConsistentKripke : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunction Δ₁ κ₁ κ₂ → Set
ConsistentKripkeNE : Type Δ₁ (κ₁ `→ κ₂) → KripkeFunctionNE Δ₁ κ₁ κ₂ → Set

-- τ is equivalent to neutral `n` if it's equivalent 
-- to the η and map-id expansion of n
⟦_⟧≈ne_ τ n = τ ≡ₜ ⇑ (η-norm n)

⟦_⟧≈_ {κ = ★} τ₁ τ₂ = τ₁ ≡ₜ ⇑ τ₂
⟦_⟧≈_ {κ = L} τ₁ τ₂ = τ₁ ≡ₜ ⇑ τ₂
⟦_⟧≈_ {Δ₁} {κ = κ₁ `→ κ₂} f F = ConsistentKripke f F
⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (row ρ ω) =
    let xs = ⇑ᵣ (reifyRow ρ) in 
    (τ ≡ₜ ⦅ xs ⦆ (fromWitness (⇑ₒ {ρ = reifyRow ρ} (reifyRowOrdered ω)))) × 
    (⟦ xs ⟧≈ᵣ ρ)
⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = (τ ≡ₜ (⇑ₙₑ l ▹ ⇑ (reify V))) × (⟦ ⇑ (reify V) ⟧≈ V)
⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ∖ ρ₁) {nr}) = (τ ≡ₜ (⇑ (reify ((ρ₂ ∖ ρ₁) {nr})))) × (⟦ ⇑ (reify ρ₂) ⟧≈ ρ₂) × (⟦ ⇑ (reify ρ₁) ⟧≈ ρ₁)
⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (φ $ n) = 
  ∃[ f ] ((τ ≡ₜ (f $ ⇑ₙₑ n)) × (ConsistentKripkeNE f φ))

⟦ [] ⟧≈ᵣ (zero , P) = ⊤
⟦ [] ⟧≈ᵣ (suc n , P) = ⊥
⟦ x ∷ ρ ⟧≈ᵣ (zero , P) = ⊥
⟦ x ∷ ρ ⟧≈ᵣ (suc n , P) =  (⟦ x ⟧≈₂ (P fzero)) × ⟦ ρ ⟧≈ᵣ (n , P ∘ fsuc)

ConsistentKripke {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂ : KEnv} (ρ : Renaming Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≈ V → 
      ⟦ (renₜ ρ f · v) ⟧≈ (renKripke ρ F ⟨·⟩ V)

ConsistentKripkeNE {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂ = κ₂} f F =     
    ∀ {Δ₂ : KEnv} (r : Renaming Δ₁ Δ₂) {v V} → 
      ⟦ v ⟧≈ne  V → 
      ⟦ (renₜ r f · v) ⟧≈ (F r V)

--------------------------------------------------------------------------------
-- Neutral types are equivalent to their η-normalizations

η-norm-≡ₜ'ren : ∀ (τ : NeutralType Δ₁ κ) {r : Renaming Δ₁ Δ₂} → 
                  ⇑ (ren r (η-norm τ)) ≡ₜ ⇑ₙₑ (ren r τ)
η-norm-≡ₜ'ren {κ = ★} τ = eq-refl
η-norm-≡ₜ'ren {κ = L} τ = eq-refl
η-norm-≡ₜ'ren {κ = κ `→ κ₁} τ {r} = 
  eq-trans 
    (eq-λ (η-norm-≡ₜ'ren (ren S τ · reify (reflect (` Z))) {liftₜ r})) 
  (eq-trans 
    (eq-λ (eq-· 
      (inst (trans (↻-ren-⇑ₙₑ (liftₜ r) (ren S τ)) (ap (renₜ (liftₜ r)) (↻-ren-⇑ₙₑ S  τ)))) 
      (η-norm-≡ₜ'ren (` Z) {liftₜ r}))) 
  (eq-trans (eq-λ (eq-· (eq-trans (inst (↻-liftₜ-weaken r (⇑ₙₑ τ))) (inst (ap (renₜ S) (sym (↻-ren-⇑ₙₑ  r τ))))) eq-refl)) 
    (eq-sym eq-η)))
η-norm-≡ₜ'ren {κ = R[ κ ]} τ {r} = eq-trans (eq-$ (eq-λ (η-norm-≡ₜ'ren (` Z) {liftₜ r})) eq-refl) eq-map-id

η-norm-≡ₜ : ∀ (τ : NeutralType Δ κ) → ⇑ (η-norm τ) ≡ₜ ⇑ₙₑ τ 
η-norm-≡ₜ  τ = 
  eq-trans 
    (tr 
      (λ X → ⇑ X ≡ₜ ⇑ₙₑ (ren id τ)) {x = ren id (η-norm τ)} 
      (renₜNF-id  (η-norm τ)) 
      ((η-norm-≡ₜ'ren τ {id}))) 
  (inst (ap ⇑ₙₑ (renₜNE-id τ)))

--------------------------------------------------------------------------------
-- - Types equivalent to neutral types under ≡ₜ reflect to equivalence under _≈_, and 
-- - Types related under _≈_ have reifications equivalent under _≡ₜ_

reflect-⟦⟧≈ : ∀ {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
             τ ≡ₜ ⇑ₙₑ υ → ⟦ τ ⟧≈ (reflect υ)
reify-⟦⟧≈ : ∀ {τ : Type Δ κ} {V :  SemType Δ κ} → 
               ⟦ τ ⟧≈ V → τ ≡ₜ ⇑ (reify V)

reflect-⟦⟧≈ {κ = ★} e = e  
reflect-⟦⟧≈ {κ = L} e = e 
reflect-⟦⟧≈ {κ = κ₁ `→ κ₂} {τ} {υ} e = 
    λ ρ q → reflect-⟦⟧≈ 
    (eq-· 
        (eq-sym (eq-trans (inst (↻-ren-⇑ₙₑ ρ υ)) 
            (renₜ-≡ₜ ρ (eq-sym e)))) 
        (reify-⟦⟧≈ q)) 
reflect-⟦⟧≈ {κ = R[ κ ]} e = 
  `λ (⇑ (η-norm (` Z))) , eq-trans (eq-sym eq-map-id) (eq-$ (eq-λ (eq-sym (η-norm-≡ₜ (` Z)))) e) , 
  λ r {v = v} {V} eq → reflect-⟦⟧≈ (eq-trans 
    (eq-· eq-refl eq) 
    (eq-trans 
      eq-β 
      (eq-trans 
        (inst (sym (↻-subₜ-renₜ (⇑ (reify (reflect _)))))) 
        (eq-trans 
          (subₜ-≡ₜ (η-norm-≡ₜ (` Z))) (η-norm-≡ₜ V)))))

reify-⟦⟧≈ {κ = ★} {τ} {V} e = e 
reify-⟦⟧≈ {κ = L} {τ} {V} e = e
reify-⟦⟧≈ {κ = κ₁ `→ κ₂} {τ} {F} e = 
    eq-trans 
        eq-η 
        (eq-λ (eq-trans 
            (reify-⟦⟧≈ (e S (reflect-⟦⟧≈ eq-refl))) 
            eq-refl))

reify-⟦⟧≈ {κ = R[ κ ]} {τ} {row (zero , P) _} (eq , I) = eq
reify-⟦⟧≈ {κ = R[ κ ]} {τ} {row (suc n , P) _} (eq , I) = eq-trans eq (eq-row (eq-cons refl eq-refl (instᵣ refl)))
reify-⟦⟧≈ {κ = R[ κ ]} {τ} {l ▹ V} eq = fst eq
reify-⟦⟧≈ {κ = R[ κ ]} {τ} {V₂ ∖ V₁} eq = eq .fst
reify-⟦⟧≈ {κ = R[ κ ]} {τ} {φ $ ρ} (f , eq , rel) = 
  eq-trans 
    eq 
    (eq-$  
      (eq-trans 
        eq-η
        (eq-λ (reify-⟦⟧≈ (rel S (eq-sym (η-norm-≡ₜ (` Z))))))) 
      eq-refl)

reify-⟦⟧≈ᵣ : ∀ {xs : RowLiteral (Type Δ κ)} {V :  Row (SemType Δ κ)} → 
               ⟦ xs ⟧≈ᵣ V → xs ≡ᵣ ⇑ᵣ (reifyRow V)
reify-⟦⟧≈ᵣ {xs = []} {zero , P} rel = eq-[]
reify-⟦⟧≈ᵣ {xs = x ∷ xs} {suc n , P} (eq , I) = eq-cons (eq .fst) (reify-⟦⟧≈ (eq .snd)) (reify-⟦⟧≈ᵣ I)

--------------------------------------------------------------------------------
-- Equivalent types relate to the same semantic types

subst-⟦⟧≈ : ∀ {τ₁ τ₂ : Type Δ κ} → 
  τ₁ ≡ₜ τ₂ → 
  {V : SemType Δ κ} → 
  ⟦ τ₁ ⟧≈ V → 
  ---------
  ⟦ τ₂ ⟧≈ V 

subst-⟦⟧≈ {κ = ★} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≈ {κ = L} {τ₁ = τ₁} {τ₂} q {V} rel = eq-trans (eq-sym q) rel
subst-⟦⟧≈ {κ = κ `→ κ₁} {τ₁ = τ₁} {τ₂} q {F} rel = λ ρ {v} {V} rel-v → subst-⟦⟧≈ (eq-· (renₜ-≡ₜ ρ q) eq-refl) (rel ρ rel-v)
subst-⟦⟧≈ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {φ $ n} (f , eq , rel) = f , (eq-trans (eq-sym q) eq) , rel
subst-⟦⟧≈ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {row (n , P) _} (eq , I) = eq-trans (eq-sym q) eq , I
subst-⟦⟧≈ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {l ▹ τ} (eq , rel) = eq-trans (eq-sym q) eq , rel
subst-⟦⟧≈ {κ = R[ κ ]} {τ₁ = τ₁} {τ₂} q {V₂ ∖ V₁} (eq , rel₁ , rel₂) = eq-trans (eq-sym q) eq , rel₁ , rel₂

--------------------------------------------------------------------------------
-- Equivalent rows relate to the same semantic rows

subst-⟦⟧≈ᵣ : ∀ {xs ys : RowLiteral (Type Δ κ)} → 
  xs ≡ᵣ ys → 
  {ρ : Row (SemType Δ κ)} → 
  ⟦ xs ⟧≈ᵣ ρ → 
  ---------
  ⟦ ys ⟧≈ᵣ ρ

subst-⟦⟧≈ᵣ eq-[] rel = rel
subst-⟦⟧≈ᵣ (eq-cons refl eq-x eq-xs) {suc n , P} ((eq , rel-x) , rel-xs) = (eq , subst-⟦⟧≈ eq-x rel-x) , (subst-⟦⟧≈ᵣ eq-xs rel-xs) 

-- --------------------------------------------------------------------------------
-- -- Stability rule for reification

refl-⟦⟧≈ : ∀ {Δ : KEnv} {κ : Kind} {v : Type Δ κ} {V : SemType Δ κ} → 
                ⟦ v ⟧≈ V  →
               ⟦ ⇑ (reify V) ⟧≈ V 
refl-⟦⟧≈ {κ = κ} rel-v = subst-⟦⟧≈ (reify-⟦⟧≈ rel-v) rel-v

refl-⟦⟧≈ᵣ : ∀ {Δ : KEnv} {κ : Kind} {xs : RowLiteral (Type Δ κ)} {ρ : Row (SemType Δ κ)} → 
                ⟦ xs ⟧≈ᵣ ρ  →
               ⟦ ⇑ᵣ (reifyRow ρ) ⟧≈ᵣ ρ
refl-⟦⟧≈ᵣ {κ = κ} rel = subst-⟦⟧≈ᵣ (reify-⟦⟧≈ᵣ rel) rel
    

--------------------------------------------------------------------------------
-- renaming respects consistency relation

ren-⟦⟧≈ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} 
            (ρ : Renaming Δ₁ Δ₂) 
           {v : Type Δ₁ κ} 
           {V : SemType Δ₁ κ} → 
           ⟦ v ⟧≈ V → 
           ⟦ renₜ ρ v ⟧≈ renSem ρ V

-- We need to state the renaming lemma over both semantic and syntactic row renaming
ren-⟦⟧≈ᵣ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
             (ρ : Renaming Δ₁ Δ₂) → 
             (n : ℕ) (P : Fin n → Label × SemType Δ₁ κ) → 
           ⟦ ⇑ᵣ (reifyRow (n , P)) ⟧≈ᵣ (n , P) → 
           ⟦ ⇑ᵣ (reifyRow (n , map₂ (renSem ρ) ∘ P)) ⟧≈ᵣ (n , map₂ (renSem ρ) ∘ P)

ren-⟦⟧≈ᵣ' : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
             (ρ : Renaming Δ₁ Δ₂) → 
             (n : ℕ) (P : Fin n → Label × SemType Δ₁ κ) → 
           ⟦ ⇑ᵣ (reifyRow (n , P)) ⟧≈ᵣ (n , P) → 
           ⟦ ren ρ (⇑ᵣ (reifyRow (n , P))) ⟧≈ᵣ renRow ρ (n , P)


-- and that renaming commutes over (⇑ ∘ reify)
↻-ren-⇑-reify-∖ : ∀ (r : Renaming Δ₁ Δ₂) (V₂ V₁ : SemRow Δ₁ (λ Δ → SemType Δ κ) R[ κ ]) →
                ⟦ ⇑ (reify V₂) ⟧≈ V₂ →
                ⟦ ⇑ (reify V₁) ⟧≈ V₁ →  
                (ev : NotRowLiteral V₂ or NotRowLiteral V₁) → 
                renₜ r (⇑ (reify ((V₂ ∖ V₁) {ev}))) ≡ₜ ⇑ (reify ((renSem r V₂ ∖ renSem r V₁) {nrRenSem' r V₂ V₁ ev}))
↻-ren-⇑-reify :  ∀ (r : Renaming Δ₁ Δ₂) (V : SemRow Δ₁ (λ Δ → SemType Δ κ) R[ κ ]) →
                ⟦ ⇑ (reify V) ⟧≈ V →
                renₜ r (⇑ (reify V)) ≡ₜ ⇑ (reify (renSem r V))

--------------------------------------------------------------------------------
-- renaming respects consistency relation (definitions)

↻-ren-⇑-reify r (φ $ N) (f , eq , rel₁) = 
  (eq-trans 
    (renₜ-≡ₜ r eq) 
    (eq-$ 
      (eq-trans 
        eq-η 
        (eq-λ (eq-trans 
          (eq-· (inst (sym (renₜ-comp r S f))) eq-refl)
          ((reify-⟦⟧≈ (rel₁ (S ∘ r) (eq-sym (η-norm-≡ₜ (` Z))))))))) 
      (inst (sym (↻-ren-⇑ₙₑ r N)))))
↻-ren-⇑-reify r (x₁ ▹ x₂) rel = 
  eq-▹ 
    (inst (sym (↻-ren-⇑ₙₑ r x₁))) 
    (reify-⟦⟧≈ (ren-⟦⟧≈ r (rel .snd)))
↻-ren-⇑-reify r (row (n , P) x₁) rel = eq-row (reify-⟦⟧≈ᵣ (ren-⟦⟧≈ᵣ' r n P (rel .snd)))
↻-ren-⇑-reify r ((V₂ ∖ V₁) {nr}) (eq , rel₂ , rel₁) = ↻-ren-⇑-reify-∖ r V₂ V₁ rel₂ rel₁ nr                 

↻-ren-⇑-reify-∖ r (l ▹ τ) V₂ rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify r (l ▹ τ) rel₂) (↻-ren-⇑-reify r V₂ rel₁)
↻-ren-⇑-reify-∖ r ρ₂@(row ρ x₁) ρ₁@(φ $ x₂) rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-∖ r ρ₂@(row ρ x₁) ρ₁@(x₂ ▹ x₃) rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-∖ r (row ρ x₁) (row ρ₁ x₂) rel₂ rel₁ (left ())
↻-ren-⇑-reify-∖ r (row ρ x₁) (row ρ₁ x₂) rel₂ rel₁ (right ())
↻-ren-⇑-reify-∖ r ρ₂@(row ρ x₁) ρ₁@(V₂ ∖ V₃) rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify r ρ₂ rel₂) (↻-ren-⇑-reify r ρ₁ rel₁)
↻-ren-⇑-reify-∖ r ((ρ₂ ∖ ρ₁) {nr}) V₂ rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify-∖ r ρ₂ ρ₁ (rel₂ .snd .fst) (rel₂ .snd .snd) nr) (↻-ren-⇑-reify r V₂ rel₁)
↻-ren-⇑-reify-∖ r (φ $ n) V₂ rel₂ rel₁ ev = eq-∖ (↻-ren-⇑-reify r (φ $ n) rel₂) (↻-ren-⇑-reify r V₂ rel₁)

ren-⟦⟧≈ᵣ' ρ zero P rel = tt
ren-⟦⟧≈ᵣ' ρ (suc n) P (rel-fzero , rel-fsuc) = (refl , (ren-⟦⟧≈ ρ (rel-fzero .snd))) , ren-⟦⟧≈ᵣ' ρ n  (P ∘ fsuc) rel-fsuc 
ren-⟦⟧≈ᵣ ρ zero P rel = tt
ren-⟦⟧≈ᵣ ρ (suc n) P (rel-fzero , rel-fsuc) = (refl , refl-⟦⟧≈ (ren-⟦⟧≈ ρ (rel-fzero .snd))) , ren-⟦⟧≈ᵣ ρ n (λ x → P (fsuc x)) rel-fsuc

ren-⟦⟧≈ {κ = ★} ρ {v} {V} rel-v = eq-trans (renₜ-≡ₜ ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≈ {κ = L} ρ {v} {V} rel-v = eq-trans (renₜ-≡ₜ ρ rel-v) (eq-sym ((inst (↻-ren-⇑ ρ V))))
ren-⟦⟧≈ {κ = κ `→ κ₁} ρ₁ {v₁} {V₁} rel-v₁ ρ₂ {v₂} {V₂} rel-v₂  = subst-⟦⟧≈ (eq-· (inst (renₜ-comp ρ₁ ρ₂ v₁)) eq-refl) (rel-v₁ (ρ₂ ∘ ρ₁) rel-v₂)
ren-⟦⟧≈ {κ = R[ κ ]} ρ {v} {φ $ n} (f , eq , rel-v) = 
  renₜ ρ f , 
  eq-trans (renₜ-≡ₜ ρ eq) (eq-$ eq-refl (inst (sym (↻-ren-⇑ₙₑ ρ n)))) , 
  (λ r v-eq → subst-⟦⟧≈ (eq-· (inst (renₜ-comp ρ r f)) eq-refl) (rel-v (r ∘ ρ) v-eq)) 
ren-⟦⟧≈ {κ = R[ κ ]} ρ {v} {row (n , P) _} (eq , rel) = 
  eq-trans 
    (renₜ-≡ₜ ρ eq) 
    (eq-row ( reify-⟦⟧≈ᵣ (ren-⟦⟧≈ᵣ' ρ n P rel))) , 
  ren-⟦⟧≈ᵣ ρ n P rel
ren-⟦⟧≈ {κ = R[ κ ]} r {v} {l ▹ V} (eq , rel) = 
  eq-trans 
    (renₜ-≡ₜ r eq) 
    (eq-▹ 
      (inst (sym (↻-ren-⇑ₙₑ r l))) 
      (reify-⟦⟧≈ (ren-⟦⟧≈ r rel))) , refl-⟦⟧≈  (ren-⟦⟧≈ r rel)
ren-⟦⟧≈ {κ = R[ κ ]} r {v} {(V₂ ∖ V₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans (renₜ-≡ₜ r eq) (↻-ren-⇑-reify-∖ r V₂ V₁ rel₂ rel₁ nr)) , 
  (refl-⟦⟧≈ (ren-⟦⟧≈ r rel₂)) , 
  (refl-⟦⟧≈ (ren-⟦⟧≈ r rel₁))

--------------------------------------------------------------------------------
-- Relating syntactic substitutions to semantic environments
 
⟦_⟧≈ₑ_ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} → Substitution Δ₁ Δ₂ → SemEnv Δ₁ Δ₂ → Set  
⟦_⟧≈ₑ_ {Δ₁ = Δ₁} σ η = ∀ {κ : Kind} (α : TVar Δ₁ κ) → ⟦ (σ α) ⟧≈ (η α)

-- Identity relation
idEnv-⟦⟧≈ : ∀ {Δ₁ : KEnv} →  ⟦ ` ⟧≈ₑ (idEnv {Δ₁})
idEnv-⟦⟧≈ α = reflect-⟦⟧≈ eq-refl

--------------------------------------------------------------------------------
-- Extended substitutions relate to extended environments

extend-⟦⟧≈ : ∀ {κ : Kind} {σ : Substitution Δ₁ Δ₂} {η : SemEnv Δ₁ Δ₂} → 
             ⟦ σ ⟧≈ₑ η →
             ∀ {τ : Type Δ₂ κ} {V : SemType Δ₂ κ} → 
             ⟦ τ ⟧≈ V → 
             ⟦ (extendₜ σ τ) ⟧≈ₑ (extende η V)
extend-⟦⟧≈ p q Z = q
extend-⟦⟧≈ p q (S x) = p x

--------------------------------------------------------------------------------
-- Weakened substitutions relate to weakened environments
 
weaken-⟦⟧≈ : ∀ {κ : Kind} {σ : Substitution Δ₁ Δ₂} {η : SemEnv Δ₁ Δ₂} → 
           ⟦ σ ⟧≈ₑ η → 
           ⟦ liftsₜ {κ = κ} σ ⟧≈ₑ (extende (λ {κ'} v → renSem S (η v)) (reflect (` Z)))
weaken-⟦⟧≈ e Z = reflect-⟦⟧≈ eq-refl
weaken-⟦⟧≈ e (S α) = ren-⟦⟧≈ S (e α)           

--------------------------------------------------------------------------------
--  Substituting syntactic substitutions in related environments

substEnv-⟦⟧≈ : ∀ {σ₁ σ₂ : Substitution Δ₁ Δ₂} {η : SemEnv Δ₁ Δ₂} → 
             (∀ {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) →
             ⟦ σ₁ ⟧≈ₑ η →
             ⟦ σ₂ ⟧≈ₑ η
substEnv-⟦⟧≈ eq rel x rewrite sym (eq x) = rel x

--------------------------------------------------------------------------------
-- A necessary lemma difficult to describe

map₂-⟦⟧≈ : ∀ {n : ℕ} {Δ₂ : KEnv} {κ₁ : Kind} {κ₂ : Kind}
             {P : Fin n → Label × SemType Δ₂ κ₁} 
             {σ : Substitution Δ₁ Δ₂}
             {η : SemEnv Δ₁ Δ₂}
             (f : Type Δ₁ (κ₁ `→ κ₂)) → 
             ⟦ subₜ σ f ⟧≈ (⟦ f ⟧ₜ η) → 
             ⟦ ⇑ᵣ (reifyRow (n , P)) ⟧≈ᵣ (n , P) → 
            ⟦ ⇑ᵣ (reifyRow (n , map₂ (⟦ f ⟧ₜ η id) ∘ P)) ⟧≈ᵣ (n , (map₂ (⟦ f ⟧ₜ η id)) ∘ P)
map₂-⟦⟧≈ {n = zero} F rel-f rel = tt
map₂-⟦⟧≈ {n = suc n} F rel-f ((refl , rel-fzero) , rel-fsuc) = 
  (refl , (refl-⟦⟧≈ (rel-f id rel-fzero))) , map₂-⟦⟧≈ {n = n} F rel-f rel-fsuc 

--------------------------------------------------------------------------------
-- To be clear, although we use an existential in defining ⟦ τ ⟧≈(φ $ n), 
-- we know more precisely that τ ≡ₜ `λ (⇑ (reify (φ₂ S (` Z)))) $ ⇑ₙₑ n.

reifyConsistentKripkeNE-≡ₜ : ∀ {τ : Type Δ R[ κ₂ ]} {f : Type Δ (κ₁ `→ κ₂)} {n : NeutralType Δ R[ κ₁ ]} 
        {φ : KripkeFunctionNE Δ κ₁ κ₂} → 
        τ ≡ₜ f $ ⇑ₙₑ n → 
        ConsistentKripkeNE f φ → 
        τ ≡ₜ (`λ (⇑ (reify (φ S (` Z)))) $ ⇑ₙₑ n)
reifyConsistentKripkeNE-≡ₜ eq rel-f = 
  (eq-trans 
      eq
      (eq-$ 
        (eq-trans eq-η (eq-λ (reify-⟦⟧≈ (rel-f S {` Z} (eq-sym (η-norm-≡ₜ (` Z))))))) 
        eq-refl))


--------------------------------------------------------------------------------
-- The property implied by the notation holds:
-- if τ is related to V under the consistency LR, then ⟦ τ ⟧ ≈ V under the soundness LR.

-- ⇑-reify-≈ : ∀ {V : SemType Δ κ} → ⟦ ⇑ (reify V) ⟧ idEnv ≈ V 
-- ⇑-reify-≈ {V = V} = {! fund-≈ {τ₁ = ⇑ (reify V)}  !} 

-- ⟦⟧≈-to-≈ : ∀ {τ : Type Δ κ} {V : SemType Δ κ} → 
--            ⟦ τ ⟧≈ V →  ⟦ τ ⟧ idEnv ≈ V
-- ⟦⟧≈-to-≈ {κ = κ} {τ = τ} {V} e = 
--   trans-≈ (fund-≈ idEnv-≈ (reify-⟦⟧≈ e)) ⇑-reify-≈
-- -- ⟦⟧≈-to-≈ {κ = ★} {τ = τ} {V} e = soundness e ○ stability V
-- -- ⟦⟧≈-to-≈ {κ = L} {τ = τ} {V} e = soundness e ○ stability V
-- -- ⟦⟧≈-to-≈ {κ = κ₁ `→ κ₂} {τ = τ} {V} e = (λ r₁ r₂ V₁ V₂ x → {! e r₁ {⇑ (reify V₁)} {V₂}  !}) , ({!   !} , {!   !})
-- -- ⟦⟧≈-to-≈ {κ = R[ κ ]} {τ = τ} {V} e = {! soundness (reify-⟦⟧≈ e)  !}            