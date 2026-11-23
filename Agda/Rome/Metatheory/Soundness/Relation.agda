-- 
module Rome.Metatheory.Soundness.Relation where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.Properties.Renaming as NTypeProps
open import Rome.NBE.Syntax
open import Rome.NBE.Renaming
open import Rome.NBE.Normalization

--------------------------------------------------------------------------------
-- Soundness relation on semantic types

infixr 4 _≈_
infixr 4 _≈NE_
infixr 4 _≈₂_ 
infixr 4 _≈ᵣ_
_≈_ : SemType Δ κ → SemType Δ κ → Set
_≈NE_ : NeutralType Δ κ₁ → NeutralType Δ κ₂ → Set
_≈₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
(l₁ , τ₁) ≈₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≈ τ₂
_≈ᵣ_ : (ρ₁ ρ₂ : Row (SemType Δ κ)) → Set 
(n , P) ≈ᵣ (m , Q) = Σ[ pf ∈ (n ≡ m) ] (∀ (i : Fin m) →  
  (substᵢₓ pf P) i ≈₂ Q i)

PointEqual-≈ : ∀ {Δ₁ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (F G : KripkeFunction Δ₁ κ₁ κ₂) → Set
PointEqualNE-≈ : ∀ {Δ₁ : KEnv} {κ₁ : Kind} {κ₂ : Kind}  (F G : KripkeFunctionNE Δ₁ κ₁ κ₂) → Set
Uniform :  ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} → KripkeFunction Δ κ₁ κ₂ → Set
UniformNE :  ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} → KripkeFunctionNE Δ κ₁ κ₂ → Set

convK : ι₁ ≡ ι₂ → Kind → Kind
convK refl k = k 
convNE : κ₁ ≡ κ₂ → NeutralType Δ κ₁ → NeutralType Δ κ₂
convNE refl n = n 

convNE' : {κ₁ : Kind} {κ₂ : Kind} → 
  (pf : ι₁ ≡ ι₂) → 
  convK pf κ₁ ≡ κ₂ → NeutralType Δ κ₁ → NeutralType Δ κ₂
convNE' refl refl n = n

convKripkeNE₁ : ∀ {κ₁ : Kind} {κ₁' : Kind} → 
                (pf : ι₁ ≡ ι₂) → 
                convK pf κ₁ ≡ κ₁' → 
                KripkeFunctionNE Δ κ₁ κ₂ → KripkeFunctionNE Δ κ₁' κ₂
convKripkeNE₁ refl refl f = f

_≈NE_ {_} {κ₁} {κ₂} n₁ n₂ = 
  Σ[ pf ∈ κ₁ ≡ κ₂ ] (tr (NeutralType _) pf n₁ ≡ n₂)
  -- Σ[ pf₁ ∈ ικ₁ ≡ ικ₂ ] 
  -- Σ[ pf₂ ∈ convK pf₁ κ₁ ≡ κ₂ ]
  -- convNE' pf₁ pf₂ n₁ ≡ n₂

infixr 4 _≈kf_
_≈kf_ : ∀ {κ₁ : Kind} {κ₁′ : Kind} → 
        KripkeFunctionNE Δ κ₁ κ₂ → KripkeFunctionNE Δ κ₁′ κ₂ → Set 
_≈kf_ {Δ = Δ} {κ₁ = κ₁} {κ₁′} F G = 
  Σ[ pf ∈ (κ₁ ≡ κ₁′) ]
  ( UniformNE F 
  × UniformNE G 
  × PointEqualNE-≈ (tr (λ x → KripkeFunctionNE Δ x _) pf F) G)

_≈_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
_≈_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
_≈_ {Δ₁} {κ = κ₁ `→ κ₂} F G = 
  Uniform F × Uniform G × PointEqual-≈ {Δ₁} F G 
_≈_ {Δ₁} {κ = R[ κ₂ ]} (_$_ {κ₁} φ₁ n₁) (_$_ {κ₁′} φ₂ n₂) = 
  φ₁ ≈kf φ₂ × n₁ ≈NE n₂
_≈_ {Δ₁} {κ = R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = (l₁ ≈NE l₂) × τ₁ ≈ τ₂
_≈_ {Δ₁} {κ = R[ κ ]} (row (n , P) x₁) (row (m , Q) x₂) = (n , P) ≈ᵣ (m , Q)
_≈_ {Δ₁} {κ = R[ κ ]} (ρ₁ ∖ ρ₂) (ρ₃ ∖ ρ₄) = ρ₁ ≈ ρ₃ × ρ₂ ≈ ρ₄
_≈_ _ _ = ⊥ 
 
PointEqual-≈ {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂} F G = 
  ∀  {Δ₂ : KEnv} (r : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
  V₁ ≈ V₂ → F r V₁ ≈ G r V₂

PointEqualNE-≈ {Δ₁ = Δ₁} {κ₁ = κ₁} {κ₂} F G = 
  ∀  {Δ₂ : KEnv} (r : Renaming Δ₁ Δ₂) (V : NeutralType Δ₂ κ₁) → 
  F r V ≈ G r V

Uniform {Δ = Δ₁} {κ₁ = κ₁} {κ₂} F = 
  ∀ {Δ₂ : KEnv} {Δ₃ : KEnv} (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) (V₁ V₂ : SemType Δ₂ κ₁) →
  V₁ ≈ V₂ → (renSem r₂ (F r₁ V₁)) ≈ (renKripke r₁ F r₂ (renSem r₂ V₂))

UniformNE {Δ = Δ₁} {κ₁ = κ₁} {κ₂} F = 
  ∀ {Δ₂ : KEnv} {Δ₃ : KEnv} (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) (n : NeutralType Δ₂ κ₁) →
  (renSem r₂ (F r₁ n)) ≈ F (r₂ ∘ r₁) (ren r₂ n)

--------------------------------------------------------------------------------
-- Pointwise PER for environments

infixr 4 _≈ₑ_
_≈ₑ_ : {Δ₁ : KEnv} (η₁ η₂ : SemEnv Δ₁ Δ₂) → Set
_≈ₑ_ {Δ₁ = Δ₁} η₁ η₂ = ∀ {κ : Kind} (x : TVar Δ₁ κ) → (η₁ x) ≈ (η₂ x)

-- extension
extend-≈ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv}
             {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
             η₁ ≈ₑ η₂ → 
             {κ : Kind} → 
             {V₁ V₂ : SemType Δ₂ κ} → 
             V₁ ≈ V₂ → 
             (extende η₁ V₁) ≈ₑ (extende η₂ V₂)
extend-≈ p q Z = q
extend-≈ p q (S v) = p v


--------------------------------------------------------------------------------
-- Semantic equality forms a PER
-- - Kind of reflexive (as not all SemTypes satisfy Uniformity.)
-- - symmetric
-- - transitive

refl-≈ˡ : ∀ {Δ : KEnv} {κ : Kind} {V₁ V₂ : SemType Δ κ}     → V₁ ≈ V₂ → V₁ ≈ V₁
refl-≈ʳ : ∀ {Δ : KEnv} {κ : Kind} {V₁ V₂ : SemType Δ κ}     → V₁ ≈ V₂ → V₂ ≈ V₂
sym-≈ : ∀ {Δ : KEnv} {κ : Kind} {τ₁ τ₂ : SemType Δ κ}      → τ₁ ≈ τ₂ → τ₂ ≈ τ₁
trans-≈ : ∀ {Δ : KEnv} {κ : Kind} {τ₁ τ₂ τ₃ : SemType Δ κ} → τ₁ ≈ τ₂ → τ₂ ≈ τ₃ → τ₁ ≈ τ₃
trans-≈ᵣ : ∀ {Δ : KEnv} {κ : Kind} {τ₁ τ₂ τ₃ : Row (SemType Δ κ)} → τ₁ ≈ᵣ τ₂ → τ₂ ≈ᵣ τ₃ → τ₁ ≈ᵣ τ₃

sym-≈ {κ = ★}  refl = refl
sym-≈ {κ = L}  refl = refl
sym-≈ {κ = κ `→ κ₁} 
  {F} {G} 
  (Unif-F , (Unif-G , Ext)) = 
     Unif-G ,  Unif-F , (λ {Δ₂} ρ {V₁} {V₂} z → sym-≈ (Ext ρ (sym-≈ z)))
sym-≈ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} ((refl , refl) , rel) = (refl , refl) , (sym-≈ rel)
sym-≈ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} (refl , eq-ρ) =
  refl , 
  (λ i → (sym (eq-ρ i .fst)) , (sym-≈ (eq-ρ i .snd)))
sym-≈ {κ = R[ κ ]} {ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} (rel₁ , rel₂) = (sym-≈ rel₁) , (sym-≈ rel₂)
sym-≈ {κ = R[ κ ]} {φ₁ $ n₁} {φ₂ $ n₂} ((refl , Unif-φ₁ , Unif-φ₂ , Ext) , (refl , n-eq)) = (refl , Unif-φ₂ , Unif-φ₁ , (λ r v → sym-≈ (Ext r v)) ) , refl , sym n-eq
refl-≈ˡ q = trans-≈ q (sym-≈ q)
refl-≈ʳ q = refl-≈ˡ (sym-≈ q)

trans-≈ {κ = ★} q₁ q₂ = trans q₁ q₂
trans-≈ {κ = L} q₁ q₂ = trans q₁ q₂
trans-≈ {κ = κ₁ `→ κ₂} {F} {G} {H} 
  (unif-F , unif-G , Ext-F-G) (unif-G' , unif-H , Ext-G-H) = 
    unif-F , 
    unif-H , 
    λ ρ q → trans-≈ (Ext-F-G ρ q) (Ext-G-H ρ (refl-≈ˡ (sym-≈ q)))
trans-≈ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} {l₃ ▹ τ₃} ((refl , eq-l₁) , rel-τ₁) ((refl , eq-l₂) , rel-τ₂) = (refl , trans eq-l₁ eq-l₂) , trans-≈ rel-τ₁ rel-τ₂
trans-≈ {κ = R[ κ ]} {row (n , P) _} {row (m , Q) _} {row (o , R) _} (refl , rel₁) (refl , rel₂) = 
  refl , λ { i → trans (rel₁ i .fst) (rel₂ i .fst) , trans-≈ (rel₁ i .snd) (rel₂ i .snd) }
trans-≈ {κ = R[ κ ]} {ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} {ρ₆ ∖ ρ₅} (rel₁ , rel₂) (rel₃ , rel₄) = (trans-≈ rel₁ rel₃) , (trans-≈ rel₂ rel₄)
trans-≈ {κ = R[ κ ]} {φ₁ $ n₁} {φ₂ $ n₂} {φ₃ $ n₃} 
  ((refl , Unif-φ₁ , Unif-φ₂ , Ext₁) , (refl , refl)) 
  ((refl , _ , Unif-φ₃ , Ext₂) , (refl , refl)) = (refl , Unif-φ₁ , Unif-φ₃ , (λ r v → trans-≈ (Ext₁ r v) (Ext₂ r v))) , (refl , refl) 

trans-≈ᵣ {τ₁ = (n , P)} {τ₂ = (m , Q)} {τ₃ = (j , K)} (refl , rel₁) (refl , rel₂) = refl , (λ { i → trans (rel₁ i .fst) (rel₂ i .fst)  , trans-≈ (rel₁ i .snd) (rel₂ i .snd) })

--------------------------------------------------------------------------------
-- Pointwise extensionality (accordingly) forms a PER

refl-Extₗ : ∀ {κ₁ : Kind} {κ₂ : Kind} 
            {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≈ F G → PointEqual-≈ F F
refl-Extₗ Ext ρ q = trans-≈ (Ext ρ q) (sym-≈ (Ext ρ (refl-≈ˡ (sym-≈ q))))

sym-Ext : ∀ {κ₁ : Kind} {κ₂ : Kind} 
            {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≈ F G → PointEqual-≈ G F
sym-Ext Ext ρ q = trans-≈ (refl-≈ˡ (sym-≈ (Ext ρ (sym-≈ q)))) (sym-≈ (Ext ρ (sym-≈ q)))

refl-Extᵣ : ∀ {κ₁ : Kind} {κ₂ : Kind} 
              {F G : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≈ F G → PointEqual-≈ G G
refl-Extᵣ Ext ρ q = refl-Extₗ (sym-Ext Ext) ρ q

trans-Ext : ∀ {κ₁ : Kind} {κ₂ : Kind} → 
              {F G H : KripkeFunction Δ₁ κ₁ κ₂} → PointEqual-≈ F G → PointEqual-≈ G H → PointEqual-≈ F H
trans-Ext Ext-FG Ext-GH ρ q = trans-≈ (Ext-FG ρ q) (trans-≈ (Ext-GH ρ (sym-≈ q)) (refl-Extᵣ Ext-GH ρ q))

-- --------------------------------------------------------------------------------
-- Reification of semantic equality and reflection of propositional equality
-- N.b. other definitions necessarily mutually recursive.

reflect-≈  : ∀ {Δ : KEnv} {κ : Kind} → 
               {τ₁ τ₂ : NeutralType Δ κ} → τ₁ ≡ τ₂ → reflect τ₁ ≈ reflect τ₂
reify-≈    : ∀ {Δ : KEnv} {κ : Kind} → 
               {V₁ V₂ : SemType Δ κ} → V₁ ≈ V₂ → reify V₁ ≡ reify V₂ 
reify-≈ᵣ : ∀ {Δ : KEnv} {κ : Kind} 
               {n} (P Q : Fin n → Label × SemType Δ κ) →  
               (∀ (i : Fin n) → P i ≈₂ Q i) → 
               reifyRow (n , P) ≡ reifyRow (n , Q)
↻-ren-reflect  : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
                 (r : Renaming Δ₁ Δ₂) (τ : NeutralType Δ₁ κ) → 
                 (renSem r (reflect τ)) ≈ (reflect (ren r τ))
↻-ren-reify-∖ : ∀ {Δ₁ : KEnv} {Δ₁ : KEnv} {κ : Kind} → 
                (r : Renaming Δ₁ Δ₂) {V₂ V₁ V₄ V₃ : SemType Δ₁ R[ κ ]} → 
                V₂ ≈ V₄ → V₁ ≈ V₃ → 
                {nr₁ : NotRowLiteral V₂ or NotRowLiteral V₁} → 
                {nr₂ : NotRowLiteral V₄ or NotRowLiteral V₃} → 
                ren r (reify ((V₂ ∖ V₁) {nr₁})) ≡ reify (renSem r ((V₄ ∖ V₃) {nr₂}))

↻-ren-reify : ∀ {Δ₁ : KEnv} {Δ₁ : KEnv} {κ : Kind}
                (r : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                V₁ ≈ V₂ →  ren r (reify V₁) ≡ reify (renSem r V₂)

↻-ren-reifyRow : ∀ {Δ₁ : KEnv} {Δ₁ : KEnv} {κ : Kind}
                   {n} (P Q : Fin n → Label × SemType Δ₁ κ) →  
                        (ρ : Renaming Δ₁ Δ₂) → 
                        (∀ (i : Fin n) → P i ≈₂ Q i) → 
                        ren ρ (reifyRow (n , P)) ≡ reifyRow (n , λ i → map₂ (renSem ρ) (Q i)) 

--------------------------------------------------------------------------------
-- reflect-≈ asserts that well kinded neutral types are in the relation

reflect-≈ {κ = ★} refl = refl
reflect-≈ {κ = L} refl = refl
reflect-≈ {κ = κ₁ `→ κ₂} {f} refl = Unif-f , Unif-f , PE-f
  where
    Unif-f : Uniform (λ ρ v → reflect (ren ρ f · reify v))
    Unif-f {Δ₂ = Δ₂} ρ₁ ρ₂ V₁ V₂ q =
      trans-≈ 
        (↻-ren-reflect ρ₂ (ren ρ₁ f · reify V₁)) 
        (reflect-≈ (cong₂ _·_ (sym (renₜNE-comp ρ₁ ρ₂ f)) 
        (↻-ren-reify {Δ₁ = Δ₂} ρ₂ q)))


    PE-f : PointEqual-≈ (λ ρ v → reflect (ren ρ f · reify v)) (λ ρ v → reflect (ren ρ f · reify v))
    PE-f ρ v = reflect-≈ (cong₂ _·_ refl (reify-≈ {κ = κ₁} v))
reflect-≈ {κ = R[ κ ]} {τ₁ = τ₁} refl = 
  (refl , (λ _ → ↻-ren-reflect) , (λ _ → ↻-ren-reflect) , (λ r V → reflect-≈ refl)) , 
  (refl , refl)

--------------------------------------------------------------------------------
-- reify-≈ asserts that related semantic types reify to the same normal form.

reify-≈ {κ = ★}  sem-eq = sem-eq
reify-≈ {κ = L} sem-eq = sem-eq
reify-≈ {κ = κ₁ `→ κ₂} {F} {G}
  ( unif-F , ( unif-G , ext ) ) = ap `λ (reify-≈  (ext S (reflect-≈ {κ = κ₁} refl)))
reify-≈ {κ = R[ κ ]} {l₁ ▹ τ₁} {l₂ ▹ τ₂} ((refl , refl) , rel) = (cong₂ _▹ₙ_ refl (reify-≈ rel))
reify-≈ {κ = R[ κ ]} {row (zero , P) _} {row (_ , Q) _} (refl , eq) = refl
reify-≈ {κ = R[ κ ]} {row (suc n , P) _} {row (_ , Q) _} (refl , eq) = 
  cong-⦅ (reify-≈ᵣ {n = suc n} P Q λ i → eq i) ⦆nf
reify-≈ {κ = R[ κ ]} {a@(φ₁ $ n₁) ∖ V₂} {b@(φ₂ $ n₂) ∖ V₃} (rel₁@((refl , _) , (refl , _)) , rel₂) = 
  cong-∖ (reify-≈ {V₁ = a} {V₂ = b} rel₁) (reify-≈ rel₂)

reify-≈ {κ = R[ κ ]} {(x₁ ▹ x₂) ∖ ρ₁} {(x₃ ▹ x₄) ∖ ρ₃} (((refl , refl) , rel₁) , rel₂) = 
  cong-∖ (ap (x₁ ▹ₙ_) (reify-≈ rel₁)) (reify-≈ rel₂)
reify-≈ {κ = R[ κ ]} {row (n , P) x₁ ∖ (x₃ ▹ x₄)} {row (m , Q) x₂ ∖ (x₅ ▹ x₆)} ((refl , rel₁) , (refl , refl) , rel₂) = 
 cong-∖ (cong-⦅ reify-≈ᵣ P Q rel₁  ⦆nf) (ap (x₃ ▹ₙ_) (reify-≈ rel₂))
reify-≈ {κ = R[ κ ]} {row ρ x₁ ∖ row ρ₁ x₃} {(row ρ₂ x₂ ∖ row ρ₃ x₄) {left ()}} (rel₁ , rel₂)
reify-≈ {κ = R[ κ ]} {row ρ x₁ ∖ row ρ₁ x₃} {(row ρ₂ x₂ ∖ row ρ₃ x₄) {right ()}} (rel₁ , rel₂)
reify-≈ {κ = R[ κ ]} {row (n , P) x₁ ∖ (ρ₁ ∖ ρ₃)} {row (n , Q) x₂ ∖ (ρ₄ ∖ ρ₅)} ((refl , rel₁) , rel₂) = cong-∖ (cong-⦅ reify-≈ᵣ P Q rel₁ ⦆nf) (reify-≈ {V₁ = ρ₁ ∖ ρ₃} {V₂ = ρ₄ ∖ ρ₅} rel₂)
reify-≈ {κ = R[ κ ]} {row (n , P) x₁ ∖ (φ₁ $ n₁)} {row (n' , Q) x₂ ∖ (φ₂ $ n₂)} ((refl , rel) , rel') = cong-∖ (cong-⦅ reify-≈ᵣ P Q rel ⦆nf) (reify-≈ {κ = R[ κ ]} {φ₁ $ n₁} {φ₂ $ n₂} rel')
reify-≈ {κ = R[ κ ]} {(ρ₂ ∖ ρ₄) ∖ ρ₁} {(ρ₅ ∖ ρ₆) ∖ ρ₃} (rel₁ , rel₂) = cong-∖ (reify-≈ {V₁ = ρ₂ ∖ ρ₄} {ρ₅ ∖ ρ₆} rel₁) (reify-≈ rel₂)
reify-≈ {κ = R[ κ ]} {φ₁ $ n₁} {φ₂ $ n₂} ((refl , _ , _ , Ext) , (refl , refl)) = 
  ap₂ _$_ (ap `λ (reify-≈ (Ext S (` Z)))) refl

reify-≈ᵣ {n = zero} P Q eq = refl
reify-≈ᵣ {n = suc n} P Q eq = 
  ap₂ _∷_ 
  (cong₂ _,_ (eq fzero .fst) (reify-≈ (eq fzero .snd))) 
  (reify-≈ᵣ {n = n} (P ∘ fsuc) (Q ∘ fsuc) (eq ∘ fsuc))

--------------------------------------------------------------------------------
-- 
-- Renaming commutes with reification.

            
--                renSem ρ 
-- SemType Δ₁ κ -------------> SemType Δ₂ Κ
--  |                          |
--  | reify                    | reify
--  |                          |
--  V                          V 
-- NormalType Δ₁ κ ----------> NormalType Δ₂ κ
--                   ren ρ 

↻-ren-reify-R[κ] : ∀ {Δ₁ : KEnv} (r : Renaming Δ₁ Δ₂) (x y : SemType Δ₁ R[ κ ])  → x ≈ y → ren r (reify x) ≡ reify (renSem r y)
↻-ren-reify-R[κ] {Δ₁ = Δ₁} r (φ₁ $ τ₁) (φ₂ $ τ₂) ((refl , _ , Unif-φ₂ , Ext) , (refl , refl)) = 
  ap₂ _$_ (ap `λ (trans (↻-ren-reify {Δ₁ = Δ₁} (liftₜ r) (Ext S (` Z))) (reify-≈ (Unif-φ₂ S (liftₜ r) (` Z))))) refl
↻-ren-reify-R[κ] {Δ₁ = Δ₁} r (x₁ ▹ x₂) (x₃ ▹ x₄) ((refl , refl) , rel) = (cong₂ (_▹ₙ_) refl (↻-ren-reify {Δ₁ = Δ₁} r rel))
↻-ren-reify-R[κ] {Δ₁ = Δ₁} r (row (n , P) x₁) (row (m , Q) x₂) (refl , i) = (cong-⦅ ↻-ren-reifyRow {Δ₁ = Δ₁} P Q r i ⦆nf)
↻-ren-reify-R[κ] {Δ₁ = Δ₁} r (x₁ ∖ x₂) (y₁ ∖ y₂) (rel₁ , rel₂) = ↻-ren-reify-∖ {Δ₁ = Δ₁} r rel₁ rel₂ 

↻-ren-reify-∖ r {φ $ x₁} {x} {φ₁ $ x₂} {y} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r (φ $ x₁) (φ₁ $ x₂) rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-∖ r a@{x₁ ▹ x₂} {x} b@{x₃ ▹ x₄} {y} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-∖ r {a@(row (n , P) oP)} x@{φ $ x₁} {b@(row (m , Q) oQ)} y@{φ₁ $ x₂} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-∖ r {a@(row (n , P) oP)} x@{x₁ ▹ x₂} {b@(row (m , Q) oQ)} y@{x₃ ▹ x₄} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-∖ r {a@(row (n , P) oP)} {row ρ x₁} {b@(row (m , Q) oQ)} {row ρ₁ x₂} rel₁ rel₂ {left ()}
↻-ren-reify-∖ r {a@(row (n , P) oP)} {row ρ x₁} {b@(row (m , Q) oQ)} {row ρ₁ x₂} rel₁ rel₂ {right ()}
↻-ren-reify-∖ r {a@(row (n , P) oP)} x@{x₁ ∖ x₂} {b@(row (m , Q) oQ)} y@{y₁ ∖ y₂} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)
↻-ren-reify-∖ r a@{ρ₂ ∖ ρ₁} {x} b@{ρ₄ ∖ ρ₃} {y} rel₁ rel₂ = cong-∖ (↻-ren-reify-R[κ] r a b rel₁) (↻-ren-reify-R[κ] r x y rel₂)

↻-ren-reifyRow {n = zero} P Q ρ eq = refl
↻-ren-reifyRow {Δ₁ = Δ₁} {n = suc n} P Q ρ eq = 
  ap₂ _∷_ 
    (cong₂ _,_ (eq fzero .fst) (↻-ren-reify {Δ₁ = Δ₁} ρ (eq fzero .snd))) -- (↻-ren-reify ρ (eq fzero)) 
    (↻-ren-reifyRow {Δ₁ = Δ₁} {n = n} (P ∘ fsuc) (Q ∘ fsuc) ρ (eq ∘ fsuc)) 

↻-ren-reify {κ = ★} r {V₁} {V₂} refl = refl 
↻-ren-reify {κ = L} r {V₁} {V₂} refl = refl
↻-ren-reify {Δ₁ = Δ₁} {Δ₂} {κ = κ₁ `→ κ₂} ρ f@{F} g@{G} q@(Unif-F , Unif-G , Ext) = 
  ap `λ 
    (trans 
      (↻-ren-reify {Δ₁ = Δ₁} (liftₜ ρ) (Ext S (reflect-≈ (refl {x = ` Z})))) 
      (reify-≈ (trans-≈ 
        (Unif-G S (liftₜ ρ) _ _ (reflect-≈ refl)) 
        (refl-Extᵣ Ext (S ∘ ρ) (↻-ren-reflect (liftₜ ρ) (` Z))))))
↻-ren-reify {κ = R[ κ ]} r {V₁} {V₂} rel = ↻-ren-reify-R[κ] r V₁ V₂ rel 

--------------------------------------------------------------------------------
-- Renaming commutes with reflection of neutral types

--             
--            ren ρ 
-- Type Δ₁ κ -------------> Type Δ₂ κ 
--  |                        |
--  | reflect              | reflect
--  |                        |
--  V                        V 
-- SemType Δ₁ κ ----------> SemType Δ₂ κ
--               renSem ρ 

↻-ren-reflect {κ = ★} ρ τ = refl
↻-ren-reflect {κ = L} ρ τ = refl
↻-ren-reflect {Δ₁ = Δ₁} {κ = κ `→ κ₁} ρ τ = 
  (λ ρ₁ ρ₂ V₁ V₂ x → 
    trans-≈ 
    (↻-ren-reflect ρ₂ (ren (λ x₁ → ρ₁ (ρ x₁)) τ · reify V₁)) 
    (reflect-≈ (cong₂ _·_ (sym (renₜNE-comp (ρ₁ ∘ ρ) ρ₂ τ)) (↻-ren-reify {Δ₁ = Δ₁} ρ₂ x)))) , 
  (λ ρ₁ ρ₂ V₁ V₂ x → 
    trans-≈ 
      (↻-ren-reflect ρ₂ (ren ρ₁ (ren ρ τ) · reify V₁)) 
      (reflect-≈ (cong₂ _·_ (sym (renₜNE-comp ρ₁ ρ₂ (ren ρ τ))) (↻-ren-reify {Δ₁ = Δ₁} ρ₂ x)))) , 
  λ ρ' v → reflect-≈ (cong₂ _·_ (renₜNE-comp ρ ρ' τ) (reify-≈ v))
↻-ren-reflect {κ = R[ κ ]} ρ τ = reflect-≈ {κ = R[ κ ]} refl

--------------------------------------------------------------------------------
-- Functorial actions

renSem-id-≈    : ∀ {Δ₁ : KEnv} {κ : Kind} → 
                   ∀ {V₁ V₂ : SemType Δ₁ κ} → V₁ ≈ V₂  → (renSem id V₁) ≈ V₂
renSem-id-≈ {κ = ★} refl = renₜNF-id _
renSem-id-≈ {κ = L} refl = renₜNF-id _
renSem-id-≈ {κ = κ `→ κ₁} {F} {G} e = e
renSem-id-≈ {κ = R[ κ ]} {(l₁ ▹ τ₁)} {(l₂ ▹ τ₂)} ((refl , refl) , rel) = (refl , renₜNE-id l₁) , renSem-id-≈ rel
renSem-id-≈ {κ = R[ κ ]} {row (n , P) _} {row (n , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-id-≈ (eq i .snd) } -- renSem-id-≈ ∘ eq
renSem-id-≈ {κ = R[ κ ]} {ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} (rel₁ , rel₂) = (renSem-id-≈ rel₁) , (renSem-id-≈ rel₂)
renSem-id-≈ {κ = R[ κ ]} {φ₁ $ n₁} {φ₂ $ n₂} ((refl , Unif-φ₁ , Unif-φ₂ , Ext) , (refl , refl)) = 
  (refl , Unif-φ₁ , Unif-φ₂ , Ext) , (refl , renₜNE-id n₁) -- refl , Ext , Unif-φ₁ , Unif-φ₂ , renₜ-id n₁

renSem-comp-≈  : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} → 
                 (ρ₁ : Renaming Δ₁ Δ₂)(ρ₂ : Renaming Δ₂ Δ₃){V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≈ V₂ → (renSem (ρ₂ ∘ ρ₁) V₁) ≈ (renSem ρ₂ (renSem ρ₁ V₂))
renSem-comp-≈ {κ = ★} ρ₁ ρ₂ refl = renₜNF-comp _ _ _
renSem-comp-≈ {κ = L} ρ₁ ρ₂ refl = renₜNF-comp _ _ _
renSem-comp-≈ {κ = κ `→ κ₁} ρ₁ ρ₂ {F} {G} (Unif-F , Unif-G , Ext) = 
  (λ ρ₃ → Unif-F (ρ₃ ∘ ρ₂ ∘ ρ₁)) ,
  (λ ρ₃ → Unif-G (ρ₃ ∘ ρ₂ ∘ ρ₁)) , 
  (λ ρ₃ → Ext (ρ₃ ∘ ρ₂ ∘ ρ₁))
renSem-comp-≈ {κ = R[ κ ]} ρ₁ ρ₂ {l₁ ▹ τ₁} {l₂ ▹ τ₂} ((refl , refl) , rel) = (refl , (renₜNE-comp ρ₁ ρ₂ l₁)) , (renSem-comp-≈ ρ₁ ρ₂ rel)
renSem-comp-≈ {κ = R[ κ ]} ρ₁ ρ₂ {row (n , P) _} {row (_ , Q) _} (refl , eq) = refl , λ { i → eq i .fst , renSem-comp-≈  ρ₁ ρ₂ (eq i .snd) }
renSem-comp-≈ {κ = R[ κ ]} r₁ r₂ {φ₁ $ n₁} {φ₂ $ n₂} ((refl , Unif-φ₁ , Unif-φ₂ , Ext) , (refl , refl)) = 
  (refl , 
    (λ ρ₁ ρ₂ V → Unif-φ₁ (ρ₁ ∘ r₂ ∘ r₁) ρ₂ V) , 
    (λ ρ₁ ρ₂ V → Unif-φ₂ (ρ₁ ∘ r₂ ∘ r₁) ρ₂ V) , 
    (λ r₃ V → Ext (r₃ ∘ r₂ ∘ r₁) V)) , 
  (refl , renₜNE-comp r₁ r₂ n₁) 
renSem-comp-≈ {κ = R[ κ ]} r₁ r₂ {ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} (rel₁ , rel₂) = (renSem-comp-≈ r₁ r₂ rel₁) , (renSem-comp-≈ r₁ r₂ rel₂)

↻-lift-weaken-≈ₜ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
                     {κ' : Kind} (ρ : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₁ κ} → 
                 V₁ ≈ V₂ → 
                renSem (liftₜ {κ = κ'} ρ) (renSem S V₁) ≈ renSem S (renSem ρ V₂)
↻-lift-weaken-≈ₜ {κ' = κ'} ρ {V₁} {V₂} v = 
  trans-≈ 
    (sym-≈ (renSem-comp-≈ (S {κ₂ = κ'}) (liftₜ ρ) (sym-≈ v))) 
    (renSem-comp-≈ ρ S (refl-≈ʳ v))

--------------------------------------------------------------------------------
-- Alternative definition for reifying semantic row equivalence


--------------------------------------------------------------------------------
-- renaming respects ≈

ren-≈ : ∀ {Δ₁ : KEnv} {κ : Kind} 
        {V₁ V₂ : SemType Δ₁ κ} 
        (ρ : Renaming Δ₁ Δ₂) → 
        V₁ ≈ V₂ → 
        (renSem ρ V₁) ≈ (renSem ρ V₂)
ren-≈ {κ = ★} {V₁ = V₁} {V₂} ρ refl = refl
ren-≈ {κ = L} {V₁ = V₁} {V₂} ρ refl = refl
ren-≈ {κ = κ₁ `→ κ₂} {V₁ = F} {G} ρ₁ (unif-F , unif-G , Ext) = 
  (λ ρ₂ ρ₃ V₁  → unif-F (ρ₂ ∘ ρ₁) ρ₃ V₁) , 
  (λ ρ₂ ρ₃ V₁  → unif-G (ρ₂ ∘ ρ₁) ρ₃ V₁) ,  
  λ ρ₃ q → Ext (ρ₃ ∘ ρ₁) q
ren-≈ {κ = R[ κ ]} {V₁ = (l₁ ▹ τ₁)} {(l₂ ▹ τ₂)} ρ ((refl , refl) , rel) = 
  (refl , refl) , (ren-≈ ρ rel)
ren-≈ {κ = R[ κ ]} {V₁ = row _ _ } {row _ _} ρ (refl , eq) = 
  refl , λ { i → eq i .fst , ren-≈ ρ (eq i .snd) }
ren-≈ {κ = R[ κ ]} {V₁ = ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} r (rel₁ , rel₂) = (ren-≈ r rel₁) , (ren-≈ r rel₂)
ren-≈ {κ = R[ κ ]} {V₁ = φ₁ $ n₁} {φ₂ $ n₂} r ((refl , Unif-φ₁ , Unif-φ₂ , Ext ) , (refl , refl)) = 
  (refl ,
  (λ r₁ r₂ v → Unif-φ₁ (r₁ ∘ r) r₂ v) , 
  (λ r₁ r₂ v → Unif-φ₂ (r₁ ∘ r) r₂ v) , 
  (λ r' v → Ext (r' ∘ r) v)) , 
  (refl , refl)

--------------------------------------------------------------------------------
-- Lifted environments are related

idEnv-≈ : _≈ₑ_ {Δ₁ = Δ} idEnv idEnv
idEnv-≈ _ = reflect-≈ refl

lifte-≈ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
             {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
             η₁ ≈ₑ η₂ → 
             (lifte {κ = κ} η₁) ≈ₑ (lifte η₂)
lifte-≈ e = extend-≈ (ren-≈ S ∘ e) (idEnv-≈ Z) 
