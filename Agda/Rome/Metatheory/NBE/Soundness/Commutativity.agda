-- 
module Rome.Metatheory.NBE.Soundness.Commutativity where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Properties.Renaming
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.Properties.Renaming

open import Rome.NormalTypes.NBE.Syntax
open import Rome.NormalTypes.NBE.Renaming
open import Rome.NormalTypes.NBE.Normalization
open import Rome.Metatheory.NBE.Soundness.Relation
open import Rome.Metatheory.NBE.Soundness.Congruence

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with application.

↻-renSem-app : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (r : Renaming Δ₁ Δ₂) {F G : SemType Δ₁ (κ₁ `→ κ₂)} → _≈_ {κ = κ₁ `→ κ₂} F G → 
                {V₁ V₂ : SemType Δ₁ κ₁} → V₁ ≈ V₂ →  
                renSem r (F ⟨·⟩ V₁) ≈ (renSem {κ = κ₁ `→ κ₂} r G ⟨·⟩ renSem r V₂)
↻-renSem-app r {F} {G} (Unif-F , Unif-G , Ext) {V₁} {V₂} v = 
  trans-≈ (Unif-F id r V₁ V₂ v) ((Ext r (ren-≈ r (refl-≈ˡ (sym-≈ v)))))

-- --------------------------------------------------------------------------------
-- -- Renaming commutes with $

↻-renSem-$ : ∀ (r : Renaming Δ₁ Δ₂) 
            {V₁ V₂ : SemType Δ₁ (κ₁ `→ κ₂)} → 
           _≈_ {κ = κ₁ `→ κ₂} V₁ V₂ → 
           {W₁ W₂ : SemType Δ₁ R[ κ₁ ]} → 
            _≈_ {κ = R[ κ₁ ]} W₁ W₂ → 
           _≈_ {κ = R[ κ₂ ]} (renSem {κ = R[ κ₂ ]} r (V₁ ⟨$⟩ W₁)) (renSem {κ = κ₁ `→ κ₂} r V₂ ⟨$⟩ renSem {κ = R[ κ₁ ]} r W₂)
↻-renSem-$ r {V₁} {V₂} v {l₁ ▹ τ₁} {l₁ ▹ τ₂} ((refl , refl) , rel) = (refl , refl) , (↻-renSem-app r v rel)
↻-renSem-$ r {V₁} {V₂} v {row (n , P) _} {row (_ , Q) _} (refl , eq) = refl , λ i → eq i .fst , (↻-renSem-app r v (eq i .snd))
↻-renSem-$ r {V₁} {V₂} v {ρ₂ ∖ ρ₁} {ρ₄ ∖ ρ₃} (rel₁ , rel₂) = (↻-renSem-$ r v rel₁) , (↻-renSem-$ r v rel₂)
↻-renSem-$ r {F} {G} (Unif-F , Unif-G , Ext-FG) {φ₁ $ n₁} {φ₂ $ n₂} ((refl , Unif-φ₁ , Unif-φ₂ , Ext-φ) , (refl , refl)) = 
  (refl ,
  (λ r₁ r₂ n → 
    trans-≈ 
      (Unif-F (r₁ ∘ r) r₂ (φ₁ (r₁ ∘ r) n) (φ₁ (r₁ ∘ r) n) (trans-≈ (Ext-φ (r₁ ∘ r) n) (sym-≈ (Ext-φ (r₁ ∘ r) n)))) 
      (refl-Extₗ Ext-FG _ (Unif-φ₁ _ _ n))) , 
  (λ r₁ r₂ n → 
    trans-≈ 
      (Unif-G (r₁ ∘ r) r₂ (φ₂ (r₁ ∘ r) n) (φ₂ (r₁ ∘ r) n) (trans-≈ (sym-≈ (Ext-φ (r₁ ∘ r) n)) (Ext-φ (r₁ ∘ r) n))) 
      (refl-Extᵣ Ext-FG _ (Unif-φ₂ _ _ n))), 
  (λ r' v → Ext-FG (r' ∘ r) (Ext-φ _ v))) , 
  (refl , refl )
-- --------------------------------------------------------------------------------
-- -- Renaming commutes over complement

↻-renSem-compl : {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} {n m : ℕ} 
                 (r : Renaming Δ₁ Δ₂) → 
                 (A B : Fin n → Label × SemType Δ₁ κ)
                 (C D : Fin m → Label × SemType Δ₁ κ) → 
                 ((i : Fin n) → A i ≈₂ B i) → 
                 ((i : Fin m) → C i ≈₂ D i) → 
                 renRow r (compl A C) ≈ᵣ 
                 compl (map₂ (renSem r) ∘ B) (map₂ (renSem r) ∘ D)
↻-renSem-compl {n = zero} r A B C D i₁ i₂ = refl , (λ ())
↻-renSem-compl {n = suc n} r A B C D i₁ i₂ with
      A fzero .fst ∈Row? C 
    | (B fzero .fst) ∈Row? (map₂ (renSem r) ∘ D)
... | yes p         | yes q  =
  ↻-renSem-compl r (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂
... | yes (j , eq₂) | no q          = 
  ⊥-elim (q (j , (trans (sym (i₁ fzero .fst)) (trans eq₂ (i₂ j .fst)))))
... | no q          | yes (j , eq₂) = ⊥-elim (q (j , trans (i₁ fzero .fst) (trans eq₂ (sym (i₂ j .fst)))))
... | no  p         | no q  with
      (compl (A ∘ fsuc) C) 
    | compl (map₂ (renSem r) ∘ (B ∘ fsuc)) (map₂ (renSem r) ∘ D)
    | (↻-renSem-compl r (A ∘ fsuc) (B ∘ fsuc) C D (i₁ ∘ fsuc) i₂) 
... | n₁ , P | n₂ , Q | refl , ih =  refl , λ { fzero → i₁ fzero .fst  , (ren-≈ r (i₁ fzero .snd)) ; (fsuc i) → ih i }

↻-renSem-∖v : {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} (r : Renaming Δ₁ Δ₂) → 
              {V₁ V₂ W₁ W₂ : Row (SemType Δ₁ κ)} → 
              V₂ ≈ᵣ W₂ → 
              V₁ ≈ᵣ W₁ → 
              renRow r (V₂ ∖v V₁) ≈ᵣ (renRow r W₂ ∖v renRow r W₁)
↻-renSem-∖v r {n , P} {m , Q} {_ , R} {_ , I} (refl , V₂≈) (refl , V₁≈) = ↻-renSem-compl r Q I P R V₂≈ V₁≈

↻-renSem-⟨∖⟩ : {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} (r : Renaming Δ₁ Δ₂) → 
              {V₁ V₂ W₁ W₂ : SemType Δ₁ R[ κ ]} → 
              V₂ ≈ W₂ → 
              V₁ ≈ W₁ → 
              renSem r (V₂ ⟨∖⟩ V₁) ≈ (renSem r W₂ ⟨∖⟩ renSem r W₁)

↻-renSem-⟨∖⟩ r ρ₁@{x₁ ▹ x₂} ρ₂@{x₃ ▹ x₄} ρ₃@{x₅ ▹ x₆} ρ₄@{x₇ ▹ x₈} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{x₁ ▹ x₂} ρ₂@{row _ x₃} ρ₃@{x₄ ▹ x₅} ρ₄@{row _ x₆} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{x₁ ▹ x₂} ρ₂@{(V₂ ∖ V₃) {nr₁}} ρ₃@{x₃ ▹ x₄} ρ₄@{(W₂ ∖ W₃) {nr₂}} rel₁ rel₂ =  ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{x₁ ▹ x₂} ρ₂@{_ $ _} ρ₃@{x₃ ▹ x₄} ρ₄@{_ $ _} rel₁ rel₂ =  ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{row _ x₁} ρ₂@{x₂ ▹ x₃} ρ₃@{row _ x₄} ρ₄@{x₅ ▹ x₆} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r {row ρ x₁} {row ρ₁ x₂} {row ρ₂ x₃} {row ρ₃ x₄} rel₁ rel₂ = ↻-renSem-∖v r rel₁ rel₂
↻-renSem-⟨∖⟩ r ρ₁@{row _ x₁} ρ₂@{V₂ ∖ V₃} ρ₃@{row _ x₂} ρ₄@{W₂ ∖ W₃} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{row _ x₁} ρ₂@{_ $ _} ρ₃@{row _ x₂} ρ₄@{_ $ _} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{V₁ ∖ V₂} ρ₂@{x₁ ▹ x₂} ρ₃@{W₁ ∖ W₂} ρ₄@{x₃ ▹ x₄} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{V₁ ∖ V₂} ρ₂@{row _ x₁} ρ₃@{W₁ ∖ W₂} ρ₄@{row _ x₂} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{V₁ ∖ V₂} ρ₂@{V₃ ∖ V₄} ρ₃@{W₁ ∖ W₂} ρ₄@{W₃ ∖ W₄} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r ρ₁@{V₁ ∖ V₂} ρ₂@{_ $ _} ρ₃@{W₁ ∖ W₂} ρ₄@{_ $ _} rel₁ rel₂ = ren-≈ {V₁ = ρ₂}   {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r {ρ₁@(φ₁ $ n₁)} ρ₂@{φ $ x₁} {ρ₃@(φ₂ $ n₂)} ρ₄@{φ₃ $ x₂} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r {ρ₁@(φ₁ $ n₁)} ρ₂@{x₁ ▹ x₂} {ρ₃@(φ₂ $ n₂)}  ρ₄@{x₃ ▹ x₄} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r {ρ₁@(φ₁ $ n₁)} ρ₂@{row ρ x₁} {ρ₃@(φ₂ $ n₂)} ρ₄@{row _ _} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂
↻-renSem-⟨∖⟩ r {ρ₁@(φ₁ $ n₁)} ρ₂@{_ ∖ _} {ρ₃@(φ₂ $ n₂)}  ρ₄@{_ ∖  _} rel₁ rel₂ = ren-≈ {V₁ = ρ₂} {V₂ = ρ₄} r rel₁ , ren-≈ {V₁ = ρ₁} {V₂ = ρ₃} r rel₂

--------------------------------------------------------------------------------
-- Uniformity of ⟨?⟩

Unif-<?> : ∀ {κ₁ : Kind} (f : SemType Δ R[ κ₁ `→ κ₂ ]) → f ≈ f → 
            Uniform (λ r v → (renSem r f ⟨?⟩ v))
Unif-<?> f q ρ₁ ρ₂ V₁ V₂ v = 
  trans-≈ 
  (↻-renSem-$ ρ₂ 
    (cong-apply (refl-≈ˡ v))
    (ren-≈ ρ₁ q)) 
  (cong-$ 
    (ren-Uniform ρ₂ (Unif-apply (refl-≈ˡ v)) , 
      Unif-apply (ren-≈ ρ₂ (refl-≈ʳ v)) , 
      λ r v' → third v' id ((renSem-comp-≈ ρ₂ r v))) 
    (sym-≈ (renSem-comp-≈ ρ₁ ρ₂ q))) 
    
--------------------------------------------------------------------------------
-- - Renaming commutes with ξ
-- - ξ is congruent w.r.t. semantic equivalence 


Unif-ξ : ∀ {Δ : KEnv} {κ : Kind} (Ξ : Xi) → Uniform {Δ = Δ} {κ₁ = R[ κ ]} {κ₂ = κ} (ξ-Kripke Ξ)
↻-renSem-ξ : ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} (Ξ : Xi) {κ : Kind} (r : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          _≈_ {κ = R[ κ ]} V₁ V₂ → renSem r (ξ Ξ V₁) ≈ ξ Ξ (renSem {κ = R[ κ ]} r V₂) 
cong-ξ : ∀ (Ξ : Xi) {κ : Kind} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≈_ {κ = R[ κ ]} τ₁ τ₂ → ξ Ξ τ₁ ≈ ξ Ξ τ₂

Unif-ξ Ξ r = ↻-renSem-ξ Ξ

Unif-ξ<?> : ∀ {κ₁ : Kind} {κ₂ : Kind} (Ξ : Xi) (f : SemType Δ R[ κ₁ `→ κ₂ ]) → f ≈ f → Uniform (λ r v → ξ Ξ (renSem r f ⟨?⟩ v))
Unif-ξ<?> Ξ f f≈f ρ₂ ρ₃ V₁ V₂ v = 
  trans-≈
    (Unif-ξ Ξ id ρ₃ (renSem ρ₂ f ⟨?⟩ V₁) (renSem ρ₂ f ⟨?⟩ V₁) 
      (cong-$ 
        (Unif-apply (sym-≈ v) , Unif-apply (sym-≈ v) , (λ r v' → third v' id (ren-≈ r (refl-≈ˡ v)))) 
        (ren-≈ ρ₂ f≈f)))
    (cong-ξ Ξ (Unif-<?> f f≈f ρ₂ ρ₃ V₁ V₂  v))

open Xi
↻-renSem-ξ {Δ₁ = Δ₁} Ξ {★} r x y x≈y = 
  trans 
    (Ξ .ren-★ r (reify x)) 
    (ap (Ξ .Ξ★) 
      (trans 
        (↻-ren-reify {Δ₁ = Δ₁} r x≈y) 
        (reify-≈ (ren-≈ r (refl-≈ʳ x≈y)))))
↻-renSem-ξ Ξ {L} r x y x≈y = refl
↻-renSem-ξ Ξ {κ₁ `→ κ₂} r f g f≈g =
  ren-Uniform 
    {F = λ ρ₁ v → ξ Ξ (renSem ρ₁ f ⟨?⟩  v)} 
    r 
    (Unif-ξ<?> Ξ f (refl-≈ˡ f≈g)) , 
  Unif-ξ<?> Ξ (renSem r g) (ren-≈ r (refl-≈ʳ f≈g)) , 
  λ r' v → cong-ξ Ξ 
    (cong-$ 
      (cong-apply v) 
      (renSem-comp-≈ r r' f≈g))
↻-renSem-ξ Ξ {R[ κ ]} r x y x≈y = ↻-renSem-$ r (Unif-ξ Ξ , Unif-ξ Ξ , λ r → cong-ξ Ξ) x≈y

cong-ξ Ξ {κ = ★} {x} {y} x≈y = ap (Ξ .Ξ★) (reify-≈ x≈y)
cong-ξ Ξ {κ = L} {x} {y} x≈y = refl
cong-ξ Ξ {κ = κ₁ `→ κ₂} {f} {g} f≈g  =
  Unif-ξ<?> Ξ f (refl-≈ˡ f≈g)  , 
  Unif-ξ<?> Ξ g (refl-≈ʳ f≈g) , 
  λ r {V₁} {V₂} v → cong-ξ Ξ 
    (cong-$ 
      (cong-apply v) 
      (ren-≈ r f≈g))
cong-ξ Ξ {κ = R[ κ ]} {x} {y} x≈y = cong-$ (Unif-ξ Ξ , Unif-ξ Ξ , (λ r → cong-ξ Ξ {_})) x≈y

---------------------------------------
-- instantiations for Π

↻-renSem-Π :  ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} (r : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≈ V₂ → renSem r (⟨Π⟩ V₁) ≈ ⟨Π⟩ (renSem {κ = R[ κ ]} r V₂) 
↻-renSem-Π = ↻-renSem-ξ Π-rec

cong-⟨Π⟩ : ∀ {Δ : KEnv} {κ : Kind} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≈_ {κ = R[ κ ]} τ₁ τ₂ → ⟨Π⟩ τ₁ ≈ ⟨Π⟩ τ₂
cong-⟨Π⟩ = cong-ξ Π-rec

Unif-Π : ∀ {Δ : KEnv} {κ : Kind} → Uniform (Π-Kripke {Δ = Δ} {κ = κ})
Unif-Π ρ₁ = ↻-renSem-Π

---------------------------------------
-- instantiations for σ

↻-renSem-Σ :  ∀ {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} (r : Renaming Δ₁ Δ₂) → (V₁ V₂ : SemType Δ₁ R[ κ ]) → 
          V₁ ≈ V₂ → renSem r (⟨Σ⟩ V₁) ≈ ⟨Σ⟩ (renSem {κ = R[ κ ]} r V₂) 
↻-renSem-Σ = ↻-renSem-ξ Σ-rec

cong-⟨Σ⟩ : ∀ {Δ : KEnv} {κ : Kind} {τ₁ τ₂ : SemType Δ R[ κ ]} → _≈_ {κ = R[ κ ]} τ₁ τ₂ → ⟨Σ⟩ τ₁ ≈ ⟨Σ⟩ τ₂
cong-⟨Σ⟩ = cong-ξ Σ-rec

Unif-Σ : ∀ {Δ : KEnv} {κ : Kind} → Uniform (Σ-Kripke {Δ = Δ} {κ = κ})
Unif-Σ ρ₁ = ↻-renSem-Σ

--------------------------------------------------------------------------------
-- semantic renaming commutes with evaluation
--
--            eval in (renSem r ∘ η₂)
--  Type Δ₁ κ  ------
--  |                \            
--  | ⟦ in ⟧ₜ η₁       \          
--  |                    \          
--  V                      V        
-- NormalType Δ₂ κ ----------> SemType Δ₂ κ
--                  renSem r 


↻-renSem-eval : ∀ {Δ₂ : KEnv} {Δ₃ : KEnv} {κ : Kind} 
                  (r : Renaming Δ₂ Δ₃) 
                  (τ : Type Δ₁ κ) → 
                  {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
                  (Ρ : η₁ ≈ₑ η₂) → 
                  (renSem r (⟦ τ ⟧ₜ η₁)) ≈ ⟦ τ ⟧ₜ (renSem r ∘ η₂)
↻-renSem-eval-pred : (r : Renaming Δ₂ Δ₃) 
                     (π : Pred (Type Δ₁ R[ κ ])) → 
                     {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
                     (Ρ : η₁ ≈ₑ η₂) → 
                     (ren r (⟦ π ⟧ₚ η₁)) ≡ ⟦ π ⟧ₚ (renSem r ∘ η₂)
↻-renSem-evalRow : {Δ₂ : KEnv} {Δ₃ : KEnv} {κ : Kind} 
                    (r : Renaming Δ₂ Δ₃) 
                    (ρ : RowLiteral (Type Δ₁ κ)) → 
                    {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
                    (Ρ : η₁ ≈ₑ η₂) → 
                    renRow r (⟦ ρ ⟧ᵣ η₁) ≈ᵣ ⟦ ρ ⟧ᵣ (renSem r ∘ η₂)  

idext : {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} 
        {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
        η₁ ≈ₑ η₂ → 
        (τ : Type Δ₁ κ) →
        ⟦ τ ⟧ₜ η₁ ≈ ⟦ τ ⟧ₜ η₂
idext-pred : {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
             η₁ ≈ₑ η₂ → 
             (π : Pred (Type Δ₁ R[ κ ])) →
             ⟦ π ⟧ₚ η₁ ≡ ⟦ π ⟧ₚ η₂

idext-row :  {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind}
             {η₁ η₂ : SemEnv Δ₁ Δ₂} → (e : η₁ ≈ₑ η₂) → 
             (ρ : RowLiteral (Type Δ₁ κ)) → 
             (⟦ ρ ⟧ᵣ η₁) ≈ᵣ ⟦ ρ ⟧ᵣ η₂

↻-renSem-eval-pred {Δ₁ = Δ₁} ρ (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} P rewrite 
    ↻-ren-reify {Δ₁ = Δ₁} ρ (idext (refl-≈ˡ ∘ P) ρ₁) | reify-≈ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify {Δ₁ = Δ₁} ρ (idext (refl-≈ˡ ∘ P) ρ₂) | reify-≈ (↻-renSem-eval ρ ρ₂ P)  
  | ↻-ren-reify {Δ₁ = Δ₁} ρ (idext (refl-≈ˡ ∘ P) ρ₃) | reify-≈ (↻-renSem-eval ρ ρ₃ P)  = refl
↻-renSem-eval-pred {Δ₁ = Δ₁} ρ (ρ₁ ≲ ρ₂) P rewrite
    ↻-ren-reify {Δ₁ = Δ₁} ρ (idext (refl-≈ˡ ∘ P) ρ₁) | reify-≈ (↻-renSem-eval ρ ρ₁ P)
  | ↻-ren-reify {Δ₁ = Δ₁} ρ (idext (refl-≈ˡ ∘ P) ρ₂) | reify-≈ (↻-renSem-eval ρ ρ₂ P)  = refl


↻-renSem-eval {κ = κ} r (` α) e = ren-≈ r (e α)
↻-renSem-eval ρ₁ (`λ τ) {η₁} {η₂} e = 
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≈ 
      (↻-renSem-eval ρ₃ τ (extend-≈ {η₂ = renSem (ρ₂ ∘ ρ₁) ∘ η₂}  (λ x → ren-≈ (ρ₂ ∘ ρ₁) (e x)) v)) 
      (idext (λ { Z → ren-≈ ρ₃ (refl-≈ˡ (sym-≈ v)) ; (S x) → sym-≈ (renSem-comp-≈ (ρ₂ ∘ ρ₁) ρ₃ (e x)) }) τ)) ,
  (λ ρ₂ ρ₃ V₁ V₂ v → 
    trans-≈ 
      (↻-renSem-eval ρ₃ τ (extend-≈ {η₂ = renSem ρ₂ ∘ (renSem ρ₁ ∘ η₂)}  (λ x → ren-≈ ρ₂ (sym-≈ (ren-≈ ρ₁ (refl-≈ˡ (sym-≈ (e x)))))) v)) 
      (idext 
        (λ {     Z → ren-≈ ρ₃ (refl-≈ˡ (sym-≈ v)) 
           ; (S x) → sym-≈ (renSem-comp-≈ ρ₂ ρ₃ (ren-≈ ρ₁ (refl-≈ˡ (sym-≈ (e x))))) }) τ)) ,
  λ ρ₂ q → idext (λ { Z → q ; (S x) → renSem-comp-≈ ρ₁ ρ₂ (e x) }) τ
↻-renSem-eval {κ = .κ₂} r (_·_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {η₁} {η₂} e = 
  trans-≈
    (↻-renSem-app r (idext (refl-≈ˡ ∘ e) τ₁) (idext (refl-≈ˡ ∘ e) τ₂))     
    (cong-App (↻-renSem-eval r τ₁ e) (↻-renSem-eval r τ₂ e))
↻-renSem-eval r (τ₁ `→ τ₂) e = ap₂ _`→_ (↻-renSem-eval r τ₁ e) (↻-renSem-eval r τ₂ e)
↻-renSem-eval r (`∀ τ) {η₁} {η₂} e = ap (`∀) 
  (trans 
    (↻-renSem-eval (liftₜ r) τ {lifte η₁} {lifte η₂} 
      (extend-≈ (ren-≈ S ∘ e) (reflect-≈ refl))) 
    (idext E τ))
  where
    E : (renSem (liftₜ r) ∘ lifte {κ = κ} η₂) ≈ₑ (lifte (renSem r ∘ η₂))
    E Z = ↻-ren-reflect (liftₜ r) (` Z)
    E (S x) = 
      trans-≈ 
        (sym-≈ (renSem-comp-≈ S (liftₜ r) (refl-≈ˡ (sym-≈ (e x))))) 
        (renSem-comp-≈ r S (refl-≈ʳ (e x)))
↻-renSem-eval {Δ₁ = Δ₁} r (μ τ) {η₁} {η₂} e = ap μ 
  (trans 
    (↻-ren-reify {Δ₁ = Δ₁} r (idext e τ)) 
    (reify-≈ (↻-renSem-eval r τ (refl-≈ʳ ∘ e))))
↻-renSem-eval r (π ⇒ τ) e = ap₂ _⇒_ (↻-renSem-eval-pred r π e) (↻-renSem-eval r τ e)
↻-renSem-eval r (lab l) e = refl
↻-renSem-eval r Π e = Unif-Π , Unif-Π , (λ ρ₁ x → cong-⟨Π⟩ x) 
↻-renSem-eval r Σ e = Unif-Σ , Unif-Σ , (λ ρ₁ x → cong-⟨Σ⟩ x) 
↻-renSem-eval r (τ₁ $ τ₂) {η₁} {η₂} e = 
  trans-≈ 
    (↻-renSem-$ r (idext e τ₁) (idext e τ₂)) 
    (cong-$ (↻-renSem-eval r τ₁ (refl-≈ʳ ∘ e)) (↻-renSem-eval r τ₂ (refl-≈ʳ ∘ e)))
↻-renSem-eval r (⦅ ρ ⦆ ω) {η₁} {η₂} e = ↻-renSem-evalRow r ρ e
↻-renSem-eval r (ρ₂ ∖ ρ₁) {η₁} {η₂} e =
  trans-≈ 
    (↻-renSem-⟨∖⟩ r (idext e ρ₂) (idext e ρ₁)) 
    (cong-⟨∖⟩ (↻-renSem-eval r ρ₂ (refl-≈ʳ ∘ e)) (↻-renSem-eval r ρ₁ (refl-≈ʳ ∘ e)))
↻-renSem-eval r (l ▹ τ) {η₁} e with ⟦ l ⟧ₜ η₁ | ↻-renSem-eval r l e 
... | ne x | ih rewrite (sym ih)   = (refl , refl) , (↻-renSem-eval r τ e) 
... | lab l' | ih rewrite (sym ih) = refl , (λ { fzero → refl , (↻-renSem-eval r τ e) })

↻-renSem-evalRow r [] e = refl , (λ { () })
↻-renSem-evalRow r (x ∷ ρ) {η₁} e with ⟦ ρ ⟧ᵣ η₁ | ↻-renSem-evalRow r ρ e
... | (n , P) | refl , eq = 
  refl  , 
  λ { fzero → refl , (↻-renSem-eval r (x . snd) e) ; (fsuc i) → eq i }


-- ------------------------------------------------------------------------------
-- idext 
--   Evaluating types in related environments yields related semantic types.


idext-pred e (ρ₁ · ρ₂ ~ ρ₃) rewrite 
    sym (reify-≈ (idext e ρ₁))
  | sym (reify-≈ (idext e ρ₂)) 
  | sym (reify-≈ (idext e ρ₃))  = refl
idext-pred e (ρ₁ ≲ ρ₂) rewrite 
    sym (reify-≈ (idext e ρ₁))
  | sym (reify-≈ (idext e ρ₂))  = refl

idext {κ = ★} e (` x) = e x
idext {κ = L} e (` x) = e x
idext {κ = κ `→ κ₁} e (` x) = e x
idext {κ = R[ κ ]} e (` x) = e x
idext {κ = κ} e (`λ τ) = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≈ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≈ (ren-≈ ρ₁ ∘ refl-≈ˡ ∘ e) q))
      (idext 
        (λ { Z → ren-≈ ρ₂ (refl-≈ˡ (sym-≈ q))
           ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (refl-≈ˡ (e x))) }) τ)) ,
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≈ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≈ (ren-≈ ρ₁ ∘ refl-≈ˡ ∘ sym-≈ ∘ e) q))
      (idext 
        (λ { Z → ren-≈ ρ₂ (refl-≈ˡ (sym-≈ q))
           ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (refl-≈ʳ (e x))) }) τ)) , 
  λ r q → idext (extend-≈ (ren-≈ r ∘ e) q) τ
idext {κ = κ} e (τ₁ · τ₂) = snd (snd (idext e τ₁)) id (idext e τ₂)
idext {κ = κ} e (τ₁ `→ τ₂) = ap₂ _`→_ (idext e τ₁) (idext e τ₂)
idext {κ = κ} e (π ⇒ τ) = ap₂ _⇒_ (idext-pred e π) (idext e τ)
idext {κ = κ} e (`∀ τ) = ap (`∀) (idext (extend-≈ (ren-≈ S ∘ e) (reflect-≈ refl)) τ)
idext {κ = ★} {η₁} {η₂} e (μ τ) with ⟦ τ ⟧ₜ η₁ | ⟦ τ ⟧ₜ η₂ | idext e τ
... | F | G | (Unif-F , Unif-G , Ext) = ap μ (ap `λ (Ext S refl))
idext {κ = κ} e (lab x) = refl
idext {κ = R[ κ₁ ] `→ κ₁} {η₁} {η₂} e Π = 
  Unif-Π , 
  Unif-Π , 
  λ r x → cong-⟨Π⟩ x 
idext {κ = κ} e Σ =
  Unif-Σ , 
  Unif-Σ , 
  λ r x → cong-⟨Σ⟩ x 
idext {κ = κ} e (_$_ {κ₁} {κ₂} τ₁ τ₂) = cong-$ (idext e τ₁) (idext e τ₂)
idext e (ρ₂ ∖ ρ₁) = cong-⟨∖⟩ (idext e ρ₂) (idext e ρ₁)
idext e (⦅ xs ⦆ _) = idext-row e xs
idext {η₁ = η₁} {η₂} e (l ▹ τ) with ⟦ l ⟧ₜ η₁ | idext e l
... | ne x | ih rewrite (sym ih) = (refl , refl) , (idext e τ)
... | lab l' | ih rewrite (sym ih) = refl , (λ { fzero → refl , (idext e τ) })

idext-row e [] = refl , (λ { () })
idext-row {η₁ = η₁} e (x ∷ ρ)  with ⟦ ρ ⟧ᵣ η₁ | idext-row e ρ 
... | n , P | refl , eq = refl , (λ { fzero → refl , (idext e (x .snd)) ; (fsuc i) → eq i })

--------------------------------------------------------------------------------
-- Syntactic renaming commutes with evaluation
-- 

--            eval in (η₂ ∘ r)
--  Type Δ₁ κ  -------
--  |                 \            
--  | ren r            \          
--  |                   \          
--  V                    V        
-- Type Δ₂ κ ----------> SemType Δ₃ κ
--          ⟦ in ⟧ₜ η₁ 

↻-renₜ-eval : ∀ {Δ₃ : KEnv} {κ : Kind} 
                  (r : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ) → {η₁ η₂ : SemEnv Δ₂ Δ₃} → 
                  (e : η₁ ≈ₑ η₂) → 
                  ⟦ (renₜ r τ) ⟧ₜ η₁ ≈ ⟦ τ ⟧ₜ (η₂ ∘ r)
↻-renₜ-eval-pred : (r : Renaming Δ₁ Δ₂) 
                   (π : Pred (Type Δ₁ R[ κ ])) → 
                   {η₁ η₂ : SemEnv Δ₂ Δ₃} → 
                  (e : η₁ ≈ₑ η₂) → 
                  ⟦ (ren r π) ⟧ₚ η₁ ≡ ⟦ π ⟧ₚ (η₂ ∘ r)
↻-renₜ-evalRow : ∀ {Δ₃ : KEnv} {κ : Kind} 
                  (r : Renaming Δ₁ Δ₂) 
                  (ρ : RowLiteral (Type Δ₁ κ)) → 
                  {η₁ η₂ : SemEnv Δ₂ Δ₃} → 
                  (e : η₁ ≈ₑ η₂) → 
                  ⟦ ren r ρ ⟧ᵣ η₁ ≈ᵣ ⟦ ρ ⟧ᵣ (η₂ ∘ r)

↻-renₜ-eval-pred r (ρ₁ · ρ₂ ~ ρ₃) {η₁} {η₂} e rewrite
    reify-≈ (↻-renₜ-eval r ρ₁ e)
  | reify-≈ (↻-renₜ-eval r ρ₂ e)  
  | reify-≈ (↻-renₜ-eval r ρ₃ e)  = refl
↻-renₜ-eval-pred r (ρ₁ ≲ ρ₂) e rewrite
    reify-≈ (↻-renₜ-eval r ρ₁ e)
  | reify-≈ (↻-renₜ-eval r ρ₂ e)  = refl

↻-renₜ-eval r (` α) {η₁} {η₂} e = e (r α)
↻-renₜ-eval r (`λ τ) {η₁} {η₂} e = 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
  trans-≈ 
    (↻-renSem-eval ρ₂ 
      (renₜ (liftₜ r) τ) 
      (extend-≈ (ren-≈ ρ₁ ∘ refl-≈ˡ ∘ e) q)) 
    (idext 
      (λ { Z → ren-≈ ρ₂ (refl-≈ʳ q) 
         ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (refl-≈ˡ (e x))) }) 
      (renₜ (liftₜ r) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≈ 
      (↻-renSem-eval ρ₂ τ (extend-≈ (ren-≈ ρ₁ ∘ refl-≈ʳ ∘ e ∘ r) q)) 
      (idext 
        (λ { Z     → ren-≈ ρ₂ (refl-≈ʳ q) 
           ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (refl-≈ʳ (e (r x)))) }) 
        τ)) , 
  λ r' q → 
    trans-≈ 
      (↻-renₜ-eval (liftₜ r) τ (extend-≈ (ren-≈ r' ∘ e) q) ) 
      (idext 
        (λ { Z     → refl-≈ʳ q 
           ; (S x) → ren-≈ r' (refl-≈ʳ (e (r x))) }) 
        τ)
↻-renₜ-eval r (τ₁ · τ₂) {η₁} {η₂} e = cong-App (↻-renₜ-eval r τ₁ e) (↻-renₜ-eval r τ₂ e)
↻-renₜ-eval r (τ₁ `→ τ₂) {η₁} {η₂} e = ap₂ _`→_ (↻-renₜ-eval r τ₁ e) (↻-renₜ-eval r τ₂ e)
↻-renₜ-eval r (`∀ τ) {η₁} {η₂} e = ap (`∀) 
  (trans 
    (↻-renₜ-eval (liftₜ r) τ 
      (extend-≈ 
        (ren-≈ S ∘ e) 
        (reflect-≈ {τ₁ = ` Z} refl))) 
    (idext 
      (λ { Z     → reflect-≈ refl 
         ; (S x) → (ren-≈ S ∘ refl-≈ʳ ∘ e) (r x) }) τ))
↻-renₜ-eval r (μ τ) {η₁} {η₂} e = ap μ (reify-≈ (↻-renₜ-eval r τ e))
↻-renₜ-eval r (π ⇒ τ) {η₁} {η₂} e = ap₂ _⇒_ (↻-renₜ-eval-pred r π e) (↻-renₜ-eval r τ e)
↻-renₜ-eval r (lab l) {η₁} {η₂} e = refl
↻-renₜ-eval r Π {η₁} {η₂} e = Unif-Π , Unif-Π , λ r x → cong-⟨Π⟩ x
↻-renₜ-eval r Σ {η₁} {η₂} e = Unif-Σ , Unif-Σ , λ r x → cong-⟨Σ⟩ x
↻-renₜ-eval r (τ₁ $ τ₂) {η₁} {η₂} e = cong-$ (↻-renₜ-eval r τ₁ e) (↻-renₜ-eval r τ₂ e)
↻-renₜ-eval r (⦅ ρ ⦆ ω) {η₁} {η₂} e = ↻-renₜ-evalRow r ρ e  
↻-renₜ-eval r (ρ₂ ∖ ρ₁) {η₁} {η₂} e = cong-⟨∖⟩ (↻-renₜ-eval r ρ₂ e) (↻-renₜ-eval r ρ₁ e)
↻-renₜ-eval r (l ▹ τ) {η₁} {η₂} e with ⟦ (renₜ r l) ⟧ₜ η₁ | ↻-renₜ-eval r l e 
... | ne x  | ih rewrite (sym ih) = (refl , refl) , (↻-renₜ-eval r τ e)
... | lab l | ih rewrite (sym ih) = refl , λ { fzero → refl , (↻-renₜ-eval r τ e) }

↻-renₜ-evalRow r [] {η₁} {η₂} e = refl , λ ()
↻-renₜ-evalRow r (x ∷ ρ) {η₁} {η₂} e with ⟦ (ren r ρ) ⟧ᵣ η₁ | ↻-renₜ-evalRow r ρ e 
... | n , P | refl , eq = 
  refl , (λ { fzero → refl , ↻-renₜ-eval r (x .snd) e  ; (fsuc i) → eq i })

--------------------------------------------------------------------------------
-- Substitution lemma
--   Evaluation commutes with syntactic substitution

↻-subₜ-eval : ∀ {Δ₂ : KEnv} {κ : Kind} 
                (τ : Type Δ κ) {η₁ η₂ : SemEnv Δ₁ Δ₂} → η₁ ≈ₑ η₂ →
                (σ : Substitution Δ Δ₁) → 
                ⟦ (sub σ τ) ⟧ₜ η₁ ≈ ⟦ τ ⟧ₜ (λ x → ⟦ (σ x) ⟧ₜ η₂)
↻-subₜ-eval-pred : (π : Pred (Type Δ R[ κ ])) 
                   {η₁ η₂ : SemEnv Δ₁ Δ₂} → η₁ ≈ₑ η₂ →
                   (σ : Substitution Δ Δ₁) → 
                    ⟦ (sub σ π) ⟧ₚ η₁ ≡ ⟦ π ⟧ₚ (λ x → ⟦ (σ x) ⟧ₜ η₂)
↻-subₜ-evalRow : {Δ₂ : KEnv} {κ : Kind}
                 (ρ : RowLiteral (Type Δ κ)) 
                 {η₁ η₂ : SemEnv Δ₁ Δ₂} → η₁ ≈ₑ η₂ →
                 (σ : Substitution Δ Δ₁) → 
                 ⟦ sub σ ρ ⟧ᵣ η₁ ≈ᵣ ⟦ ρ ⟧ᵣ (λ x → ⟦ (σ x) ⟧ₜ η₂)

↻-subₜ-eval-pred (ρ₁ · ρ₂ ~ ρ₃) e σ rewrite 
    reify-≈ (↻-subₜ-eval ρ₁ e σ) 
  | reify-≈ (↻-subₜ-eval ρ₂ e σ) 
  | reify-≈ (↻-subₜ-eval ρ₃ e σ) = refl
↻-subₜ-eval-pred (ρ₁ ≲ ρ₂) e σ rewrite
    reify-≈ (↻-subₜ-eval ρ₁ e σ) 
  | reify-≈ (↻-subₜ-eval ρ₂ e σ) = refl

↻-subₜ-eval (` α) e σ = idext e (σ α)
↻-subₜ-eval (`λ τ) {η₁} {η₂} e σ =  
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≈ 
      (↻-renSem-eval ρ₂ 
        (sub (liftsₜ σ) τ) 
        (extend-≈ (ren-≈ ρ₁ ∘ refl-≈ˡ ∘ e) q)) 
      (idext 
        (λ { Z → ren-≈ ρ₂ (refl-≈ʳ q) ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (refl-≈ˡ (e x))) }) 
        (sub (liftsₜ σ) τ))) , 
  (λ ρ₁ ρ₂ V₁ V₂ q → 
    trans-≈ 
      (↻-renSem-eval ρ₂ τ 
        (extend-≈ (ren-≈ ρ₁ ∘ idext (refl-≈ʳ ∘ e) ∘ σ) q)) 
      (idext 
        (λ { Z → ren-≈ ρ₂ (refl-≈ʳ q) 
           ; (S x) → sym-≈ 
                       (renSem-comp-≈ ρ₁ ρ₂ 
                         (idext (refl-≈ʳ ∘ e) (σ x)))})
        τ)) , 
  λ r q → 
    trans-≈ 
    (↻-subₜ-eval τ 
      (extend-≈ (ren-≈ r ∘ e) q) 
      (liftsₜ σ)) 
    (idext 
      (λ { Z →  refl-≈ʳ q 
         ; (S x) → trans-≈ 
                     (↻-renₜ-eval S (σ x) (extend-≈ (ren-≈ r ∘ refl-≈ʳ ∘ e) (refl-≈ʳ q))) 
                     (sym-≈ (↻-renSem-eval r (σ x) (refl-≈ʳ ∘ e)))})
      τ)  
↻-subₜ-eval (`∀ τ) e σ = ap (`∀) 
  (trans 
    (↻-subₜ-eval τ (extend-≈ (ren-≈ S ∘ e) (reflect-≈ refl)) (liftsₜ σ) ) 
    (idext 
      (λ { Z     → reflect-≈ refl 
         ; (S x) → trans-≈ 
                      (↻-renₜ-eval S (σ x) (extend-≈ (ren-≈ S ∘ refl-≈ʳ ∘ e) (reflect-≈ refl))) 
                      (sym-≈ (↻-renSem-eval S (σ x) (refl-≈ʳ ∘ e) )) }) 
      τ))
↻-subₜ-eval (τ₁ · τ₂) e σ = cong-App (↻-subₜ-eval τ₁ e σ) (↻-subₜ-eval τ₂ e σ) 
↻-subₜ-eval (τ₁ `→ τ₂) e σ = ap₂ _`→_ (↻-subₜ-eval τ₁ e σ) (↻-subₜ-eval τ₂ e σ)
↻-subₜ-eval (μ τ) e σ = ap μ (reify-≈ (↻-subₜ-eval τ e σ))
↻-subₜ-eval (π ⇒ τ) e σ = ap₂ _⇒_ (↻-subₜ-eval-pred π e σ) (↻-subₜ-eval τ e σ)
↻-subₜ-eval (lab l) e σ = refl
↻-subₜ-eval Π e σ = Unif-Π , Unif-Π , λ r v → cong-⟨Π⟩ v
↻-subₜ-eval Σ e σ = Unif-Σ , Unif-Σ , λ r v → cong-⟨Σ⟩ v
↻-subₜ-eval (τ₁ $ τ₂) e σ = cong-$ (↻-subₜ-eval τ₁ e σ) (↻-subₜ-eval τ₂ e σ)
↻-subₜ-eval (⦅ ρ ⦆ _) {η₁} e σ = ↻-subₜ-evalRow ρ e σ
↻-subₜ-eval (ρ₂ ∖ ρ₁) {η₁} e σ = cong-⟨∖⟩ (↻-subₜ-eval ρ₂ e σ) (↻-subₜ-eval ρ₁ e σ)
↻-subₜ-eval (l ▹ τ) {η₁} {η₂} e σ with ⟦ (sub σ l) ⟧ₜ η₁ | ↻-subₜ-eval l e σ  
... | ne x₁ | ih rewrite (sym ih) = (refl , refl) , ↻-subₜ-eval τ e σ
... | lab l₁ | ih rewrite (sym ih) = refl , (λ { fzero → refl , ((↻-subₜ-eval τ e σ)) })

↻-subₜ-evalRow [] {η₁} e σ = refl , λ ()
↻-subₜ-evalRow (x ∷ ρ) {η₁} e σ with ⟦ (sub σ ρ) ⟧ᵣ η₁ | ↻-subₜ-evalRow ρ e σ 
... | n , P | refl , eq = 
  refl , λ { fzero   → refl , ↻-subₜ-eval (x .snd) e σ ; 
            (fsuc i) → eq i }

↻-eval-Kripke : ∀ {Δ₃ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (f : Type Δ₁ (κ₁ `→ κ₂)) → (r : Renaming Δ₂ Δ₃) 
                {V₁ V₂ : SemType Δ₃ κ₁} → (V₁ ≈ V₂) → 
                {η₁ η₂ : SemEnv Δ₁ Δ₂} → η₁ ≈ₑ η₂ →  
                ⟦ f ⟧ₜ (renSem r ∘ η₁) id V₁ ≈ ⟦ f ⟧ₜ η₂ r V₂
↻-eval-Kripke (` α) r v e = snd (snd (e α)) r v
↻-eval-Kripke (`λ f) r v {η₁} {η₂} e = 
  idext (λ { Z → v
           ; (S x) → renSem-id-≈ 
                      {V₁ = (renSem r ∘ η₁) x} 
                      {(renSem r ∘ η₂) x} 
                      (ren-≈ r (e x)) }) f
↻-eval-Kripke (f · a) r {V₁} {V₂} v {η₁} {η₂} e with 
    ↻-eval-Kripke f r {⟦ a ⟧ₜ (renSem r ∘ η₁)} {⟦ a ⟧ₜ (renSem r ∘ η₂)} (idext (ren-≈ r ∘ e) a) {η₁} {η₂} e
  | ↻-eval-Kripke f id {⟦ a ⟧ₜ η₁} {⟦ a ⟧ₜ η₂} (idext e a) e
... | (Unif-ρ₁ , Unif-ρ₂ , Ext-ρ) | (Unif-id₁ , Unif-id₂ , Ext-id) =
    trans-≈ 
      (Ext-ρ id v) 
      (sym-≈ (trans-≈ 
        (third ((fst ∘ snd) (idext e f) id r (⟦ a ⟧ₜ η₂) (⟦ a ⟧ₜ η₂) (refl-≈ʳ (idext e a))) id (refl-≈ʳ v)) 
        (third (third (idext (refl-≈ʳ ∘ e) f) r (↻-renSem-eval r a (refl-≈ʳ ∘ e))) id (refl-≈ʳ v))))
↻-eval-Kripke Π r v e = cong-⟨Π⟩ v
↻-eval-Kripke Σ r v e = cong-⟨Σ⟩ v

--------------------------------------------------------------------------------
-- Evaluating a weakened typed in an extended environment is cancellative

weaken-extend : ∀ {Δ₂ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (τ : Type Δ₁ κ₁) → 
                  {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
                  η₁ ≈ₑ η₂ → 
                  {V : SemType Δ₂ κ₂}  → 
                  V ≈ V →
                  ⟦ weakenₜ τ ⟧ₜ (extende η₁ V) ≈ ⟦ τ ⟧ₜ η₂
weaken-extend τ {η₁} {η₂} e {V} v = ↻-renₜ-eval S τ {extende η₁ V} {extende η₂ V} (extend-≈ e v)   

weaken-lifte-cancel : ∀ {Δ₂ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (τ : Type Δ₁ κ₁) → 
                        {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
                        η₁ ≈ₑ η₂ → 
                          ⟦ weakenₜ {κ₁ = κ₂} τ ⟧ₜ (lifte η₁) 
                        ≈ renSem S (⟦ τ ⟧ₜ η₂)
weaken-lifte-cancel τ e = 
  trans-≈ (↻-renₜ-eval S τ (lifte-≈ (refl-≈ˡ ∘ e))) (sym-≈ (↻-renSem-eval S τ (sym-≈ ∘ e))) 

--------------------------------------------------------------------------------
-- The length of a reified row is the index of the row 

length-reify : ∀ {Δ : KEnv} {κ : Kind} (n : ℕ) (P : Fin n → Label × SemType Δ κ) → 
                 length (reifyRow (n , P)) ≡ n
length-reify zero P = refl
length-reify (suc n) P = ap suc (length-reify n (P ∘ fsuc))

--------------------------------------------------------------------------------
-- Length of a row is preserved by embedding

length-⇑ : ∀ (xs : RowLiteral (NormalType Δ κ)) → 
            length (⇑ᵣ xs) ≡ length xs
length-⇑ [] = refl
length-⇑ (x ∷ xs) = ap suc (length-⇑ xs)

-- Combining the two above 
length-⇑-reify : ∀ {Δ : KEnv} {κ : Kind} (n : ℕ) (P : Fin n → Label × SemType Δ κ) → 
                  length (⇑ᵣ (reifyRow (n , P))) ≡ n
length-⇑-reify n P = trans (length-⇑ (reifyRow (n , P))) (length-reify n P)        

--------------------------------------------------------------------------------
--⟨$⟩ commutes over complement operators

↻-⟨$⟩-compl₁ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              (λ {Δ : KEnv} → F {Δ}) ≈ (λ {Δ} → G {Δ}) → 
              (n , P) ≈ᵣ (n , P') → 
              (m , Q) ≈ᵣ (m , Q') → 
              compl P Q .fst ≡ compl (map₂ (G id) ∘ P') (map₂ (G id) ∘ Q') .fst
↻-⟨$⟩-compl₁ F G zero zero P P' Q Q' (_ , _ , Ext) (refl , PP) Q≈Q' = Q≈Q' .fst
↻-⟨$⟩-compl₁ F G zero (suc m) P P' Q Q' (_ , _ , Ext) (refl , PP) Q≈Q' = refl
↻-⟨$⟩-compl₁ F G (suc n) zero P P' Q Q' F≈G (refl , PP) Q≈Q' = ap suc (↻-⟨$⟩-compl₁ F G n zero (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) Q≈Q')
↻-⟨$⟩-compl₁ F G (suc n) (suc m) P P' Q Q' F≈G (refl , PP) (refl , QQ) with P fzero .fst ∈Row? Q | (map₂ (G id) ∘ P') fzero .fst ∈Row? (map₂ (G id) ∘ Q')
... | yes p | yes q  = ↻-⟨$⟩-compl₁ F G n (suc m) (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ)
... | yes (i , eq) | no q  = ⊥-elim (q (i , trans (sym (PP fzero .fst)) (trans eq (QQ i .fst))))
... | no p | yes (i , eq)  = ⊥-elim (p (i , trans (PP fzero .fst) (trans eq (sym (QQ i .fst)))))
... | no p | no q  = ap suc (↻-⟨$⟩-compl₁ F G n (suc m) (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ))


↻-⟨$⟩-compl₂ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              (λ {Δ : KEnv} → F {Δ}) ≈ (λ {Δ} → G {Δ}) → 
              (n , P) ≈ᵣ (n , P') → 
              (m , Q) ≈ᵣ (m , Q') → 
              compl (map₂ (F id) ∘ P) (map₂ (F id) ∘ Q) ≈ᵣ compl (map₂ (G id) ∘ P') (map₂ (G id) ∘ Q')
↻-⟨$⟩-compl₂ F G n m P P' Q Q' F≈G@(_ , _ , Ext) (refl , PP) (refl , QQ) = 
  cong-compl 
    (map₂ (F id) ∘ P) (map₂ (G id) ∘ P') 
    (map₂ (F id) ∘ Q) (map₂ (G id) ∘ Q') 
    (λ i → (PP i .fst) , cong-App F≈G (PP i .snd)) 
    (λ i → (QQ i .fst) , cong-App F≈G (QQ i .snd))

lem : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} 
        (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin (suc n) → Label × SemType Δ κ₁)
              (Q Q' : Fin m → Label × SemType Δ κ₁) → 
              (PP : ∀ i → P i ≈₂ P' i) → 
              (QQ : ∀ i → Q i ≈₂ Q' i) →
              (λ {Δ : KEnv} → F {Δ}) ≈ (λ {Δ} → G {Δ}) → 
              (pf : compl (P ∘ fsuc) Q .fst ≡ compl (map₂ (G id) ∘ (P' ∘ fsuc)) (map₂ (G id) ∘ Q') .fst) → 
              (i' : Fin
                (compl
                  (λ Δ₂ → P' (fsuc Δ₂) .fst , G (λ i₁ → i₁) (P' (fsuc Δ₂) .snd))
                  (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd)) .fst)) → 
              substᵢₓ pf
             (λ x₁ →
               compl (λ x₂ → P (fsuc x₂)) Q .snd x₁ .fst ,
             F (λ x₂ → x₂) (compl (λ x₂ → P (fsuc x₂)) Q .snd x₁ .snd))
            i'
          ≈₂
          compl
          (λ x₁ → P' (fsuc x₁) .fst , G (λ x₂ → x₂) (P' (fsuc x₁) .snd))
          (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd)) .snd i'
lem F G (suc n) m P P' Q Q' PP QQ f pf i' with 
     P (fsuc fzero) .fst ∈Row? Q 
    | P' (fsuc fzero) .fst ∈Row? (map₂ (G id) ∘ Q') 
... | yes (j , eq) | yes q = lem F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' (PP ∘ fsuc) QQ f pf i'
... | yes (j , eq) | no q  = ⊥-elim (q (j , trans (sym (PP (fsuc fzero) .fst)) (trans eq (QQ j .fst))))
... | no q         | yes (j , eq)   = ⊥-elim (q (j , trans (PP (fsuc fzero) .fst) (trans eq (sym (QQ j .fst)))))
... | no _         | no _  with 
        compl (P ∘ fsuc ∘ fsuc) Q 
     | compl (λ x → (P' ∘ fsuc ∘ fsuc) x .fst , G id (P' (fsuc (fsuc x)) .snd))
             (λ x₁ → Q' x₁ .fst , G (λ x₂ → x₂) (Q' x₁ .snd))
     | lem F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' (PP ∘ fsuc) QQ f
lem F G (suc n) m P P' Q Q' PP QQ f refl fzero | no _ | no _ | h , H | j , J | e = PP (fsuc fzero) .fst , f .snd .snd id (PP (fsuc fzero) .snd)
lem F G (suc n) m P P' Q Q' PP QQ f refl (fsuc i') | no _ | no _ | h , H | j , J | e = e refl i'

↻-⟨$⟩-⟨∖⟩ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} 
              (F G : SemType Δ (κ₁ `→ κ₂)) (n m : ℕ) 
              (P P' : Fin n → String × SemType Δ κ₁)
              {oP : OrderedRow (n , P)}
              {oP' : OrderedRow (n , P')}
              (Q Q' : Fin m → String × SemType Δ κ₁) → 
              {oQ : OrderedRow (m , Q)}
              {oQ' : OrderedRow (m , Q')} →
              (λ {Δ : KEnv} → F {Δ}) ≈ (λ {Δ} → G {Δ}) → 
              (n , P) ≈ᵣ (n , P') → 
              (m , Q) ≈ᵣ (m , Q') → 
              (F ⟨$⟩ (row (n , P) oP ⟨∖⟩ row (m , Q) oQ)) ≈ 
              ((G ⟨$⟩ row (n , P') oP') ⟨∖⟩ (G ⟨$⟩ row (m , Q') oQ'))
             
↻-⟨$⟩-⟨∖⟩ F G zero m P P' {oP} {oP'} Q Q' {oQ} {oQ'} F≈G P≈P' Q≈Q' = refl , (λ ())
↻-⟨$⟩-⟨∖⟩ F G (suc n) m P P' {oP} {oP'} Q Q' {oQ} {oQ'} F≈G (refl , PP) (refl , QQ) with
      P fzero .fst ∈Row? Q | P' fzero .fst ∈Row? (map₂ (G id) ∘ Q') | PP fzero 
    | ↻-⟨$⟩-compl₂ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ)
... | yes (i , eq) | yes (j , q) | e , d | fst-eq , snd-eq = 
  ↻-⟨$⟩-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ) , 
  λ i' → lem F G n m P P' Q Q' PP QQ F≈G (↻-⟨$⟩-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ)) i' 
... | yes (i , eq) | no q | e , d | cc = ⊥-elim (q (i , trans (sym e) (trans eq (QQ i .fst))))
... | no q | yes (i , eq) | e , d | cc = ⊥-elim (q (i , trans e (trans eq (sym (QQ i .fst)))))
... | no  p | no q | _ | compl₂ with 
       compl (P ∘ fsuc) Q 
    |  ↻-⟨$⟩-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ) 
    | lem F G n m P P' Q Q' PP QQ F≈G (↻-⟨$⟩-compl₁ F G n m (P ∘ fsuc) (P' ∘ fsuc) Q Q' F≈G (refl , PP ∘ fsuc) (refl , QQ))
... | a | refl | lem₁ = refl , λ { fzero → (PP fzero .fst) , (F≈G .snd .snd id (PP fzero .snd)) ; (fsuc i) → lem₁ i }

--------------------------------------------------------------------------------
-- A function f are is pointwise equivalent to its η-expansion

weaken-η-≈ : ∀ {Δ₃ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {κ' : Kind} (f : Type Δ₁ (κ₁ `→ κ₂)) {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
               (η₁ ≈ₑ η₂) →  (r : Renaming Δ₂ Δ₃) → 
               {V₁ V₂ : SemType Δ₃ κ₁} → 
               V₁ ≈ V₂ → 
               (W : SemType Δ₃ κ') → 
               W ≈ W → 
            ⟦ f ⟧ₜ η₁ r V₁ ≈ ⟦ (renₜ S f) ⟧ₜ (extende (renSem r ∘ η₂) W) id V₂
weaken-η-≈ f {η₁} {η₂} e r {V₁} {V₂} v W w =  sym-≈ 
    (trans-≈ 
        (third (↻-renₜ-eval S f 
                    {η₂ = (extende (λ {κ} v' → renSem r (η₂ v')) W)} 
                    (extend-≈ (ren-≈ r ∘ refl-≈ʳ ∘ e) w)) 
                    id 
                    (sym-≈ v)) 
        ((↻-eval-Kripke f r (refl-≈ˡ v) (sym-≈ ∘ e))))

weaken-η-≈' : ∀ {Δ₄ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {κ' : Kind} 
                (f : Type Δ₁ (κ₁ `→ κ₂)) {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
               (η₁ ≈ₑ η₂) →  (r₁ : Renaming Δ₂ Δ₃) (r₂ : Renaming Δ₃ Δ₄) → 
               {V₁ V₂ : SemType Δ₃ κ₁} → 
               V₁ ≈ V₂ → 
               (W : SemType Δ₃ κ') → 
               W ≈ W → 
              ⟦ f ⟧ₜ η₁ (r₂ ∘ r₁) (renSem r₂ V₁) 
            ≈ ⟦ renₜ S f ⟧ₜ (extende (renSem r₁ ∘ η₂) W) r₂ (renSem r₂ V₂)
weaken-η-≈' f {η₁ = η₁} {η₂} e r₁ r₂ v W w = 
  trans-≈ 
    (weaken-η-≈ f e (r₂ ∘ r₁) (ren-≈ r₂ v) _ (ren-≈ r₂ w)) 
    (trans-≈ 
      (idext 
        {η₁ = extende (renSem (r₂ ∘ r₁) ∘ η₂) (renSem r₂ W)} 
        {renSem r₂ ∘ extende (renSem r₁ ∘ η₁) W} 
        (λ { Z     → ren-≈ r₂ w ; 
            (S x₁) → renSem-comp-≈ r₁ r₂ (sym-≈ (e x₁)) }) (renₜ S f) .snd .snd id (ren-≈ r₂ (sym-≈ v))) 
      (↻-eval-Kripke (renₜ S f) r₂ (ren-≈ r₂ v) (extend-≈ (ren-≈ r₁ ∘ e) w)))

--------------------------------------------------------------------------------
-- Map ID & composition law for semantic rows 

map-id-≈ : ∀ {ρ₁ ρ₂ : SemType Δ R[ κ ]} → ρ₁ ≈ ρ₂ → ((λ ρ v → v) ⟨$⟩ ρ₁) ≈ ρ₂
map-id-≈ {ρ₁ = φ $ x₁} {ρ₂ = _ $ _} rel = rel
map-id-≈ {ρ₁ = x₁ ▹ x₂} {ρ₂ = _ ▹ _} rel = rel
map-id-≈ {ρ₁ = row ρ x₁} {ρ₂ = row _ _} rel = rel
map-id-≈ {ρ₁ = ρ₂ ∖ ρ₁} {ρ₂ = _ ∖ _} (rel₂ , rel₁) = map-id-≈ rel₂ , map-id-≈ rel₁ 

map-∘-≈ :  ∀ {κ₁ : Kind} {κ₂ : Kind} {κ₃ : Kind} (f : Type Δ₁ (κ₂ `→ κ₃)) 
             (g : Type Δ₁ (κ₁ `→ κ₂)) 
             {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
             (η₁ ≈ₑ η₂) →  
             (r : Renaming Δ₂ Δ₃) → 
             {ρ₁ ρ₂ : SemType Δ₂ R[ κ₁ ]} → 
             ρ₁ ≈ ρ₂ →
               ⟦ f ⟧ₜ η₁ ⟨$⟩ (⟦ g ⟧ₜ η₁ ⟨$⟩ ρ₁)
             ≈ (λ ρ v →
                    ((⟦ renₜ S f ⟧ₜ (extende (renSem ρ ∘ η₂) v) id)
                  ∘  (⟦ renₜ S g ⟧ₜ (extende (renSem ρ ∘ η₂) v) id)) v) 
                ⟨$⟩ ρ₂
map-∘-≈ f g {η₁ = η₁} {η₂} e r {φ₁ $ x₁} {φ₂ $ x₂} ((refl ,  Unif-φ₁ , Unif-φ₂ , Ext-φ) , (refl , refl)) with idext e f | idext e g 
... | Unif-f₁ , Unif-f₂ , Ext-f | Unif-g₁ , Unif-g₂ , Ext-g = 
  (refl ,
  (λ r₁ r₂ V → 
    trans-≈ 
      (Unif-f₁ r₁ r₂ _ _ (Ext-g  r₁ (Ext-φ r₁ V) )) 
      (refl-Extₗ Ext-f (r₂ ∘ r₁) 
    (trans-≈ (Unif-g₂ r₁ r₂ _ _ (refl-≈ʳ (Ext-φ r₁ V))) 
       (sym-≈ (Ext-g (r₂ ∘ r₁) (trans-≈ 
         (sym-≈ (Unif-φ₁ r₁ r₂ V)) 
         (ren-≈ r₂ (Ext-φ r₁ V)))) )))) , 
  (λ r₁ r₂ V → 
    let Unif-f' , _ , Ext-f' = idext (extend-≈ (ren-≈ r₁ ∘ refl-≈ʳ ∘ e) (refl-≈ʳ (Ext-φ r₁ V))) (renₜ S f) in
    let Unif-g' , _ , Ext-g' = idext (extend-≈ (ren-≈ r₁ ∘ refl-≈ʳ ∘ e) (refl-≈ʳ (Ext-φ r₁ V))) (renₜ S g) in
    trans-≈ 
      (trans-≈ 
        (Unif-f' id r₂ _ _ (sym-≈ (weaken-η-≈ g e r₁ (refl-≈ʳ (Ext-φ r₁ V)) _ ((refl-≈ʳ (Ext-φ r₁ V)))) ) ) 
        (trans-≈
           (sym-≈ (weaken-η-≈' f e r₁ r₂ (refl-Extₗ Ext-g r₁ (refl-≈ʳ (Ext-φ r₁ V)) ) (φ₂ r₁ V) (refl-≈ʳ (Ext-φ r₁ V))) )
           (refl-Extₗ Ext-f (r₂ ∘ r₁) 
           (trans-≈ 
             (Unif-g₁ r₁ r₂ _ _ (refl-≈ʳ (Ext-φ r₁ V))) 
             (sym-≈ (refl-Extₗ Ext-g (r₂ ∘ r₁) (sym-≈ (Unif-φ₂ r₁ r₂ V)))))))) 
      (weaken-η-≈ f e (r₂ ∘ r₁) 
         (weaken-η-≈ g e (r₂ ∘ r₁) ((refl-≈ʳ (Ext-φ (r₂ ∘ r₁) (ren r₂ V)))) (φ₂ (r₂ ∘ r₁) (ren r₂ V)) (refl-≈ʳ (Ext-φ (r₂ ∘ r₁) (ren r₂ V)))) 
         (φ₂ (r₂ ∘ r₁) (ren r₂ V)) 
         (refl-≈ʳ (Ext-φ (r₂ ∘ r₁) (ren r₂ V)))))
      , 
  (λ r V → weaken-η-≈ f e r (weaken-η-≈ g e r (Ext-φ r V) (φ₂ r V) (refl-≈ʳ (Ext-φ r V))) (φ₂ r V) (refl-≈ʳ (Ext-φ r V)))) , 
  (refl , refl)
map-∘-≈ f g e r {l₁ ▹ τ₁} {l₂ ▹ τ₂} ((refl , refl) , rel) =
  (refl , refl) , weaken-η-≈ f e id (weaken-η-≈ g e id rel τ₂ (refl-≈ʳ rel)) τ₂ (refl-≈ʳ rel)
map-∘-≈ f g {η₁ = η₁} {η₂} e r {row (zero , P) x₁} {row (zero , Q) x₂} rel = refl , λ ()
map-∘-≈ f g {η₁ = η₁} {η₂} e r {row (suc n , P) x₁} {row (suc m , Q) x₂} (refl , rel) = 
      refl , λ { i → (rel i .fst) , 
                 (weaken-η-≈ f e id (weaken-η-≈ g e id (rel i .snd) _ (refl-≈ʳ (rel i .snd))) _ (refl-≈ʳ (rel i .snd))) }
map-∘-≈ f g e r {ρ₁ ∖ ρ₂} {ρ₃ ∖ ρ₄} (rel₁ , rel₂) = map-∘-≈ f g e r rel₁ , map-∘-≈ f g e r rel₂


--------------------------------------------------------------------------------
-- syntactic 
