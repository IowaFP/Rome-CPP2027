-- 
module Rome.Metatheory.NBE.Consistency where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming 
open import Rome.Types.Substitution

open import Rome.Types.Properties.Renaming
open import Rome.Types.Properties.Substitution
open import Rome.Types.Properties.Equivalence
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.Properties.Renaming
  using (↻-ren-⇑ₙₑ ; ↻-ren-⇑)

open import Rome.NormalTypes.NBE.Syntax
open import Rome.NormalTypes.NBE.Renaming
open import Rome.NormalTypes.NBE.Normalization

open import Rome.Types.Equivalence

open import Rome.Metatheory.NBE.Soundness
open import Rome.Metatheory.NBE.Stability
open import Rome.Metatheory.NBE.Consistency.Relation public



--------------------------------------------------------------------------------
-- ⇑ ∘ reify commutes over _∖_

↻-⇑-reify-∖ : ∀ (ρ₂ ρ₁ : SemRow Δ₂ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]) → 
                   {nr   : notRowLiteral ρ₂ or notRowLiteral ρ₁} → 
                  ⇑ (reify ((ρ₂ ∖ ρ₁) {nr})) ≡ₜ ⇑ (reify ρ₂) ∖ ⇑ (reify ρ₁)
↻-⇑-reify-∖ (φ $ n) (φ' $ n') {nr} = eq-refl
↻-⇑-reify-∖ (φ $ n) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-∖ (φ $ n) (row ρ x₂) {nr} = eq-refl
↻-⇑-reify-∖ (φ $ n) (ρ₁ ∖ ρ₂) {nr} = eq-refl
↻-⇑-reify-∖ (x₁ ▹ x₂) (φ $ n) {nr} = eq-refl
↻-⇑-reify-∖ (x₁ ▹ x₂) (x₃ ▹ x₄) {nr} = eq-refl
↻-⇑-reify-∖ (x₁ ▹ x₂) (row ρ x₃) {nr} = eq-refl
↻-⇑-reify-∖ (x₁ ▹ x₂) (ρ₁ ∖ ρ₂) {nr} = eq-refl
↻-⇑-reify-∖ (row ρ x₁) (φ $ n) {nr} = eq-refl
↻-⇑-reify-∖ (row ρ x₁) (x₂ ▹ x₃) {nr} = eq-refl
↻-⇑-reify-∖ (row ρ x₁) (row ρ₁ x₂) {left ()}
↻-⇑-reify-∖ (row ρ x₁) (row ρ₁ x₂) {right ()}
↻-⇑-reify-∖ (row ρ x₁) (ρ₁ ∖ ρ₂) {nr} = eq-refl
↻-⇑-reify-∖ (ρ₂ ∖ ρ₃) (φ $ n) {nr} = eq-refl
↻-⇑-reify-∖ (ρ₂ ∖ ρ₃) (x₁ ▹ x₂) {nr} = eq-refl
↻-⇑-reify-∖ (ρ₂ ∖ ρ₃) (row ρ x₁) {nr} = eq-refl
↻-⇑-reify-∖ (ρ₂ ∖ ρ₃) (ρ₁ ∖ ρ₄) {nr} = eq-refl

--------------------------------------------------------------------------------
-- syntactic mapping relates to semantic precomposition

map-over-⇑ᵣ : ∀ {Δ : KEnv} {κ₁ : Kind} (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (n : ℕ) (P : Fin n → Label × SemType Δ κ₁) → 
                ⟦ f ⟧≈ F → 
                ⟦ ⇑ᵣ (reifyRow (n , P)) ⟧≈ᵣ (n , P) → 
                ⟦ map (map₂ (f ·_)) (⇑ᵣ (reifyRow (n , P))) ⟧≈ᵣ (n , map₂ (F id) ∘ P)
map-over-⇑ᵣ f F zero P rel-f rel-P = tt
map-over-⇑ᵣ f F (suc n) P rel-f rel-P = 
  (refl , 
  (subst-⟦⟧≈ (eq-· (inst (renₜ-id f)) eq-refl) (rel-f id (rel-P .fst .snd)))) , 
  (map-over-⇑ᵣ f F n (P ∘ fsuc) rel-f (rel-P .snd))              

--------------------------------------------------------------------------------
-- Congruence over syntactic/semantic mapping

cong-$⟦⟧≈ : ∀ (f : Type Δ (κ₁ `→ κ₂)) (F : SemType Δ (κ₁ `→ κ₂)) 
                (v : Type Δ R[ κ₁ ]) (V : SemType Δ R[ κ₁ ]) → 
                ⟦ f ⟧≈ F → 
                ⟦ v ⟧≈ V → 
                ⟦ f $ v ⟧≈ F ⟨$⟩ V 
cong-$⟦⟧≈ f F v (φ $ n) rel-f (g , g-eq , g-sound) = 
  (`λ (weakenₜ f · (weakenₜ g · (` Z)))) , 
  (eq-trans (eq-$ eq-refl g-eq) eq-map-∘) , 
  (λ r vee → 
    subst-⟦⟧≈ 
      (eq-trans 
        (eq-· 
          (inst (subₜ-weaken-over-lift r f _)) 
          (eq-· 
            (inst (subₜ-weaken-over-lift r g _)) 
            eq-refl)) (eq-sym eq-β)) 
      (rel-f r (g-sound r vee)))
cong-$⟦⟧≈ f F v (l ▹ τ) rel-f (eq , rel) = 
  eq-trans 
    (eq-$ eq-refl eq) 
  (eq-trans 
    eq-▹$ 
  (eq-▹ 
    eq-refl 
    (reify-⟦⟧≈ 
      (subst-⟦⟧≈ 
        (eq-· (inst (renₜ-id f)) eq-refl) 
        (rel-f id rel))))) , 
  refl-⟦⟧≈ (rel-f id rel)
cong-$⟦⟧≈ f F v (row (n , P) x₁) rel-f (eq , rel) = 
  (eq-trans 
    (eq-$ eq-refl eq) 
  (eq-trans eq-map 
  (eq-row (reify-⟦⟧≈ᵣ (map-over-⇑ᵣ f F n P rel-f rel))))) , 
  refl-⟦⟧≈ᵣ (map-over-⇑ᵣ f F n P rel-f rel)
cong-$⟦⟧≈ f F v ((V₂ ∖ V₁) {nr}) rel-f (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-$ eq-refl (eq-trans eq (↻-⇑-reify-∖ V₂ V₁ {nr}))) 
  (eq-trans 
    eq-$-∖ 
  (eq-trans 
    (eq-∖ 
      (reify-⟦⟧≈ (cong-$⟦⟧≈ f F (⇑ (reify V₂)) V₂ rel-f rel₂)) 
      ((reify-⟦⟧≈ (cong-$⟦⟧≈ f F (⇑ (reify V₁)) V₁ rel-f rel₁)))) 
    (eq-sym (↻-⇑-reify-∖ (F ⟨$⟩ V₂) (F ⟨$⟩ V₁) {notRowLiteral$ nr}))))) , 
  (refl-⟦⟧≈ (cong-$⟦⟧≈ f F (⇑ (reify V₂)) V₂ rel-f rel₂)) , 
  (refl-⟦⟧≈ (cong-$⟦⟧≈ f F (⇑ (reify V₁)) V₁ rel-f rel₁))

--------------------------------------------------------------------------------
-- Congruence over complement

∈Row→∈L≈ : ∀ {Δ : KEnv} {κ : Kind} {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈Row P → l ∈L (⇑ᵣ (reifyRow' n P))
∈Row→∈L≈ {n = n} (fzero , refl) = Here
∈Row→∈L≈ {n = n} (fsuc i , eq) = There (∈Row→∈L≈ (i , eq))

∈L→∈Row≈ : ∀ {Δ : KEnv} {κ : Kind} {n : ℕ} {P : Fin n → Label × SemType Δ κ} {l : Label} → 
              l ∈L (⇑ᵣ (reifyRow' n P)) → l ∈Row P
∈L→∈Row≈ {n = suc n} Here = fzero , refl
∈L→∈Row≈ {n = suc n} (There ev) with ∈L→∈Row≈ ev 
... | i , eq = (fsuc i) , eq

cong-compl⟦⟧≈ : ∀ {Δ : KEnv} {κ : Kind} {n m : ℕ} 
                {P : Fin n → Label × SemType Δ κ}
                {Q : Fin m → Label × SemType Δ κ} →
                ⟦ ⇑ᵣ (reifyRow' n P) ⟧≈ᵣ (n , P) → 
                ⟦ ⇑ᵣ (reifyRow' m Q) ⟧≈ᵣ (m , Q) → 
                ⟦ ⇑ᵣ (reifyRow' n P) ∖s ⇑ᵣ (reifyRow' m Q) ⟧≈ᵣ compl P Q
cong-compl⟦⟧≈ {n = zero} {P = P} {Q} P≈ Q≈ = tt
cong-compl⟦⟧≈ {n = suc n} {m} {P = P} {Q} P≈ Q≈ with P fzero .fst ∈Row? Q | P fzero .fst ∈L? ⇑ᵣ (reifyRow' m Q) 
... | yes p | yes q = cong-compl⟦⟧≈ (P≈ .snd) Q≈
... | yes p | no q = ⊥-elim (q (∈Row→∈L≈ p))
... | no p | yes q = ⊥-elim (p (∈L→∈Row≈ q))
... | no p | no q = (refl , P≈ .fst .snd) , (cong-compl⟦⟧≈ (P≈ .snd) Q≈)

--------------------------------------------------------------------------------
-- Apply is sound

sound-apply : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} (v : Type Δ κ₁) (V : SemType Δ κ₁) → 
               ⟦ v ⟧≈ V → 
               SoundKripke {κ₂ = κ₂} (`λ (` Z · renₜ S v)) (apply V)
sound-apply v V rel-v r {g} {G} rel-G = 
  subst-⟦⟧≈ 
    (eq-sym eq-β)
  (subst-⟦⟧≈ 
    (eq-sym 
      (eq-· eq-refl 
      (eq-trans 
        (inst (ap (sub (extendₜ ` g)) (↻-liftₜ-weaken r v)))
        (inst (subₜ-weaken (renₜ r v) g))))) 
  (subst-⟦⟧≈ 
    (eq-· (inst (renₜ-id g)) eq-refl) 
    (rel-G id (ren-⟦⟧≈ r rel-v))))

--------------------------------------------------------------------------------
-- Π and Π-Kripke are soundly related

sound-Π : ∀ {nl : NotLabel κ₁} → 
        SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Π {notLabel = nl}) Π-Kripke
sound-Σ : ∀ {nl : NotLabel κ₁} → 
        SoundKripke {Δ₁ = Δ₁} {κ₁ = R[ κ₁ ]} {κ₂ = κ₁} (Σ {notLabel = nl}) Σ-Kripke

-- Mapping _apply_ over a row is semantic application
map-apply : ∀ {Δ₂ : KEnv} {κ₁ : Kind}{κ₂ : Kind}
              (n : ℕ) (P : Fin n → Label × KripkeFunction Δ₁ κ₁ κ₂) → 
               (φ : Renaming Δ₁ Δ₂) → 
               (rel : ⟦ ⇑ᵣ (reifyRow' n P) ⟧≈ᵣ (n , P)) → 
               (v : Type Δ₂ κ₁) (V : SemType Δ₂ κ₁) → 
               (rel-v : ⟦ v ⟧≈ V) → 
             ⟦ map (map₂ (_·_ (`λ (` Z · weakenₜ v))))
               (sub (extendₜ ` v)
                 (ren S (ren φ (⇑ᵣ (reifyRow (n , P))))))
             ⟧≈ᵣ (n , λ x → (P x . fst) , apply V id (renKripke φ (P x .snd)))
map-apply zero P φ rel v V rel-v = tt
map-apply (suc n) P φ (rel-fzero , rel-fsuc) v V rel-v = 
  (refl , 
  subst-⟦⟧≈ 
    (eq-sym eq-β) 
  (subst-⟦⟧≈ 
    (eq-sym eq-β) 
  (subst-⟦⟧≈ 
    (inst (subₜ-comp (renₜ (liftₜ S)
            (renₜ (liftₜ φ) (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))))) 
  (subst-⟦⟧≈ 
    (inst (↻-subₜ-renₜ (renₜ (liftₜ φ) (⇑ (reify ((P fzero .snd) S (reflect (` Z)))))))) 
  (subst-⟦⟧≈ 
    (inst (↻-subₜ-renₜ (⇑ (reify ((P fzero .snd) S (reflect (` Z))))) )) 
  (subst-⟦⟧≈ 
    (inst (subₜ-cong {σ₁ = extendₜ (` ∘ φ) v} (λ { Z → sym (subₜ-weaken v _) ; (S x) → refl })  (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))) 
  (subst-⟦⟧≈ 
    (eq-trans 
      eq-β 
    (eq-trans 
      (inst (sym (↻-subₜ-renₜ {r = liftₜ φ} {σ = extendₜ ` (renₜ id v)} (⇑ (reify ((P fzero .snd) S (reflect (` Z)))))))) 
    (inst (subₜ-cong (λ { Z → renₜ-id v ; (S x) → refl }) (⇑ (reify ((P fzero .snd) S (reflect (` Z))))))))) 
  ((rel-fzero .snd) φ (ren-⟦⟧≈ id rel-v))))))))) , 
  (map-apply n (P ∘ fsuc) φ rel-fsuc v V rel-v)

--------------------------------------------------------------------------------
--
-- Mapping Π over a row relates to pre-composition by semantic Π 
--
-- N.b. we can't use map-over-⇑ᵣ to define map-Π without violating termination
-- checking in sound-Π later.

map-Π : ∀ {nl : NotLabel κ} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑ᵣ (reifyRow' n P) ⟧≈ᵣ (n , P)) → 
        ⟦ map (map₂ (_·_ (Π {notLabel = nl}))) (⇑ᵣ (reifyRow' n P)) ⟧≈ᵣ (n ,  λ i → P i .fst , ΠV (P i .snd))

map-Σ : ∀ {nl : NotLabel κ} (n : ℕ) (P : Fin n → Label × SemType Δ R[ κ ]) → 
        (rel : ⟦ ⇑ᵣ (reifyRow' n P) ⟧≈ᵣ (n , P)) → 
        ⟦ map (map₂ (_·_ (Σ {notLabel = nl}))) (⇑ᵣ (reifyRow' n P)) ⟧≈ᵣ (n ,  λ i → P i .fst , ΣV (P i .snd))

--------------------------------------------------------------------------------
-- Consistency of Π and ΠV definition

sound-Π {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≈ q)
sound-Π {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Π {κ₁ = κ₁ `→ κ₂} ρ {v} {φ $ n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≈ 
    (eq-· (eq-· eq-refl (eq-sym (renₜ-≡ₜ r eq))) eq-refl) 
  (subst-⟦⟧≈ 
    (eq-sym eq-Π-assoc)
    (sound-Π id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-$ 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₜ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₜ-≡ₜ S (inst (subₜ-weaken (renₜ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₜ-weaken (renₜ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₜ-weaken (renₜ r (⇑ₙₑ n)) v')) 
        (eq-sym (inst (↻-ren-⇑ₙₑ r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : SoundKripkeNE 
              (`λ (renₜ S (renₜ r f) · ` Z · renₜ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≈ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₜ-id _) (renₜ-comp r r₁  f))) 
                  (inst (renₜ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₜ-weaken-over-lift r₁ (renₜ r f) _)) eq-refl) 
                (inst (subₜ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≈ r₁ rel-v))     
sound-Π {κ₁ = R[ κ ]} ρ {v} {φ $ n} (f , eq , sound-f) = 
  (`λ (weakenₜ Π · (weakenₜ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Π (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≈ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≈ 
      (eq-sym eq-β) 
      (sound-Π id 
        (subst-⟦⟧≈ 
          (eq-· 
            (inst (subₜ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
sound-Π {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (eq , rel) ρ₂ {v} {V} rel-v = 
  subst-⟦⟧≈ (eq-sym (eq-Π-assoc)) (sound-Π ρ₂ {renₜ ρ₂ f ?? v} 
  ((eq-trans 
    (eq-· 
      (eq-· 
        eq-refl 
        (renₜ-≡ₜ ρ₂ eq)) 
      eq-refl) 
  (eq-trans 
    (eq-· eq-β eq-refl) 
  (eq-trans 
    eq-β 
  (eq-trans 
    eq-map 
  (eq-row 
    (reify-⟦⟧≈ᵣ (map-apply n P ρ₂ rel v V rel-v))))))) , 
  refl-⟦⟧≈ᵣ (map-apply n P ρ₂ rel v V rel-v)))
sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {f} {l ▹ F} (eq , sound-F) r₂ {v} {V} rel-V = 
  subst-⟦⟧≈ (eq-sym (eq-Π-assoc)) 
    (sound-Π r₂ 
      ((eq-trans 
        (eq-· (eq-· eq-refl (renₜ-≡ₜ r₂ eq)) eq-refl) 
        (eq-trans (eq-· eq-β eq-refl) 
        (eq-trans 
          eq-β 
        (eq-trans 
          eq-▹$ 
          (eq-▹ 
            (inst (trans (subₜ-weaken (renₜ r₂ (⇑ₙₑ l)) v) (sym (↻-ren-⇑ₙₑ r₂ l)))) 
            (eq-trans 
              eq-β 
            (eq-trans 
              eq-β 
            (eq-trans 
              (inst (sym (subₜ-comp (renₜ (liftₜ S)
              (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))))))) 
            (eq-trans 
              (inst (sym (↻-subₜ-renₜ (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z))))))))) 
            (eq-trans 
              (inst 
                (subₜ-cong {σ₂ = extendₜ ` (renₜ id v)} 
                (λ { Z → trans (subₜ-weaken v _) (sym (renₜ-id v)) ; (S x₁) → refl }) 
                (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))))) 
              (eq-trans 
                (eq-sym 
                  (eq-β {τ₁ = renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))} {renₜ id v})) 
              (reify-⟦⟧≈ (sound-F r₂ (ren-⟦⟧≈ id rel-V)))))))))))))) , 
    refl-⟦⟧≈ (sound-F r₂ {_} {renSem id V} (ren-⟦⟧≈ id rel-V))))
  
sound-Π {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ∖ V₁) {nr}} rel r₂ {v} {V} rel-V = 
  subst-⟦⟧≈ 
    (eq-· (eq-· eq-refl (eq-sym (renₜ-≡ₜ r₂ (eq-trans (rel .fst) (↻-⇑-reify-∖ V₂ V₁ {nr}))))) eq-refl) 
  (subst-⟦⟧≈ 
    (eq-sym eq-Π-assoc) 
  (sound-Π r₂ 
    (eq-trans 
      (eq-trans 
        (eq-· eq-β eq-refl) 
      (eq-trans 
          eq-β 
      (eq-trans 
        eq-$-∖ 
      (eq-∖ 
        (eq-trans 
          (eq-$ eq-refl (inst (subₜ-weaken (renₜ r₂ (⇑ (reify V₂))) v))) 
          (reify-⟦⟧≈ 
            {V = apply V ⟨$⟩ renSem r₂ V₂} 
            (cong-$⟦⟧≈ 
              (`λ (` Z · renₜ S v)) 
              (apply V) 
              (renₜ r₂ (⇑ (reify V₂))) 
              (renSem r₂ V₂) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≈ r₂ (rel .snd .fst))))) 
        ((eq-trans 
          (eq-$ eq-refl (inst (subₜ-weaken (renₜ r₂ (⇑ (reify V₁))) v))) 
          (reify-⟦⟧≈ 
            {V = apply V ⟨$⟩ renSem r₂ V₁} 
            (cong-$⟦⟧≈ 
              (`λ (` Z · renₜ S v)) 
              (apply V) 
              (renₜ r₂ (⇑ (reify V₁))) 
              (renSem r₂ V₁) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≈ r₂ (rel .snd .snd)))))))))) 
    (eq-sym 
      (↻-⇑-reify-∖ 
        (apply V ⟨$⟩ renSem r₂ V₂) (apply V ⟨$⟩ renSem r₂ V₁) {notRowLiteral$ (nrRenSem' r₂ V₂ V₁ nr)})) , 
    (refl-⟦⟧≈ (cong-$⟦⟧≈ (`λ (` Z · renₜ S v)) (apply V)
                 (renₜ r₂ (⇑ (reify V₂))) (renSem r₂ V₂) (sound-apply v V rel-V) (ren-⟦⟧≈ r₂ (rel .snd .fst))) , 
    refl-⟦⟧≈ (cong-$⟦⟧≈ (`λ (` Z · renₜ S v)) (apply V)
                 (renₜ r₂ (⇑ (reify V₁))) (renSem r₂ V₁) (sound-apply v V rel-V) (ren-⟦⟧≈ r₂ (rel .snd .snd)))))))
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (eq , rel) =
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  (eq-trans 
    eq-map 
    (eq-row (reify-⟦⟧≈ᵣ (map-Π n P rel))))) , 
  refl-⟦⟧≈ᵣ (map-Π {nl = nl} n P rel)
sound-Π {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (eq , rel) = 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Π (eq-trans eq-▹$ (eq-▹ eq-refl (reify-⟦⟧≈ (sound-Π id rel)))))) , 
  (refl-⟦⟧≈ (sound-Π {nl = nl} id rel))
sound-Π {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ∖ ρ₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Π 
  (eq-trans 
    (eq-$ eq-refl (↻-⇑-reify-∖ ρ₂ ρ₁ {nr})) 
  (eq-trans 
    eq-$-∖ 
  (eq-trans 
    (eq-∖ (eq-sym eq-Π) (eq-sym eq-Π)) 
  (eq-trans 
    (eq-∖ (reify-⟦⟧≈ (sound-Π id rel₂)) (reify-⟦⟧≈ (sound-Π id rel₁))) 
  (eq-trans (eq-sym (↻-⇑-reify-∖ ((λ ρ → ΠV) ⟨$⟩ ρ₂) ((λ ρ → ΠV) ⟨$⟩ ρ₁) {nr = notRowLiteral$ nr})) eq-refl))))))) , (refl-⟦⟧≈ (sound-Π {nl = nl} id rel₂)) , ((refl-⟦⟧≈ (sound-Π {nl = nl} id rel₁)))

map-Π zero P rel = tt
map-Π {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Π {nl = nl} id rel-fzero) , (map-Π n (P ∘ fsuc) rel-fsuc)

--------------------------------------------------------------------------------
-- Consistency of Σ and ΣV definition (identical to Π def'n above)

sound-Σ {κ₁ = ★} ρ {v} {V} q = eq-· eq-refl (reify-⟦⟧≈ q)
sound-Σ {κ₁ = L} {nl = ()} ρ {v} {V} q
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ {v} {φ $ n} (f , eq , sound-f) r {v'} {V'} rel-v = 
  subst-⟦⟧≈ 
    (eq-· (eq-· eq-refl (eq-sym (renₜ-≡ₜ r eq))) eq-refl) 
  (subst-⟦⟧≈ 
    (eq-sym eq-Σ-assoc)
    (sound-Σ id 
    (_ , 
    ((eq-trans 
        (eq-· eq-β eq-refl) 
    (eq-trans 
      eq-β 
    (eq-trans 
      eq-map-∘ 
    (eq-$ 
      (eq-trans 
        (eq-λ (eq-· 
          (eq-λ (eq-· 
            eq-refl 
            (eq-trans 
              (inst (↻-liftₜ-weaken S v')) 
              eq-refl))) 
          (eq-· 
            (renₜ-≡ₜ S (inst (subₜ-weaken (renₜ r f) v'))) eq-refl))) 
        (eq-trans 
          (eq-λ eq-β) 
        (eq-trans (eq-λ (eq-· eq-refl (inst (subₜ-weaken (renₜ S v') _)))) eq-refl)))
      (eq-trans 
        (inst (subₜ-weaken (renₜ r (⇑ₙₑ n)) v')) 
        (eq-sym (inst (↻-ren-⇑ₙₑ r n)))))))) , 
    (λ {Δ} → sound {Δ})))))
    where 
      sound : SoundKripkeNE 
              (`λ (renₜ S (renₜ r f) · ` Z · renₜ S v'))
              (λ {Δ'} r₁ x₁ → apply V' r₁ (φ (r₁ ∘ r) x₁))
      sound r₁ n = 
        subst-⟦⟧≈ 
          (eq-trans 
            (eq-trans 
              (eq-· 
                (eq-· 
                  (inst (trans (renₜ-id _) (renₜ-comp r r₁  f))) 
                  (inst (renₜ-id _))) 
                eq-refl) 
              (eq-· 
                (eq-· (inst (subₜ-weaken-over-lift r₁ (renₜ r f) _)) eq-refl) 
                (inst (subₜ-weaken-over-lift r₁ v' _)))) 
            (eq-sym eq-β)) 
          (sound-f (r₁ ∘ r) n id (ren-⟦⟧≈ r₁ rel-v))     
sound-Σ {κ₁ = R[ κ ]} ρ {v} {φ $ n} (f , eq , sound-f) = 
  (`λ (weakenₜ Σ · (weakenₜ f · ` Z))) , 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Σ (eq-trans eq-map-∘ eq-refl))) , 
  λ r m → subst-⟦⟧≈ 
    (eq-· eq-refl (eq-sym m)) 
    (subst-⟦⟧≈ 
      (eq-sym eq-β) 
      (sound-Σ id 
        (subst-⟦⟧≈ 
          (eq-· 
            (inst (subₜ-weaken-over-lift r f (⇑ (η-norm _)))) 
            m)
          (sound-f r m))))
sound-Σ {κ₁ = κ₁ `→ κ₂} ρ₁ {f} {row (n , P) _} (eq , rel) ρ₂ {v} {V} rel-v = 
  subst-⟦⟧≈ (eq-sym (eq-Σ-assoc)) (sound-Σ ρ₂ {renₜ ρ₂ f ?? v} 
  ((eq-trans 
    (eq-· 
      (eq-· 
        eq-refl 
        (renₜ-≡ₜ ρ₂ eq)) 
      eq-refl) 
  (eq-trans 
    (eq-· eq-β eq-refl) 
  (eq-trans 
    eq-β 
  (eq-trans 
    eq-map 
  (eq-row 
    (reify-⟦⟧≈ᵣ (map-apply n P ρ₂ rel v V rel-v))))))) , 
  refl-⟦⟧≈ᵣ (map-apply n P ρ₂ rel v V rel-v)))
sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {f} {l ▹ F} (eq , sound-F) r₂ {v} {V} rel-V = 
  subst-⟦⟧≈ (eq-sym (eq-Σ-assoc)) 
    (sound-Σ r₂ 
      ((eq-trans 
        (eq-· (eq-· eq-refl (renₜ-≡ₜ r₂ eq)) eq-refl) 
        (eq-trans (eq-· eq-β eq-refl) 
        (eq-trans 
          eq-β 
        (eq-trans 
          eq-▹$ 
          (eq-▹ 
            (inst (trans (subₜ-weaken (renₜ r₂ (⇑ₙₑ l)) v) (sym (↻-ren-⇑ₙₑ r₂ l)))) 
            (eq-trans 
              eq-β 
            (eq-trans 
              eq-β 
            (eq-trans 
              (inst (sym (subₜ-comp (renₜ (liftₜ S)
              (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))))))) 
            (eq-trans 
              (inst (sym (↻-subₜ-renₜ (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z))))))))) 
            (eq-trans 
              (inst 
                (subₜ-cong {σ₂ = extendₜ ` (renₜ id v)} 
                (λ { Z → trans (subₜ-weaken v _) (sym (renₜ-id v)) ; (S x₁) → refl }) 
                (renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))))) 
              (eq-trans 
                (eq-sym 
                  (eq-β {τ₁ = renₜ (liftₜ r₂) (⇑ (reify (F S (reflect (` Z)))))} {renₜ id v})) 
              (reify-⟦⟧≈ (sound-F r₂ (ren-⟦⟧≈ id rel-V)))))))))))))) , 
    refl-⟦⟧≈ (sound-F r₂ {_} {renSem id V} (ren-⟦⟧≈ id rel-V))))
  
sound-Σ {κ₁ = κ₁ `→ κ₂} r₁ {f} {(V₂ ∖ V₁) {nr}} rel r₂ {v} {V} rel-V = 
  subst-⟦⟧≈ 
    (eq-· (eq-· eq-refl (eq-sym (renₜ-≡ₜ r₂ (eq-trans (rel .fst) (↻-⇑-reify-∖ V₂ V₁ {nr}))))) eq-refl) 
  (subst-⟦⟧≈ 
    (eq-sym eq-Σ-assoc) 
  (sound-Σ r₂ 
    (eq-trans 
      (eq-trans 
        (eq-· eq-β eq-refl) 
      (eq-trans 
          eq-β 
      (eq-trans 
        eq-$-∖ 
      (eq-∖ 
        (eq-trans 
          (eq-$ eq-refl (inst (subₜ-weaken (renₜ r₂ (⇑ (reify V₂))) v))) 
          (reify-⟦⟧≈ 
            {V = apply V ⟨$⟩ renSem r₂ V₂} 
            (cong-$⟦⟧≈ 
              (`λ (` Z · renₜ S v)) 
              (apply V) 
              (renₜ r₂ (⇑ (reify V₂))) 
              (renSem r₂ V₂) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≈ r₂ (rel .snd .fst))))) 
        ((eq-trans 
          (eq-$ eq-refl (inst (subₜ-weaken (renₜ r₂ (⇑ (reify V₁))) v))) 
          (reify-⟦⟧≈ 
            {V = apply V ⟨$⟩ renSem r₂ V₁} 
            (cong-$⟦⟧≈ 
              (`λ (` Z · renₜ S v)) 
              (apply V) 
              (renₜ r₂ (⇑ (reify V₁))) 
              (renSem r₂ V₁) 
              (sound-apply v V rel-V) 
              (ren-⟦⟧≈ r₂ (rel .snd .snd)))))))))) 
    (eq-sym 
      (↻-⇑-reify-∖ 
        (apply V ⟨$⟩ renSem r₂ V₂) (apply V ⟨$⟩ renSem r₂ V₁) {notRowLiteral$ (nrRenSem' r₂ V₂ V₁ nr)})) , 
    (refl-⟦⟧≈ (cong-$⟦⟧≈ (`λ (` Z · renₜ S v)) (apply V)
                 (renₜ r₂ (⇑ (reify V₂))) (renSem r₂ V₂) (sound-apply v V rel-V) (ren-⟦⟧≈ r₂ (rel .snd .fst))) , 
    refl-⟦⟧≈ (cong-$⟦⟧≈ (`λ (` Z · renₜ S v)) (apply V)
                 (renₜ r₂ (⇑ (reify V₁))) (renSem r₂ V₁) (sound-apply v V rel-V) (ren-⟦⟧≈ r₂ (rel .snd .snd)))))))
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {row (n , P) _} (eq , rel) =
  eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  (eq-trans 
    eq-map 
    (eq-row (reify-⟦⟧≈ᵣ (map-Σ n P rel))))) , 
  refl-⟦⟧≈ᵣ (map-Σ {nl = nl} n P rel)
sound-Σ {κ₁ = R[ κ ]} {nl = nl} ρ {v} {l ▹ τ} (eq , rel) = 
  (eq-trans (eq-· eq-refl eq) (eq-trans eq-Σ (eq-trans eq-▹$ (eq-▹ eq-refl (reify-⟦⟧≈ (sound-Σ id rel)))))) , 
  (refl-⟦⟧≈ (sound-Σ {nl = nl} id rel))
sound-Σ {κ₁ = R[ κ ]} {nl = nl} r {v} {(ρ₂ ∖ ρ₁) {nr}} (eq , rel₂ , rel₁) = 
  (eq-trans 
    (eq-· eq-refl eq) 
  (eq-trans 
    eq-Σ 
  (eq-trans 
    (eq-$ eq-refl (↻-⇑-reify-∖ ρ₂ ρ₁ {nr})) 
  (eq-trans 
    eq-$-∖ 
  (eq-trans 
    (eq-∖ (eq-sym eq-Σ) (eq-sym eq-Σ)) 
  (eq-trans 
    (eq-∖ (reify-⟦⟧≈ (sound-Σ id rel₂)) (reify-⟦⟧≈ (sound-Σ id rel₁))) 
  (eq-trans (eq-sym (↻-⇑-reify-∖ ((λ ρ → ΣV) ⟨$⟩ ρ₂) ((λ ρ → ΣV) ⟨$⟩ ρ₁) {nr = notRowLiteral$ nr})) eq-refl))))))) , (refl-⟦⟧≈ (sound-Σ {nl = nl} id rel₂)) , ((refl-⟦⟧≈ (sound-Σ {nl = nl} id rel₁)))

map-Σ zero P rel = tt
map-Σ {nl = nl} (suc n) P ((refl , rel-fzero) , rel-fsuc) = (refl , sound-Σ {nl = nl} id rel-fzero) , (map-Σ n (P ∘ fsuc) rel-fsuc)


--------------------------------------------------------------------------------
-- Fundamental lemma  

fund-⟦⟧≈ : ∀ (τ : Type Δ₁ κ){σ : Substitution Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≈ₑ η  → ⟦ sub σ τ ⟧≈ (⟦ τ ⟧ₜ η)

--------------------------------------------------------------------------------
-- Fundamental lemma for rows

fund-⟦⟧≈ᵣ : ∀ (xs : RowLiteral (Type Δ₁ κ)){σ : Substitution Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≈ₑ η  → ⟦ sub σ xs ⟧≈ᵣ (⟦ xs ⟧ᵣ η)
fund-⟦⟧≈ᵣ [] e = tt
fund-⟦⟧≈ᵣ ((l , τ) ∷ xs) e = (refl , fund-⟦⟧≈ τ e ) , fund-⟦⟧≈ᵣ xs e

--------------------------------------------------------------------------------
-- mapping an application over a row is application of the semantic row.

fund-⟦⟧≈-map-app : ∀ {Δ₂ : KEnv} {κ₁ : Kind} (n : ℕ) (P : Fin n → Label × SemType Δ₂ κ₁) →  
                (τ₁ : Type Δ₁ (κ₁ `→ κ₂)) → 
                (rel : ⟦ ⇑ᵣ (reifyRow' n P) ⟧≈ᵣ (n , P)) → 
                {σ : Substitution Δ₁ Δ₂} → {η : SemEnv Δ₁ Δ₂} → 
                ⟦ σ ⟧≈ₑ η → 
                ⟦ map (map₂ (_·_ (sub σ τ₁))) (⇑ᵣ (reifyRow' n P)) ⟧≈ᵣ (n , (λ x → P x .fst , ⟦ τ₁ ⟧ₜ η id (P x .snd)))

fund-⟦⟧≈-map-app zero P _ _ _ = tt
fund-⟦⟧≈-map-app (suc n) P τ₁ (rel-fzero , rel-fsuc) {σ} e =
  (refl , (subst-⟦⟧≈ (eq-· (inst (renₜ-id (sub σ τ₁))) eq-refl) (fund-⟦⟧≈ τ₁ e id (rel-fzero .snd)))) ,
  fund-⟦⟧≈-map-app n (P ∘ fsuc) τ₁ rel-fsuc e

--------------------------------------------------------------------------------
-- Fundamental lemma for predicates
          
fund-⟦⟧≈Pred : ∀ (π : Pred (Type Δ₁ R[ κ ])){σ : Substitution Δ₁ Δ₂}{η : SemEnv Δ₁ Δ₂} → 
          ⟦ σ ⟧≈ₑ η → (sub σ π) ≡ₚ ⇑ₚ (⟦ π ⟧ₚ η)           
fund-⟦⟧≈Pred (ρ₁ · ρ₂ ~ ρ₃) e = (reify-⟦⟧≈ (fund-⟦⟧≈ ρ₁ e)) eq-· (reify-⟦⟧≈ (fund-⟦⟧≈ ρ₂ e)) ~ (reify-⟦⟧≈ (fund-⟦⟧≈ ρ₃ e))
fund-⟦⟧≈Pred (ρ₁ ≲ ρ₂) e = (reify-⟦⟧≈ (fund-⟦⟧≈ ρ₁ e)) eq-≲ (reify-⟦⟧≈ (fund-⟦⟧≈ ρ₂ e))

--------------------------------------------------------------------------------
-- Fundamental lemma definition 

fund-⟦⟧≈ (` α) {σ} {η} e = e α
fund-⟦⟧≈ (`λ τ) {σ} {η} e ρ {v} {V} q = 
  subst-⟦⟧≈ 
    (eq-sym eq-β) 
    (subst-⟦⟧≈ 
      (eq-trans 
        (eq-trans 
          (inst (subₜ-cong (λ { Z → refl ; (S x) → trans (renₜ-sub-id ρ (σ x)) (↻-subₜ-renₜ (σ x)) }) τ)) 
          (inst (subₜ-comp τ))) 
        (inst (↻-subₜ-renₜ (sub (liftsₜ σ) τ)))) 
      (fund-⟦⟧≈ τ (extend-⟦⟧≈ (ren-⟦⟧≈ ρ ∘ e) q)))
fund-⟦⟧≈ (τ₁ · τ₂) {σ} {η} e  = 
  subst-⟦⟧≈ 
    (eq-· (inst (renₜ-id (sub σ τ₁))) eq-refl) 
    (fund-⟦⟧≈ τ₁ e id (fund-⟦⟧≈ τ₂ e))
fund-⟦⟧≈ (τ₁ `→ τ₂) {σ} {η} e = eq-→ (fund-⟦⟧≈ τ₁ e) (fund-⟦⟧≈ τ₂ e)
fund-⟦⟧≈ (`∀ τ) {σ} {η} e = eq-∀ (fund-⟦⟧≈ τ {liftsₜ σ} {lifte η} (weaken-⟦⟧≈ e))
fund-⟦⟧≈ (μ τ) {σ} {η} e = eq-μ
    (eq-trans 
        (eq-η {f = sub σ τ}) 
        (eq-λ (fund-⟦⟧≈ τ e S eq-refl)))
fund-⟦⟧≈ (π ⇒ τ) {σ} {η} e = eq-⇒ (fund-⟦⟧≈Pred π e) (fund-⟦⟧≈ τ e)
fund-⟦⟧≈ (lab l) {σ} {η} e = eq-refl
fund-⟦⟧≈ (Π {notLabel = nl}) {σ} {η} e = sound-Π {nl = nl}
fund-⟦⟧≈ Σ {σ} {η} e = sound-Σ
fund-⟦⟧≈ (τ₁ $ τ₂) {σ} {η} e with ⟦ τ₂ ⟧ₜ η | inspect (λ x → ⟦ x ⟧ₜ η) τ₂ | fund-⟦⟧≈ τ₂ e 
... | row (n , P) _ | [[ eq ]] | eqₜ , rel = 
    (eq-trans 
      (eq-$ 
        eq-refl
        eqₜ) 
    (eq-trans 
      eq-map 
      (eq-row (reify-⟦⟧≈ᵣ (fund-⟦⟧≈-map-app n P τ₁ rel e) )))) , 
    refl-⟦⟧≈ᵣ (fund-⟦⟧≈-map-app n P τ₁ rel e)  
... | l ▹ τ | [[ eq ]] | eqₜ , rel = 
  (eq-trans 
    (eq-$ eq-refl eqₜ) 
    (eq-trans 
      eq-▹$ 
      (eq-▹ 
        eq-refl 
        (eq-trans 
          (eq-· 
            (inst (sym (renₜ-id (sub σ τ₁)))) 
            eq-refl) 
          (reify-⟦⟧≈ (fund-⟦⟧≈ τ₁ e id rel)))))) , 
  refl-⟦⟧≈ (fund-⟦⟧≈ τ₁ e id rel)
fund-⟦⟧≈  {Δ₂ = Δ₂} ( _$_ {κ₁ = κ₁} {κ₂ = κ₂} τ₁ τ₂) {σ} {η} e | (ρ₂ ∖ ρ₁) {nr} | [[ eq ]] | t-eq , rel₂ , rel₁ = 
  (eq-trans 
    (eq-$ eq-refl t-eq) 
    (cong-$⟦⟧≈ (sub σ τ₁) (⟦ τ₁ ⟧ₜ η) (⇑ (reify ((ρ₂ ∖ ρ₁) {nr}))) ((ρ₂ ∖ ρ₁) {nr}) (fund-⟦⟧≈ τ₁ e) (eq-refl , rel₂ , rel₁) .fst)) , 
    refl-⟦⟧≈ (cong-$⟦⟧≈ (sub σ τ₁) (⟦ τ₁ ⟧ₜ η) (⇑ (reify ρ₂)) ρ₂ (fund-⟦⟧≈ τ₁ e) rel₂) , 
    refl-⟦⟧≈ (cong-$⟦⟧≈ (sub σ τ₁) (⟦ τ₁ ⟧ₜ η) (⇑ (reify ρ₁)) ρ₁ (fund-⟦⟧≈ τ₁ e) rel₁)
fund-⟦⟧≈ (τ₁ $ τ₂) {σ} {η} e | φ $ n | [[ eq ]] | (f , eq-f , rel-f) with ⟦ τ₁ ⟧ₜ η | fund-⟦⟧≈ τ₁ e
... | F | rel-F = cong-$⟦⟧≈ (sub σ τ₁) F (sub σ τ₂) (φ $ n) rel-F (f , eq-f , rel-f)
fund-⟦⟧≈ (⦅ xs ⦆ oxs) {σ} {η} e with fund-⟦⟧≈ᵣ xs e
fund-⟦⟧≈ (⦅ [] ⦆ tt) {σ} {η} e | tt = eq-refl , tt
fund-⟦⟧≈ (⦅ (l , τ) ∷ xs ⦆ oxs) {σ} {η} e | ((refl , ih-τ) , ih-xs) = eq-row (eq-cons refl (reify-⟦⟧≈ (fund-⟦⟧≈ τ e)) (reify-⟦⟧≈ᵣ ih-xs)) , ((refl , refl-⟦⟧≈ ih-τ) , refl-⟦⟧≈ᵣ ih-xs)
fund-⟦⟧≈ (ρ₂ ∖ ρ₁) {σ} {η} e with ⟦ ρ₂ ⟧ₜ η | fund-⟦⟧≈ ρ₂ e 
fund-⟦⟧≈ (ρ₂ ∖ ρ₁) {σ} {η} e | φ $ n | (f , eq-f , rel-f) with 
  ⟦ ρ₁ ⟧ₜ η | fund-⟦⟧≈ ρ₁ e 
... | φ₂ $ n₂   | (g , eq-g , rel-g) = (eq-∖ (reifySoundKripkeNE-≡ₜ eq-f rel-f) (reifySoundKripkeNE-≡ₜ eq-g rel-g)) , 
  (f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f) , 
  (g , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-g) , rel-g)
... | x₂ ▹ x₃  | ih' = (eq-∖ (reifySoundKripkeNE-≡ₜ eq-f rel-f) (ih' .fst)) , ((f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f) , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = 
  (eq-∖ (reifySoundKripkeNE-≡ₜ eq-f rel-f) (eq-trans (ih' .fst) (eq-row reflᵣ))) , 
  ((f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f)  , ((eq-row reflᵣ) , (ih' .snd)))
... | c ∖ c₁   | ih' = 
    (eq-∖ (reifySoundKripkeNE-≡ₜ eq-f rel-f) (ih' .fst)) , 
    ((f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f) , (eq-refl , (ih' .snd .fst) , (ih' .snd .snd)))
fund-⟦⟧≈ (ρ₂ ∖ ρ₁) {σ} {η} e | x₁ ▹ x₂ | (eq , rel) with ⟦ ρ₁ ⟧ₜ η | fund-⟦⟧≈ ρ₁ e 
... | φ $ n    | (f , eq-f , rel-f) = 
   eq-∖ eq (reifySoundKripkeNE-≡ₜ eq-f rel-f) , 
    (eq-refl , rel) , (f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f)
... | x₂ ▹ x₃  | ih' = eq-∖ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
... | row ρ x₂ | ih' = eq-∖ eq (eq-trans (ih' .fst) (eq-row reflᵣ)) , (eq-refl , rel) , (eq-row reflᵣ , (ih' .snd))
... | c ∖ c₁   | ih' = eq-∖ eq (ih' .fst) , (eq-refl , rel) , (eq-refl , (ih' .snd))
fund-⟦⟧≈ (ρ₂ ∖ ρ₁) {σ} {η} e | row (n , P) oP | ih with ⟦ ρ₁ ⟧ₜ η | fund-⟦⟧≈ ρ₁ e 
... | φ $ n    | (f , eq-f , rel-f) = 
  eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (reifySoundKripkeNE-≡ₜ eq-f rel-f) , 
  ((eq-row reflᵣ , (ih .snd)) , f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f)
... | x₂ ▹ x₃  | ih' = eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , (ih' .snd)))
... | row (m , Q) oQ | ih' = 
  eq-trans 
    (eq-∖ (ih .fst) (ih' .fst)) 
    (eq-trans 
      (eq-compl {ozs = fromWitness (ordered-∖s {xs = ⇑ᵣ (reifyRow (n , P))}
                {ys = ⇑ᵣ (reifyRow (m , Q))} (⇑ₒ {ρ = reifyRow' n P} (reifyRowOrdered {ρ = n , P} oP)))}) 
      (eq-row (reify-⟦⟧≈ᵣ (cong-compl⟦⟧≈ (ih .snd) (ih' .snd))))) , 
  refl-⟦⟧≈ᵣ (cong-compl⟦⟧≈ (ih .snd) (ih' .snd))
... | c ∖ c₁   | ih' = eq-∖ (eq-trans (ih .fst) (eq-row reflᵣ)) (ih' .fst) , ((eq-row reflᵣ , (ih .snd)) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
fund-⟦⟧≈ (ρ₂ ∖ ρ₁) {σ} {η} e | c ∖ c₁ | ih with ⟦ ρ₁ ⟧ₜ η | fund-⟦⟧≈ ρ₁ e 
... | φ $ n    | (f , eq-f , rel-f) = 
  eq-∖ (ih .fst) (reifySoundKripkeNE-≡ₜ eq-f rel-f) , 
  ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (f , eq-sym (reifySoundKripkeNE-≡ₜ eq-refl rel-f) , rel-f))
... | x₂ ▹ x₃  | ih' = eq-∖ (ih .fst) (ih' .fst) , ((eq-refl , (ih .snd)) , (eq-refl , (ih' .snd)))
... | row ρ x₂ | ih' = eq-trans (eq-∖ (ih .fst) (ih' .fst)) (eq-∖ eq-refl (eq-row reflᵣ)) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-row reflᵣ , (ih' .snd)))
... | c ∖ c₁   | ih' = eq-∖ (ih .fst) (ih' .fst) , ((eq-refl , ((ih .snd .fst) , (ih .snd .snd))) , (eq-refl , ((ih' .snd .fst) , (ih' .snd .snd))))
fund-⟦⟧≈ (l ▹ τ) {σ} {η} e with ⟦ l ⟧ₜ η | fund-⟦⟧≈ l e
... | ne x₁ | ih = (eq-▹ ih (reify-⟦⟧≈ (fund-⟦⟧≈ τ e))) , refl-⟦⟧≈ (fund-⟦⟧≈ τ e)
... | lab l' | ih = eq-trans (eq-▹ eq-refl (reify-⟦⟧≈ (fund-⟦⟧≈ τ e))) (eq-labTy ih) , 
                    (refl , (refl-⟦⟧≈ (fund-⟦⟧≈ τ e))) , 
                    tt

--------------------------------------------------------------------------------
-- Fundamental theorem when substitution is the identity

⊢⟦_⟧≈ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≈ ⟦ τ ⟧ₜ idEnv
⊢⟦ τ ⟧≈ = subst-⟦⟧≈ (inst (sub-id τ)) (fund-⟦⟧≈ τ idEnv-⟦⟧≈)

--------------------------------------------------------------------------------
-- Consistency

consistency :  ∀ {Δ₁} {κ} → (τ : Type Δ₁ κ) → τ ≡ₜ ⇑ (⇓ₜ τ) 
consistency τ = reify-⟦⟧≈ (⊢⟦ τ ⟧≈)

------------------------------------------------------------------------------
-- If τ₁ normalizes to ⇓ₜ τ₂ then the embedding of τ₁ is equivalent to τ₂

embed-≡ₜ : ∀ {τ₁ : NormalType Δ κ} {τ₂ : Type Δ κ}  → τ₁ ≡ (⇓ₜ τ₂) → ⇑ τ₁ ≡ₜ τ₂
embed-≡ₜ {τ₁ = τ₁} {τ₂} refl = eq-sym (consistency τ₂) 

--------------------------------------------------------------------------------
-- consistency in lifted environments

consistency-liftsₜ : ∀ {Δ₁ : KEnv} {κ₁ : Kind} → (τ : Type (Δ₁ , κ₁) κ) → sub (liftsₜ `) τ ≡ₜ ⇑ (reify (⟦ τ ⟧ₜ (lifte idEnv)))
consistency-liftsₜ τ = 
  reify-⟦⟧≈ (fund-⟦⟧≈ τ (weaken-⟦⟧≈ {σ = `} {η = idEnv} idEnv-⟦⟧≈))

--------------------------------------------------------------------------------
-- Consistency claim, for rows

consistencyRow : ∀ (xs : RowLiteral (Type Δ κ)) → xs ≡ᵣ ⇑ᵣ (⇓ᵣ xs)
consistencyRow xs = reify-⟦⟧≈ᵣ (subst-⟦⟧≈ᵣ (instᵣ (subRowₜ-id xs)) (fund-⟦⟧≈ᵣ xs idEnv-⟦⟧≈)) 
