-- 
module Rome.Metatheory.NBE.Soundness where

open import Rome.Prelude

open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Substitution
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.Properties.Renaming

open import Rome.NormalTypes.NBE.Syntax
open import Rome.NormalTypes.NBE.Normalization
open import Rome.NormalTypes.NBE.Renaming

open import Rome.Metatheory.NBE.Soundness.Relation public 
open import Rome.Metatheory.NBE.Soundness.Congruence public 
open import Rome.Metatheory.NBE.Soundness.Commutativity public

open import Rome.Types.Equivalence



--------------------------------------------------------------------------------
-- Equivalence of membership in syntactic and semantic spaces

∈L→∈Row : ∀ {Δ₂ : KEnv} {κ : Kind} {l : Label} 
            {η₁ : SemEnv Δ₁ Δ₂} 
            {ys : RowLiteral (Type Δ₁ κ)} → 
            l ∈L ys → 
            l ∈Row (⟦ ys ⟧ᵣ η₁ .snd)
∈L→∈Row {ys = ys} Here = fzero , refl
∈L→∈Row {ys = (l' , τ) ∷ ys} (There ev) = (fsuc (∈L→∈Row ev .fst)) , (∈L→∈Row ev .snd)

∈Row→∈L : ∀ {Δ₂ : KEnv} {κ : Kind} 
            {l : Label} {η₁ : SemEnv Δ₁ Δ₂} 
            {ys : RowLiteral (Type Δ₁ κ)} → 
            l ∈Row (⟦ ys ⟧ᵣ η₁ .snd) → 
            l ∈L ys
∈Row→∈L {ys = (l , τ) ∷ ys} (fzero , refl) = Here
∈Row→∈L {ys = (l , τ) ∷ ys} (fsuc i , refl) = There (∈Row→∈L (i , refl))

--------------------------------------------------------------------------------
-- Commutativity of syntactic and semantic complement

↻-syn/sem-compl : ∀ {Δ₂ : KEnv} {κ : Kind} 
                    {η₁ η₂ : SemEnv Δ₁ Δ₂} (xs ys : RowLiteral (Type Δ₁ κ)) → 
                  η₁ ≈e η₂ → 
                  (⟦ xs ⟧ᵣ η₁ ∖v ⟦ ys ⟧ᵣ η₁) ≈ᵣ ⟦ (xs ∖s ys) ⟧ᵣ η₂
↻-syn/sem-compl [] ys e = refl , (λ ())
↻-syn/sem-compl {η₁ = η₁} {η₂} ((l , τ) ∷ xs) ys e with 
    l ∈Row? (⟦ ys ⟧ᵣ η₁ .snd) | l ∈L? ys
... | yes p                   | yes q = ↻-syn/sem-compl xs ys e
... | yes p                   | no q = ⊥-elim (q (∈Row→∈L p)) 
... | no q                    | yes p = ⊥-elim (q (∈L→∈Row p)) 
... | no p                    | no q  with 
    compl (⟦ xs ⟧ᵣ η₁ .snd) (⟦ ys ⟧ᵣ η₁ .snd) 
  | ⟦ (xs ∖s ys) ⟧ᵣ η₂ 
  | ↻-syn/sem-compl xs ys e
↻-syn/sem-compl ((l , τ) ∷ xs) ys e 
  | no p | no q | x | y | (refl , ih') = 
    refl , λ { fzero → refl , idext e τ ; (fsuc i) → ih' i }

--------------------------------------------------------------------------------
-- Commutativity of syntactic/semantic complement as a strict equality

↻-∖s-∖v : ∀ {κ : Kind} {n m}
          (P : Fin n → Label × SemType Δ κ) → 
          (Q : Fin m → Label × SemType Δ κ) → 
          reifyRow' n P ∖s reifyRow' m Q ≡
          reifyRow (compl P Q)
↻-∖s-∖v {n = zero} P Q = refl
↻-∖s-∖v {n = suc n} {m} P Q with 
  P fzero .fst ∈L? reifyRow' m Q | P fzero .fst ∈Row? Q 
... | yes p                      | yes q = ↻-∖s-∖v (P ∘ fsuc) Q
... | yes p                      | no  q = ⊥-elim (q (In p))
  where
    In : ∀ {l} {m} {κ : Kind}  
            {Q : Fin m → Label × SemType Δ κ} → 
            l ∈L reifyRow' m Q → 
            l ∈Row Q
    In {l} {m = suc m} Here = fzero , refl
    In {m = suc m} (There ev) = fsuc (In ev .fst) ,  In ev .snd
... | no  p | yes q = ⊥-elim (p (In q))
  where
    In : ∀ {l} {m} {κ : Kind} 
           {Q : Fin m → Label × SemType Δ κ} → 
           l ∈Row Q → 
           l ∈L reifyRow' m Q
    In {l} {m = suc m} (fzero , refl) = Here
    In {l} {m = suc m} (fsuc i , eq) = There (In (i , eq))
    
... | no  p | no  q = ap₂ _∷_ refl (↻-∖s-∖v (P ∘ fsuc) Q)   

--------------------------------------------------------------------------------
-- Normalization commutes with complement

⇓ᵣ-preserves-labels : ∀ (l : Label) (xs : RowLiteral (Type Δ₁ κ)) → 
                          l ∈L xs ↔ l ∈L ⇓ᵣ xs
⇓ᵣ-preserves-labels l [] = (λ ()) , (λ ())
⇓ᵣ-preserves-labels l (x ∷ xs) = 
  (λ { Here → Here ; (There l∈xs) → There (⇓ᵣ-preserves-labels l xs .to l∈xs) }) , 
  λ { Here → Here ; (There l∈⇓ᵣxs) → There (⇓ᵣ-preserves-labels l xs .from l∈⇓ᵣxs) }


↻-⇓ᵣ-∖s : ∀ (ys xs : RowLiteral (Type Δ κ)) → ⇓ᵣ (ys ∖s xs) ≡ ⇓ᵣ ys ∖s ⇓ᵣ xs 
↻-⇓ᵣ-∖s [] xs = refl
↻-⇓ᵣ-∖s ((l , τ) ∷ ys) xs with l ∈L? xs | l ∈L? ⇓ᵣ xs
... | yes p | yes q  = ↻-⇓ᵣ-∖s ys xs
... | no  p | yes q  = ⊥-elim (p (⇓ᵣ-preserves-labels l xs .from q)) 
... | yes p | no  q  = ⊥-elim (q (⇓ᵣ-preserves-labels l xs .to p)) 
... | no  p | no  q  = ap ((l , ⇓ₜ τ) ∷_) (↻-⇓ᵣ-∖s ys xs)

-------------------------------------------------------------------------------
-- Fundamental theorem (soundness)

fund-≈ : ∀ {Δ₂ : KEnv} {κ : Kind} {τ₁ τ₂ : Type Δ₁ κ} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
       η₁ ≈e η₂ → τ₁ ≡ₜ τ₂ → ⟦ τ₁ ⟧ₜ η₁ ≈ ⟦ τ₂ ⟧ₜ η₂
fund-≈-pred : ∀ {π₁ π₂ : Pred (Type Δ₁ R[ κ ])} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
            η₁ ≈e η₂ → π₁ ≡ₚ π₂ → ⟦ π₁ ⟧ₚ η₁ ≡ ⟦ π₂ ⟧ₚ η₂
fund-≈ᵣ : ∀ {Δ₂ : KEnv} {κ : Kind} 
              {ρ₁ ρ₂ : RowLiteral (Type Δ₁ κ)} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
            η₁ ≈e η₂ → ρ₁ ≡ᵣ ρ₂ → ⟦ ρ₁ ⟧ᵣ η₁ ≈ᵣ ⟦ ρ₂ ⟧ᵣ η₂

fund-≈-pred e (τ₁ eq-≲ τ₂) = ap₂ _≲_ (reify-≈ (fund-≈ e τ₁)) (reify-≈ (fund-≈ e τ₂))
fund-≈-pred e (τ₁ eq-· τ₂ ~ τ₃) rewrite
    reify-≈ (fund-≈ e τ₁) 
  | reify-≈ (fund-≈ e τ₂) 
  | reify-≈ (fund-≈ e τ₃) = refl

fund-≈ {τ₁ = τ} e eq-refl = idext e τ
fund-≈ e (eq-sym eq) = sym-≈ (fund-≈ (sym-≈ ∘ e) eq)
fund-≈ e (eq-trans eq₁ eq₂) = trans-≈ (fund-≈ (refl-≈ₗ ∘ e) eq₁) (fund-≈ e eq₂)
fund-≈ e (eq-→ eq-τ eq-υ) = ap₂ _`→_ (fund-≈ e eq-τ) (fund-≈ e eq-υ)
fund-≈ {κ = κ} e (eq-· eq₁ eq₂) = cong-App (fund-≈ e eq₁) (fund-≈ e eq₂)
fund-≈ e (eq-∀ eq) = ap `∀ (fund-≈ (extend-≈ (ren-≈ S ∘ e) (reflect-≈ refl)) eq)
fund-≈ {η₁ = η₁} {η₂} e (eq-μ {τ = τ} {υ} eq) 
  with ⟦ τ ⟧ₜ η₁ | ⟦ υ ⟧ₜ η₂ | fund-≈ e eq
... |  y         | y₁        | Unif-F , Unif-G , Ext = 
  ap μ (ap `λ (Ext S refl))
fund-≈ e (eq-λ {τ = τ} {υ = υ} eq) = 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≈ 
      (↻-renSem-eval ρ₂ τ (extend-≈ (λ x → ren-≈ ρ₁ (e x)) q)) 
      (idext (λ { Z → ren-≈ ρ₂ (refl-≈ᵣ q)
                ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (e x)) }) τ))  , 
    (λ ρ₁ ρ₂ V₁ V₂ q → trans-≈ 
      (↻-renSem-eval ρ₂ υ (extend-≈ (λ x → ren-≈ ρ₁ (sym-≈ (e x))) q)) 
      (idext (λ { Z → ren-≈ ρ₂ (refl-≈ᵣ q)
                ; (S x) → sym-≈ (renSem-comp-≈ ρ₁ ρ₂ (sym-≈ (e x))) }) υ)), 
    λ ρ q → fund-≈ (extend-≈ (λ x → ren-≈ ρ (e x)) q) eq
fund-≈ {η₁ = η₁} {η₂ = η₂} e (eq-η {f = f}) = 
  fst (idext e f) , 
  fst (snd (idext {η₁ = η₁} {η₂ = η₂} e (`λ (weakenₜ f · (` Z))))) , 
  λ r {V₁} {V₂} v → weaken-η-≈ f e r v V₂ (refl-≈ᵣ v)

fund-≈ {η₁ = η₁} {η₂ = η₂} e (eq-β {τ₁ = τ₁} {τ₂}) = 
    trans-≈ 
        (idext 
            {η₂ = extende η₁ (⟦ τ₂ ⟧ₜ η₁)} 
            (λ { Z → idext {η₂ = η₁}  (refl-≈ₗ ∘ e) τ₂
           ; (S x) → renSem-id-≈ (refl-≈ₗ  (e x)) }) τ₁) 
        (sym-≈ 
            (trans-≈ 
                ((↻-subₜ-eval τ₁ (sym-≈ ∘ e) (extendₜ ` τ₂))) 
                (idext (λ { Z → idext (refl-≈ₗ ∘ e) τ₂
                          ; (S x) → (refl-≈ₗ ∘ e) x }) τ₁)))
fund-≈ {η₁ = η₁} {η₂} e (eq-▹ {l₁ = l₁} {l₂} eq-l eq-τ) with ⟦ l₁ ⟧ₜ η₁ | ⟦ l₂ ⟧ₜ η₂ | fund-≈ e eq-l 
... | ne x | ne x | refl = (refl , refl) , fund-≈ e eq-τ
... | lab l | lab l | refl = refl , (λ { fzero → refl , fund-≈ e eq-τ } )
fund-≈ e (eq-⇒ eq-π eq-τ) = ap₂ _⇒_ (fund-≈-pred e eq-π) (fund-≈ e eq-τ)
fund-≈ e (eq-Π-assoc {ρ = ρ} {τ}) = 
  cong-Π 
    (cong-$ 
      (cong-apply (idext e τ))
      (ren-≈ id (idext e ρ))) 
fund-≈ e (eq-Σ-assoc {ρ = ρ} {τ}) =
  cong-Σ 
    (cong-$ 
      (cong-apply (idext e τ))
      (ren-≈ id (idext e ρ))) 
fund-≈ e (eq-Π {ρ = ρ} {nl}) = cong-$ (idext e (Π {notLabel = nl})) (idext e ρ)
fund-≈ e (eq-Σ {ρ = ρ} {nl}) = cong-$ (idext e (Σ {notLabel = nl})) (idext e ρ) 
fund-≈ e (eq-$ t u) = cong-$ (fund-≈ e t) (fund-≈ e u)
fund-≈ {Δ₁ = Δ₁} {κ = κ} {η₁ = η₁} {η₂} e (eq-map {κ₁ = κ₁} {κ₂} {F = F} {ρ = ρ} {ω}) = go ρ
  where
    go : (ρ : RowLiteral (Type Δ₁ κ₁)) → 
            (⟦ ρ ⟧ᵣ η₁ .fst ,
            (map₂ (⟦ F ⟧ₜ η₁ id) ∘ (⟦ ρ ⟧ᵣ η₁ .snd)))
          ≈ᵣ ⟦ map (map₂ (_·_ F)) ρ ⟧ᵣ η₂ 
    go [] = refl , (λ ())
    go (x ∷ ρ) with ⟦ ρ ⟧ᵣ η₁ | go ρ
    ... | n , P | refl , eq = refl , (λ { fzero → refl , (cong-App (idext e F) (idext e (x . snd))) ; (fsuc i) → eq i })
fund-≈ e (eq-row eq) = fund-≈ᵣ e eq
fund-≈ e (eq-lab refl) = refl
fund-≈ {η₁ = η₁} {η₂} e (eq-▹$ {l = l} {τ = τ} {F}) with ⟦ l ⟧ₜ η₁ | ⟦ l ⟧ₜ η₂ | idext e l
... | ne x | ne x | refl = (refl , refl) , cong-App (idext e F) (idext e τ)
... | lab l | lab l | refl = refl , λ { fzero → refl , idext e (F · τ) }
fund-≈ {η₁ = η₁} {η₂} e (eq-∖ eq₂ eq₁) = cong-∖V (fund-≈ e eq₂) (fund-≈ e eq₁)
fund-≈ {η₁ = η₁} {η₂} e (eq-labTy {l = l} {τ = τ} eq) with ⟦ l ⟧ₜ η₁ | fund-≈ e eq 
... | lab ℓ | refl = refl , (λ { fzero → refl , idext e τ })
fund-≈ {η₁ = η₁} {η₂} e (eq-$-∖ {F = F} {ρ₂} {ρ₁}) 
  with ⟦ ρ₂ ⟧ₜ η₁ | ⟦ ρ₂ ⟧ₜ η₂ | idext e ρ₂
fund-≈ {η₁ = η₁} {η₂} e (eq-$-∖ {F = F} {ρ₂} {ρ₁}) | x₁ ▹ x₂ | x₃ ▹ x₄ | fst₁ , snd₁ = 
  (fst₁ , idext e F .snd .snd id snd₁) , (cong-$ (idext e F) (idext e ρ₁))
fund-≈ {η₁ = η₁} {η₂} e (eq-$-∖ {F = F} {ρ₂} {ρ₁}) | x₁ ∖ x₂ | y₁ ∖ y₂ | fst₁ , snd₁ = 
  ((cong-$ (idext e F) fst₁) , (cong-$ (idext e F) snd₁)) , (cong-$ (idext e F) (idext e ρ₁))
fund-≈ {η₁ = η₁} {η₂} e (eq-$-∖ {F = F} {ρ₂} {ρ₁}) | φ₁ $ n₁ | φ₂ $ n₂ | ((refl , Unif-φ₁ , Unif-φ₂ , Ext-φ) , (refl , refl)) = 
  ((refl ,
  (λ r₁ r₂ n → trans-≈ 
      (idext e F .fst r₁ r₂ (φ₁ r₁ n) (φ₂ r₁ n) (Ext-φ r₁ n)) 
      (refl-Extₗ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≈ 
        (Unif-φ₂ r₁ r₂ n) 
        (sym-≈ (Ext-φ (r₂ ∘ r₁) (ren r₂ n)))))) , 
  (λ r₁ r₂ n → trans-≈
    (idext e F .snd .fst r₁ r₂ (φ₂ r₁ n) (φ₁ r₁ n)
     (sym-≈ (Ext-φ r₁ n)))
    (refl-Extᵣ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≈
      (Unif-φ₁ r₁ r₂ n) 
      (Ext-φ (r₂ ∘ r₁) (ren r₂ n))))) , 
  (λ r v → idext e F .snd .snd  r (Ext-φ r v))) , 
  (refl , refl)) ,
  (cong-$ (idext e F) (idext e ρ₁))
fund-≈ {η₁ = η₁} {η₂} e (eq-$-∖ {F = F} {ρ₂} {ρ₁}) | row (n , P) ω₂-1 | row (.n , P') ω₂-2 | refl , I
  with ⟦ ρ₁ ⟧ₜ η₁ | ⟦ ρ₁ ⟧ₜ η₂ | idext e ρ₁ 
... | x₃ ▹ x₄ | x₅ ▹ x₆ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , fst₂ , (idext e F .snd .snd id snd₂)
... | c₂ ∖ c₁ | d₂ ∖ d₁ | fst₂ , snd₂ = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , (cong-$ (idext e F) fst₂) , (cong-$ (idext e F) snd₂)
... | row (m , Q) ω₁-1 | row (.m , Q') ω₁-2 | refl , J = 
  ↻-⟨$⟩-∖V 
    (⟦ F ⟧ₜ η₁) (⟦ F ⟧ₜ η₂) 
    n m P P' {ω₂-1} {ω₂-2} 
    Q Q' {ω₁-1} {ω₁-2} 
    (idext e F) (refl , I) (refl , J)
... | φ₁ $ n₁ | φ₂ $ n₂ | ((refl , Unif-φ₁ , Unif-φ₂ , Ext-φ) , (refl , refl)) = 
  (refl , (λ i → I i .fst , idext e F .snd .snd id (I i .snd))) , 
  ((refl , 
  (λ r₁ r₂ n → trans-≈ 
      (idext e F .fst r₁ r₂ (φ₁ r₁ n) (φ₂ r₁ n) (Ext-φ r₁ n)) 
      (refl-Extₗ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≈ 
        (Unif-φ₂ r₁ r₂ n) 
        (sym-≈ (Ext-φ (r₂ ∘ r₁) (ren r₂ n)))))) , 
  (λ r₁ r₂ n → trans-≈
    (idext e F .snd .fst r₁ r₂ (φ₂ r₁ n) (φ₁ r₁ n)
     (sym-≈ (Ext-φ r₁ n)))
    (refl-Extᵣ (idext e F .snd .snd) (r₂ ∘ r₁) (trans-≈
      (Unif-φ₁ r₁ r₂ n) 
      (Ext-φ (r₂ ∘ r₁) (ren r₂ n))))) , 
  (λ r v → idext e F .snd .snd  r (Ext-φ r v))) , 
  (refl , refl))
fund-≈ {Δ₁ = Δ₁} {η₁ = η₁} {η₂} e (eq-compl {xs = xs} {ys}) = ↻-syn/sem-compl xs ys e
fund-≈ {η₁ = η₁} {η₂} e (eq-map-id {τ = τ}) = map-id-≈ (idext e τ) 
fund-≈ {η₁ = η₁} {η₂} e (eq-map-∘ {f = f} {g = g} {τ = τ}) = map-∘-≈ f g e id (idext e τ)


fund-≈ᵣ e eq-[] = refl , (λ ())
fund-≈ᵣ {η₁ = η₁} e (eq-cons {xs = xs} eq-l eq-τ eq-r) with 
 ⟦ xs ⟧ᵣ η₁ | fund-≈ᵣ e eq-r 
... | n , P | refl , eq = refl , (λ { fzero → eq-l , (fund-≈ e eq-τ) ; (fsuc i) → eq i })

-- An immediate consequence:
eval-refl-≈ : ∀ {Δ₂ : KEnv} {κ : Kind} {τ : Type Δ₁ κ} {η₁ η₂ : SemEnv Δ₁ Δ₂} → 
              η₁ ≈e η₂ → ⟦ τ ⟧ₜ η₁ ≈ ⟦ τ ⟧ₜ η₂
eval-refl-≈ {τ = τ} e = fund-≈ {τ₁ = τ} e eq-refl


-------------------------------------------------------------------------------
-- Soundness

soundness : ∀ {τ₁ τ₂ : Type Δ κ} → τ₁ ≡ₜ τ₂ → ⇓ₜ τ₁ ≡ ⇓ₜ τ₂
soundness eq = reify-≈ (fund-≈ idEnv-≈ eq)  

-------------------------------------------------------------------------------
-- Transporting along type equality

tr-≡ₜ : {τ : Type Δ κ} (B : (υ : NormalType Δ κ) → Set ℓ)
          {υ : Type Δ κ} (p : τ ≡ₜ υ) → B (⇓ₜ τ) → B (⇓ₜ υ)
tr-≡ₜ {τ = τ} B {υ = υ} p b = tr B (soundness p) b

-------------------------------------------------------------------------------
-- Soundness for rows

soundness-row : ∀ {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} → ρ₁ ≡ᵣ ρ₂ → ⇓ᵣ ρ₁ ≡ ⇓ᵣ ρ₂
soundness-row {ρ₁ = ρ₁} {ρ₂} eq with 
   ⟦ ρ₁ ⟧ᵣ idEnv 
  | ⟦ ρ₂ ⟧ᵣ idEnv
  | fund-≈ᵣ {ρ₁ = ρ₁} {ρ₂} idEnv-≈ eq 
... | n , P | m , Q | refl , I = reify-≈ᵣ P Q I

 

--------------------------------------------------------------------------------
-- renaming commutes with ⇓ₜ 

↻-ren-⇓ₜ : ∀ (r : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ) → ren r (⇓ₜ τ) ≡ ⇓ₜ (renₜ r τ)
↻-ren-⇓ₜ {Δ₁ = Δ₁} r τ = 
  trans 
    (↻-ren-reify {Δ₁ = Δ₁} r {V₁ = ⟦ τ ⟧ₜ idEnv} {V₂ = ⟦ τ ⟧ₜ idEnv} (fund-≈ {τ₁ = τ} idEnv-≈ eq-refl)) 
    (reify-≈ 
      (trans-≈ 
        (↻-renSem-eval r τ idEnv-≈) 
        (trans-≈ (idext (λ { x → ↻-ren-reflect r (` x) }) τ) (sym-≈ (↻-renₜ-eval r τ idEnv-≈)))))

↻-ren-⇓ᵣ : ∀ (r : Renaming Δ₁ Δ₂) (ρ : RowLiteral (Type Δ₁ κ)) → 
               ren r (⇓ᵣ ρ) ≡ ⇓ᵣ (ren r ρ)
↻-ren-⇓ᵣ {Δ₁ = Δ₁} r ρ with 
   ⟦ ρ ⟧ᵣ idEnv 
  |  ⟦ ρ ⟧ᵣ (idEnv ∘ r)
  | ⟦ (ren r ρ) ⟧ᵣ idEnv
  | fund-≈ᵣ {ρ₁ = ρ} idEnv-≈ reflᵣ 
  | ↻-renₜ-evalRow r ρ idEnv-≈ 
  | ↻-renSem-evalRow r ρ idEnv-≈ 
  | idext-row (λ { x → ↻-ren-reflect r (` x) }) ρ
... | n , P | m , Q | j , K | (refl , d) | (refl , rel₁) | (refl , rel₂) | (refl , rel₃) =
  trans 
    (↻-ren-reifyRow {Δ₁ = Δ₁} P P r (λ { i → refl , d i .snd })   ) 
    (reify-≈ᵣ (λ i → map₂ (renSem r) (P i)) K (λ { i → (trans (rel₂ i .fst) (trans (rel₃ i .fst) (sym (rel₁ i .fst)))) , (trans-≈ (rel₂ i .snd) (trans-≈ (rel₃ i .snd) (sym-≈ (rel₁ i .snd)))) }))

--------------------------------------------------------------------------------
-- Lemma stating that evaluation forces ⇑ and ren to commute over $.

↻-ren-⇓-$ : ∀ (ρ : Renaming Δ₁ Δ₂) → 
          (F : NormalType Δ₁ (κ₁ `→ κ₂))
          (ρ₁ : NormalType Δ₁ R[ κ₁ ]) → 
          ⇓ₜ (⇑ (ren ρ F) $ ⇑ (ren ρ ρ₁)) ≡  ren ρ (⇓ₜ (⇑ F $ ⇑ ρ₁))
↻-ren-⇓-$ {Δ₁ = Δ₁} ρ F ρ₁ rewrite 
    (↻-ren-⇑ ρ ρ₁) 
  | (↻-ren-⇑ ρ F) = 
      (trans 
        (reify-≈ 
          (trans-≈ (↻-renₜ-eval ρ (⇑ F $ ⇑ ρ₁) idEnv-≈) 
          (trans-≈ 
            (idext (sym-≈ ∘ ↻-ren-reflect ρ ∘ `) (⇑ F $ ⇑ ρ₁)) 
            (sym-≈ (↻-renSem-eval ρ (⇑ F $ ⇑ ρ₁) idEnv-≈))))) 
        (sym (↻-ren-reify {Δ₁ = Δ₁} ρ 
          {V₁ = (↑ F ⟨$⟩ ↑ ρ₁)} 
          {V₂ = (↑ F ⟨$⟩ ↑ ρ₁)} 
          (fund-≈ 
            {τ₁ = ⇑ F $ ⇑ ρ₁} 
            {τ₂ = ⇑ F $ ⇑ ρ₁} 
            idEnv-≈ 
            (eq-$ 
              eq-refl 
              eq-refl))))) 

-------------------------------------------------------------------------------
-- Helper to substitute under an eval
 
evalCRSubst : ∀ {Δ₂ : KEnv} {κ : Kind} {η₁ η₂ : SemEnv Δ₁ Δ₂}
    → η₁ ≈e η₂
    → {τ₁ τ₂ : Type Δ₁ κ}
    → τ₁ ≡ τ₂
    → (⟦ τ₁ ⟧ₜ η₁) ≈ (⟦ τ₂ ⟧ₜ η₂)
evalCRSubst p {τ₁ = τ} refl = idext p τ
