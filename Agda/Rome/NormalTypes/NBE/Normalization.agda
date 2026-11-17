-- 
module Rome.NormalTypes.NBE.Normalization where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming
open import Rome.NormalTypes.NBE.Syntax
open import Rome.NormalTypes.NBE.Renaming

--------------------------------------------------------------------------------
-- reflection of neutral types & reification of semantic types

reflect : ∀ {Δ : KEnv} {κ : Kind} → NeutralType Δ κ → SemType Δ κ
reify : ∀ {Δ : KEnv} {κ : Kind} → SemType Δ κ → NormalType Δ κ

reflect {κ = ★} τ            = ne τ
reflect {κ = L} τ            = ne τ
reflect {κ = R[ κ ]} ρ       = (λ r n → reflect n) $ ρ 
reflect {κ = κ₁ `→ κ₂} τ = λ ρ v → reflect (ren ρ τ · reify v)

reifyKripke   : {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} → 
                KripkeFunction Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripkeNE : {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} → 
                KripkeFunctionNE Δ κ₁ κ₂ → NormalType Δ (κ₁ `→ κ₂)
reifyKripke {κ₁ = κ₁} F = `λ (reify (F S (reflect {κ = κ₁} ((` Z)))))
reifyKripkeNE F = `λ (reify (F S (` Z)))

reifyRow' : (n : ℕ) → (Fin n → Label × SemType Δ κ) → RowLiteral (NormalType Δ κ)
reifyRow' zero P    = []
reifyRow' (suc n) P with P fzero
... | (l , τ) = (l , reify τ) ∷ reifyRow' n (P ∘ fsuc)

reifyRow : Row (SemType Δ κ) → RowLiteral (NormalType Δ κ)
reifyRow (n , P) = reifyRow' n P

reifyRowOrdered : ∀ {Δ : KEnv} {κ : Kind} {ρ : Row (SemType Δ κ)} → OrderedRow ρ →  Ordered (reifyRow ρ)
reifyRowOrdered' : ∀ {Δ : KEnv} {κ : Kind} (n : ℕ) → (P : Fin n → Label × SemType Δ κ) → 
                      OrderedRow (n , P) →  Ordered (reifyRow (n , P))

reifyRowOrdered' zero P ω = tt
reifyRowOrdered' (suc zero) P ω = tt
reifyRowOrdered' (suc (suc n)) P (l₁<l₂ , ih) = l₁<l₂ , (reifyRowOrdered' (suc n) (P ∘ fsuc) ih)

reifyRowOrdered {ρ = n , P} ω = reifyRowOrdered' n P ω

reifyPreservesNR : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : notRowLiteral ρ₁ or notRowLiteral ρ₂) → notRowLiteralNF (reify ρ₁) or notRowLiteralNF (reify ρ₂)

reifyPreservesNR' : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
                     (nr : notRowLiteral ρ₁ or notRowLiteral ρ₂) → notRowLiteralNF (reify ((ρ₁ ∖ ρ₂) {nr}))

reify {κ = ★} τ = τ
reify {κ = L} τ = τ
reify {κ = κ₁ `→ κ₂} F = `λ (reify (F S (reflect {κ = κ₁} ((` Z)))))
reify {κ = R[ κ ]} (l ▹ τ) = (l ▹ₙ (reify τ))
reify {κ = R[ κ ]} (row ρ q) = ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered q))
reify {κ = R[ κ ]} (φ $ τ) =  (`λ (reify (φ S (` Z))) $ τ)
reify {κ = R[ κ ]} ((ρ₂ ∖ ρ₁) {nrl}) = (reify ρ₂ ∖ reify ρ₁) {fromWitness (reifyPreservesNR ρ₂ ρ₁ nrl)}

reifyPreservesNR (x₁ ▹ x₂) ρ₂ (left x) = left tt
reifyPreservesNR ((ρ₁ ∖ ρ₃) {nr}) ρ₂ (left x) = left (reifyPreservesNR' ρ₁ ρ₃ nr)
reifyPreservesNR (φ $ ρ) ρ₂ (left x) = left tt
reifyPreservesNR ρ₁ (x ▹ x₁) (right y) = right tt
reifyPreservesNR ρ₁ ((ρ₂ ∖ ρ₃) {nr}) (right y) = right (reifyPreservesNR' ρ₂ ρ₃ nr)
reifyPreservesNR ρ₁ ((φ $ ρ₂)) (right y) = right tt

reifyPreservesNR' (x₁ ▹ x₂) ρ₂ (left x) = tt
reifyPreservesNR' (ρ₁ ∖ ρ₃) ρ₂ (left x) = tt
reifyPreservesNR' (φ $ n) ρ₂ (left x) = tt
reifyPreservesNR' (φ $ n) ρ₂ (right y) = tt
reifyPreservesNR' (x ▹ x₁) ρ₂ (right y) = tt
reifyPreservesNR' (row ρ x) (x₁ ▹ x₂) (right y) = tt
reifyPreservesNR' (row ρ x) (ρ₂ ∖ ρ₃) (right y) = tt
reifyPreservesNR' (row ρ x) (φ $ n) (right y) = tt
reifyPreservesNR' (ρ₁ ∖ ρ₃) ρ₂ (right y) = tt

--------------------------------------------------------------------------------
-- η normalization of neutral types

η-norm : NeutralType Δ κ → NormalType Δ κ 
η-norm = reify ∘ reflect

-- --------------------------------------------------------------------------------
-- -- Semantic environments

SemEnv : KEnv → KEnv → Set
SemEnv Δ₁ Δ₂ = ∀ {κ : Kind} → TVar Δ₁ κ → SemType Δ₂ κ

idEnv : SemEnv Δ Δ
idEnv = reflect ∘ `

extende : (η : SemEnv Δ₁ Δ₂) → (V : SemType Δ₂ κ) → SemEnv (Δ₁ , κ) Δ₂
extende η V Z     = V
extende η V (S x) = η x

lifte : SemEnv Δ₁ Δ₂ → SemEnv (Δ₁ , κ) (Δ₂ , κ)
lifte {Δ₁} {Δ₂} {κ} η  = extende (weakenSem ∘ η) (idEnv Z)

--------------------------------------------------------------------------------
-- Semantic application

infixr 5 _⟨·⟩_
_⟨·⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → SemType Δ κ₂
F ⟨·⟩ V = F id V

--------------------------------------------------------------------------------
-- Semantic complement

infixr 5 _∈Row_
_∈Row_ : ∀ {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Set 
_∈Row_ {m = m} l Q = Σ[ i ∈ Fin m ] (l ≡ Q i .fst)

_∈Row?_ : ∀ {Δ : KEnv} {κ : Kind} {m} → (l : Label) → 
         (Q : Fin m → Label × SemType Δ κ) → 
         Dec (l ∈Row Q)
_∈Row?_ {m = zero} l Q = no λ { () }
_∈Row?_ {m = suc m} l Q with l ≟ Q fzero .fst
... | yes p = yes (fzero , p)
... | no  p with l ∈Row? (Q ∘ fsuc)
...        | yes (n , q) = yes ((fsuc n) , q) 
...        | no  q = no λ { (fzero , q') → p q' ; (fsuc n , q') → q (n , q') }

compl : ∀ {n m} → 
        (P : Fin n → Label × SemType Δ κ) 
        (Q : Fin m → Label × SemType Δ κ) → 
        Row (SemType Δ κ)
compl {n = zero} {m} P Q = ε
compl {n = suc n} {m} P Q with P fzero .fst ∈Row? Q 
... | yes _ = compl (P ∘ fsuc) Q 
... | no _ = (P fzero) ⨾⨾ (compl (P ∘ fsuc) Q)

-- --------------------------------------------------------------------------------
-- -- Semantic complement preserves well-ordering

open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

lemma : ∀ {n m q} {Δ : KEnv} {κ : Kind} → 
          (P : Fin (suc n) → Label × SemType Δ κ)
          (Q : Fin m → Label × SemType Δ κ) → 
          (R : Fin (suc q) → Label × SemType Δ κ) → 
             OrderedRow (suc n , P) →
             compl (P ∘ fsuc) Q ≡ (suc q , R) → 
          P fzero .fst < R fzero .fst
lemma {n = suc n} P Q R oP eq₁ with P (fsuc fzero) .fst ∈Row? Q 
lemma {n = suc n} P Q R oP refl | no _ = oP .fst
... | yes _ = <-trans {i = P fzero .fst} {j = P (fsuc fzero) .fst} {k = R fzero .fst} (oP .fst) (lemma {n = n} (P ∘ fsuc) Q R (oP .snd) eq₁)

ordered-⨾⨾ : ∀ {n m} {Δ : KEnv} {κ : Kind} → 
                 (P : Fin (suc n) → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (suc n , P) → 
                 OrderedRow (compl (P ∘ fsuc) Q) → OrderedRow (P fzero ⨾⨾ compl (P ∘ fsuc) Q)
ordered-⨾⨾ {n = n} P Q oP oC with compl (P ∘ fsuc) Q | inspect (compl (P ∘ fsuc)) Q
... | zero , R  | _        = tt
... | suc n , R | [[ eq ]] = lemma P Q R oP eq  , oC

ordered-compl :  ∀ {n m} {Δ : KEnv} {κ : Kind} → 
                 (P : Fin n → Label × SemType Δ κ) 
                 (Q : Fin m → Label × SemType Δ κ) → 
                 OrderedRow (n , P) → OrderedRow (m , Q) → OrderedRow (compl P Q)
ordered-compl {n = zero} P Q ω₁ ω₂ = tt
ordered-compl {n = suc n} P Q ω₁ ω₂ with P fzero .fst ∈Row? Q
... | yes _ = ordered-compl (P ∘ fsuc) Q (ordered-cut ω₁) ω₂
... | no _ = ordered-⨾⨾ P Q ω₁ (ordered-compl (P ∘ fsuc) Q (ordered-cut ω₁) ω₂)

--------------------------------------------------------------------------------
-- Semantic complement on Rows
                
infixr 5 _∖v_                
_∖v_ : Row (SemType Δ κ) → Row (SemType Δ κ) → Row (SemType Δ κ)
(n , P) ∖v (m , Q) = compl P Q

ordered∖v : ∀ {Δ : KEnv} {κ : Kind} (ρ₂ ρ₁ : Row (SemType Δ κ)) → OrderedRow ρ₂ → OrderedRow ρ₁ → OrderedRow (ρ₂ ∖v ρ₁)
ordered∖v (n , P) (m , Q) ω₂ ω₁ = ordered-compl P Q ω₂ ω₁

--------------------------------------------------------------------------------
-- Semantic mapping

infixr 5 _⟨$⟩_                
_⟨$⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → SemType Δ R[ κ₂ ]
notRowLiteral$ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {F : SemType Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : SemRow Δ (λ Δ' → SemType Δ' κ₁) R[ κ₁ ]} → 
              notRowLiteral ρ₂ or notRowLiteral ρ₁ → notRowLiteral (F ⟨$⟩ ρ₂) or notRowLiteral (F ⟨$⟩ ρ₁)

_⟨$⟩_ {κ₁ = κ₁} {κ₂ = κ₂} F (l ▹ τ) = l ▹ (F ⟨·⟩ τ) -- l ▹ (F ⟨·⟩ τ)
F ⟨$⟩ row (n , P) q = row (n , map₂ (F id) ∘ P) (orderedMap₂ (F id) q)
F ⟨$⟩ ((ρ₂ ∖ ρ₁) {nr}) = ((F ⟨$⟩ ρ₂) ∖ (F ⟨$⟩ ρ₁)) {notRowLiteral$ nr}
F ⟨$⟩ (G $ n) = (λ {Δ'} r → F r ∘ G r) $ n

notRowLiteral$ {F = F} {x₁ ▹ x₂} {ρ₁} (left x) = left tt
notRowLiteral$ {F = F} {ρ₂ ∖ ρ₃} {ρ₁} (left x) = left tt
notRowLiteral$ {F = F} {φ $ n} {ρ₁} (left x) = left tt

notRowLiteral$ {F = F} {ρ₂} {x ▹ x₁} (right y) = right tt
notRowLiteral$ {F = F} {ρ₂} {ρ₁ ∖ ρ₃} (right y) = right tt
notRowLiteral$ {F = F} {ρ₂} {φ $ n} (right y) = right tt


-- -- -- --------------------------------------------------------------------------------
-- -- -- -- Semantic complement on SemTypes

_∖V_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
row ρ₂ ω₂ ∖V row ρ₁ ω₁ = row (ρ₂ ∖v ρ₁) (ordered∖v ρ₂ ρ₁ ω₂ ω₁)
ρ₂@(x ▹ x₁) ∖V ρ₁ = (ρ₂ ∖ ρ₁) {nr = left tt}
ρ₂@(row ρ x) ∖V ρ₁@(x₁ ▹ x₂) = (ρ₂ ∖ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ∖V ρ₁@(_ ∖ _) = (ρ₂ ∖ ρ₁) {nr = right tt}
ρ₂@(row ρ x) ∖V ρ₁@(_ $ _) = (ρ₂ ∖ ρ₁) {nr = right tt}
ρ@(ρ₂ ∖ ρ₃) ∖V ρ' = (ρ ∖ ρ') {nr = left tt}
ρ@(φ $ n) ∖V ρ' = (ρ ∖ ρ') {nr = left tt}

-- --------------------------------------------------------------------------------
-- -- Semantic flap

apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
apply a = λ ρ F → F ⟨·⟩ (renSem ρ a)

infixr 0 _<?>V_
_<?>V_ : SemType Δ R[ κ₁ `→ κ₂ ] → SemType Δ κ₁ → SemType Δ R[ κ₂ ]
f <?>V a = apply a ⟨$⟩ f


--------------------------------------------------------------------------------
-- (Generic) Semantic combinators for Π/Σ

record Xi : Set where 
  field
    Ξ★ : ∀ {Δ : KEnv} → NormalType Δ R[ ★ ] → NormalType Δ ★
    ren-★ : ∀ {Δ₁ : KEnv} (ρ : Renaming Δ₁ Δ₂) → (τ : NormalType Δ₁ R[ ★ ]) → ren ρ (Ξ★ τ) ≡  Ξ★ (ren ρ τ)

open Xi
ξ : ∀ {Δ : KEnv} → Xi → SemType Δ R[ κ ] → SemType Δ κ 
ξ {κ = ★} Ξ x = Ξ .Ξ★ (reify x)
ξ {κ = L} Ξ x = lab "impossible"
ξ {κ = κ₁ `→ κ₂} Ξ F = λ ρ v → ξ Ξ (renSem ρ F <?>V v)
ξ {κ = R[ κ ]} Ξ x = (λ ρ v → ξ Ξ v) ⟨$⟩ x

Π-rec Σ-rec : Xi 
Π-rec = record
  {  Ξ★ = Π ; ren-★ = λ ρ τ → refl }
Σ-rec = 
  record
  { Ξ★ = Σ ; ren-★ = λ ρ τ → refl  }

ΠV ΣV : ∀ {Δ : KEnv} → SemType Δ R[ κ ] → SemType Δ κ
ΠV = ξ Π-rec
ΣV = ξ Σ-rec

ξ-Kripke : Xi → KripkeFunction Δ R[ κ ] κ
ξ-Kripke Ξ ρ v = ξ Ξ v

Π-Kripke Σ-Kripke : KripkeFunction Δ R[ κ ] κ
Π-Kripke = ξ-Kripke Π-rec
Σ-Kripke = ξ-Kripke Σ-rec

--------------------------------------------------------------------------------
-- Type evaluation.

⟦_⟧ₜ : Type Δ₁ κ → SemEnv Δ₁ Δ₂ → SemType Δ₂ κ
⟦_⟧ₚ : Pred (Type Δ₁ κ) → SemEnv Δ₁ Δ₂ → Pred (NormalType Δ₂ κ)

⟦_⟧ᵣ        : (ρ : RowLiteral (Type Δ₁ κ)) → SemEnv Δ₁ Δ₂ → Row (SemType Δ₂ κ)
⟦_⟧ₒ : {ρ : RowLiteral (Type Δ₁ κ)} → 
       (ω : Ordered ρ) 
       (η : SemEnv Δ₁ Δ₂) → 
       OrderedRow (⟦ ρ ⟧ᵣ η)

⟦ [] ⟧ᵣ η = ε 
⟦ (l , τ) ∷ ρ ⟧ᵣ η = (l , (⟦ τ ⟧ₜ η)) ⨾⨾ (⟦ ρ ⟧ᵣ η) 

⇓ᵣ-isMap : ∀ {Δ₂ : KEnv} {κ : Kind} (η : SemEnv Δ₁ Δ₂) → (xs : RowLiteral (Type Δ₁ κ))  → 
                      reifyRow (⟦ xs ⟧ᵣ η) ≡ map (λ { (l , τ) → l , (reify (⟦ τ ⟧ₜ η)) }) xs
⇓ᵣ-isMap η [] = refl
⇓ᵣ-isMap η (x ∷ xs) = ap₂ _∷_ refl (⇓ᵣ-isMap η xs)

⟦ (ρ₁ · ρ₂ ~ ρ₃) ⟧ₚ η = 
  reify (⟦ ρ₁ ⟧ₜ η) · reify (⟦ ρ₂ ⟧ₜ η) ~ reify (⟦ ρ₃ ⟧ₜ η)
⟦ (ρ₁ ≲ ρ₂) ⟧ₚ η = 
  reify (⟦ ρ₁ ⟧ₜ η) ≲ reify (⟦ ρ₂ ⟧ₜ η)

⟦ ` x ⟧ₜ η = η x
⟦ τ₁ · τ₂ ⟧ₜ η = (⟦ τ₁ ⟧ₜ η) ⟨·⟩ (⟦ τ₂ ⟧ₜ η)
⟦ τ₁ `→ τ₂ ⟧ₜ η = (⟦ τ₁ ⟧ₜ η) `→ (⟦ τ₂ ⟧ₜ η)
⟦ π ⇒ τ ⟧ₜ η = ⟦ π ⟧ₚ η ⇒ ⟦ τ ⟧ₜ η
⟦ `∀ τ ⟧ₜ η = `∀ (⟦ τ ⟧ₜ (lifte η)) 
⟦ μ τ ⟧ₜ η = μ (reify (⟦ τ ⟧ₜ η))
⟦ ρ₂ ∖ ρ₁ ⟧ₜ η = ⟦ ρ₂ ⟧ₜ η ∖V ⟦ ρ₁ ⟧ₜ η
⟦ lab l ⟧ₜ η = lab l
⟦ `λ τ ⟧ₜ η = λ ρ v → ⟦ τ ⟧ₜ (extende (λ {κ} v' → renSem {κ = κ} ρ (η v')) v)
⟦ Π ⟧ₜ η = Π-Kripke
⟦ Σ ⟧ₜ η = Σ-Kripke
⟦ (f $ a) ⟧ₜ η = (⟦ f ⟧ₜ η) ⟨$⟩ (⟦ a ⟧ₜ η)
⟦ (ξ ▹ τ) ⟧ₜ η with ⟦ ξ ⟧ₜ η 
... | ne n = (n ▹ ⟦ τ ⟧ₜ η)
... | lab l = row (⁅ (l , ⟦ τ ⟧ₜ η) ⁆) tt
⟦ (⦅ ρ ⦆ ω) ⟧ₜ η = row (⟦ ρ ⟧ᵣ η) (⟦ toWitness ω ⟧ₒ η)
⟦_⟧ₒ {ρ = []} ω η = tt
⟦_⟧ₒ {ρ = _ ∷ []} ω η = tt
⟦_⟧ₒ {ρ = (l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ} (l₁<l₂ , ω) η with 
 ⟦ ρ ⟧ᵣ η | ⟦ ω ⟧ₒ η 
... | zero , P | ih = l₁<l₂ , tt
... | suc n , P | ih₁ , ih₂ =  l₁<l₂ , ih₁ , ih₂

record EvaluateTC (𝒯 𝒱 : KEnv → Kind → Set) : Set where
  constructor Eval
  field
    ⟦_⟧ : 𝒯 Δ₁ κ → SemEnv Δ₁ Δ₂ → 𝒱 Δ₂ κ
open EvaluateTC {{...}} public

instance
  eval : EvaluateTC Type SemType
  eval = Eval ⟦_⟧ₜ 

  evalPred : EvaluateTC 
              (λ Δ → Pred ∘ Type Δ) 
              (λ Δ → Pred ∘ NormalType Δ)
  evalPred = Eval ⟦_⟧ₚ       

  evalRow : EvaluateTC 
              (λ Δ → RowLiteral ∘ Type Δ) 
              (λ Δ → Row ∘ SemType Δ)
  evalRow = Eval ⟦_⟧ᵣ


--------------------------------------------------------------------------------
-- Type normalization

-- Normalization algorithm
⇓ₜ : ∀ {Δ : KEnv} → Type Δ κ → NormalType Δ κ
⇓ₜ τ = reify (⟦ τ ⟧ₜ idEnv)

⇓ₚ : ∀ {Δ : KEnv} → Pred (Type Δ κ) → Pred (NormalType Δ κ) 
⇓ₚ π = ⟦ π ⟧ₚ idEnv

⇓ᵣ : ∀ {Δ : KEnv} → RowLiteral (Type Δ κ) → RowLiteral (NormalType Δ κ) 
⇓ᵣ ρ = reifyRow (⟦ ρ ⟧ᵣ idEnv)

⇓ₙₑ : ∀ {Δ : KEnv} → NeutralType Δ κ → NormalType Δ κ
⇓ₙₑ τ = reify (⟦ (⇑ₙₑ τ) ⟧ₜ idEnv)

-- reabstraction
↑ : ∀ {Δ : KEnv} → NormalType Δ κ → SemType Δ κ 
↑ τ = ⟦ (⇑ τ) ⟧ₜ idEnv

--------------------------------------------------------------------------------
-- Normalization typeclass

record NormalizeTC (𝒯 𝒱 : KEnv → Kind → Set) : Set where
  constructor Norm
  field
    ⇓ : 𝒯 Δ κ → 𝒱 Δ κ
open NormalizeTC {{...}} public

instance
  norm : NormalizeTC Type NormalType
  norm = Norm ⇓ₜ

  normNE : NormalizeTC NeutralType NormalType
  normNE = Norm ⇓ₙₑ

  normPred : NormalizeTC 
              (λ Δ → Pred ∘ Type Δ) 
              (λ Δ → Pred ∘ NormalType Δ)
  normPred = Norm ⇓ₚ

  normRow : NormalizeTC 
              (λ Δ → RowLiteral ∘ Type Δ) 
              (λ Δ → RowLiteral ∘ NormalType Δ)
  normRow = Norm ⇓ᵣ 