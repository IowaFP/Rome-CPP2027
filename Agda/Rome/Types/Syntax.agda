-- 
module Rome.Types.Syntax where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Data.String using (_<_; _<?_)


--------------------------------------------------------------------------------
-- Types

infixl 5 _·_
infixr 5 _≲_
data Type (Δ : KEnv) : Kind → Set 
data Pred (Ty : Set) : Set

RowLiteral : (Ty : Set) → Set 
RowLiteral Ty   = List (Label × Ty)

Ordered : ∀ {Ty : Set} → RowLiteral Ty → Set 
ordered? : ∀ {Ty : Set} → 
             (xs : RowLiteral Ty) → 
             Dec (Ordered xs)

--------------------------------------------------------------------------------
-- Preds

data Pred Ty where
  _·_~_ : 

       (ρ₁ ρ₂ ρ₃ : Ty) → 
       --------------------- 
       Pred Ty

  _≲_ : 

       (ρ₁ ρ₂ : Ty) →
       ----------
       Pred Ty  
       
data Type Δ where

  ` : 
      (α : TVar Δ κ) →
      --------
      Type Δ κ

  `λ : {κ₁ : Kind} {κ₂ : Kind} → 
      
      (τ : Type (Δ , κ₁) κ₂) → 
      ---------------
      Type Δ (κ₁ `→ κ₂)

  _·_ : 
      
      (τ₁ : Type Δ (κ₁ `→ κ₂)) → 
      (τ₂ : Type Δ κ₁) → 
      ----------------
      Type Δ κ₂

  _`→_ : 

         (τ₁ : Type Δ ★) →
         (τ₂ : Type Δ ★) → 
         --------
         Type Δ ★

  `∀    :
      
         {κ : Kind} → (τ : Type (Δ , κ) ★) →
         -------------
         Type Δ ★

  μ     :
      
         (φ : Type Δ (★ `→ ★)) → 
         -------------
         Type Δ ★

  ------------------------------------------------------------------
  -- Qualified types

  _⇒_ : ∀ {κ : Kind} → 

         (π : Pred (Type Δ R[ κ ])) → (τ : Type Δ ★) → 
         ---------------------
         Type Δ ★  


  ------------------------------------------------------------------
  -- Rω business

  ⦅_⦆ : (xs : RowLiteral (Type Δ κ)) (ordered : True (ordered? xs)) →
        ----------------------
        Type Δ R[ κ ]

  -- labels
  lab :
    
        (l : Label) → 
        --------
        Type Δ L

  -- Row formation
  _▹_ :
         (l : Type Δ L) → (τ : Type Δ κ) → 
         -------------------
         Type Δ R[ κ ]

  _$_ : 

       (φ : Type Δ (κ₁ `→ κ₂)) → (τ : Type Δ R[ κ₁ ]) → 
       ----------------------------------------
       Type Δ R[ κ₂ ]

  -- Record formation
  Π     :
          {notLabel : NotLabel κ} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  -- Variant formation
  Σ     :

          {notLabel : NotLabel κ} →
          ----------------
          Type Δ (R[ κ ] `→ κ)

  _∖_ : 
      
        Type Δ R[ κ ] → Type Δ R[ κ ] → 
        ---------------------------------
        Type Δ R[ κ ]
--------------------------------------------------------------------------------
-- NotLabel κ is irrelevant, and so Π {nl₁} · τ₁ ≡ Π  {nl₂} · τ₂ iff τ₁ ≡ τ₂.

cong-Π : {τ₁ τ₂ : Type Δ R[ κ ]} → 
         {nl₁ nl₂ : NotLabel κ} → 
         τ₁ ≡ τ₂ → 
         Π {notLabel = nl₁} · τ₁ ≡ Π {notLabel = nl₂} · τ₂
cong-Π {κ = κ} {τ₁ = τ₁} {τ₂} {nl₁} {nl₂} refl = 
       ap (λ x → Π {notLabel = x} · τ₁) (NotLabelIrrelevant κ nl₁ nl₂)

cong-Σ : {τ₁ τ₂ : Type Δ R[ κ ]} → 
         {nl₁ nl₂ : NotLabel κ} → 
         τ₁ ≡ τ₂ → 
         Σ {notLabel = nl₁} · τ₁ ≡ Σ {notLabel = nl₂} · τ₂
cong-Σ {κ = κ} {τ₁ = τ₁} {τ₂} {nl₁} {nl₂} refl = 
       ap (λ x → Σ {notLabel = x} · τ₁) (NotLabelIrrelevant κ nl₁ nl₂)

--------------------------------------------------------------------------------
-- Simple row well-formedness

Ordered [] = ⊤
Ordered (x ∷ []) = ⊤
Ordered ((l₁ , _) ∷ (l₂ , τ) ∷ xs) = l₁ < l₂ × Ordered ((l₂ , τ) ∷ xs)

ordered? [] = yes tt
ordered? (x ∷ []) = yes tt
ordered? ((l₁ , _) ∷ (l₂ , _) ∷ xs) with l₁ <? l₂ | ordered? ((l₂ , _) ∷ xs)
... | yes p | yes q  = yes (p , q)
... | yes p | no q  = no (λ { (_ , oxs) → q oxs })
... | no p  | yes q  = no (λ { (x , _) → p x})
... | no  p | no  q  = no (λ { (x , _) → p x})

OrderedIrrelevant : ∀ {Ty : Set} → (ρ : RowLiteral Ty) → Irrelevant (True (ordered? ρ))
OrderedIrrelevant ρ = Dec→Irrelevant (Ordered ρ) (ordered? ρ)

cong-⦅_⦆ : {ρ₁ ρ₂ : RowLiteral (Type Δ κ)} 
           {ω₁ : True (ordered? ρ₁)} 
           {ω₂ : True (ordered? ρ₂)} → 
           ρ₁ ≡ ρ₂ → 
           ⦅ ρ₁ ⦆ ω₁ ≡ ⦅ ρ₂ ⦆ ω₂
cong-⦅_⦆ {ρ₁ = ρ₁} {_} {ω₁} {ω₂} refl rewrite OrderedIrrelevant ρ₁ ω₁ ω₂ = refl

-- In practice, the implicits are difficult to infer for wmap. 
-- So we'll specialize to the ordered predicate. 
ωmap : {A B : Set}
       {xs : RowLiteral A} {ys : RowLiteral B} → 
       (Ordered xs → Ordered ys) → 
       True (ordered? xs) → True (ordered? ys)
ωmap f d = fromWitness (f (toWitness d))


--------------------------------------------------------------------------------
-- Syntactic row complement

_∖s_ : ∀ {Ty : Set} → 
         (xs ys : RowLiteral Ty) → 
         RowLiteral Ty
[] ∖s ys = []
((l , τ) ∷ xs) ∖s ys with l ∈L? ys 
... | yes _ = xs ∖s ys
... | no  _ = (l , τ) ∷ (xs ∖s ys)

--------------------------------------------------------------------------------
-- Ordered lemmas 

open import Relation.Binary.Structures using (IsStrictPartialOrder)
open import Data.String.Properties renaming (<-isStrictPartialOrder-≈ to SPO)
open IsStrictPartialOrder (SPO) renaming (trans to <-trans)

ordered-cons : ∀ {Ty : Set} → (x : Label × Ty) (ρ : RowLiteral Ty) → 
               Ordered (x ∷ ρ) → 
               Ordered ρ 
ordered-cons x [] oxρ = tt
ordered-cons (l , snd₁) ((l₁ , snd₂) ∷ ρ) (_ , oxρ) = oxρ 

ordered-swap : ∀ {Ty : Set} {l l' : Label} {τ τ' : Ty} {xs : RowLiteral Ty} → 
                l < l' → 
                Ordered ((l' , τ') ∷ xs) → 
                Ordered ((l , τ) ∷ xs)
ordered-swap {xs = []} l<l' oxs = tt
ordered-swap {l = l} {l'} {xs = (l'' , τ'') ∷ xs} l<l' (l'<l'' , oxs) = <-trans {i = l} {j = l'} {k = l''} l<l' l'<l'' , oxs 
                
map-map₂ : ∀ {Ty : KEnv → Kind → Set} → 
             (ρ : RowLiteral (Ty Δ₁ κ₁)) (f : Ty Δ₁ κ₁ → Ty Δ₂ κ₂) → 
              Ordered ρ → Ordered (map (map₂ f) ρ)
map-map₂ [] f ω = tt
map-map₂ (x ∷ []) f ω = tt
map-map₂ {Ty = Ty} ((l₁ , _) ∷ (l₂ , _) ∷ ρ) f (l₁<l₂ , ω) = l₁<l₂ , (map-map₂ {Ty = Ty} ((l₂ , _) ∷ ρ) f ω)

ordered-∖s-cons : ∀ {Ty : Set} {l : Label} {τ : Ty} {xs ys : RowLiteral Ty} → 
                  Ordered ((l , τ) ∷ xs) → 
                  Ordered ((l , τ) ∷ (xs ∖s ys))
ordered-∖s-cons {xs = []} oxs = tt
ordered-∖s-cons {l = l} {τ = τ} {xs = (l' , τ') ∷ xs} {ys = ys} (l<l' , oxs') with l' ∈L? ys 
...| yes p = ordered-∖s-cons (ordered-swap {l = l} {l'} {τ} {τ'} l<l' oxs')
...| no  p = l<l' , ordered-∖s-cons oxs'
                   
ordered-∖s :  ∀ {Ty : Set} {xs ys : RowLiteral Ty} → 
             Ordered xs →
             Ordered (xs ∖s ys)
ordered-∖s {xs = []} {ys} oxs = tt
ordered-∖s {xs = ((l , τ) ∷ xs)} {ys} oxs with l ∈L? ys
... | yes _  = ordered-∖s (ordered-cons (l , τ) xs oxs)
ordered-∖s  {xs = (l , τ) ∷ []} {ys} oxs | no p = tt
ordered-∖s {xs = (l , τ) ∷ (l' , τ') ∷ xs} {ys} (l<l' , oxs) | no p with l' ∈L? ys | ordered-∖s {ys = ys} oxs
... | no q | ih = l<l' , ih
... | yes q | ih = ordered-∖s-cons (ordered-swap l<l' oxs)

--------------------------------------------------------------------------------
-- Admissable constants

-- for partial application of infix fmap.
`↑ : Type Δ ((κ₁ `→ κ₂) `→ R[ κ₁ ] `→ R[ κ₂ ])
`↑ = `λ (`λ (` (S Z) $ ` Z))

-- Flapping. See https://hoogle.haskell.org/?hoogle=f%20(a%20-%3E%20b)%20-%3E%20a%20-%3E%20f%20b%20
flap : Type Δ (R[ κ₁ `→ κ₂ ] `→ κ₁ `→ R[ κ₂ ])
flap = `λ (`λ ((`λ ((` Z) · (` (S Z)))) $ (` (S Z))))

_??_ : Type Δ (R[ κ₁ `→ κ₂ ]) → Type Δ κ₁ → Type Δ R[ κ₂ ]
f ?? a = flap · f · a



