module Rome.Types.Properties.Substitution where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars
open import Rome.Types.Syntax
open import Rome.Types.Renaming
open import Rome.Types.Substitution
open import Rome.Types.Equivalence

open import Rome.Types.Properties.Renaming



--------------------------------------------------------------------------------
-- Renaming commutes over Substitution

∈L-sub : ∀ (r : Substitution Δ₁ Δ₂) → {ρ : RowLiteral (Type Δ₁ κ)} → 
                 (l : Label) → l ∈L ρ → l ∈L sub r ρ
∈L-sub r {ρ} l Here = Here
∈L-sub r {ρ} l (There ev) = There (∈L-sub r l ev)

subRowₜ-∈L : ∀ (r : Substitution Δ₁ Δ₂) → {ρ : RowLiteral (Type Δ₁ κ)} → 
                 (l : Label) → l ∈L sub r ρ → l ∈L ρ
subRowₜ-∈L r {(l' , τ) ∷ ρ} l Here = Here
subRowₜ-∈L r {(l' , τ) ∷ ρ} l (There ev) = There (subRowₜ-∈L r l ev)

↻-subRowₜ-∖s : ∀ (r : Substitution Δ₁ Δ₂) → {ρ₂ ρ₁ : RowLiteral (Type Δ₁ κ)} → 
       sub r (ρ₂ ∖s ρ₁) ≡ sub r ρ₂ ∖s sub r ρ₁
↻-subRowₜ-∖s r {[]} {ρ₁} = refl
↻-subRowₜ-∖s r {(l , τ) ∷ ρ₂} {ρ₁} with l ∈L? ρ₁ | l ∈L? sub r ρ₁
... | yes p | yes q = ↻-subRowₜ-∖s r {ρ₂} {ρ₁}
... | yes  p | no q = ⊥-elim (q (∈L-sub r l p))
... | no  p | yes q = ⊥-elim (p (subRowₜ-∈L r l q))
... | no  p | no q = ap ((l , sub r τ) ∷_) (↻-subRowₜ-∖s r {ρ₂} {ρ₁})

-------------------------------------------------------------------------------
-- Functor laws for lifting

liftsₜ-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
              (∀ {κ} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (x : TVar (Δ₁ , κ₁) κ₂) → liftsₜ σ₁ x ≡ liftsₜ σ₂ x
liftsₜ-cong e Z = refl
liftsₜ-cong e (S x) = ap (renₜ S) (e x)              

liftsₜ-id    : ∀ (x : TVar (Δ , κ₁) κ₂) → liftsₜ ` x ≡ ` x 
liftsₜ-id Z = refl
liftsₜ-id (S x) = refl

-- Fusion for liftsₜ and lift
liftsₜ-liftₜ      : ∀ {ρ : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃} 
                    (x : TVar (Δ₁ , κ₁) κ₂) → 
                    liftsₜ (σ ∘ ρ) x ≡ liftsₜ σ (liftₜ ρ x)
liftsₜ-liftₜ Z = refl
liftsₜ-liftₜ (S x) = refl

renₜ-liftₜ-liftsₜ : ∀ {σ : Substitution Δ₁ Δ₂}{ρ : Renaming Δ₂ Δ₃}(x : TVar (Δ₁ , κ₁) κ₂) → 
                    liftsₜ (renₜ ρ ∘ σ) x ≡ renₜ (liftₜ ρ) (liftsₜ σ x)
renₜ-liftₜ-liftsₜ Z = refl
renₜ-liftₜ-liftsₜ {σ = σ} {ρ} (S x) = trans (sym (renₜ-comp ρ S (σ x))) (renₜ-comp S (liftₜ ρ) (σ x))                    

-------------------------------------------------------------------------------
-- Substitution respects congruence

subₜ-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
              (∀ {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (τ : Type Δ₁ κ) → sub σ₁ τ ≡ sub σ₂ τ
subRowₜ-cong : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₁ Δ₂} →
              (∀ {κ : Kind} (x : TVar Δ₁ κ) → σ₁ x ≡ σ₂ x) → 
              (ρ : RowLiteral (Type Δ₁ κ)) → sub σ₁ ρ ≡ sub σ₂ ρ

subₜ-cong e (` α) = e α
subₜ-cong e (`λ τ) = ap `λ (subₜ-cong (liftsₜ-cong e) τ)
subₜ-cong e (τ₁ · τ₂) = ap₂ _·_ (subₜ-cong e τ₁) (subₜ-cong e τ₂)
subₜ-cong e (τ₁ `→ τ₂) = ap₂ _`→_ (subₜ-cong e τ₁) (subₜ-cong e τ₂)
subₜ-cong e (`∀ τ) = ap (`∀) (subₜ-cong (liftsₜ-cong e) τ)
subₜ-cong e (μ τ) = ap μ (subₜ-cong e τ)
subₜ-cong e ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  subₜ-cong e ρ₁ | subₜ-cong e ρ₂ | subₜ-cong e ρ₃ | subₜ-cong e τ = refl
subₜ-cong e ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  subₜ-cong e ρ₁ | subₜ-cong e ρ₂ | subₜ-cong e τ = refl
subₜ-cong e (lab l) = refl
subₜ-cong e Π = refl
subₜ-cong e Σ = refl
subₜ-cong e (τ $ τ₁) = ap₂ _$_ (subₜ-cong e τ) (subₜ-cong e τ₁)
subₜ-cong e (ρ₂ ∖ ρ₁) = ap₂ _∖_ (subₜ-cong e ρ₂) (subₜ-cong e ρ₁)
subₜ-cong {σ₁ = σ₁} e (⦅ ρ ⦆ ω) = cong-⦅ subRowₜ-cong e ρ ⦆
subₜ-cong {σ₁ = σ₁} e (l ▹ τ) = ap₂ _▹_ (subₜ-cong e l) (subₜ-cong e τ)

subRowₜ-cong eq [] = refl
subRowₜ-cong {σ₁ = σ₁} {σ₂} eq ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (subₜ-cong eq τ)) (subRowₜ-cong eq ρ)

-------------------------------------------------------------------------------
-- Substitution respects identities

sub-id : ∀ (τ : Type Δ κ) → sub ` τ ≡ τ
subRowₜ-id : ∀ (ρ : RowLiteral (Type Δ κ)) → sub ` ρ ≡ ρ

sub-id (` α) = refl
sub-id (`λ τ) = ap `λ (trans (subₜ-cong  {σ₁ = liftsₜ `} {σ₂ = `} liftsₜ-id τ) (sub-id τ))
sub-id (τ₁ · τ₂) = ap₂ _·_ (sub-id τ₁) (sub-id τ₂)
sub-id (τ₁ `→ τ₂) = ap₂ _`→_ (sub-id τ₁) (sub-id τ₂)
sub-id (`∀ τ) = ap (`∀) (trans (subₜ-cong liftsₜ-id τ) (sub-id τ))
sub-id (μ τ) = ap μ (sub-id τ)
sub-id ((ρ₁ · ρ₂ ~ ρ₃) ⇒ τ) rewrite 
  sub-id ρ₁ | sub-id ρ₂ | sub-id ρ₃ | sub-id τ = refl
sub-id ((ρ₁ ≲ ρ₂) ⇒ τ) rewrite
  sub-id ρ₁ | sub-id ρ₂ | sub-id τ = refl
sub-id (lab l) = refl
sub-id Π = refl
sub-id Σ = refl
sub-id (τ₁ $ τ₂) = ap₂ _$_ (sub-id τ₁) (sub-id τ₂)
sub-id (⦅ ρ ⦆ ω) = cong-⦅ subRowₜ-id ρ ⦆
sub-id (ρ₂ ∖ ρ₁) = ap₂ _∖_ (sub-id ρ₂) (sub-id ρ₁)
sub-id (l ▹ τ) = ap₂ _▹_ (sub-id l) (sub-id τ)

subRowₜ-id [] = refl
subRowₜ-id ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (sub-id τ)) (subRowₜ-id ρ)

-------------------------------------------------------------------------------
-- subₜstitution and renₜaming commute

↻-subₜ-renₜ : ∀ {r : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃}  
                (τ : Type Δ₁ κ) → sub (σ ∘ r) τ ≡ sub σ (renₜ r τ)
↻-subRowₜ-ren : ∀ {r : Renaming Δ₁ Δ₂}{σ : Substitution Δ₂ Δ₃}  
                (τ : RowLiteral (Type Δ₁ κ)) → sub (σ ∘ r) τ ≡ sub σ (ren r τ)

↻-subₜ-renₜ {r = r} {σ} (` α) = refl
↻-subₜ-renₜ {r = r} {σ} (`λ τ) = ap `λ (trans (subₜ-cong liftsₜ-liftₜ τ) (↻-subₜ-renₜ τ))
↻-subₜ-renₜ {r = r} {σ} (τ₁ · τ₂) = ap₂ _·_ (↻-subₜ-renₜ τ₁) (↻-subₜ-renₜ τ₂)
↻-subₜ-renₜ {r = r} {σ} (τ₁ `→ τ₂) = ap₂ _`→_ (↻-subₜ-renₜ τ₁) (↻-subₜ-renₜ τ₂) 
↻-subₜ-renₜ {r = r} {σ} (`∀ τ) = ap (`∀) (trans (subₜ-cong liftsₜ-liftₜ τ) (↻-subₜ-renₜ τ))
↻-subₜ-renₜ {r = r} {σ} (μ τ) = ap μ (↻-subₜ-renₜ τ)
↻-subₜ-renₜ {r = r} {σ} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    ↻-subₜ-renₜ {r = r} {σ} r₁ 
  | ↻-subₜ-renₜ {r = r} {σ} r₂ 
  | ↻-subₜ-renₜ {r = r} {σ} r₃ 
  | ↻-subₜ-renₜ {r = r} {σ} τ = refl
↻-subₜ-renₜ {r = r} {σ} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    ↻-subₜ-renₜ {r = r} {σ} r₁ 
  | ↻-subₜ-renₜ {r = r} {σ} r₂ 
  | ↻-subₜ-renₜ {r = r} {σ} τ = refl
↻-subₜ-renₜ {r = r} {σ} (lab l) = refl
↻-subₜ-renₜ {r = r} {σ} Π = refl
↻-subₜ-renₜ {r = r} {σ} Σ = refl
↻-subₜ-renₜ {r = r} {σ} (τ₁ $ τ₂) = ap₂ _$_ (↻-subₜ-renₜ τ₁) (↻-subₜ-renₜ τ₂) 
↻-subₜ-renₜ {r = r} {σ} (ρ₂ ∖ ρ₁) = ap₂ _∖_ (↻-subₜ-renₜ ρ₂) (↻-subₜ-renₜ ρ₁)
↻-subₜ-renₜ {r = r} {σ} (⦅ ρ ⦆ ω) = cong-⦅ ↻-subRowₜ-ren ρ ⦆
↻-subₜ-renₜ {r = r} {σ} (l ▹ τ) = ap₂ _▹_ (↻-subₜ-renₜ l) (↻-subₜ-renₜ τ)

↻-subRowₜ-ren [] = refl
↻-subRowₜ-ren {r = r} {σ} ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (↻-subₜ-renₜ τ)) (↻-subRowₜ-ren ρ)

↻-renₜ-sub         : ∀ {σ : Substitution Δ₁ Δ₂}{r : Renaming Δ₂ Δ₃}(τ : Type Δ₁ κ) →
                    sub (renₜ r ∘ σ) τ ≡ renₜ r (sub σ τ)
↻-renRowₜ-sub   : ∀ {σ : Substitution Δ₁ Δ₂}{r : Renaming Δ₂ Δ₃}(τ : RowLiteral (Type Δ₁ κ)) →
                        sub (renₜ r ∘ σ) τ ≡ ren r (sub σ τ)

↻-renₜ-sub {σ = σ} {r} (` α) = refl
↻-renₜ-sub {σ = σ} {r} (`λ τ) = ap `λ (trans (subₜ-cong renₜ-liftₜ-liftsₜ τ) (↻-renₜ-sub τ))
↻-renₜ-sub {σ = σ} {r} (τ₁ · τ₂) = ap₂ _·_ (↻-renₜ-sub τ₁) (↻-renₜ-sub τ₂)
↻-renₜ-sub {σ = σ} {r} (τ₁ `→ τ₂) = ap₂ _`→_ (↻-renₜ-sub τ₁) (↻-renₜ-sub τ₂)
↻-renₜ-sub {σ = σ} {r} (`∀ τ) = ap (`∀) (trans (subₜ-cong renₜ-liftₜ-liftsₜ τ) (↻-renₜ-sub τ))
↻-renₜ-sub {σ = σ} {r} (μ τ) = ap μ (↻-renₜ-sub τ)
↻-renₜ-sub {σ = σ} {r} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    ↻-renₜ-sub {σ = σ} {r} r₁ 
  | ↻-renₜ-sub {σ = σ} {r} r₂ 
  | ↻-renₜ-sub {σ = σ} {r} r₃ 
  | ↻-renₜ-sub {σ = σ} {r} τ = refl
↻-renₜ-sub {σ = σ} {r} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    ↻-renₜ-sub {σ = σ} {r} r₁ 
  | ↻-renₜ-sub {σ = σ} {r} r₂ 
  | ↻-renₜ-sub {σ = σ} {r} τ = refl
↻-renₜ-sub {σ = σ} {r} (lab l) = refl
↻-renₜ-sub {σ = σ} {r} (τ₁ ▹ τ₂) = ap₂ _▹_ (↻-renₜ-sub τ₁) (↻-renₜ-sub τ₂)
↻-renₜ-sub {σ = σ} {r} Π = refl
↻-renₜ-sub {σ = σ} {r} Σ = refl
↻-renₜ-sub {σ = σ} {r} (τ₁ $ τ₂) = ap₂ _$_ (↻-renₜ-sub τ₁) (↻-renₜ-sub τ₂)
↻-renₜ-sub {σ = σ} {r} (ρ₂ ∖ ρ₁) = ap₂ _∖_ (↻-renₜ-sub ρ₂) (↻-renₜ-sub ρ₁)
↻-renₜ-sub {σ = σ} {r} (⦅ ρ ⦆ ω) = cong-⦅ ↻-renRowₜ-sub {σ = σ} {r} ρ ⦆

↻-renRowₜ-sub {σ = σ} {r} [] = refl
↻-renRowₜ-sub {σ = σ} {r} ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (↻-renₜ-sub τ)) (↻-renRowₜ-sub ρ)

subₜ-weaken : ∀ (τ : Type Δ κ₁) (v : Type Δ κ₂) → 
             sub (extendₜ ` v) (renₜ S τ) ≡ τ 
subₜ-weaken τ v = trans (sym (↻-subₜ-renₜ {r = S} {σ = extendₜ ` v} τ)) (sub-id τ)

-------------------------------------------------------------------------------
-- Arrow functor law for liftsₜ & sub (needs commutativity of sub and renₜ)

liftsₜ-comp : ∀ (σ₁ : Substitution Δ₁ Δ₂)(σ₂ : Substitution Δ₂ Δ₃)
                (x : TVar (Δ₁ , κ₁) κ₂) → liftsₜ (sub σ₂ ∘ σ₁) x ≡ sub (liftsₜ σ₂) (liftsₜ σ₁ x)
liftsₜ-comp σ₁ σ₂ Z = refl
liftsₜ-comp σ₁ σ₂ (S x) = trans (sym (↻-renₜ-sub (σ₁ x))) (↻-subₜ-renₜ (σ₁ x)) 

subₜ-comp : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₂ Δ₃}
                (τ : Type Δ₁ κ) → sub (sub σ₂ ∘ σ₁) τ ≡ sub σ₂ (sub σ₁ τ)
subRowₜ-comp : ∀ {σ₁ : Substitution Δ₁ Δ₂}{σ₂ : Substitution Δ₂ Δ₃}
                (τ : RowLiteral (Type Δ₁ κ)) → sub (sub σ₂ ∘ σ₁) τ ≡ sub σ₂ (sub σ₁ τ)

subₜ-comp (` α) = refl
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`λ τ) = 
  ap `λ ((trans 
    (subₜ-cong (liftsₜ-comp σ₁ σ₂) τ) 
    (subₜ-comp {σ₁ = liftsₜ σ₁} {σ₂ = liftsₜ σ₂} τ)))
subₜ-comp (τ₁ · τ₂) = ap₂ _·_ (subₜ-comp τ₁) (subₜ-comp τ₂)
subₜ-comp (τ₁ `→ τ₂) = ap₂ _`→_ (subₜ-comp τ₁) (subₜ-comp τ₂)
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} (`∀ τ) =   
  ap (`∀) ((trans 
    (subₜ-cong (liftsₜ-comp σ₁ σ₂) τ) 
    (subₜ-comp {σ₁ = liftsₜ σ₁} {σ₂ = liftsₜ σ₂} τ)))
subₜ-comp (μ τ) = ap μ (subₜ-comp τ)
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((r₁ · r₂ ~ r₃) ⇒ τ) rewrite 
    subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₁ 
  | subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₂ 
  | subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₃ 
  | subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} ((r₁ ≲ r₂) ⇒ τ) rewrite 
    subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₁ 
  | subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} r₂ 
  | subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} τ = refl
subₜ-comp (lab l) = refl
subₜ-comp Π = refl
subₜ-comp Σ = refl
subₜ-comp (τ₁ $ τ₂) = ap₂ _$_ (subₜ-comp τ₁) (subₜ-comp τ₂)
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} (⦅ ρ ⦆ ω) = cong-⦅ subRowₜ-comp {σ₁ = σ₁} {σ₂} ρ ⦆
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} (ρ₂ ∖ ρ₁) = ap₂ _∖_ (subₜ-comp ρ₂) (subₜ-comp ρ₁)
subₜ-comp {σ₁ = σ₁} {σ₂ = σ₂} (l ▹ τ) = ap₂ _▹_ (subₜ-comp l) (subₜ-comp τ)

subRowₜ-comp [] = refl
subRowₜ-comp ((l , τ) ∷ ρ) = ap₂ _∷_ (cong₂ _,_ refl (subₜ-comp τ)) (subRowₜ-comp ρ)

-------------------------------------------------------------------------------
-- lifting commutes with weakening

↻-liftsₜ-weaken : ∀ {κ' : Kind} (σ : Substitution Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                sub (liftsₜ {κ = κ'} σ) (renₜ S τ) ≡ renₜ S (sub σ τ)
↻-liftsₜ-weaken {κ' = κ'} σ τ = 
  trans 
    (sym (↻-subₜ-renₜ {r = S} {σ = liftsₜ σ} τ)) 
    (↻-renₜ-sub {σ = σ} {r = S} τ)


-------------------------------------------------------------------------------
-- Renaming by r is equivalent to substitution by the identity sub composed with r 

renₜ-sub-id : ∀ (r : Renaming Δ₂ Δ₃) 
                (τ :  Type Δ₂ κ) → renₜ r τ ≡ sub (` ∘ r) τ
renₜ-sub-id r τ = trans (ap (renₜ r) (sym (sub-id τ))) (trans (sym (↻-renₜ-sub τ)) refl )
-------------------------------------------------------------------------------
-- Renaming commutes with β-reduction

↻-renₜ-β      : (r : Renaming Δ₁ Δ₂) (τ₁ : Type (Δ₁ , κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                renₜ r (τ₁ βₜ[ τ₂ ]) ≡ (renₜ (liftₜ r) τ₁) βₜ[ (renₜ r τ₂) ]  
↻-renₜ-β r τ₁ τ₂ = 
  trans 
    (sym (↻-renₜ-sub τ₁)) 
    (trans 
      (subₜ-cong (λ { Z → refl ; (S x) → refl }) τ₁) 
      (↻-subₜ-renₜ {r = liftₜ r} {extendₜ ` (renₜ r τ₂)} τ₁))                  

-------------------------------------------------------------------------------
-- Substitution commutes with β-reduction 

↻-subₜ-β      : (σ : Substitution Δ₁ Δ₂) (τ₁ : Type (Δ₁ , κ₁) κ₂) (τ₂ : Type Δ₁ κ₁) → 
                (sub (liftsₜ σ) τ₁ βₜ[ sub σ τ₂ ]) ≡ sub σ (τ₁ βₜ[ τ₂ ])
↻-subₜ-β σ τ₁ τ₂ = 
  trans 
    (sym (subₜ-comp {σ₁ = liftsₜ σ} {extendₜ ` (sub σ τ₂)} τ₁)) 
    (trans 
      (subₜ-cong (λ { Z → refl
                    ; (S x) → trans 
                        (sym (↻-subₜ-renₜ {r = S} {extendₜ ` (sub σ τ₂)} (σ x))) 
                        (sub-id (σ x)) }) τ₁) 
      (subₜ-comp {σ₁ = extendₜ ` τ₂} {σ} τ₁))

--------------------------------------------------------------------------------
-- Substitution commutes with mapping over rows

↻-sub-map : ∀ (σ : Substitution Δ₁ Δ₂) (F : Type Δ₁ (κ₁ `→ κ₂)) (ρ : RowLiteral (Type Δ₁ κ₁)) → 
              map (map₂ (sub σ F ·_)) (sub σ ρ) ≡ sub σ (map (map₂ (F ·_)) ρ)
↻-sub-map σ F [] = refl 
↻-sub-map σ F (x ∷ ρ) = ap (_ ∷_) (↻-sub-map σ F ρ)

--------------------------------------------------------------------------------
-- An empty substitution behaves as the identity

emptySub : ∀ (τ : Type ∅ κ) → (σ : Substitution ∅ ∅) → 
                sub σ τ ≡ τ
emptySub τ σ = trans (subₜ-cong {σ₁ = σ} {σ₂ = `} (λ { () }) τ) (sub-id τ)

realEmptySub : ∀ (τ : Type ∅ κ) → 
               sub (λ ()) τ ≡ τ 
realEmptySub τ = trans (subₜ-cong {σ₁ = λ ()} {σ₂ = `} (λ { () }) τ) (sub-id τ)


-------------------------------------------------------------------------------
-- Extension of a weakening over a lifting is just the renaming

subₜ-weaken-over-lift : ∀ (r : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ₁) (v : Type Δ₂ κ₂) → 
                        renₜ r τ ≡ (renₜ (liftₜ r) (weakenₜ τ)) [ (extendₜ ` v) ]ₛ 
subₜ-weaken-over-lift r τ v = 
  (trans 
    (trans 
      (renₜ-sub-id r τ)
      (↻-subₜ-renₜ τ))
    (↻-subₜ-renₜ (weakenₜ τ)))

