-- 
module Rome.Types.Properties.Renaming where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars
open import Rome.Types.Syntax
open import Rome.Types.Renaming
open import Rome.Types.Substitution



--------------------------------------------------------------------------------
-- Renaming commutes over complement

∈L-ren : ∀ (r : Renaming Δ₁ Δ₂) → {ρ : RowLiteral (Type Δ₁ κ)} → 
                 (l : Label) → l ∈L ρ → l ∈L ren r ρ
∈L-ren r {ρ} l Here = Here
∈L-ren r {ρ} l (There ev) = There (∈L-ren r l ev)

renRowₜ-∈L : ∀ (r : Renaming Δ₁ Δ₂) → {ρ : RowLiteral (Type Δ₁ κ)} → 
                 (l : Label) → l ∈L ren r ρ → l ∈L ρ
renRowₜ-∈L r {(l' , τ) ∷ ρ} l Here = Here
renRowₜ-∈L r {(l' , τ) ∷ ρ} l (There ev) = There (renRowₜ-∈L r l ev)

↻-renRowₜ-∖s : ∀ (r : Renaming Δ₁ Δ₂) → {ρ₂ ρ₁ : RowLiteral (Type Δ₁ κ)} → 
       ren r (ρ₂ ∖s ρ₁) ≡ ren r ρ₂ ∖s ren r ρ₁
↻-renRowₜ-∖s r {[]} {ρ₁} = refl
↻-renRowₜ-∖s r {(l , τ) ∷ ρ₂} {ρ₁} with l ∈L? ρ₁ | l ∈L? ren r ρ₁
... | yes p | yes q = ↻-renRowₜ-∖s r {ρ₂} {ρ₁}
... | yes  p | no q = ⊥-elim (q (∈L-ren r l p))
... | no  p | yes q = ⊥-elim (p (renRowₜ-∈L r l q))
... | no  p | no q = ap ((l , renₜ r τ) ∷_) (↻-renRowₜ-∖s r {ρ₂} {ρ₁})

--------------------------------------------------------------------------------
-- lifting respects congruence, identities, and composition.
-- 

liftₜ-id : ∀ (x : TVar (Δ , κ₂) κ₁) → liftₜ id x ≡ x
liftₜ-id Z = refl
liftₜ-id (S x) = refl

liftₜ-comp : ∀ (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) → 
            ∀ (x : TVar (Δ₁ , κ₂) κ₁) → liftₜ (r₂ ∘ r₁) x ≡ liftₜ r₂ (liftₜ r₁ x)
liftₜ-comp r₁ r₂ Z = refl
liftₜ-comp r₁ r₂ (S x) = refl

liftₜ-cong : ∀ {r₁ r₂ : Renaming Δ₁ Δ₂} → (∀ {κ : Kind} (x : TVar Δ₁ κ) → r₁ x ≡ r₂ x) → 
              (x : TVar (Δ₁ , κ₂) κ) → liftₜ r₁ x ≡ liftₜ r₂ x
liftₜ-cong eq Z = refl
liftₜ-cong eq (S x) = ap S (eq x)


--------------------------------------------------------------------------------
-- Renaming respects congruence

renₜ-cong :  ∀ {r₁ r₂ : Renaming Δ₁ Δ₂} →  (∀  {κ : Kind} (x : TVar Δ₁ κ) → r₁ x ≡ r₂ x) → 
              (τ : Type Δ₁ κ) → renₜ r₁ τ ≡ renₜ r₂ τ
renRowₜ-cong : ∀ {r₁ r₂ : Renaming Δ₁ Δ₂} →  (∀ {κ : Kind} (x : TVar Δ₁ κ) → r₁ x ≡ r₂ x) → 
                  (xs : RowLiteral (Type Δ₁ κ)) → ren r₁ xs ≡ ren r₂ xs
renPredₜ-cong : ∀ {r₁ r₂ : Renaming Δ₁ Δ₂} →  (∀ {κ : Kind} (x : TVar Δ₁ κ) → r₁ x ≡ r₂ x) → 
                  (π : Pred (Type Δ₁ R[ κ ])) → ren r₁ π ≡ ren r₂ π
                  
renₜ-cong eq (` x) rewrite eq x = refl
renₜ-cong eq (`λ τ)  = ap `λ (renₜ-cong (liftₜ-cong eq) τ)
renₜ-cong eq (τ₁ · τ₂) rewrite renₜ-cong eq τ₁ | renₜ-cong eq τ₂ = refl
renₜ-cong eq (τ₁ `→ τ₂) rewrite renₜ-cong eq τ₁ | renₜ-cong eq τ₂ = refl
renₜ-cong eq (π ⇒ τ) rewrite renPredₜ-cong eq π | renₜ-cong eq τ = refl
renₜ-cong eq (`∀ τ) rewrite renₜ-cong (liftₜ-cong eq) τ = refl
renₜ-cong eq (μ F) rewrite renₜ-cong eq F = refl 
renₜ-cong eq Π = refl 
renₜ-cong eq Σ = refl 
renₜ-cong eq (lab _) = refl
renₜ-cong eq (f $ a) rewrite renₜ-cong eq f | renₜ-cong eq a = refl
renₜ-cong {r₁ = r₁} {r₂} eq (⦅ ρ ⦆ ω) = cong-⦅ renRowₜ-cong eq ρ ⦆ 
renₜ-cong eq (ρ₂ ∖ ρ₁) rewrite renₜ-cong eq ρ₂ | renₜ-cong eq ρ₁ = refl
renₜ-cong eq (l ▹ τ) = ap₂ _▹_ (renₜ-cong eq l) (renₜ-cong eq τ) 

renPredₜ-cong eq (r₁ · r₂ ~ r₃) 
  rewrite renₜ-cong eq r₁ | renₜ-cong eq r₂ | renₜ-cong eq r₃ = refl
renPredₜ-cong eq (r₁ ≲ r₂) 
  rewrite renₜ-cong eq r₁ | renₜ-cong eq r₂ = refl

renRowₜ-cong eq [] = refl
renRowₜ-cong eq ((l , τ) ∷ xs) = ap₂ _∷_ (cong₂ _,_ refl (renₜ-cong eq τ)) (renRowₜ-cong eq xs)

-- --------------------------------------------------------------------------------
-- -- Renaming respects identities.

renₜ-id : ∀ (τ : Type Δ κ) → renₜ id τ ≡ τ
renPredₜ-id : ∀ (π : Pred (Type Δ R[ κ ])) → ren id π ≡ π
renRowₜ-id : ∀ (ρ : RowLiteral (Type Δ κ)) → ren id ρ ≡ ρ

renₜ-id (` x) = refl
renₜ-id (`λ τ) rewrite renₜ-cong liftₜ-id τ | renₜ-id τ = refl 
renₜ-id (τ₁ · τ₂) rewrite renₜ-id τ₁ | renₜ-id τ₂ = refl
renₜ-id (τ₁ `→ τ₂) rewrite renₜ-id τ₁ | renₜ-id τ₂ = refl
renₜ-id (π ⇒ r) rewrite renPredₜ-id π | renₜ-id r  = refl
renₜ-id (`∀ τ) rewrite renₜ-cong liftₜ-id τ | renₜ-id τ = refl
renₜ-id (μ F) rewrite renₜ-id F = refl
renₜ-id Π = refl
renₜ-id Σ = refl
renₜ-id (lab _) = refl
renₜ-id (f $ a) rewrite renₜ-id f | renₜ-id a = refl
renₜ-id (⦅ ρ ⦆ ω)  =  cong-⦅ renRowₜ-id ρ ⦆
renₜ-id (ρ₂ ∖ ρ₁) rewrite renₜ-id ρ₂ | renₜ-id ρ₁ = refl
renₜ-id (l ▹ τ) rewrite renₜ-id l | renₜ-id τ = refl

renPredₜ-id (ρ₁ · ρ₂ ~ ρ₃) 
  rewrite renₜ-id ρ₁ | renₜ-id ρ₂ | renₜ-id ρ₃ = refl
renPredₜ-id (ρ₁ ≲ ρ₂)
  rewrite renₜ-id ρ₁ | renₜ-id ρ₂ = refl 

renRowₜ-id [] = refl
renRowₜ-id ((l , τ) ∷ xs) = ap₂ _∷_ (cong₂ _,_ refl (renₜ-id τ)) (renRowₜ-id xs)

--------------------------------------------------------------------------------
-- Renaming respects composition.

renₜ-comp : ∀ (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) → 
           ∀ (τ : Type Δ₁ κ) → renₜ (r₂ ∘ r₁) τ ≡ renₜ r₂ (renₜ r₁ τ)
renPredₜ-comp : ∀ (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) → 
                ∀ (π : Pred (Type Δ₁ R[ κ ])) → ren (r₂ ∘ r₁) π ≡ ren r₂ (ren r₁ π)
renRowₜ-comp : ∀ (r₁ : Renaming Δ₁ Δ₂) (r₂ : Renaming Δ₂ Δ₃) → 
                ∀ (ρ : RowLiteral (Type Δ₁ κ)) → ren (r₂ ∘ r₁) ρ ≡ ren r₂ (ren r₁ ρ)

renₜ-comp r₁ r₂ (` x) = refl
renₜ-comp r₁ r₂ Π = refl
renₜ-comp r₁ r₂ Σ = refl
renₜ-comp r₁ r₂ (`λ τ)  rewrite
  trans (renₜ-cong (liftₜ-comp r₁ r₂) τ) (renₜ-comp (liftₜ r₁) (liftₜ r₂) τ) = refl
renₜ-comp r₁ r₂ (τ₁ · τ₂) rewrite
    renₜ-comp r₁ r₂ τ₁ 
  | renₜ-comp r₁ r₂ τ₂ = refl
renₜ-comp r₁ r₂ (τ₁ `→ τ₂) rewrite
    renₜ-comp r₁ r₂ τ₁ 
  | renₜ-comp r₁ r₂ τ₂ = refl
renₜ-comp r₁ r₂ (`∀ τ) rewrite
  (trans (renₜ-cong (liftₜ-comp r₁ r₂) τ) (renₜ-comp (liftₜ r₁) (liftₜ r₂) τ)) = refl
renₜ-comp r₁ r₂ (μ F) rewrite
  renₜ-comp r₁ r₂ F = refl
renₜ-comp r₁ r₂ (lab _) = refl
renₜ-comp r₁ r₂ (ρ₂ ∖ ρ₁) rewrite renₜ-comp r₁ r₂ ρ₂ | renₜ-comp r₁ r₂ ρ₁ = refl
renₜ-comp r₁ r₂ (f $ a) rewrite renₜ-comp r₁ r₂ f | renₜ-comp r₁ r₂ a = refl
renₜ-comp r₁ r₂ (π ⇒ τ) rewrite renPredₜ-comp r₁ r₂ π | renₜ-comp r₁ r₂ τ = refl
renₜ-comp r₁ r₂ (⦅ ρ ⦆ ω) = cong-⦅ renRowₜ-comp r₁ r₂ ρ ⦆ 
renₜ-comp r₁ r₂ (l ▹ τ) = ap₂ _▹_ (renₜ-comp r₁ r₂ l) (renₜ-comp r₁ r₂ τ)

renPredₜ-comp r r' (r₁ · r₂ ~ r₃) 
  rewrite renₜ-comp r r' r₁ | renₜ-comp r r' r₂ | renₜ-comp r r' r₃ = refl
renPredₜ-comp r r' (r₁ ≲ r₂)
  rewrite renₜ-comp r r' r₁ | renₜ-comp r r' r₂ = refl 

renRowₜ-comp r₁ r₂ [] = refl
renRowₜ-comp r₁ r₂ ((l , τ) ∷ r) = ap₂ _∷_ (cong₂ _,_ refl (renₜ-comp r₁ r₂ τ)) (renRowₜ-comp r₁ r₂ r)

↻-liftₜ-weaken : ∀ {κ' : Kind} (r : Renaming Δ₁ Δ₂) (τ : Type Δ₁ κ) → 
                renₜ (liftₜ {κ = κ'} r) (renₜ S τ) ≡ renₜ S (renₜ r τ)
↻-liftₜ-weaken {κ' = κ'} r τ rewrite sym (renₜ-comp (S {κ₂ = κ'}) (liftₜ r) τ) | renₜ-comp r (S {κ₂ = κ'}) τ = refl
    
--------------------------------------------------------------------------------
-- Renaming commutes with mapping over rows

↻-ren-map : ∀ (r : Renaming Δ₁ Δ₂) (F : Type Δ₁ (κ₁ `→ κ₂)) (ρ : RowLiteral (Type Δ₁ κ₁)) → 
              map (map₂ (renₜ r F ·_)) (ren r ρ) ≡ ren r (map (map₂ (F ·_)) ρ)
↻-ren-map φ F [] = refl 
↻-ren-map φ F (x ∷ ρ) = ap (_ ∷_) (↻-ren-map φ F ρ)
