-- 
module Rome.NormalTypes.NBE.Renaming where

open import Rome.Prelude
open import Rome.Kinds.Syntax
open import Rome.Kinds.GVars

open import Rome.Types.Syntax
open import Rome.Types.Renaming

open import Rome.NormalTypes.Syntax
open import Rome.NormalTypes.Renaming

open import Rome.NormalTypes.NBE.Syntax

open import Data.List.Properties using (map-id ; map-cong; map-∘)
import Data.List.Relation.Unary.All as All
open All using (All)

--------------------------------------------------------------------------------
-- Renaming semantic types.

renKripke : Renaming Δ₁ Δ₂ → KripkeFunction Δ₁ κ₁ κ₂ → KripkeFunction Δ₂ κ₁ κ₂
renKripke {Δ₁} ρ F {Δ₂} = λ ρ' → F (ρ' ∘ ρ) 

renSem : Renaming Δ₁ Δ₂ → SemType Δ₁ κ → SemType Δ₂ κ
renRow : Renaming Δ₁ Δ₂ → 
         Row (SemType Δ₁ κ) → 
         Row (SemType Δ₂ κ)

orderedRenRow : ∀ {n} {Δ₁ : KEnv} {Δ₂ : KEnv} {κ : Kind} {P : Fin n → Label × SemType Δ₁ κ} → (r : Renaming Δ₁ Δ₂) → 
                OrderedRow′ n P → OrderedRow′ n (λ i → (P i .fst) , renSem r (P i .snd))

nrRenSem :  ∀ (r : Renaming Δ₁ Δ₂) → (ρ : SemRow Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             notRowLiteral ρ → notRowLiteral (renSem r ρ)
nrRenSem' : ∀ (r : Renaming Δ₁ Δ₂) → (ρ₂ ρ₁ : SemRow Δ₁ (λ Δ' → SemType Δ' κ) R[ κ ]) → 
             notRowLiteral ρ₂ or notRowLiteral ρ₁ → notRowLiteral (renSem r ρ₂) or notRowLiteral (renSem r ρ₁)

renSem {κ = ★} r τ = ren r τ
renSem {κ = L} r τ = ren r τ
renSem {κ = κ `→ κ₁} r F = λ r' → F (r' ∘ r)
renSem {κ = R[ κ ]} r (φ $ x) = (λ {Δ₃} r' → φ (r' ∘ r)) $ (ren r x)
renSem {κ = R[ κ ]} r (l ▹ τ) = (ren r l) ▹ renSem r τ
renSem {κ = R[ κ ]} r (row (n , P) q) = row (n , ( map₂ (renSem r) ∘ P)) (orderedRenRow r q)
renSem {κ = R[ κ ]} r ((ρ₂ ∖ ρ₁) {nr}) = (renSem r ρ₂ ∖ renSem r ρ₁) {nr = nrRenSem' r ρ₂ ρ₁ nr}

nrRenSem' r ρ₂ ρ₁ (left x) = left (nrRenSem r ρ₂ x)
nrRenSem' r ρ₂ ρ₁ (right y) = right (nrRenSem r ρ₁ y)

nrRenSem r (x ▹ x₁) nr = tt
nrRenSem r (ρ ∖ ρ₁) nr = tt
nrRenSem r (φ $ ρ) nr = tt

orderedRenRow {n = zero} {P} r o = tt
orderedRenRow {n = suc zero} {P} r o = tt
orderedRenRow {n = suc (suc n)} {P = P} r (l₁<l₂ , o) =  l₁<l₂  , (orderedRenRow {n = suc n} {P = P ∘ fsuc} r o)

renRow φ (n , P) = n , map₂ (renSem φ) ∘ P 

--------------------------------------------------------------------------------
-- Weakening

weakenSem : SemType Δ κ₁ → SemType (Δ , κ₂) κ₁
weakenSem {Δ = Δ} {κ₁ = κ₁} τ = renSem {Δ₁ = Δ} {κ = κ₁} S τ

  




