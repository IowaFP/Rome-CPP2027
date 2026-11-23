# Normalization by Evaluation of Higher-Order Rows: a walk-through

```agda 
module Rome.README where 
```

## Installation
[Install Agda](https://agda.readthedocs.io/en/nightly/getting-started/installation.html) and Agda's [standard library](https://github.com/agda/agda-stdlib). This repository was built on:
- [agda 2.8.0.2](https://github.com/agda/agda/releases/#release-v2.8.0.2) (branch [release-2.8.0.2](https://github.com/agda/agda/tree/release-2.8.0.2))
- [agda-stdlib 2.4](https://github.com/agda/agda-stdlib/releases/tag/v2.4) (branch [v2.4-release](https://github.com/agda/agda-stdlib/tree/v2.4-release))

You can install specific agda versions either by:
1. downloading binaries from tagged [agda](https://github.com/agda/agda/tags) and [agda-stdlib](https://github.com/agda/agda-stdlib/tags) releases; or, 
2. installing a specific branch (e.g., `release-2.8.0.2`) via [Agda's source](https://github.com/agda/agda) and likewise cloning and checking out a specific branch of [agda-stdlib](https://github.com/agda/agda-stdlib). 

Rome should compile on slightly older/newer versions. At the time of writing, Agda 2.9 and 2.10 have been released, but do not have a compatible standard library release.

# Summary & Main Claims
For those seeking a brief exposé: the main claims of our paper
are given by: 

1. [Canonicity of normal types](./NormalTypes/Properties/Canonicity.agda)
2. [Stability, idempotency, and surjectivity of normalization](./Metatheory/NBE/Stability.agda)
3. [Soundness of the equational theory](./Metatheory/NBE/Soundness.agda)
4. [Consistency of the equational theory](./Metatheory/NBE/Consistency.agda)
4. [Completeness of the equational theory](./Metatheory/NBE/Completeness.agda)
5. [Decidability of Type Equivalence](./Metatheory/Decidability.agda)

# Technical Overview

The rest of this document serves to guide the reader through the Rome development and its correspondence to the claims in the paper. 

## Prelude 

Firstly, `Rome.Prelude` re-exports a number of modules from Agda's standard libraries and provides some common utilities. 

```agda 
open import Rome.Prelude.Base public
```

We borrow some notation and conventions from HoTT, e.g. we write: 
- `ap` for *action on paths* in lieu of `cong`;
- `tr` for *transport* in lieu of `subst`; 
- `_⁻¹` for sym; and
- `_○_` for trans

**But**, we do *not* presume univalence in any form, nor is this a cubical Agda development. To facilitate wide reuse of syntax like `_○_` for transitivity and `_⁻¹` for symmetry across propositional equality, homotopy, and type equivalence, we create a typeclass for Groupoid and Order syntax in:

```agda
open import Rome.Prelude.Groupoids public
```

We also add some functionality for Homotopies in:

```agda 
open import Rome.Prelude.Homotopies public
``` 

The modules `Levels` and `Sets`

```agda 
open import Rome.Prelude.GVars.Levels public
open import Rome.Prelude.GVars.Sets public
``` 

export generalized variables for levels (e.g., ℓ, ℓ₁ , ...) and sets (e.g., A : Set ℓ, B : Set ℓ, ...). 

### Prelude.Containment 

The `Containment` module contains some definitions and lemmas for list containment. Specifically, it has some definitions that help when working with row literals.

```agda
open import Rome.Prelude.Containment public
``` 

## Kind syntax (§ 3.1)

The syntax of kinds, kinding environments, and type variables is given by:

```agda 
open import Rome.Kinds.Syntax public 
``` 

We also define some generalized variables, e.g., Δ for kinding envs and κ for Kinds, in: 
```agda 
open import Rome.Kinds.GVars public
```

That syntactic kind equality is decidable (§7.3) is defined in: 

```agda 
open import Rome.Kinds.Properties.Decidability public
```

## Types (§3.2)

The syntax of types, row literals, and predicates is defined in: 

```agda
open import Rome.Kinds.Syntax public
``` 

Type renaming and substitution are defined in: 

```agda 
open import Rome.Types.Renaming public
open import Rome.Types.Substitution public
``` 

Properties of renaming and substitution (i.e., lemmas and theorems) are defined in:

```agda 
open import Rome.Types.Properties.Renaming public
open import Rome.Types.Properties.Substitution public
```

### Type Equivalence (§3.3)

The inductive relation `_≡t_` for type equivalence, as well as its metatheoretic properties, are defined (resp.) in:

```agda 
open import Rome.Types.Equivalence public
open import Rome.Types.Properties.Equivalence public
```

The claim in §3.3 that Π and Σ commute over λ-bindings is given in:

```agda 
open import Rome.Types.Properties.Derivable public
```

## Normal Types (§3.4)

The syntax of normal types is defined in: 

```agda
open import Rome.NormalTypes.Syntax public
``` 

Renaming (§4.1) and substitution (§4.2), as well as their properties, are defined in:

```agda 
open import Rome.NormalTypes.Renaming public
open import Rome.NormalTypes.Substitution public
open import Rome.NormalTypes.Properties.Renaming public
open import Rome.NormalTypes.Properties.Substitution public
``` 

That normal type equality (§7.5) is decidable is defined in: 

```agda 
open import Rome.NormalTypes.Properties.Decidability public
``` 

Canonicity of normal forms (§7.1) is given in: 

```agda 
open import Rome.Metatheory.Canonicity public
``` 

## Semantic Domain (§5) 

The semantic domains and Normalization by Evaluation (NbE) machinery is all defined in `NBE`.

The syntax and renaming (§5.1) of semantic types are defined in: 

```agda 
open import Rome.NBE.Syntax public
open import Rome.NBE.Renaming public
```

### Normalization by Evaluation (§5--§6)

Reflection (§5.2), reification (§5.3), and evaluation (§6) are defined in: 

```agda 
open import Rome.NBE.Normalization public
``` 

## Metatheory (§7)

most main theorems and lemmas are housed in `Rome.Metatheory`, with some exception: 

### Canonicity of Normal Types

Canonicity of Normal types is defined in `Rome.Metatheory.Canonicity` (above).

### Stability 

Stability is defined and proven in: 

```agda
open import Rome.Metatheory.Stability public 
``` 

### Soundness 

The soundness logical relation is defined in: 

```agda 
open import Rome.Metatheory.Soundness.Relation public
``` 

We require a great deal of commutativity lemmas to prove the fundamental lemma,
which are given in: 

```agda 
open import Rome.Metatheory.Soundness.Commutativity public
``` 

We also require a great deal of congruence lemmas, given in: 

```agda 
open import Rome.Metatheory.Soundness.Congruence public
``` 

Finally, the fundamental lemma and soundness are proven in: 

```agda 
open import Rome.Metatheory.Soundness public 
``` 

### Consistency

The consistency logical relation is defined in: 

```agda 
open import Rome.Metatheory.Consistency.Relation public
``` 

The fundamental lemma and consistency are proven in: 

```agda 
open import Rome.Metatheory.Consistency public 
``` 

### Completeness 

Completeness follows from consistency, which is shown in: 

```agda 
open import Rome.Metatheory.Completeness public
``` 

### Normalization 

That the step relation is normalizing is proved, at least in essence, by:

```agda
open import Rome.Metatheory.Normalization public
``` 

### Decidability of Type Equivalence

Decidability of type equivalence follows from soundness, completeness,
and the decidability of equality on normal forms:

```agda 
open import Rome.Metatheory.Decidability public
``` 




