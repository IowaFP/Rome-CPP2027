# Managerial / infrastructural
- [x] Create public repo "RomeNBE-CPP2027", rename this one to Rome-CPP2026 (private)
- [x] Clean up this entire repo, actually, and couple/publish .lagda and .latex with code 
- [x] Remove header.tex; unfuck package management
- [ ] Upload artifact to Zenodo
- [ ] FIX CITATION TO ZENODO in .bib!
- [ ] Upload pre-print to arxiv
- [ ] When ready to publish, nuke the git history

# Rosi Pygments
- [x] Add Rosi pygments to its own repo
  - [x] Update so that $ and \mathdollar are not red-highlighted
- [x] Update rosi-pygments so that ⋆ and L are reserved keywords

# Styling / formatting
- [x] Format inlined Rosi code, and some Agda code, to \R
- [x] Format Rosi code segments with minted using dissertation styling
- [x] Change all ' to ′
- [x] Replace `sub` with `_[_]_{\sigma}`
- [x] Can I make the Agda and Rosi colors match? Would probably need to implement my own Minted color theme.
  - Update: Yes, I did have to. See Rosi Pygments.
- [x] Format in-lined agda using native TeX macros
  - Rely on Math Mode in **General**, only use in-lining for *references to specific Agda constructs*, e.g., the names "Type, NormalType", etc.
  - Just check what's in NBE.tex and copy the styling directly.
  - Less painful than Agda's experimental support for automatica-inlining (see [documentation](https://agda.readthedocs.io/en/latest/tools/generating-latex.html#latex-inline-references))
    

# Writing
- [x] Change example in paper to be over row singletons Π (l ▹ λ x. τ) ≡ₜ λ x. Π (l ▹ τ); 
      link to derivation.
- [x] Remove claim of strong normalization.
- [x] Explain that consistency *is* weak normalization.
- [x] Clarify nomenclature divergence
- [x] Use and explain ωmap
- [x] Expand on PER and other properties of consistency/soundness relations
- [ ] Outline intended changes to draft in response to reviewer feedback
- [ ] Implement copy changes
- [x] Add citations to Zenodo & github
- [x] Add hyperlinks for each claim to public repo
- [x] **Refactor README.lagda.md** to reference new section numbers, titles, and locations
- [ ] Trim back down to 13 pages

# Code 
- [x] Change semantic helpers to be <$>, <Π>, etc
- [x] Change subtitution syntax to `_[_]ₛ` via typeclass
- [x] Change ₖ to ₜ
- [x] Change ≡t to ≡ₜ, ≡p to ≡ₚ, ≡r to ≡ᵣ, and format Unicode char to print as _{\tau}, _{\pi}, _{\rho}
- [x] Change `[[_]]r~~` to `[[_]]_{ρ}~~`
- [x] Change eval to `[[_]]_{t}`
  - [x] evalRow to `[[_]]_{r}`
  - [x] evalpred to `[[_]]_{p}` 
- [x] Refactor completeness code to use `_≡ₜ_` infix notation
- [x] Refactor Ordered to ω
- [x] Use a typeclass for ⇓, or rename to subscripted
  - [x] Can likewise use a typeclass for evaluation
- [x] ~~In response to cranky reviewer: Prove strong normalization.~~
  - (It is not true.)
- [x] Use ωmap instead of fromWitness (foo (toWitness)) etc in text

# elsewhere
- [ ] Update github.com/IowaFP/ROmega to acccommate changes to syntax made in the code here
