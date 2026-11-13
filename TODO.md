# Managerial / infrastructural
- [ ] Create public repo "RomeNBE-CPP2027", rename this one to Rome-CPP2026 (private)
- [ ] Clean up this entire repo, actually, and couple/publish .lagda and .latex with code 
- [ ] Upload artifact to Zenodo
- [x] Add Rosi pygments to its own repo
  - [x] Update so that $ and \mathdollar are not red-highlighted
- [ ] When ready to publish, nuke the git history

# Writing
- [ ] Outline intended changes to draft in response to reviewer feedback
- [ ] Implement copy changes
- [ ] Add citations to Zenodo & github
- [ ] Add hyperlinks for each claim to public repo
- [x] Change example in paper to be over row singletons Π (l ▹ λ x. τ) ≡ₜ λ x. Π (l ▹ τ); 
      link to derivation.
- [x] Format inlined Rosi code, and some Agda code, to \R
- [x] Format Rosi code segments with minted using dissertation styling
- [x] Change all ' to ′
- [ ] Can I make the Agda and Rosi colors match? Would probably need to implement my own Minted color theme.
  - Will probably need to build a different Pygments component, so add to iowaFP/rosi-pygments
  - Mainly, change:
    - reserved keywords to Agda's orange
    - Capitalized Type names to Agda's blue
    - Labels to Agda's green

# Code 
- [x] Change semantic helpers to be <$>, <Π>, etc
- [x] Change subtitution syntax to `_[_]σ` via typeclass
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
- [ ] Use ωmap instead of fromWitness (foo (toWitness)) etc in text
- [ ] In response to cranky reviewer: Prove strong normalization.
  - [ ] Weak is just surjectivity... Specify the connection in paper.
 

elsewhere: 
- [ ] Update github.com/IowaFP/ROmega to acccommate changes to syntax made in the code here
