CPP 2027 Paper #14 Reviews and Comments
===========================================================================
Paper #14 Normalization by Evaluation of Higher-Order Rows


Review #14A
===========================================================================

Overall merit
-------------
5. Strong accept

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
This paper presents a higher-kinded row type theory `Rωμ`, an extension of `Rω` with row mappings, iso-recursive types and a complement operator for rows. These extensions made to `Rω` seem to makes the language much more expressive and appropriate for real-world usage rather than simply being a toy-language to prove properties about.
I believe a type system containing both row polymorphism and iso-recursive types to be novel, similarly for the addition of a complement operator.
The paper furthermore presents a Normalization-by-Evaluation (NbE) algorithm for the types of that system, and shows the soundness, consistency and completeness of this algorithm to prove the decidability of type conversion. All of these constructions and proofs are mechanised in Agda's `--safe` fragment, which provides confidence in the correctness of the work produced. The paper provides good explanations of the shortcomings that occured during the formalisation, and the solutions found to circumvent them.

Comments for authors
--------------------
Overall, I think this is a nice paper that presents what seems like sweet spot between expressivity and ease of use. The combination of row-polymorphism and iso-recursive types in particular allows for manipulating complex datatypes internally to the system, without having to rely on full dependent types to achieve that goal. While this paper only discusses the kinds and types of the system, I would expect said type-system to allow for expressive term-level controls. Section 2 offers a glimpse of what `Rωμ` offers, I would be curious to see additional examples.

## Minor comments: 

- L 68 "An equational theory [...] cannot defer to its parent system to inherit a proof of type normalization": Not sure what the sentence tries to say here, clarification needed.
- L118: Π and Σ discussed but not introduced before
- L173: It is not made explicit whether the flap operator is defined at the meta-level or internally to `Rωμ`. I would guess it is the former, as the helper universally quantifies over a kind variable `κ`, which does not seem doable internally.  
- L916: The definition of semantic environment looks rather a lot like a (semantic) substitution.
- L1275: Rocq, not Coq. Also missing a citation like for Lean at L1281.



Review #14B
===========================================================================

Overall merit
-------------
3. Weak accept

Reviewer expertise
------------------
2. Some familiarity

Paper summary
-------------
The paper presents $R\omega\mu$, a higher-order row-type calculus extending System $R\omega$ (Hubers and Morris, ICFP~2023) with row mapping, iso-recursive types, and a row complement operator. It provides a sound and complete equational theory for its types. Types are normalized by evaluation (NbE) in Agda, over intrinsically well-kinded syntax. The authors identify the normal and neutral forms that higher-order rows require: inert maps over neutral rows, singleton rows with neutral labels, ordered row literals and residual complements. The semantic domain interprets arrow kinds as Kripke function spaces and rows as a data type parameterized by a functor, an encoding adapted from Allais et al.\ to satisfy Agda's positivity checker. Evaluation implements $\beta$-reduction, map fusion, distribution of maps over complements, and the reassociation and pushing-in of $\Pi$ and $\Sigma$ over higher-order and nested rows. The metatheory, checked under \ag{-{}-safe}, proves stability (normal forms are fixed points), soundness (equivalent types have equal normal forms) via a uniform, extensional logical relation, and consistency (every type is equivalent to its normal form) via a second Kripke logical relation, from which completeness follows. Together, these give a constructive decision procedure for type equivalence, presented as the first for a higher-order row type theory.

I am just familiar with the topic, so I cannot judge the novelty of the results as an expert would. Within this limit, the paper seems well motivated, technically
solid and carefully mechanized, and fits CPP well. Its NbE adaptations to inert maps, neutral labels, and complements are clearly explained. The weaknesses I noticed are presentational: some overclaims, slips in the rules, and missing artifact details. I lean towards acceptance.

Comments for authors
--------------------
\textbf{Strong normalization (l.~77--79).} The introduction says
  the theory, ``viewed as a reduction sequence, is strongly
  normalizing''. Section~7 proves stability, soundness, and completeness
  of a normalization \emph{function}. It proves neither strong
  normalization of a reduction relation nor confluence. Either drop the
  claim or prove it.

\textbf{The artifact.}
 
Give an (anonymized) link, the Agda and standard-library
    versions, size (lines of code, number of modules) and checking
    time.

Confirm that $\texttt{-{}-safe}$ is used throughout and that nothing is
    postulated.

Add a table mapping each displayed definition and theorem to
    its module.
 

\textbf{Executability.} Since constructiveness is a selling point
  (l.~100--108), show the normalizer at work: for example, the Agda
  normal forms of the types of $\texttt{fmap}\Sigma$ and $\texttt{desugarOr}$
  from Section~2. Comment on efficiency, since rows are represented as
  functions $\mathsf{Fin}\;n \to \mathsf{Label} \times A$.

\textbf{De Bruijn indices and renamings (l.~48, 271--274,
  597--608).} The mechanization uses intrinsically well-scoped
  de~Bruijn variables, under which $\alpha$-equivalent types are
  syntactically identical; yet the paper speaks of renaming variables
  (Sec. 4.1) and, at l.~48, of comparing normal forms ``modulo
  $\alpha$-equivalence''. Please clarify that the renamings
  $\texttt{Renaming}\;\Delta_1\;\Delta_2 =
  \forall\{\kappa\} \to \texttt{TVar}\;\Delta_1\;\kappa \to
  \texttt{TVar}\;\Delta_2\;\kappa$ are not $\alpha$-conversions but
  re-indexings of variables between kinding environments, required
  for weakening: going under a binder shifts the free indices, as in
  the Kripke function spaces (Sec. 5.1), in $\texttt{reflect}} (which uses
  $\texttt{ren}\;r\;\phi$), and in $\texttt{reify}$ (which applies $\phi$ to the
  weakening $\texttt{S}$ and the fresh variable $\texttt{`\,Z}$). Correspondingly,
  the decision procedure of Sec. 7.5 compares normal forms by plain
  syntactic equality, so the phrase ``modulo $\alpha$-equivalence''
  should be removed or qualified.

\textbf{The relation $\approx$ (l.~1040--1087).} Say explicitly
  that mismatched constructors and the $\texttt{no}$ branches of the
  decidable kind and length tests are mapped to~$\bot$. Mention the
  symmetry and transitivity lemmas (it is a partial equivalence
  relation) that the fundamental lemma needs.

\textbf{``Derivable'' rule (l.~477--480).} The rule commuting
  $\Xi \in \{\Pi, \Sigma\}$ over $\lambda$-bindings
  is said to be derivable. Give the derivation.


\textbf{Typos}



l.53  \texttt{"un-stucks"}, straight quotes (also l.~172--173) $\mapsto$
  use TeX quotes \texttt{``\ldots''} 

l.100  propositionally irrelevant universe $\mapsto$ proof-irrelevant universe 

l.192 takes places $\mapsto$  takes place 

l.199 fixedpoint $\mapsto$  fixed point 

l.325--326  Permitting label variables in row literals permits an
  opportunity for row labels to overlap $\mapsto$
  Allowing label variables in row literals would allow labels to
  overlap upon instantiation 

l.474  As this type has arrow kind, It is desirable $\mapsto$
  \ldots, it is desirable 

l.530--531  applicands $\mapsto$ operands
 
l.548  sweet-spot   $\mapsto$ sweet spot 

l.595--596  the painful transports \ldots{} that comes $\mapsto$
  \ldots{} that come 

l.611  A Substitution renames in parallel $\mapsto$
  A Substitution substitutes in parallel 

l.621--622  While each Substitution is a total function, not all
  variables are changed $\mapsto$
  rephrase (the point is that the identity substitution exists) 

l.645  at type and label kind $\mapsto$ at kinds $\star$ and $\Lab$ 

l.707  occurence (twice) $\mapsto$ occurrence 

l.743  while The function $\mapsto$ while the function 

l.765  migh attempt $\mapsto$ might attempt 

l.799  Finally, The NormalType $\mapsto$ Finally, the NormalType 

l.1319  features forbade by $\mapsto$features forbidden by 

\textbf{References}

\textbf{Abel 2013} is a habilitation thesis, not a ``Ph.D. Dissertation''.



Review #14C
===========================================================================

Overall merit
-------------
4. Accept

Reviewer expertise
------------------
3. Knowledgeable

Paper summary
-------------
This paper suggests a calculus with computation for higher-order row types.
Row types map labels to types and are are used to type records and variants structurally. The authors introduce R-omega-mu, an extension of System R-omega by Hubers and Morris with additional type-level computation, including row mapping, a row complement operator, and iso-recursive types.

The main focus is on type conversion. The authors define an equational theory for the calculus and develop a normalization-by-evaluation procedure that reduces types to canonical normal forms. They mechanize the development in Agda and establish properties including stability, soundness, completeness, and decidability of type equivalence.

Comments for authors
--------------------
Strengths: 
- I enjoyed reading this paper and found the development interesting and instructive. Despite the technical nature of the material, the paper is well structured and the concepts are introduced carefully.
- The examples are well chosen and are very helpful in motivating the various operations on rows.
- I appreciated the separation between the mathematical presentation and the corresponding mechanized representations. The authors explain several of the formalization choices and difficulties.
- The metatheoretic results are developed systematically.

Questions/Remarks 
- Section 3.2 requires row literals to contain strictly ordered constant labels. Potentially variable labels are supported only through singleton rows.
Could the authors clarify the consequences of this restriction for the expressiveness of R-omega-mu, particularly in comparison with System R-omega and its support for first-class labels?
- The introduction suggests that the artifact serves as a reference for future NbE and logical-relation proofs for systems with computation beyond β-reduction (lines 94–99). I would be interested in a more explicit discussion of which parts of the development are reusable beyond the particular row calculus studied.

Line Comments
- l. 90: Would the authors agree of this claim after having done their development?
- l. 97: If the goal is to serve  as a reference it would be helpful to put some remarks in the text: what are the relevant changes/pitfalls…?
- l. 323: Figure not referred to
- I don’t understand l. 298
- l. 335: It might help to explain the purpose of the `Ty` parameter more explicitly when introducing `Pred`, perhaps with an example of its instantiation for types and normal types. I found this hard to follow.
- l. 356: Could the authors clarify the intended notion of irrelevance and its consequence for equality of constructors?
- l. 362: The canonical ordering of row literals was already explained earlier.
- l. 494: I didn’t understand the purpose of the highlighting in this case (I found it useful in the previouse use case)
- l. 1147: kripke
