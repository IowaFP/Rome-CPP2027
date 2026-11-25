\documentclass[sigplan,screen]{acmart}
% \settopmatter{printccs=true,printacmref=true}
 
\usepackage{accents}        % accents below math symbols
\usepackage{amsfonts}       % math fonts and blackboards
\usepackage{amsthm}         % theorem environments
\usepackage{array}          % extended table column types
\usepackage{caption}        % customize figure captions
\usepackage{centernot}      % center negation over symbols
\usepackage{enumitem}       % customize list layouts
\usepackage{ifthen}         % conditional logic in macros
\usepackage{minted}         % Pygments syntax highlighting
\usepackage{newunicodechar} % define Unicode chars in TeX
\usepackage{stmaryrd}       % extra math/logic symbols
\usepackage{subcaption}     % subfigures and subcaptions
\usepackage{xspace}         % smart spaces after macros
\usepackage{xparse}         % for better conditional formatting of \newcommands
\usepackage{tikz}           % Diagrams
\usepackage{tikz-cd}        % Commutative Diagrams
\usepackage{microtype}      % As requested by Camera-Ready Author Instructions

% -----------------------------------------------------------------------------
% Configured packages

\usepackage[para]{footmisc}                % paragraph-style footnotes
\usepackage[utf8]{inputenc}                % UTF-8 source text encoding
\usepackage[T1]{fontenc}                   % T1 output font encoding
% \usepackage[svgnames, dvipsnames]{xcolor}  % named colors and shading
\usepackage[capitalize,noabbrev]{cleveref} % capitalized cross-refs
\usepackage[normalem]{ulem}                % text underlining/striking
\PassOptionsToPackage{unicode}{hyperref}

% -----------------------------------------------------------------------------
% Conditionals:
%   - set `comments` to true to render text box comments
%   - set `mono` to true to render pdf without colored syntax highlighting
%     (better for printing to black and white, since some colors are 
%      quite light.)

\newif\ifcomments\commentstrue
\newif\ifmono\monofalse
  
% -----------------------------------------------------------------------------
% My packages

\ifmono
\usemintedstyle{bw}
\usepackage[bw]{./sty/agda}
\else
\usemintedstyle{rosi-agda}
\usepackage{./sty/agda}
\fi 

\usepackage{./sty/mathwidth}
\usepackage{./sty/infer}
\usepackage{./sty/NBE}
\usepackage{./sty/commands}
\usepackage{./sty/environments}
\usepackage{./sty/unicode}


% -----------------------------------------------------------------------------
% Some configuration

% Removes vertical space before and after Agda code blocks
\AgdaNoSpaceAroundCode

% -----------------------------------------------------------------------------
% ACM Stuff

%%% The following is specific to CPP '27 and the paper
    %%% 'Normalization by Evaluation of Higher-Order Rows'
    %%% by Alexander Hubers and J. Garrett Morris.
    %%%
\setcopyright{cc}
\setcctype{by-nc-nd}
\acmDOI{10.1145/3871849.3871874}
\acmYear{2027}
\copyrightyear{2027}
\acmISBN{979-8-4007-3146-4/2027/01}
\acmConference[CPP '27]{Proceedings of the 16th ACM SIGPLAN International Conference on Certified Programs and Proofs}{January 11--12, 2027}{Mexico City, Mexico}
\acmBooktitle{Proceedings of the 16th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP '27), January 11--12, 2027, Mexico City, Mexico}
\acmSubmissionID{poplws27cppmain-p14-p}
\received{2026-09-10}
\received[accepted]{2026-11-10}

%% Bibliography style
\bibliographystyle{ACM-Reference-Format}
\citestyle{acmauthoryear}  %% For author/year citations

\begin{CCSXML}
<ccs2012>
<concept>
<concept_id>10003752.10003790.10011740</concept_id>
<concept_desc>Theory of computation~Type theory</concept_desc>
<concept_significance>500</concept_significance>
</concept>
</ccs2012>
\end{CCSXML}

\ccsdesc[500]{Theory of computation~Type theory}

\keywords{row types, normalization by evaluation, Agda}

% -----------------------------------------------------------------------------
% Title and Authors

\title{Normalization by Evaluation of Higher-Order Rows}
\author{Alex Hubers}
\orcid{0000-0002-6237-3326}
\affiliation{%
  \institution{University of Iowa}
  \city{Iowa City}
  \country{USA}
}
\email{alexander-hubers@uiowa.edu}

\author{J. Garrett Morris}
\orcid{0000-0002-3992-1080}
\affiliation{%
  \institution{University of Iowa}
  \city{Iowa City}
  \country{USA}
}
\email{garrett-morris@uiowa.edu}


% -----------------------------------------------------------------------------
% Section conditionals
% (For faster building)

\newif\ifintro\introtrue
\newif\ifrowsInAction\rowsInActiontrue
\newif\ifrome\rometrue
\newif\ifdesign\designtrue
\newif\ifNbE\NbEtrue
\newif\ifevaluation\evaluationtrue
\newif\ifmetatheory\metatheorytrue
\newif\ifrelatedWork\relatedWorktrue

% -----------------------------------------------------------------------------
% Document

\begin{document}

\begin{code}[hide]
{-# OPTIONS -W noUnreachableClauses #-}
module NBE where 
open import Rome.Prelude
\end{code}

% -----------------------------------------------------------------------------
% Abstract

\begin{abstract}
Row types map labels to types, and are used to \emph{structurally} type records and variants. The presence of higher-order rows, in which labels map to types of higher kind, introduces nontrivial forms of type computation. This paper presents a sound and complete equational theory for types in \Rome{} (pronounced ``Rome''), a higher-order row type theory. We normalize \Rome{} types by evaluation in the interactive proof assistant Agda. Moreover, we contribute extensions to logical relation techniques for intrinsic mechanization to prove this procedure is stable, sound, and complete. As a result, we obtain the first decidable type-conversion algorithm for a higher-order row type theory.
\end{abstract}

% -----------------------------------------------------------------------------
% Title

\maketitle

% -----------------------------------------------------------------------------
% Introduction

% \section{Link test}
% Here is a link where the text and the route differ \Link{Types.Syntax}{Types}. Here is a link to source \Source{Types}. Here is an anchored linked to the definition \Name{Types.Syntax}{Type}. Here is an Agda-formatted link to \Datatype[Types.Syntax]{Type}.

\section{Introduction}
\label{sec:intro}
\ifintro

Row types, as introduced by \citet{wand87}, describe type-level associations of labels to types. Rows can be used dually to type \emph{records} (i.e., classes and objects) and \emph{variants} (i.e., algebraic data types). Recent row type systems~\citep{HubersM23,Chlipala10,Chlipala16, TooheyCJX26} use higher-order rows to describe meta- and generic programs. However, these calculi lack a formal metatheory of type computation.

Systems with type equivalence $\Infix{\TEqv}$ and type computation typically include a \emph{type conversion} rule, in which a term $M$ at type $\tau$ may be converted to type $\upsilon$ provided some derivation of $\tau \TEqv \upsilon$. But this rule (i) complicates decidability, and (ii) impedes preservation and progress. For (i), consider the judgment $\TypeJ {\Gamma, x : \tau} {x} {\upsilon}$, which is well-typed if $\tau \TEqv \upsilon$ and ill-typed otherwise. Likewise, when analyzing an application $\TypeJ \Gamma {M\, N} {\upsilon}$ in a proof of (ii), inverting the head term $\TypeJ \Gamma M {\tau \to \upsilon}$  may yield a conversion, leaving the proof \emph{stuck}. 

% The way out is typically to index terms by types in \emph{normal form}, thereby rendering the conversion rule redundant. That is, we needn't equate syntactically identical (normal) types. This reduces the problems above to a matter of \emph{type normalization}. Of course, that invocation of conversion is superfluous only holds if any two types it might equate are indeed derivably equivalent. That is, we not only must map types to normal forms, but such a procedure must necessarily be \emph{sound} and \emph{complete}.

% Type conversion is typically decided by reducing types to normal forms and performing a syntactic equality check. In fact, we can eliminate the conversion rule entirely: that terms are indexed by normal forms means any use of the conversion rule superfluously equates identical types. Of course, that such a use is superfluous only holds if any two types it might equate are indeed derivably equivalent. That is, we not only must map types to normal forms, but such a procedure must necessarily be \emph{sound} and \emph{complete}.


% Systems with type computation typically include a \emph{type conversion} rule, in which a term $M$ at type $\tau$ may be converted to type $\upsilon$ provided that $\tau = \upsilon$. But this rule complicates type checking (\cf{} $\TypeJ {\Gamma, x : \tau} {x} {\upsilon}$, which is well-typed if $\tau \equiv \upsilon$ and ill-typed otherwise) and impedes \emph{preservation/progress} (inverting the head term in an application $\TypeJ \Gamma {M\, N} {\upsilon}$ may yield a conversion rather than a canonical $\lambda$-binding). Type conversion is typically decided by reducing types to normal forms and performing a syntactic equality check. In fact, the presence of normal forms permits the system to eliminate the type conversion rule entirely: terms may be indexed by types in normal form, and thus any use of the conversion rule would superfluously equate identical types. Eliminating the conversion rule ``unstucks'' proofs of progress, as the head term in an application must be in canonical form (a $\lambda$-binding).

The typical way out is to index terms by types in \emph{normal form}, thereby rendering the conversion rule redundant. (That is, we needn't equate syntactically identical types.) This reduces the problems above to a matter of \emph{type normalization}. Of course, that invocations of the conversion rule are redundant only holds if any two types we might equate are indeed derivably equivalent. That is, we not only must map types to normal forms, but such a procedure must necessarily be \emph{sound} and \emph{complete}.

This can be challenging to prove. An equational theory for System \FO involves only one nontrivial equation: $\beta$-reduction. But the presence of higher-order row types and type operators introduces an abundance of nontrivial type equalities, e.g., the reduction of a map over a row. For this reason, extant higher-order row-typed systems have until now only presented incomplete equational theories~\citep{HubersM23}, elaborated away the intricacies of row computation~\citep{TooheyCJX26}, or instead conjectured confluence and termination of type reduction.~\citep{Chlipala10}

% Likewise, subtle boundary cases arise when constructing record and variant types from nested rows, or applying records of type operators to types.

This paper closes this metatheoretic gap. We introduce \Rome{} (pronounced ``Rome''), a novel row calculus extending System \RO~\citep{HubersM23} with row mapping, iso-recursive types, and a novel complement operator on rows. We provide a sound and complete equational theory of \Rome{} types and prove that this theory is normalizing with respect to a normalization function.

This involves two key contributions. First, we implement a \emph{normalization by evaluation} (NbE) procedure that maps types to normal forms. This procedure is not only responsible for reducing along nontrivial row type equalities, but also for identifying the precise normal and neutral forms of rows and row operations. Second, we prove the equational theory via two Kripke-style logical relations, which are noted by \Citet{AbelAHPMSS19} as an important but challenging mechanization technique. Our contributions are mechanized in the interactive theorem prover Agda.   % \Citet{AbelAHPMSS19} highlight the challenge of \emph{Kripke-style logical relations} on \emph{intrinsically well-typed terms}, for which ``developing [logical relation] proofs for realistic languages can require an almost heroic mechanization effort in existing general-purpose proof assistants.'' Our development follows \citet{AllaisBM13} and \citet{ChapmanKNW19} in contributing additional tooling for this known challenge. Our artifact serves as a reference for future NbE and logical-relation proofs of normalization for systems with computation beyond $\beta$-reduction.

In contrast to mechanized developments where normalization predicates live in a proof-irrelevant universe (e.g., that of \citet{TooheyCJX26}), our development is \emph{constructive}: we do not merely assert the existence of normal forms, but rather compute a normal form $\hat{\tau}$ for each type $\tau$. Moreover, decidability of the equational theory is constructive: given types $\KindJ \Delta \tau \kappa$ and $\KindJ \Delta \upsilon \kappa$, we can either (i) compute a derivation of $\TEqvJ \Delta \tau \upsilon \kappa$, or (ii) show no such derivation can exist.   

% -----------------------------------------------------------------------------
% Contributions

In summary, this paper contributes: 

\begin{enumerate}
  \item \Rome{}'s types, kinds, and equational theory \cref{sec:rome};
  \item a classification of the normal and neutral forms required for higher-order rows, including inert maps, neutral-label rows, and residual row complements \cref{sec:normal-forms};
  \item an NbE algorithm whose semantic operations implement $\beta$-reduction, row mapping and complements, and nested row computation (\S\ref{sec:NbE} and \S\ref{sec:evaluation});  
  \item mechanized proofs of stability, soundness, and completeness in Agda, yielding a decision procedure for \Rome{} type equivalence \cref{sec:metatheory}; and
  \item a \emph{fully safe} Agda artifact witnessing the computability of normal forms and type equivalence.
\end{enumerate}

Our artifact is free and available on Github~\citep{GithubArtifact} for quick browsing and Zenodo~\citep{Artifact} for long-term archival; modules, definitions, and mechanized claims are also \href{\DocBase}{hyperlinked} throughout the paper.
\fi 

% -----------------------------------------------------------------------------
% Rows in Action

\section{Rows in Action}
\label{sec:rows-in-action}
\ifrowsInAction

We begin by illustrating some of the novel type computation features in \Rome. Code excerpts are formatted \ala{} \Rosi~\citep{Rosi}, an experimental implementation of \Rome. The corresponding \Rosi{} terms are given in full \href{\RosiCode}{online}~\citep{GithubArtifact}.

\paragraph{Row types} Rows in \Rome{} are a type-level representation of record fields and variant constructors.  A \emph{row} is simply an association of labels to types, like so:
\begin{rosi} 
row Point = {'x ▹ Nat , 'y ▹ Nat}
\end{rosi} 

We use a quote prefix to identify the label literals \R{'x} and \R{'y}, which are each associated with the type \R{Nat}. The operator $\Pi$ constructs a record from a row, where labels describe attribute names and types describe outputs:

\begin{rosi} 
point : Π {'x ▹ Nat , 'y ▹ Nat}
\end{rosi}


Dually, the operator $\Sigma$ constructs a variant from a row, where labels describe constructor names and types describe constructor inputs. For example,  a binary tree type can be specified as a recursive variant: 

\begin{rosi}
tree : μ (Σ {'Leaf   ▹ Const Nat, 
             'Branch ▹ λ tree. tree × tree})
\end{rosi}

\Ni The row underlying the \R{tree} type is a row of type operators, permitted by \Rome's higher-order capabilities. We can abstract over such rows to do powerful metaprogramming. For example, we can simulate the deriving of a functor typeclass instance: 

\begin{rosi}
type Functor : (* → *) → *
type Functor f = ∀ a b. (a → b) → f a → f b
fmapΣ : ∀ z : R[* → *]. Π (Functor ＠ z) → Functor (Σ z)
\end{rosi}

The syntax $\forall z : \RowK {\TypeK \to \TypeK}$ quantifies a \emph{row variable} $z$ containing type operators at kind $\TypeK \to \TypeK$. The syntax \R{Functor} \R{＠ z} denotes the mapping of the \R{Functor} type operator over row $z$---that is, the application of \R{Functor} to each operator in $z$. The type of \R{fmapΣ} states that, given a record of \R{fmap} instances at type \R{Π (Functor} \R{＠ z)}, we can give a \R{Functor} instance for \R{Σ z}. This is analogous to components of Haskell's \emph{Deriving Functor} machinery~\citep{Laarhoven07}, but without resort to Haskell meta-programming (\ala{} GHC internals~\citep{GhcAPI} or Template Haskell~\cite{SheardJ02}).

\paragraph{Reducing rows}
\label{sec:reducing-rows2}

The type of \R{fmapΣ} is \emph{not} in normal form. Expanding the \R{Functor} type synonym and reducing the application \R{Functor} \R{(Σ z)} yields:


\begin{rosi}
fmapΣ : ∀ z : R[* → *].
        Π ((λ f. ∀ a b. 
            (a → b) → f a → f b) ＠ z) →
        ∀ a b. (a → b) → (Σ z) a → (Σ z) b 
\end{rosi}


But what is \R{(Σ z) a}? Intuitively, we expect this to mean ``the variant produced by supplying the variable \R{a} as an argument to each operator in the row variable \R{z}. Hence this application reduces in \Rome{} according to an associativity rule. First, for conceptual clarity, let us define some metanotation for a ``flipped mapping'' helper \R{(?)} (read as ``flap''):

\begin{rosi}
type r ? t = (λ f. f t) ＠ r
\end{rosi}

\Ni The flap operator takes a row of type operators and an argument, yielding a row of the applications of each operator to that argument. Now the return type of \R{fmapΣ} is:

\begin{rosi}
fmapΣ : ... → ∀ a b. (a → b) → Σ (z ? a) → Σ (z ? b) 
\end{rosi}

This type is in normal form, but there is \emph{potential} computation waiting: all we need is a proper value for the row variable \R{z}. Consider when \R{z} is the row underlying the tree functor. Then the return type is:

\begin{rosi}
fmapΣ : ... → Σ ({'Leaf ▹ Const Nat, 
                   'Branch ▹ λ t. t × t} ? b)
\end{rosi}

\Ni Expanding the flap metanotation yields:
\begin{rosi}
fmapΣ : ... → Σ ((λ f. f b) ＠  
               {'Leaf ▹ Const Nat, 'Branch ▹ λ t. t × t})
\end{rosi}
\Ni which maps and $\beta$-reduces to: 

\begin{rosi}
fmapΣ : ... → Σ {'Leaf ▹ Nat, 'Branch ▹ b × b}
\end{rosi}

\Ni Similar reduction takes place in the input type.

\paragraph{Desugaring Booleans}

Consider a Boolean AST realized by the row of type operators \R{BoolF}, which has constructors for truth, falsity, conditionals, and disjunction.

\begin{rosi} 
row BoolF = {'True ▹ Const ⊤ , 'False ▹ Const ⊤ , 
              'If ▹ λ b. b × b × b , 'Or ▹ λ b. b × b}  
\end{rosi}

We specify an evaluation function as taking the least fixed-point of the variant constructed by \R{BoolF} and returning a variant that is either the true or false case.

\begin{rosi}
eval : μ (Σ BoolF) → Σ {'True ▹ ⊤ , 'False ▹ ⊤}
\end{rosi}

Observe first that $\mu$, the least fixed-point type operator in \Rome, expects its input to be canonically $\lambda$-bound, otherwise the types of terms (e.g., the constant \R{out} \R{:} \R{μ BoolF} \R{→} \R{BoolF (μ BoolF)}) cannot compute. But then the expression \R{Σ BoolF} must (in-line and) normalize to:  % As \R{Σ BoolF} has kind $\TypeK \to \TypeK$ in an empty context, this \emph{should} be the case. But then the expression \R{Σ BoolF} must (in-line and) normalize to: 

\begin{rosi}
λ b. Σ {'True ▹ ⊤ , 'False ▹ ⊤ , 
        'If ▹ b × b × b , 'Or ▹ b × b}  
\end{rosi}

\Ni Hence canonicalization requires a sort of commutativitity of record $\Infix{\Pi}$ and variant $\Infix{\Sigma}$ formers over binders in rows.

Next consider a desugaring pass to replace the \R{'Or} constructor with \R{'If} statements. Such a pass is typed as follows:

\begin{rosi}
row Or    = {'Or ▹ λ b. b × b}
desugarOr : μ (Σ BoolF) → μ (Σ (BoolF ∖ Or))
\end{rosi}

\Ni The syntax \R{(BoolF ∖ Or)} describes the row obtained by removing the \R{Or} row fields from the \R{BoolF} row---hence the type specifies precisely the intent of desugaring. We should expect the following to compute:

\begin{rosi}
  BoolF ∖ Or
= {'True  ▹ Const ⊤, 
   'False  ▹ Const ⊤, 
   'If ▹ λ b. b × b × b}
\end{rosi}

\paragraph{Predicates and containment}
Perhaps instead we wish to desugar \emph{all} Boolean constructs to the untyped $\lambda$-Calculus: 

\begin{rosi}
row LamF = {'Lam ▹ λ x. x , 
            'App ▹ λ x. x × x , 
            'Var ▹ Const Nat}
\end{rosi}

Using row polymorphism and the \emph{row containment} predicates (i) \R{BoolF < z} and (ii) \R{LamF < (z  ∖  BoolF)}, we specify that (i) \R{desugar} can operate on any row \R{z} that includes at least the \R{BoolF} fields and (ii) once those fields are removed, still contains the \R{LamF} fields. In other words, we can desugar \emph{any} AST that incorporates syntax for $\lambda$-Calculus and Booleans expressions. % This formulation provides a powerful abstraction, enabling \R{desugar} to process any AST that incorporates Boolean constructors.

\begin{rosi}
desugar : ∀ z : R[* → *]. BoolF < z, 
          LamF < (z ∖ BoolF) ⇒
          μ (Σ z) → μ (Σ (z ∖ BoolF))  
\end{rosi}

While this example demonstrates no new forms of \emph{row computation}, it highlights that with each additional row operator comes (possibly many) new \emph{neutral} forms: the types \R{z ∖ BoolF} and \R{BoolF ∖ z} each may not reduce without a row literal value for \R{z}.
\fi

% -----------------------------------------------------------------------------
% Rωμ type system

\section{The \Rome{} Type System}
\label{sec:rome}
\ifrome

This section defines the \Rome{} type system. \Cref{fig:kinding} gives the kinding rules for the highlighted \Rome{} types. We omit the syntax of terms and typing rules, as we are focused purely on type-level computation.

\subsection{Kind Syntax}
\input{figures/syntax-types}

\Cref{fig:syntax-types} describes the syntax of kinds, predicates, and types in \Rome. We have highlighted the syntax that extends System \Fome in \cref{fig:syntax-types}. Labels (i.e., record field and variant constructor names) live at the type level, and are classified by kind $\LabK$. Rows of kind $\kappa$ are classified by $\RowK \kappa$. When possible, we use $\phi$ for type functions, $\rho$ for types of row kind, and $\xi$ for types of label kind. 

 % \Source{Kinds.Syntax}
 \paragraph{Mechanized representations \SourceP{Kinds.Syntax}} The types \Datatype[Kinds.Syntax]{Kind} and \Datatype[Kinds.Syntax]{KEnv} represent kinds and kinding environments, respectively. Kinding environments are right-growing lists of kinds.

\begin{code}[hide]
module Syntax where
\end{code}
\begin{code}
  data Kind : Set 
  data KEnv : Set where
    ∅ : KEnv 
    _,_ : KEnv → Kind → KEnv
\end{code}
\begin{code}[hide]
  data Kind where 
    ★ L : Kind 
    _`→_ : Kind → Kind → Kind 
    R[_] : Kind → Kind 
\end{code}

Our mechanization employs intrinsically well-scoped De Bruijn variables, meaning variables are effectively indices into a kinding environment $\Delta$. The variables $\kappa$ and $\Delta$ are implicitly quantified kinds and kinding environments (\Name{Kinds.GVars}{Kinds.\-GVars}).

\begin{code}[hide]
  private 
    variable 
      Δ Δ₁ Δ₂ Δ₃ : KEnv 
      κ κ₁ κ₂ : Kind
\end{code}
\begin{code} 
  data TVar : KEnv → Kind → Set where
    Z : TVar (Δ , κ) κ
    S : TVar Δ κ₁ → TVar (Δ , κ₂) κ₁ 
\end{code}

\subsection{Type Syntax \& Kinding}
\input{figures/kinding}

The type $\pi \then \tau$ denotes a \emph{qualified type} \citep{Jones92}, which generalize typeclasses~\citep{WadlerB89}. In essence, the predicate $\pi$ restricts the instantiation of the type variables in $\tau$. The predicate $\LeqP {\rho_1} {\rho_2}$ denotes that $\rho_1$ is \emph{contained} in $\rho_2$. Note that the predicate $\LeqP {\rho_1} {\rho_2}$ relates only row-kinded types (rule \ksrule{$\lesssim$}): it is \emph{not} a full-fledged subtyping relation. The predicate $\PlusP {\rho_{1}} {\rho_{2}} {\rho_{3}}$ denotes that rows $\rho_{1}$ and $\rho_{2}$ concatenate to the row $\rho_{3}$. We index the judgment $\KindJ \Delta \pi {\RowK \kappa}$ by row kind, which expresses that the rows constrained in $\pi$ house types with kind $\kappa$.

We presume a set of \emph{label literals} $\mathcal L$ for which equality is decidable and over which $\Infix{<}$ induces a strict, total ordering. \Rome{} employs a \emph{simple row theory}~\citep{MorrisM19}, meaning row literals are (i) identified modulo permutation of fields and (ii) label overlaps are forbidden. Property (i) is enforced by \krrule{row}, which requires that row literals be well-ordered. This avoids the need to equate e.g. $\Row{\ell_1 \Labels \tau_1, \ell_2 \Labels \tau_2}$ and $\Row{\ell_2 \Labels \tau_2, \ell_1 \Labels \tau_1}$, as the latter is simply ill-formed (presuming WLOG that $\ell_1 < \ell_2$). Property (ii) is enforced by the strictness of ordering, as e.g. we do not have that $\ell < \ell$ for the row $\Row{\ell \Labels \tau, \ell \Labels \upsilon}$. 

Care must be taken that the instantiation of variable labels does not introduce an overlap. For example, the row $\Row{\ell \Labels \tau, \alpha \Labels \upsilon}$ will be ill-formed if the label variable $\alpha$ is instantiated with label literal $\ell$. Hence we distinguish singleton rows \krrule{rsing}, which may have variable (or un-reduced) label $\xi$, from row literals \ksrule{row} with literal labels $\ell_i$. This is not as restrictive as it might appear. Rather, we capture the mixture of variable and label literals via predicates, writing $\PlusP {\Row{\ell \Labels \tau}} {\Row{\alpha \Labels \upsilon}} {z} \then \dots$ to let $z$ denote $\Row{\ell \Labels \tau, \alpha \Labels \upsilon}$. 

Lastly, the syntax $\Mapp \phi \rho$ maps the type operator $\phi$ across a row $\rho$, and the syntax $\rho_2 \Compl \rho_1$ denotes the \emph{row complement} of $\rho_{2}$ by $\rho_{1}$, analogous to set complements.

\paragraph{Mechanized representations \SourceP{Types.Syntax}}
Our mechanization is \emph{intrinsic}, meaning types are indexed by context and kind. The shape of predicates does not differ be they constraining a \emph{type} or a normal form, and hence the \Datatype[Types.Syntax]{Pred} type generalizes over both via the \Var{Ty} parameter. For example, predicates housing \Datatype[Types.Syntax]{Type}s are described by \Datatype{Pred} \Symbol{(}\Datatype{Type} \GVar{Δ} \Constructor{R[}\GVar{κ}\Constructor{]}\Symbol{)}.
\begin{AgdaAlign}
\begin{code} 
  data Pred (Ty : Set) : Set
  data Type (Δ : KEnv) : Kind → Set
\end{code}

% TODO[Agda-inline][The Ordered stuff... agda uses a different font]
The type synonym \Function[Types.Syntax]{RowLiteral} defines row literals as lists of label-type associations; like with \Datatype{Pred}, this definition may be reused for normal forms, and so is parameterized by \Var{Ty}. The predicate \Function[Types.Syntax]{Ordered} \Var{xs} asserts that the row literal \Var{xs} is well-ordered on labels. The function \Function[Types.Syntax]{ordered?} witnesses that this predicate is decidable.


\begin{code}[hide]
  private variable
    Ty : Set 
\end{code}
\begin{code}
  RowLiteral : (Ty : Set) → Set 
  RowLiteral Ty = List (Label × Ty)
  Ordered  : RowLiteral Ty → Set 
  ordered? : (ρ : RowLiteral Ty) → Dec (Ordered ρ) 
\end{code}
\begin{code}[hide]
  NotLabel : Kind → Set
  NotLabel _ = ⊤

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
  data Pred Ty where
  data Type Δ where
\end{code}

Two sets of \Datatype{Type} constructors are interesting. First, the conditions $\kappa \notin \mathcal K$ (\cref{fig:kinding}) and \Function[Kinds.Syntax]{NotLabel} (below) restrict the formation of \Constructor[Types.Syntax][Type.Π]{Π} and \Constructor[Types.Syntax][Type.Σ]{Σ} to just kinds that do not yield label-valued rows. This restriction later ensures canonicity of label-kinded types. Consider, for example, the application $\KindJ {\Delta} {\Pi \Row{\ell \Labels \ell}} {\LabK}$, which would otherwise be well-kinded.

\begin{code} 
    Π     : {nl : NotLabel κ} → Type Δ (R[ κ ] `→ κ)
    Σ     : {nl : NotLabel κ} → Type Δ (R[ κ ] `→ κ)
\end{code}
\end{AgdaAlign}

 The \Function{NotLabel} $\kappa$ predicate computes to \Term{\Name[Data]{Empty}{⊥}} when $\kappa \in \mathcal K$ and \Term{\Name[Agda]{Builtin.Unit}{⊤}} otherwise, making it \emph{irrelevant}. Hence congruence over $\Pi$ and $\Sigma$ may be defined without regard for this evidence. That is, we have \Constructor{Π} \Symbol{\{}\Var{nl₁}\Symbol{\}} \Var{ρ₁} \Datatype{≡} \Constructor{Π} \Symbol{\{}\Var{nl₂}\Symbol{\}} \Var{ρ₂} iff \Var{ρ₁} \Datatype{≡} \Var{ρ₂} (\Function[Types.Syntax]{cong-Π}).

Second, The constructor \Constructor[Types.Syntax][Type.⦅\Underscore⦆]{⦅\Underscore⦆} for row literal types is guarded by the predicate \Function{True} \Symbol{(}\Function{ordered?} \Var{xs}\Symbol{)}.

\begin{code}
    ⦅_⦆ : (xs : RowLiteral (Type Δ κ)) → True (ordered? xs) →
          Type Δ R[ κ ]
\end{code}

\Ni Unlike \Function{NotLabel} $\kappa$, the \Function{Ordered} \Var{xs} predicate is not (i) trivially irrelevant, nor does it (ii) compute to \Datatype{⊤} or \Datatype{⊥} on closed terms. However, that it is decidable (via \Function{ordered?} \Var{xs}) allows evidence to be \emph{squashed} via the \Type{\Name[Relation]{Nullary.Decidable.Core}{True}} operator~\citep{AgdaStdLib}, yielding a type that satifies both (i) and (ii), and with the desired congruence property that \Constructor{⦅} \Var{xs} \Constructor{⦆} \Var{ω}$_{xs}$ \Datatype{≡} \Constructor{⦅} \Var{ys} \Constructor{⦆} \Var{ω}$_{ys}$ iff \Var{xs} \Datatype{≡} \Var{ys} (\Function[Types.Syntax]{cong-⦅\Underscore⦆}).

\subsection{Type Equivalence and Reduction}
\label{sec:type-equivalence}


\input{figures/equivalence}

We define reduction on types by directing the type equivalence judgment $\TEqvJ \Delta \tau {\upsilon} \kappa$ (\cref{fig:equivalence}) from left to right. The full equivalence relation is the congruence closure of \cref{fig:equivalence} plus rules for reflexivity, symmetry, and transitivity. 

The rules \erule{$\beta$} and \erule{$\eta$} are expected. The rules \erule{map} and \erule{map$_\Labels$} map the type operator $\phi$ over the contents of the row literal $\Row{\LabTy {\ell_i} {\tau_i}}$ and row singleton $\Row{\LabTy \xi \tau}$, respectively.

The rules \erule{map$_\mathsf{id}$} and \erule{map$_{\circ}$} describe functor mapping laws. Normally, the rules \erule{$\eta$} and \erule{map$_{\circ}$} would be presented in the opposite direction (i.e., that $\TEqvJ {\Delta} {\Mapp {(\lambda \alpha. \alpha)} \rho} {\rho} {\RowK \kappa}$). However, the direction chosen enforces that arrow-kinded variables are canonically $\lambda$-bound and row-kinded variables are canonically maps. Incorporating these rules into the equational theory is not mandatory---\citet{ChapmanKNW19}, for example, do not reason modulo $\eta$-equivalence. However, ruling out row-kinded and arrow-kinded neutrals simplifies the definition of semantic types~\cref{sec:residual-semantics} and logical relations~\cref{sec:consistency} later.

The interesting rules describe row complement computation and the interplay of $\Pi$ and $\Sigma$ with edge cases. The rule \erule{$\Compl$} reduces row complements algorithmically by subtracting the elements of the second operand from the first. The syntax $\{ \LabTy {\ell} {\tau}, \rho\}$ is metanotation, treating rows as lists. The rule \erule{map$_\setminus$} specifies that mapping distributes over complements. The rule \erule{assoc$_\Xi$} reassociates applications of $\Pi$ and $\Sigma$ of the form $(\Pi\, \rho)\, \tau$ to $\Pi\, (\rho \, \Flap \, \tau)$, ensuring that $\Pi$ is the outermost syntax and that reduction may continue by supplying each operator in $\rho$ with the argument $\tau$. The rule \erule{$\Xi$} reveals that the application of $\Pi$ and $\Sigma$ to nested rows is instead mapping. To illustrate, consider the following type with kind $\TypeK \to \TypeK$.

\begin{rosi} 
Π (Σ {'x ▹ {'y ▹ λ α. α}})
\end{rosi}

\Ni The row \R{{'x ▹ {'y ▹ λ α. α}}} has kind $\RowK{\RowK {\TypeK \to \TypeK}}$, and so rule \errule{$\Sigma$} asserts that the application of $\Sigma$ to this row can be ``pushed in'' to the inner row \R{{'y ▹ λ α. α}}, as so: 

\begin{rosi} 
Π {'x ▹ Σ {'y ▹ λ α. α}}
\end{rosi}

\Ni This process is repeated as many times as necessary. Of note too is that, as this type has arrow kind, normalization must produce a canonical $\lambda$-bound form. We might expect to need the following rule to commute $\Xi \in \{\Pi, \Sigma\}$ over $\lambda$-bindings in rows: 

{\small
\setlength{\abovedisplayskip}{-13pt}
\[
\ib{\irule[\erule{$\Xi\lambda$}]
  {\KindJ 
    {\Delta, \alpha \co \kappa_1} 
    {\tau} 
    {\kappa_2}}
  {\KindJ \Delta {\xi} {\LabK}};
  {\TEqvJ 
    {\Delta} 
    {\Xi \, {\Row {\LabTy {\xi} {\lambda \alpha \co \kappa_1. \tau}}}} 
    {\lambda \alpha \co \kappa_1. {\Xi \, {\Row {\LabTy {\xi} {\tau}}}}} 
    {\kappa_1 \to \kappa_2}}}
\]}

\Ni but the rules \erule{$\beta$}, \erule{$\eta$}, \erule{map$_\Labels$}, and \errule{assoc$_\Xi$} are in fact sufficient to derive it (\Function[Types.Derivable]{eq-Πλ}, \Source{Types.Derivable}). 

\paragraph{Mechanized representations \SourceP{Types.Equivalence}}
Equivalence on predicates and types is represented mechanically by the typed relations (\Datatype[Types.Equivalence][\Underscore≡ₜ\Underscore]{≡ₜ}) and (\Datatype[Types.Equivalence][\Underscore≡ₚ\Underscore]{≡ₚ}).

\begin{AgdaAlign}
\begin{code}
  data _≡ₚ_ : (π₁ π₂ : Pred (Type Δ R[ κ ])) → Set
  data _≡ₜ_ : (τ₁ τ₂ : Type Δ κ) → Set 
\end{code}
\begin{code}[hide]
  data _≡ₚ_ where
  data _≡ₜ_ where
\end{code}
\end{AgdaAlign}

\Ni Well-kindedness of each inference rule is enforced intrinsically by the kind indices of each predicate and type.

\subsection{Normal Forms}
\label{sec:normal-forms}


The directed type equivalence relation yields normal forms. The syntax of normal types is given in \cref{fig:syntax-normal}. Differences from the type syntax (\cref{fig:syntax-types}) and kinding rules (\cref{fig:kinding}) have been shaded for discussion.

\input{figures/syntax-normal}

Normalization reduces applications and maps except when a variable blocks computation, which we represent as a \emph{neutral type}. A neutral type is either a variable or a spine of applications with a variable in head position. We distinguish ground kinds $\gamma$ from functional and row kinds, as neutral types may only be promoted to normal type at ground kind (rule \kruleNF{ne}). Neutral types $\nu$ at functional kind must be $\eta$-expanded to have an outer-most $\lambda$-binding (e.g., to $\lambda x. \, \nu\, x$), and neutral types at row kind are expanded to an inert map by the identity function (e.g., to $\Mapp {(\lambda x. x)} {\nu}$). Likewise, repeated maps are composed: For example, $\Mapp {\phi_{1}} {(\Mapp {\phi_{2}} {\nu})}$ normalizes by letting $\phi_{1}$ and $\phi_{2}$ compose into $\Mapp {(\phi_{1} \circ \phi_{2})} \nu$. By design, the former is simply inexpressible in the normal type syntax.

We distinguish singleton rows $\{\LabTy \nu \Normal \tau\}$ with neutral labels from row literals $\RowIx i 0 m {\LabTy {\ell_i} {\Normal {\tau_i}}}$ with literal labels $\ell_i$. A row is otherwise an inert map $\Mapp \phi \nu$ or the complement of two rows $\Normal{\tau_2} \Compl \Normal{\tau_1}$. We require in the kinding of normal row complements \kruleNF{$\Compl$} that one (or both) rows are not literal, otherwise the complement would compute. By consequence of $\eta$-expansion, records and variants need only be formed at kind $\TypeK$. The remaining normal type syntax and normal kinding rules do not differ from their counterparts in \cref{fig:syntax-types} and \cref{fig:kinding}.

% Using \paragraph{} Here is adding a MASSIVE space above the text;
% \fakeparagraph is just an alias for italicized bold text with a newline.
\paragraph{Mechanized representations \SourceP{NormalTypes.Syntax}} Normal and neutral types are represented intrinsically as the following types.

\begin{AgdaAlign}
\begin{code}
  data NormalType  : KEnv → Kind → Set
  data NeutralType : KEnv → Kind → Set
\end{code}
\begin{code}[hide]
  data NormalType where
  data NeutralType where
\end{code}
\end{AgdaAlign}

\Rome{} Predicates housing \Datatype[NormalTypes.Syntax]{NormalType}s are described by \Datatype{Pred} \Symbol{(}\Datatype{Norma\-lType} \GVar{Δ} \Constructor{R[}\GVar{κ}\Constructor{]}\Symbol{)}, and, likewise, row literals of \Datatype{NormalType}s are described by \Type{RowLiteral} \Symbol{(}\Datatype{NormalType} \GVar{Δ} \GVar{κ}\Symbol{)}. Just as with the \Datatype{Type} syntax, some constructors require implicit constraints. Promotion of a neutral type $\nu$ to a normal type via the constructor \Constructor[NormalTypes.Syntax][NormalType.ne]{ne} is guarded by the predicate \Function[Kinds.Syntax]{Ground} $\kappa$, which computes to $\top$ when $\kappa \in \{ \TypeK , \LabK \}$ and $\bot$ otherwise. Likewise, the construction of the row complement $\rho_{2} \Compl \rho_{1}$ is guarded by a predicate \Type{True} \Symbol{(}\Function{notRowLiterals?} $\rho_{2}$ $\rho_{1}$\Symbol{)} asserting that at most one of the operands is a row literal. The predicates \Function[NormalTypes.Syntax][NotRowLiteralNF]{NotRowLiteral} and \Function[NormalTypes.Syntax][notRowLiteralNFs?]{notRowLiterals?} are (admittedly awkwardly) stated in negated form to avoid the explicit negation \Function{¬} (\Function{IsRowLiteral} \Var{ρ₂} $\wedge$ \Function{IsRowLiteral} \Var{ρ₁}), which does not compute on closed terms to the empty or unit type.


\Cref{fig:embedding} defines an embedding of normal (\Function[NormalTypes.Syntax][⇑ₜ]{⇑}) and neutral types (\Function[NormalTypes.Syntax][⇑ₙₑ]{⇑ₙₑ}) back to \Datatype{Type} syntax, which can be used as a reference for the mechanized constructor names for \Datatype{Type}s, \Datatype{NeutralType}s, and \Datatype{NormalType}s. The definitions \Function[NormalTypes.Syntax][⇑ₚ]{⇑ₚ} and \Function[NormalTypes.Syntax][⇑ᵣ]{⇑ᵣ} map embedding over the types contained in predicates and row literals; we use a typeclass (\Record[NormalTypes.Syntax]{EmbedTC}) so that the symbol \Typeclass{⇑} hereafter applies to rows, predicates, and neutral types alike.

We must also prove, via \Function[NormalTypes.Syntax][⇑ₒ]{⇑ₒ}, that embedding preserves ordering. Some bookkeeping is necessary, as the evidence of the row's well-ordering (\Var{ω} \Symbol{:} \Type{True} \Symbol{(}\Function{ordered?} \Var{xs}\Symbol{)}) is squashed. However, decidability of \Function{Ordered} \Var{xs} allows evidence to be reproduced, and vice versa: the function \Function{\Name[Relation]{Nullary.Decidable.Core}{toWitness}} converts $\omega$ \Symbol{:} \Type{True} \Symbol{(}\Function{ordered?} \Var{xs}\Symbol{)} into evidence of type \Function{Ordered} \Var{xs}, with \Function{\Name[Relation]{Nullary.Decidable.Core}{fromWitness}} its inverse. This bookkeeping is packaged into the helper \Function[Types.Syntax]{ωmap} for convenience. %, which produces (squashed) evidence that \Var{ys} is well-ordered provided (i) (squashed) evidence that \Var{xs} is well-ordered, and (ii) a map of type \Function{Ordered} \Var{xs} \Symbol{→} \Function{Ordered} \Var{ys}. % \Function{True} (\Function{ordered?} \Var{ys}) provided a map of type (\Function{Ordered} \Var{xs} \Symbol{→} \Function{Ordered} \Var{ys}) and a witness of type \Function{True} (\Function{ordered?} \Var{xs}).

\begin{figure}[t]
\begin{AgdaAlign}
\begin{code}[hide]
module Embedding where
  open import Rome.Types.Syntax hiding (ωmap)
  import Rome.NormalTypes.Syntax as Rωμ
  open import Rome.NormalTypes.Syntax hiding (⇑ ; ⇑ₙₑ ; ⇑ₒ)
  open import Rome.Kinds.GVars
  private 
    variable 
      A : Set
      xs ys : RowLiteral A
\end{code}
\begin{code}
  ⇑   : NormalType Δ κ  → Type Δ κ
  ⇑ₙₑ : NeutralType Δ κ → Type Δ κ
  ⇑ₒ : Ordered xs → Ordered (⇑ᵣ xs)
  ⇑ₙₑ (` x)     = ` x
  ⇑ₙₑ (τ₁ · τ₂) = ⇑ₙₑ τ₁ · ⇑ τ₂
  ⇑ (ne x)      = ⇑ₙₑ x
  ⇑ (`λ τ)      = `λ (⇑ τ)
  ⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
  ⇑ (`∀ τ)      = `∀ (⇑ τ)
  ⇑ (μ τ)    = μ (⇑ τ)
  ⇑  (lab l)    = lab l
  ⇑  (Π x)      = Π · ⇑ x
  ⇑  (Σ x)      = Σ · ⇑ x
  ⇑  (π ⇒ τ)   = ⇑ₚ π ⇒ ⇑ τ
  ⇑  (ρ₂ ∖ ρ₁)  = ⇑ ρ₂ ∖ ⇑ ρ₁
  ⇑  (l ▹ₙ τ)   = ⇑ₙₑ l ▹ ⇑ τ
  ⇑  (F $ ν)  = ⇑ F $ ⇑ₙₑ ν
  ⇑  (⦅ xs ⦆ ω)  = ⦅ ⇑ᵣ xs ⦆ (ωmap ⇑ₒ ω)
    where 
      ωmap : (Ordered xs → Ordered ys) → 
             True (ordered? xs) → True (ordered? ys)
      ωmap f ω = fromWitness (f (toWitness ω))
\end{code}
\begin{code}[hide]
  ⇑ₒ = Rωμ.⇑ₒ
\end{code}
\end{AgdaAlign}
\caption{Embedding}
\label{fig:embedding}
\end{figure}
\fi 

% -----------------------------------------------------------------------------
% Design choices, renaming, substitution

\section{Design Choices in Formalized Metatheory}
\label{sec:design}
\ifdesign

Our development occupies a sweet spot in intrinsically well-typed syntax. Because variables are well-scoped and types are well-kinded, relations and functions defined on types preserve kind and context definitionally. This reduces the overhead of tedious well-formedness predicates and preservation lemmas. 


Reaping the benefits of intrinsic syntax while dodging the downfalls is largely thanks to the \Rome{}'s stratification of types from kinds. Intrinsic syntax is notoriously prone to ``transport hell'' \citep{SaffrichTM24, ChenNFT26}, in which effectively equivalent terms are indexed by unfortunately unequal indices. Notably absent from our Mechanized representations are inductively-defined renamings and substitutions, which in turn prevents constructors for \emph{explicit substitution} in the syntax of types. Because \Rome{} enjoys a stratification of types from kinds, no substitution calculus is necessary, as substitution and renaming may be defined functionally without unpleasant circularity. Instead, following \citet{ChapmanKNW19}, we use a higher-order representation of renamings and substitutions. Hence we inherit the benefits of functions (e.g., associativity of composition) without encumbering definitions with the painful transports on indices that come from explicit substitutions.

\subsection{Renamings}

A \Type[Types.Renaming]{Renaming} is a function mapping type variables in environment $\Delta_1$ to environment $\Delta_2$. As our variables are De Bruijn indices and not named, this is not strictly \emph{renaming}---more accurate is to say that the function \Term[Types.Renaming][renₜ]{ren} \emph{reassigns} each free variable (i.e., an index to a kind in environment $\Delta_1$) in the input type $\tau$ to a kind in environment $\Delta_2$.

\begin{AgdaAlign}
\begin{code}[hide]
module Renaming where
  open import Rome.Kinds.Syntax
  open import Rome.Kinds.GVars
  open import Rome.Types.Syntax 
  open import Rome.NormalTypes.Syntax
\end{code}
\begin{code}
  Renaming : KEnv → KEnv → Set
  Renaming Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → TVar Δ₂ κ
  ren : Renaming Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
\end{code}
\begin{code}[hide]
  import Rome.Types.Renaming as Renaming
  ren = Renaming.renₜ
\end{code}
\end{AgdaAlign}

Renaming is defined as one would expect for normal and neutral types, row literals, and predicates; we use a typeclass (\Record[Types.Renaming]{RenamingTC}) to permit the name \Typeclass{ren} to operate over each.

\subsection{Substitutions} 

A \Type[Types.Substitution]{Substitution} substitutes in parallel by mapping type variables in environment $\Delta_1$ to types well-kinded by $\Delta_2$. The function \Function[Types.Substitution][subₜ]{\Underscore[\Underscore]ₛ} substitutes all free variables in input type $\tau$ according to an input substitution.

\begin{AgdaAlign}
\begin{code}[hide]
module Substitution where
  open import Rome.Kinds.Syntax
  open import Rome.Kinds.GVars
  open import Rome.Types.Syntax 
  open import Rome.NormalTypes.Syntax
\end{code}
\begin{code}
  Substitution : KEnv → KEnv → Set
  Substitution Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → Type Δ₂ κ
  _[_]ₛ : Type Δ₁ κ → Substitution Δ₁ Δ₂ → Type Δ₂ κ
\end{code}
\begin{code}[hide]
  import Rome.Types.Substitution as Substitution 
  τ [ σ ]ₛ = Substitution.subₜ σ τ
\end{code}
\end{AgdaAlign}

Like with renaming, we introduce a typeclass (\Record[Types.Substitution]{SubstitutionTC}) so that the syntax \Typeclass{\Underscore{}[\Underscore{}]ₛ} operates over types, neutral and normal types, rows, and predicates.

A given \Type{Substitution} need not change any variables. In particular, the \Datatype{Type} constructor \Constructor[Types.Syntax][Type.`]{`} constructs a \Datatype{Type} from a \Datatype[Kinds.Syntax]{TVar}, fixing each type variable, and thus forms the \emph{identity substitution} over types.

\begin{code}[hide]
module SubId where
  open import Rome.Kinds ; open import Rome.Types ; open import Rome.NormalTypes
\end{code} 
\begin{code}
  sub-id : ∀ (τ : Type Δ κ) → τ [ ` ]ₛ ≡ τ
\end{code}
\begin{code}[hide]
  import Rome.Types.Properties.Substitution as Substitution
  sub-id = Substitution.sub-id
\end{code}
\fi

% -----------------------------------------------------------------------------
% Normalization by Evaluation

\section{Normalization by Evaluation}
\label{sec:NbE}
\ifNbE

\input{figures/nbe}


Normalization by evaluation \SourceP{NBE.Normalization} consists of three key domains and three functions over these domains (\cref{fig:nbe}). We define the syntax of types, neutral and normal forms, and the embedded domain of semantic types. From there we \emph{reflect} neutral types to semantic types, \emph{reify} from semantic types to normal types, and \emph{evaluate} (\Function{⟦\Underscore⟧}) types to semantic types. The composition of these functions yields procedures for (i) \emph{normalization} (\Function[NBE.Normalization][⇓ₜ]{⇓}) from types to normal types, and (ii) \emph{$\eta$-expansion} (\Function[NBE.Normalization]{η-norm}) from neutral to normal types.

\subsection{Residualizing Semantics}
\label{sec:residual-semantics}

We define our semantic domain \SourceP{NBE.Syntax} in Agda recursively over the syntax of kinds. Our semantics is \emph{residualizing}~\citep{Lindley05} because we distinguish \emph{values} in the semantic domain (functions and rows) from \emph{residual values} (unbound variables, applications with a variable in head position, and normal forms) at ground kind. Hence semantic types are residual values at kinds $\TypeK$ and $\LabK$.

\begin{AgdaAlign}
\begin{code}[hide]
module SemTypes where
  open import Rome.Kinds.Syntax public 
  open import Rome.Kinds.GVars public 
  open import Rome.Types.Syntax public
  open import Rome.Types.Renaming public
  open import Rome.NormalTypes.Syntax public
  
  private
    variable
      A : Set
\end{code}

\begin{code}[hide]
  module _ where private
\end{code}
\begin{code}
    SemType : KEnv → Kind → Set
    SemType Δ ★ = NormalType Δ ★
    SemType Δ L = NormalType Δ L
\end{code}
\begin{code}[hide]
    SemType Δ₁ _ = ⊥
\end{code}


\paragraph{Functions} We interpret arrow-kinded types as \emph{Kripke function spaces} \citep{JungT93, Abel13}, which permit the application of interpreted function $\KindJ {\Delta_1} \phi {\kappa_1 \to \kappa_2}$ at any environment $\Delta_2$ provided a renaming from $\Delta_1$ into $\Delta_2$. The Kripke flavor here is that environments may be viewed as \emph{worlds}, and so each Kripke function returns a type in any \emph{reachable} environment.

\begin{code}[hide]
  module _ where private
    SemType : KEnv → Kind → Set
\end{code}
\begin{code}
    KripkeFunction : KEnv → Kind → Kind → Set
    KripkeFunction Δ₁ κ₁ κ₂ =  
      ∀ {Δ₂} → Renaming Δ₁ Δ₂ → 
                SemType Δ₂ κ₁ → SemType Δ₂ κ₂
    SemType Δ (κ₁ `→ κ₂) = KripkeFunction Δ κ₁ κ₂
\end{code}
\begin{code}[hide]
    SemType _ _ = ⊥
\end{code}

Because we choose to reason modulo $\eta$-equivalence, arrow-kinded types are canonically $\lambda$-bound, and hence our definition of \Datatype{SemType} needn't account for the evaluation of arrow-kinded variables. Contrast our definition with that of \citet{ChapmanKNW19}, for which the evaluation of e.g. the variable \Var{v} $:$ $\TypeK \to \TypeK$ is \Function{left} \Symbol{(}\Constructor{`} \Var{v}\Symbol{)}: 

% We disable the NoUnreachableClauses warning at the start of this file
% so that the following unreachable equation does not throw an error
\begin{code}
    SemType Δ (κ₁ `→ κ₂) = 
        NeutralType Δ (κ₁ `→ κ₂) 
     or KripkeFunction Δ κ₁ κ₂
\end{code} 


\paragraph{Row literals} We define the interpretation of row literals ${\RowIx i 0 n {\LabTy {\ell_i} {\tau_i}}}$ as the type \Type{Row} \Symbol{(}\Type{SemType} $\Delta$ $\kappa$\Symbol{)}, which is defined generically over arbitrary type \GVar{A} \Symbol{:} \Prim{Set} below. The \Type[NBE.Syntax]{Row} type is a finitely indexed map. We choose this representation because operations like row mapping can be expressed as function composition. We will commonly refer to the empty row and cons case on \Type{Row}s as \Function[NBE.Syntax]{ε} and (\Function[NBE.Syntax][_⨾⨾_]{⨾⨾}), respectively.

\begin{code}
  Row : Set → Set 
  Row A = Σ[ n ∈ ℕ ] (Fin n → Label × A)
\end{code}
\begin{code}[hide]
  OrderedRow : Row A → Set
  OrderedRow _ = ⊤
\end{code}


\begin{code}[hide]
  ε : Row A 
  ε = 0 , λ ()
  _⨾⨾_ :  Label × A → Row A → Row A
  a ⨾⨾ (n , P) = suc n , λ { fzero → a 
                          ; (fsuc x) → P x }
\end{code}


\paragraph{Semantic rows, in full}
\begin{code}[hide]
module SemRows where
  open import Rome.Kinds
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NBE hiding (SemType ; SemRow)
\end{code}
\begin{code}[hide]
\end{code}

Not all row-kinded semantic types are row literals. We must account for \emph{inert} row kinded types for which neutral types halt reduction to row literals. For example, the singleton $\Row {\LabTy \nu \tau}$ is not a row literal because its label is neutral. In summary, a semantic row is either: a row literal, a neutral-labeled row singleton, an inert map, or an inert row complement.  In order to enforce rule \erule{map$_\circ$}---that the nested map $\Mapp{\phi_{1}}{(\Mapp{\phi_{2}}{\rho})}$ be recomposed to $\Mapp{(\phi_{1} \circ \phi_{2})}{\rho}$---we want to represent the type operator in inert maps functionally. However, a direct attempt in doing so runs afoul of Agda's positivity checker. Consider the following definition of \Type[NBE.Syntax]{SemRow} for an inert map constructor:
\begin{code} 
  data SemRow (Δ : KEnv) : Kind → Set where
    _$_ : KripkeFunction Δ κ₁ κ₂ → 
            NeutralType Δ R[ κ₁ ] → SemRow Δ R[ κ₂ ]
\end{code}

The Kripke function argument has both a negative occurrence and a non-strictly positive occurrence of \Datatype{SemType}, and so Agda rejects this definition (correctly) as ill-founded. We recover a well-founded definition following a subtle encoding trick found in \citet{AllaisBM13}. For the negative occurrence, it is sufficient to instead quantify over \emph{neutral type} arguments; for the non-strictly positive occurrence, we parameterize \Type{SemRow} by a functor $\mathcal T$ \Symbol{:} \Datatype{KEnv} $\to$ \Prim{Set}, which serves as a placeholder for \Datatype{SemType} $(\Dash)$ \GVar{κ}. 

\begin{figure}[t]
\begin{code}[hide]
module Caveat where
  open import Rome.Kinds
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NBE.Syntax hiding (SemRow ; SemType ; NotRowLiteral)

  data SemRow (Δ₁ : KEnv) (𝒯 : KEnv → Set) : Kind → Set
  NotRowLiteral : ∀ {Δ} {𝒯 : KEnv → Set} → 
                  SemRow Δ 𝒯 R[ κ ] → Set 
\end{code}
\begin{code}
  data SemRow Δ₁ 𝒯 where
    _$_ : (∀  {Δ₂} → Renaming Δ₁ Δ₂ → 
                NeutralType Δ₂ κ₁ → 𝒯 Δ₂) → 
            NeutralType Δ₁ R[ κ₁ ] → 
            SemRow Δ₁ 𝒯 R[ κ₂ ]
    _▹_ : ∀ {κ} → NeutralType Δ₁ L → 
            𝒯 Δ₁ → SemRow Δ₁ 𝒯 R[ κ ]
    row : (ρ : Row (𝒯 Δ₁)) → OrderedRow ρ → 
          SemRow Δ₁ 𝒯 R[ κ ]
    _∖_ : (ρ₂ ρ₁ : SemRow Δ₁ 𝒯 R[ κ ]) → 
          {nr : NotRowLiteral ρ₂ or NotRowLiteral ρ₁} →
          SemRow Δ₁ 𝒯 R[ κ ]
\end{code}
\begin{code}[hide]
  NotRowLiteral (x ▹ x₁) = ⊤
  NotRowLiteral (row ρ x) = ⊥
  NotRowLiteral (ρ ∖ ρ₁) = ⊤
  NotRowLiteral (φ $ ρ) = ⊤
\end{code}
\caption{Semantic rows}
\label{fig:semrow}
\end{figure}

The constructors in \cref{fig:semrow} specify inert maps, singleton rows with neutral label, row literals, and inert row complements. As in the syntax, we require predicates that row literals are well-ordered and row complements have at most one row literal. Finally, we adjust the definition of \Type{SemType} $\Delta$ \Constructor{R[} $\kappa$ \Constructor{]} accordingly so that $\mathcal T =$ \Datatype{SemType} $(\Dash)$ \GVar{κ}.
\begin{code}[hide]
  SemType : KEnv → Kind → Set 
\end{code}
\begin{code}
  SemType Δ₁ R[ κ ] = 
    SemRow Δ₁ (λ Δ₂ → SemType Δ₂ κ) R[ κ ]  
\end{code}
\begin{code}[hide]
  SemType Δ ★ = NormalType Δ ★
  SemType Δ L = NormalType Δ L
  SemType Δ₁ (κ₁ `→ κ₂) = ∀ {Δ₂} → Renaming Δ₁ Δ₂ → 
              SemType Δ₂ κ₁ → SemType Δ₂ κ₂
\end{code}

\end{AgdaAlign}

\subsection{Reflection}
\begin{AgdaAlign}
\begin{code}[hide]
module ReflectReify where
  open import Rome.Kinds.Syntax ; open import Rome.Kinds.GVars 
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.NBE.Syntax ; open import Rome.NBE.Renaming
\end{code}
\begin{figure}[t]
\begin{code}
  reflect : NeutralType Δ κ → SemType Δ κ
  reify : SemType Δ κ → NormalType Δ κ
  
  reflect {κ = ★} τ            = ne τ
  reflect {κ = L} τ            = ne τ
  reflect {κ = κ₁ `→ κ₂} φ = λ r v → reflect (ren r φ · reify v)
  reflect {κ = R[ κ ]} ρ       = (λ r → reflect) $ ρ 
\end{code}
\caption{Reflection}
\label{fig:reflection}
\end{figure}



Reflection asserts that neutral forms have semantic representations. We define reflection (\Function[NBE.Normalization]{reflect}, \cref{fig:reflection}) mutually recursively with reification (\Function[NBE.Normalization]{reify}, \cref{fig:reification}). Types at kind $\TypeK$ and $\LabK$ can be promoted straightforwardly with the \Constructor{ne} constructor. Neutral types at arrow kind must be expanded into Kripke functions: The input \Var{v} has type \Type{SemType} $\Delta_2$ $\kappa_1$ and must be reified, while the function \Var{φ} is kinded in environment $\Delta_1$ and so must be renamed to $\Delta_2$, the environment of \Var{v}. Finally, a neutral row (e.g., a row variable) must be expanded into an inert mapping by \Symbol{(}\Op{λ} \Var{r} $\to$ \Term{reflect}\Symbol{)}. This equation implements rule \erule{map$_\mathsf{id}$} for neutral types.

\subsection{Reification}
\label{sec:reification}

\begin{figure}[t]
\begin{code}[hide]
  reifyNRL : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ′ → SemType Δ′ κ) R[ κ ]) → 
                     (nr : NotRowLiteral ρ₁ or NotRowLiteral ρ₂) → notRowLiteralNF (reify ρ₁) or notRowLiteralNF (reify ρ₂)
  reifyNRL′ : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ′ → SemType Δ′ κ) R[ κ ]) → 
                     (nr : NotRowLiteral ρ₁ or NotRowLiteral ρ₂) → notRowLiteralNF (reify ((ρ₁ ∖ ρ₂) {nr}))
\end{code}
\begin{code}
  reifyRow : Row (SemType Δ κ) → 
             RowLiteral (NormalType Δ κ)
  reifyRow⃗ : (n : ℕ) → (Fin n → Label × SemType Δ κ) → 
              RowLiteral (NormalType Δ κ)
\end{code}
\begin{code}[hide]
  reifyRowOrdered⃗  : (n : ℕ) → (P : Fin n → Label × SemType Δ κ) → 
                      OrderedRow (n , P) → 
                      Ordered (reifyRow⃗ n P)
  reifyRowOrdered : ∀ {Δ : KEnv} {κ : Kind} {ρ : Row (SemType Δ κ)} → OrderedRow ρ →  Ordered (reifyRow ρ)
\end{code}
\begin{code}
  reify {κ = ★} τ = τ
  reify {κ = L} τ = τ
  reify {κ = κ₁ `→ κ₂} φ = `λ (reify (φ S (reflect {κ = κ₁} ((` Z)))))
  reify {κ = R[ κ ]} (l ▹ τ) = (l ▹ₙ (reify τ))
  reify {κ = R[ κ ]} (φ $ τ) =  (`λ (reify (φ S (` Z))) $ τ)
  reify {κ = R[ κ ]} ((ρ₂ ∖ ρ₁) {q}) = 
    (reify ρ₂ ∖ reify ρ₁) {fromWitness (reifyNRL ρ₂ ρ₁ q)}
  reify {κ = R[ κ ]} (row ρ ω) = 
    ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ω))

  reifyRow⃗ zero _     = []
  reifyRow⃗ (suc n) P with P fzero
  ... | (l , τ) = (l , reify τ) ∷ reifyRow⃗ n (P ∘ fsuc)
  reifyRow (n , P) = reifyRow⃗ n P
\end{code}
\begin{code}[hide]
  reifyRowOrdered⃗ zero P ω = tt
  reifyRowOrdered⃗ (suc zero) P ω = tt
  reifyRowOrdered⃗ (suc (suc n)) P (l₁<l₂ , ih) = 
    l₁<l₂ , (reifyRowOrdered⃗ (suc n) (P ∘ fsuc) ih)
  reifyRowOrdered {ρ = n , P} q = reifyRowOrdered⃗ n P q

  reifyNRL (x₁ ▹ x₂) ρ₂ (left x) = left tt
  reifyNRL ((ρ₁ ∖ ρ₃) {nr}) ρ₂ (left x) = left (reifyNRL′ ρ₁ ρ₃ nr)
  reifyNRL (φ $ ρ) ρ₂ (left x) = left tt
  reifyNRL ρ₁ (x ▹ x₁) (right y) = right tt
  reifyNRL ρ₁ ((ρ₂ ∖ ρ₃) {nr}) (right y) = right (reifyNRL′ ρ₂ ρ₃ nr)
  reifyNRL ρ₁ ((φ $ ρ₂)) (right y) = right tt
  
  reifyNRL′ (x₁ ▹ x₂) ρ₂ (left x) = tt
  reifyNRL′ (ρ₁ ∖ ρ₃) ρ₂ (left x) = tt
  reifyNRL′ (φ $ n) ρ₂ (left x) = tt
  reifyNRL′ (φ $ n) ρ₂ (right y) = tt
  reifyNRL′ (x ▹ x₁) ρ₂ (right y) = tt
  reifyNRL′ (row ρ x) (x₁ ▹ x₂) (right y) = tt
  reifyNRL′ (row ρ x) (ρ₂ ∖ ρ₃) (right y) = tt
  reifyNRL′ (row ρ x) (φ $ n) (right y) = tt
  reifyNRL′ (ρ₁ ∖ ρ₃) ρ₂ (right y) = tt
\end{code}
\caption{Reification}
\label{fig:reification}
\end{figure}
\end{AgdaAlign}

Reification asserts that semantic values have syntactic representations, and is a little more involved (\cref{fig:reification}). The first two equations are expected ($\tau$ is already in normal form). Functions are reified effectively by $\eta$\--expan\-sion. Here we see why we choose to interpret functions with a Kripke flavor, as the weakening renaming \Constructor[Kinds.Syntax][TVar.S]{S} is crucial to permitting $\phi$ to operate over the just-introduced type variable \Constructor{` Z}. The remaining equations describe the reification of the four row cases. In the $\Mapp \phi \tau$ case, we must reify the neutral Kripke function $\phi$ analogously to the reification of type operators. We reify row literals effectively by mapping reification over the contents of each semantic row, reconstructing a list as we go along. A straightforward definition of \Function[NBE.Normalization]{reifyRow} might attempt to induct over the \Type{Row} argument's length (its first component), which Agda's termination checker rejects. This is because the recursive call in the successor case will be over $(n , P \circ \text{fsuc})$, where the second component is not structurally smaller. We bypass this restriction by instead recursing over the curried form \Function[NBE.Normalization]{reifyRow⃗}. In both the row literal and row complement case, some bookkeeping is necessary to ensure that (respectively) reification respects row orderedness and reification does not produce row literals from inert rows.

Finally, the \Datatype{NormalType} constructor \Constructor{ne} stipulates that we may only promote neutral derivations to normal derivations at \emph{ground kind} (rule \kruleNF{ne}). Hence the composition of reflection and reification effectively $\eta$-expands neutral types.

\begin{code}[hide]
module ηNorm where 
  open import Rome.Types
  open import Rome.NormalTypes ; open import Rome.Kinds 
  open import Rome.NBE hiding (η-norm)
\end{code}
\begin{code}
  η-norm : NeutralType Δ κ → NormalType Δ κ 
  η-norm = reify ∘ reflect
\end{code}

\Ni This function forms the \emph{identity substitution} on normal types:

\begin{code}
  subNF-id : ∀ (τ : NormalType Δ κ) → τ [ η-norm ∘ ` ]ₛ ≡ τ 
\end{code}
\begin{code}[hide]
  import Rome.NormalTypes.Properties.Substitution as Substitution
  subNF-id = Substitution.subₜNF-id
\end{code}
\fi

% -----------------------------------------------------------------------------
% Evaluation

\section{Evaluation}
\label{sec:evaluation}
\ifevaluation

Our next task is to \emph{evaluate} terms of type \Datatype{Type} $\Delta$ $\kappa$ into the semantic domain at type \Type{SemType} $\Delta$ $\kappa$. This component of the normalization algorithm implements row computation. We proceed by defining semantic helpers that reduce \Datatype{SemType} arguments.

\begin{code}[hide]
module Evaluation where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.NBE.Syntax hiding (ε)
  open import Rome.NBE.Normalization using (reflect ; reify ; lifte ; extende ; _∈Row?_)
  open import Rome.NBE.Renaming
  open import Rome.Kinds
  open import Data.Bool
  open SemTypes using (ε)
\end{code}

\paragraph{Semantic application}

We define semantic application (\Function[NBE.Normalization][\Underscore⟨·⟩\Underscore]{⟨·⟩}) straightforwardly as Agda application under the identity renaming.

\begin{code}
  _⟨·⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → 
         SemType Δ κ₂
  F ⟨·⟩ V = F id V
\end{code}


\Ni Semantic application implements $\beta$-reduction. 

\paragraph{Semantic mapping}
We define mapping (\Function[NBE.Normalization][\Underscore⟨$⟩\Underscore]{⟨\$⟩}) over the four cases a semantic row may take. The functions \Function[NBE.Syntax][orderedMap₂]{ordered\-Map₂} and \Function[NBE.Syntax][NotRowLiteral]{NotRowLiteral\$} are bookkeeping that assert our orderedness and row literal predicates are preserved by semantic mapping.

\begin{AgdaAlign}
\begin{code}
  _⟨$⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → 
           SemType Δ R[ κ₂ ]
\end{code}
\begin{code}[hide]
  NotRowLiteral$ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {F : SemType Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : SemRow Δ (λ Δ′ → SemType Δ′ κ₁) R[ κ₁ ]} → 
                NotRowLiteral ρ₂ or NotRowLiteral ρ₁ → NotRowLiteral (F ⟨$⟩ ρ₂) or NotRowLiteral (F ⟨$⟩ ρ₁)
\end{code}
\begin{code}
  _⟨$⟩_ {κ₁ = κ₁} {κ₂ = κ₂} F (l ▹ τ) = l ▹ (F ⟨·⟩ τ)
  F ⟨$⟩ row (n , P) q = row (n , map₂ (F id) ∘ P) 
    (orderedMap₂ (F id) q)
  F ⟨$⟩ ((ρ₂ ∖ ρ₁) {nr}) = ((F ⟨$⟩ ρ₂) ∖ (F ⟨$⟩ ρ₁)) 
    {NotRowLiteral$ nr}
  F ⟨$⟩ (G $ n) = (λ {Δ′} r → F r ∘ G r) $ n
\end{code}
\begin{code}[hide]
  NotRowLiteral$ {F = F} {x₁ ▹ x₂} {ρ₁} (left x) = left tt
  NotRowLiteral$ {F = F} {ρ₂ ∖ ρ₃} {ρ₁} (left x) = left tt
  NotRowLiteral$ {F = F} {φ $ n} {ρ₁} (left x) = left tt
  
  NotRowLiteral$ {F = F} {ρ₂} {x ▹ x₁} (right y) = right tt
  NotRowLiteral$ {F = F} {ρ₂} {ρ₁ ∖ ρ₃} (right y) = right tt
  NotRowLiteral$ {F = F} {ρ₂} {φ $ n} (right y) = right tt
\end{code}
\end{AgdaAlign}

\Ni The case where $\rho$ is a row literal is interesting in that our choice of representation for row literals as finite maps pays off: we express the mapping of $\phi$ across the row $(n , P)$ by composing $P$ with $F$. (The function \Function{\Name[Data]{Product.Base}{map₂}} maps over a tuple's second component.) This equation, and line 3, implement the equational rule \errule{map}. 

The mapping of $\phi$ over a complement is distributive, following rule \errule{map$_{\setminus}$}. Likewise, we follow rule \errule{map$_\circ$} in grouping the nested map $\Mapp {\phi_1} {(\Mapp {phi_2}  n)}$ into a composed map. Here again a functional representation pays off by permitting composition in the semantic domain.

\paragraph{Semantic complement} The complement of two row-kinded semantic types (\Function[NBE.Normalization][\Underscore∖v\Underscore]{⟨∖⟩}) is always inert when one (or both) are not row literals, and thus constructed simply by the \Constructor[NBE.Syntax][SemRow.\Underscore∖\Underscore]{\Underscore{}∖\Underscore{}} constructor. The interesting case is when we must reduce two row literals to another row literal.

\begin{AgdaAlign}
\begin{code}
  _In?_ : Label → Row (SemType Δ κ) → Bool
\end{code}
\begin{code}[hide]
  l In? (n , P) = isYes (l ∈Row? P)
  {-# TERMINATING #-}
\end{code}
\begin{code}
  _⟨∖⟩_ : (ρ₂ ρ₁ : Row (SemType Δ κ)) → Row (SemType Δ κ)
  (zero , P) ⟨∖⟩ ρ = ε 
  (suc n , P) ⟨∖⟩ ρ with P fzero
  ... | (l , τ) = if l In? ρ then
                  (n , P ∘ fsuc) ⟨∖⟩ ρ else
                  (l , τ) ⨾⨾ ((n , P ∘ fsuc) ⟨∖⟩ ρ)
\end{code}
\begin{code}[hide]
  import Rome.NBE.Normalization as Normalization
  _⟨∖⟩′_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
  _⟨∖⟩′_ = Normalization._⟨∖⟩_
\end{code}
\end{AgdaAlign}

The semantic helper above implements the subtract function given in \cref{fig:equivalence}, and is effectively identical logic. In the interest of concision, we present this helper by induction over the \Type{Row} input's first component, which Agda's termination checker rejects. Like with \Function{reifyRow} (\cref{fig:reification}), our artifact instead recurses over a curried form. This nuisance highlights a shortcoming in Agda's strictly syntactic termination checking, and could be avoided with type-based alternatives~\citep{AbelP16, AbreuDHJMS23}.

\paragraph{Semantic flap}
We define a semantic version of the flap operator (\Function[NBE.Normalization][\Underscore⟨?⟩\Underscore]{⟨?⟩}) as follows. This definition is auxiliary but helpful in tidying code.

\begin{code}
  apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
  apply a = λ r F → F ⟨·⟩ (renSem r a)
  _⟨?⟩_ : SemType Δ R[ κ₁ `→ κ₂ ] → 
           SemType Δ κ₁ → SemType Δ R[ κ₂ ]
  f ⟨?⟩ a = apply a ⟨$⟩ f 
\end{code}

\paragraph{Semantic $\Pi$ and $\Sigma$} 
\label{sec:semantic-Pi}
The defining equations for the reduction of $\Pi$ is given below (\Function[NBE.Normalization]{⟨Π⟩}). The logic for \Function[NBE.Normalization]{⟨Σ⟩} is identical and omitted.

\begin{code}
  ⟨Π⟩ : SemType Δ R[ κ ] → SemType Δ κ 
  ⟨Π⟩ {κ = ★} x = Π (reify x)
  ⟨Π⟩ {κ = κ₁ `→ κ₂} F = λ r v → ⟨Π⟩ (renSem r F ⟨?⟩ v)
  ⟨Π⟩ {κ = R[ κ ]} ρ = (λ r → ⟨Π⟩) ⟨$⟩ ρ
\end{code}
\begin{code}[hide]
  ⟨Π⟩ {κ = L} x = lab "impossible"
  ⟨Σ⟩ : SemType Δ R[ κ ] → SemType Δ κ 
  ⟨Σ⟩ {κ = ★} x = Σ (reify x)
  ⟨Σ⟩ {κ = κ₁ `→ κ₂} F = λ r v → ⟨Σ⟩ (renSem r F ⟨?⟩ v)
  ⟨Σ⟩ {κ = R[ κ ]} ρ = (λ _ v → ⟨Σ⟩ v) ⟨$⟩ ρ  
  ⟨Σ⟩ {κ = L} _ = lab "impossible"
\end{code}
 
Recall that we may only construct record types in normal form at kind $\TypeK$, and so for the case that $\kappa = \TypeK$ we simply reify the input and construct the record via the \Datatype{NormalType} constructor \Constructor{Π}. We exclude the case that $\kappa = \LabK$ because it is impossible (recall that in the \Datatype{Type} syntax, we restrict the formation of the \Constructor{Π} constructor to just non-label kinds.) 

Next, when applying \Function{⟨Π⟩} to a function, we expand the semantic $\lambda$-binding outwards. Thereafter, we apply rule \errule{assoc$_\Pi$} to explain how \Function{⟨Π⟩} operates on a single operand. We implement rule \errule{$\Pi$} directly in the last equation: the application of \Function{⟨Π⟩} to a row-kinded input $\rho$ is simply the mapping of \Function{⟨Π⟩}  over $\rho$.

% These two rules characterize the computational interaction of $\Pi$ and $\Sigma$ with higher-order and nested rows. We implement row computation via our semantic helpers. The fact that the semantic helpers resemble their syntactic equational rules, modulo some plumbing, is a desirable feature of our implementation.

\paragraph{Evaluation}
A semantic environment (\Type[NBE.Normalization]{SemEnv}) maps type variables to semantic types, and thus the identity environment (\Type[NBE.Normalization]{idEnv}) fixes the meaning of variables. Evaluation (\Function[NBE.Normalization][⟦\Underscore⟧ₜ]{⟦\Underscore⟧}, \cref{fig:evaluation}) maps \Datatype{Type}s to semantic types, given a suitable semantic environment.

\begin{code}
  SemEnv : KEnv → KEnv → Set
  SemEnv Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → SemType Δ₂ κ
  idEnv : SemEnv Δ Δ
  idEnv = reflect ∘ `
\end{code}

\begin{figure}[t]
\begin{AgdaAlign}
\begin{code}[hide]
  {-# TERMINATING #-}
\end{code}
\begin{code}
  ⟦_⟧ : Type Δ₁ κ → SemEnv Δ₁ Δ₂ → SemType Δ₂ κ
\end{code}
\begin{code}[hide]
  ⟦_⟧ₚ : Pred (Type Δ₁ R[ κ ]) → SemEnv Δ₁ Δ₂ → Pred (NormalType Δ₂ R[ κ ])
  ⟦_⟧ₚ (ρ₁ · ρ₂ ~ ρ₃) η = reify (⟦ ρ₁ ⟧ η) · reify (⟦ ρ₂ ⟧ η) ~ reify (⟦ ρ₃ ⟧ η)
  ⟦_⟧ₚ (ρ₁ ≲ ρ₂) η = reify (⟦ ρ₁ ⟧ η) ≲ reify (⟦ ρ₂ ⟧ η)
\end{code}
\begin{code}
  ⟦ ` v ⟧ η       = η v
  ⟦ τ₁ · τ₂ ⟧ η   = (⟦ τ₁ ⟧ η) ⟨·⟩ (⟦ τ₂ ⟧ η)
  ⟦ ρ₂ ∖ ρ₁ ⟧ η = ⟦ ρ₂ ⟧ η ⟨∖⟩′ ⟦ ρ₁ ⟧ η
  ⟦ Π ⟧ η         = λ _ v → ⟨Π⟩ v
  ⟦ Σ ⟧ η         = λ _ v → ⟨Σ⟩ v
  ⟦ f $ a ⟧ η     = ⟦ f ⟧ η ⟨$⟩ ⟦ a ⟧ η
  ⟦ ξ ▹ τ ⟧ η with ⟦ ξ ⟧ η 
  ... | ne ν       = (ν ▹ ⟦ τ ⟧ η)
  ... | lab l      = row (1 , λ { fzero → (l , ⟦ τ ⟧ η) }) tt
  ⟦ ⦅ ρ ⦆ ω ⟧ η   = row 
    (⟦ ρ ⟧ᵣ η) 
    (⟦ toWitness ω ⟧ₒ η)
    where
      ⟦_⟧ᵣ : RowLiteral (Type Δ₁ κ) → 
            SemEnv Δ₁ Δ₂ → 
            Row (SemType Δ₂ κ)
      ⟦ [] ⟧ᵣ η          = ε
      ⟦ (l , τ) ∷ ρ ⟧ᵣ η = (l , ⟦ τ ⟧ η) ⨾⨾ ⟦ ρ ⟧ᵣ η
      ⟦_⟧ₒ : {ρ : RowLiteral (Type Δ₁ κ)} → 
             Ordered ρ → 
             (η : SemEnv Δ₁ Δ₂) → 
             OrderedRow (⟦ ρ ⟧ᵣ η)      
\end{code}
\begin{code}[hide]
      import Rome.NBE.Normalization as Normalization
      ⟦_⟧ₒ {ρ = []} ω η = tt
      ⟦_⟧ₒ {ρ = _ ∷ []} ω η = tt
      ⟦_⟧ₒ {ρ = (l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ} (l₁<l₂ , ω) η with 
            ⟦ ρ ⟧ᵣ η  | ⟦ ω ⟧ₒ η 
      ... | zero , P  | ih = l₁<l₂ , tt
      ... | suc n , P | ih₁ , ih₂ =  l₁<l₂ , ih₁ , ih₂

  ⟦ (π ⇒ τ) ⟧ η = ⟦ π ⟧ₚ η ⇒ ⟦ τ ⟧ η
  ⟦ (`∀ τ) ⟧ η = `∀ (⟦ τ ⟧ (lifte η)) 
  ⟦ (μ τ) ⟧ η = μ (reify (⟦ τ ⟧ η))
  ⟦ (lab l) ⟧ η = lab l
  ⟦ (τ₁ `→ τ₂) ⟧ η = (⟦ τ₁ ⟧ η) `→ (⟦ τ₂ ⟧ η)
  ⟦ (`λ τ) ⟧ η = λ r v → ⟦ τ ⟧ (extende (renSem r ∘ η) v)
\end{code}
\end{AgdaAlign}
\caption{Evaluation}
\label{fig:evaluation}
\end{figure}


We describe only the interesting cases of evaluation. The first equation states that variables evaluate to their meaning in environment $\eta$. As desired, the equations for application (\Constructor{\Underscore{}·\Underscore{}}), row complement (\Constructor{\Underscore{}∖\Underscore{}}), record and variant operators (\Constructor{Π} and \Constructor{Σ}), and mapping (\Constructor{\Underscore{}\$\Underscore{}}) defer to the semantic helpers defined in this section. (The operation \Function[NBE.Normalization][\Underscore⟨∖⟩\Underscore]{⟨∖⟩′} is the semantic complement operator for row literals lifted to \Datatype{SemRow}s.) Evaluation of labeled singletons must check if the label is a neutral variable \Var{ν} or label literal $\ell$, making sure to only construct row literals with literal labels. The evaluation of row literals (\Function[NBE.Normalization][⟦\Underscore⟧ᵣ]{⟦\Underscore⟧ᵣ}) is effectively inverse to \Function{reifyRow} (\cref{fig:reification}). In each case, we employ our smart constructors for semantic row literals. We have an obligation to prove that evaluation preserves the ordering evidence \Var{ω}, which is performed by the auxiliary lemma \Function[NBE.Normalization][⟦\Underscore⟧ₒ]{⟦\Underscore⟧ₒ} denoting ordered row literal evidence to ordered semantic row evidence.

\paragraph{Normalization} Finally, normalization (\Function[NBE.Normalization][⇓ₜ]{⇓}) is simply the composition of reification after evaluation.  

\begin{code}
  ⇓ : Type Δ κ → NormalType Δ κ 
  ⇓ τ = reify (⟦ τ ⟧ idEnv)
\end{code}

\Ni Similar definitions can be given for the evaluation and normalization of predicates and row literals, which are grouped under the typeclass methods \Typeclass{⟦\Underscore{}⟧} (\Record[NBE.Normalization]{EvaluateTC}) and \Typeclass{⇓} (\Record[NBE.Normalization]{NormalizeTC}).
\fi

% -----------------------------------------------------------------------------
% Metatheory

\section{Metatheory}
\label{sec:metatheory}
\ifmetatheory

This section describes the metatheory of \Rome. A note on nomenclature: what we and some others~\citep{Lindley05, Friedman75, KellerA10} refer to as \emph{soundness} and \emph{consistency} is in some NbE literature~\citep{Statman82, BergerS91, ChapmanKNW19, Abel13} referred to as \emph{completeness} and \emph{soundness}, respectively. The difference amounts to perspective: is the \emph{normalization procedure} sound and complete, or the \emph{equational theory}? Because our motivation is to show that, in contrast to System \RO~\citep{HubersM23}, the equational theory of \Rome{} is complete, we commit to the latter perspective.

\subsection{Canonicity of Normal Types}
\begin{AgdaAlign}
\begin{code}[hide]
module Canonicity where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds 
\end{code}
\emph{Canonicity} \SourceP{Metatheory.Canonicity} asserts that arrow, row, and label-kinded normal types have certain canonical forms. In any context an arrow-kinded type is canonically $\lambda$-bound:
\begin{code}
  arrow-canonicity : (f : NormalType Δ (κ₁ `→ κ₂)) → 
                     Σ[ τ ∈ (NormalType (Δ , κ₁) κ₂) ] 
                     (f ≡ `λ τ)
  arrow-canonicity (`λ f) = f , refl
\end{code}

\Ni A row in an empty context is necessarily a row literal:

\begin{code}
  row-canonicity-∅ : (ρ : NormalType ∅ R[ κ ]) → 
                    Σ[ xs ∈ RowLiteral (NormalType ∅ κ) ] 
                    Σ[ q ∈ True (ordered? xs) ] 
                    (ρ ≡ ⦅ xs ⦆ q)
  row-canonicity-∅ (⦅ xs ⦆ q) = xs , q , refl
\end{code}
\begin{code}[hide]
  row-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
  row-canonicity-∅ ((ρ ∖ ρ₁) {nrl}) = ⊥-elim (noComplements nrl refl)
  row-canonicity-∅ (l ▹ₙ ρ) = ⊥-elim (noNeutrals l)
  row-canonicity-∅ ((φ $ ρ)) = ⊥-elim (noNeutrals ρ)
\end{code}

\Ni And a label-kinded type is necessarily a label literal:

\begin{code}
  label-canonicity-∅ : ∀ (l : NormalType ∅ L) → 
                       Σ[ ℓ ∈ Label ] (l ≡ lab ℓ)
  label-canonicity-∅ (lab s) = s , refl
\end{code}
\begin{code}[hide]
  label-canonicity-∅ (ne x) = ⊥-elim (noNeutrals x)
\end{code}
\end{AgdaAlign}

\subsection{Stability}

\begin{AgdaAlign}
\begin{code}[hide]
module Metatheory where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.NBE
\end{code}
Stability \SourceP{Metatheory.Stability} asserts that embedding (\Typeclass{⇑}) is right-inverse to normalization (\Typeclass{⇓}):

\begin{code}
  stability : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ 
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.Stability as Stability
  stability = Stability.stability
\end{code}

\Ni \emph{Stability} implies \Function[Metatheory.Stability]{idempotency} of normalization:
\begin{code}
  idempotency : ∀ (τ : Type Δ κ) → 
                ((⇑ ∘ ⇓) ∘ (⇑ ∘ ⇓)) τ ≡ (⇑ ∘ ⇓) τ 
  idempotency τ = cong ⇑ (stability (⇓ τ)) 
\end{code} 

\Ni and \Function[Metatheory.Stability]{surjectivity}:

\begin{code}
  surjectivity : ∀ (τ : NormalType Δ κ) → 
                 Σ[ υ ∈ Type Δ κ ] (⇓ υ ≡ τ)
  surjectivity τ = ⇑ τ , stability τ
\end{code}
\end{AgdaAlign}

\subsection{Soundness}
\label{sec:soundness} 
\emph{Soundness} \SourceP{Metatheory.Soundness} of the equational theory states that if $\TEqvJ \Delta \tau \upsilon \kappa$, then $\tau$ and $\upsilon$ normalize to the same form.
\begin{AgdaAlign}
\begin{code}[hide]
module SoundnessStatement where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds ; open import Rome.NBE
\end{code} 
\begin{code}
  soundness : ∀ {τ υ : Type Δ κ} → τ ≡ₜ υ → ⇓ τ ≡ ⇓ υ
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.Soundness as Soundness
  soundness = Soundness.soundness
\end{code}
\end{AgdaAlign}

We prove soundness via a logical relation (\Function[Metatheory.Soundness.Relation][\Underscore≈\Underscore]{≈}) on semantic types that specifies when two semantic objects are partial-equivalent modulo \emph{uniformity} and functional extensionality.

\begin{figure}[t]
\begin{AgdaAlign}
\begin{code}[hide]
module Uniformity where
  open import Rome.Prelude
  open import Rome.Kinds
  open import Rome.Kinds.Properties.Decidability
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NBE hiding (renKripke)
  open import Rome.Metatheory.Soundness.Relation hiding 
    (Uniform ; PointEqual-≈)
\end{code}
\begin{code}
  renKripke : Renaming Δ₁ Δ₂ → 
              KripkeFunction Δ₁ κ₁ κ₂ → 
              KripkeFunction Δ₂ κ₁ κ₂
  renKripke r₁ φ = λ r₂ → φ (r₂ ∘ r₁) 

  Uniform : KripkeFunction Δ κ₁ κ₂ → Set
  Uniform {Δ = Δ₁} {κ₁ = κ₁} φ = 
    ∀ {Δ₂ Δ₃} (r₁ : Renaming Δ₁ Δ₂) 
      (r₂ : Renaming Δ₂ Δ₃) 
      (V₁ V₂ : SemType Δ₂ κ₁) →
      V₁ ≈ V₂ → 
      (renSem r₂ (φ r₁ V₁)) ≈ (renKripke r₁ φ r₂ (renSem r₂ V₂))

  PointEqual-≈ : ∀ (φ ψ : KripkeFunction Δ₁ κ₁ κ₂) → Set
  PointEqual-≈ {Δ₁ = Δ₁} {κ₁ = κ₁} φ ψ = 
    ∀ {Δ₂} (r : Renaming Δ₁ Δ₂) {V₁ V₂ : SemType Δ₂ κ₁} → 
    V₁ ≈ V₂ → 
    φ r V₁ ≈ ψ r V₂
\end{code}
\end{AgdaAlign}
\caption{Uniformity and point equality}
\label{fig:uniformity-and-PE}
\end{figure}


The relation is defined compositionally in the cases where $\kappa = \TypeK$, $\kappa = \LabK$, or $\kappa = \RowK \kappa$ and the equated rows are neutral-labeled or inert complements.
\begin{AgdaAlign}
\begin{code}[hide]
module SoundnessRelation where
  open import Rome.Prelude
  open import Rome.Kinds
  open import Rome.Kinds.Properties.Decidability
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NBE
  open import Data.Nat.Properties renaming (_≟_ to _≡ℕ?_)  
  open import Rome.Metatheory.Soundness.Relation hiding 
    (_≈_ ; _≈₂_ ; _≈ᵣ_)
\end{code}
\begin{code}
  _≈_ : SemType Δ κ → SemType Δ κ → Set
  _≈_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
  _≈_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
  _≈_ {κ = R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = (l₁ ≡ l₂) × τ₁ ≈ τ₂
  _≈_ {κ = R[ κ ]} (ρ₁ ∖ ρ₂) (ρ₃ ∖ ρ₄) = ρ₁ ≈ ρ₃ × ρ₂ ≈ ρ₄
\end{code}

\Ni In the arrow case, we assert that the Kripke functions $\phi$ and $\psi$ are \emph{uniform} (\Function[Metatheory.Soundness.Relation]{Uniform}) and \emph{extensionally equivalent} to one another ((\Function[Metatheory.Soundness.Relation]{PointEqual-≈}), \cref{fig:uniformity-and-PE}). 

\begin{code}
  _≈_ {Δ₁} {κ = κ₁ `→ κ₂} φ ψ = 
    Uniform φ × Uniform ψ × PointEqual-≈ {Δ₁} φ ψ 
\end{code}

\Ni Uniformity states that passing a renaming $r_2$ to a Kripke function is equivalent to renaming it algorithmically---that is, semantic renaming (\Function[NBE.Renaming]{renSem}) commutes with Kripke renaming. The uniformity property is attributable to \citet{AllaisBM13} but simplified by \citet{ChapmanKNW19}. The \Function{PointEqual-≈} predicate circumvents any need to postulate functional extensionality. Rather, we assert that two Kripke functions $\phi$ and $\psi$ map equivalent inputs to equivalent outputs under all renamings.

Some plumbing is necessary in the case that we are equating two inert maps $\Mapp {\phi} {\nu_1}$ and $\Mapp {\psi} {\nu_2}$: 

\begin{code}
  _≈_ {κ = R[ κ₂ ]} (_$_ {κ₁} φ ν₁) (_$_ {κ₁′} ψ ν₂) with 
    κ₁ ≡k? κ₁′ 
  ... | yes refl = UniformNE φ × UniformNE ψ × 
                   PointEqualNE-≈ φ ψ × ν₁ ≡ ν₂                  
\end{code}
\begin{code}[hide]
  ... | no _ = ⊥  
\end{code}

\Ni Kind equality is decidable (\Function[Kinds.Properties.Decidability][\Underscore≡ₖ\Underscore]{≡ₖ}), which lets us relate inert maps only when the domains of $\phi$ and $\psi$ (that is, $\kappa_{1}$ and $\kappa_1'$) are equivalent. The predicates \Function[Metatheory.Soundness.Relation]{UniformNE} and \Function[Metatheory.Soundness.Relation]{PointEqualNE-≈} are entirely analogous to \Function{Uniform} and \Function{PointEqual-≈} except that they describe Kripke functions in which the domain is a \Datatype{NeutralType} rather than \Type{SemType}. 

Finally, we relate row literals of equal length by a pointwise relation of their contents. Maps with unequal domain kinds (above) and row literals with differing lengths (below) are each mapped to \Datatype{⊥}.

\begin{code}
  _≈_ {κ = R[ κ ]} (row (n , P) p) (row (m , Q) q) with 
    n ≡ℕ? m 
  ... | yes refl = ∀ (i : Fin m) →  P i ≈₂ Q i
    where
      _≈₂_ : ∀ {A} → (x y : A × SemType Δ κ) → Set
      (l₁ , τ₁) ≈₂ (l₂ , τ₂) = l₁ ≡ l₂ × τ₁ ≈ τ₂    
\end{code}
\begin{code}[hide]
  ... | no _ = ⊥
  _ ≈ _ = ⊥
\end{code}
\end{AgdaAlign}

\paragraph{Properties}

Towards proving the fundamental lemma, we observe some crucial properties of the soundness relation. Firstly, propositionally equal neutral types reflect to equivalent semantic objects:

\begin{AgdaAlign}
\begin{code}[hide] 
module FundSoundness where
  open import Rome.Types ; open import Rome.Kinds 
  open import Rome.NormalTypes
  open import Rome.NBE renaming (idEnv to ie)
  open import Rome.Types.Equivalence
  import Rome.Metatheory.Soundness as Soundness
  open Soundness hiding (fund-≈ ; reflect-≈ ; reify-≈ ; idEnv-≈ ; _≈ₑ_ ; soundness ; refl-≈ˡ ; refl-≈ʳ ; sym-≈ ; trans-≈)
\end{code}
\begin{code}
  reflect-≈  : {ν₁ ν₂ : NeutralType Δ κ} →
               ν₁ ≡ ν₂ → reflect ν₁ ≈ reflect ν₂
\end{code}
\begin{code}[hide]
  reflect-≈ = Soundness.reflect-≈
\end{code}

\Ni Dually, equivalent semantic objects reify to propositionally equal types: 

\begin{code}
  reify-≈ : {V₁ V₂ : SemType Δ κ} → 
            V₁ ≈ V₂ → reify V₁ ≡ reify V₂ 
\end{code}
\begin{code}[hide]
  reify-≈ = Soundness.reify-≈
\end{code}

Crucial to most proofs is that the soundness relation forms a \emph{partial equivalence} (PER), meaning it is symmetric and transitive but not reflexive. As with all PERs, of course, we have a quasi-reflexive property: provided $V_1$ relates to \emph{some} $V_2$, then both $V_1$ and $V_2$ relate to themselves.

\begin{code}[hide]
  module _ {V₁ V₂ : SemType Δ κ} where 
\end{code}
\begin{code} 
    refl-≈ˡ : V₁ ≈ V₂ → V₁ ≈ V₁
    refl-≈ʳ : V₁ ≈ V₂ → V₂ ≈ V₂
\end{code}
\begin{code}[hide]
    refl-≈ˡ = Soundness.refl-≈ˡ
    refl-≈ʳ = Soundness.refl-≈ʳ
\end{code}


\paragraph{Logical environments}
We lift the soundness relation to a pointwise equivalence on semantic environments.

\begin{code}
  _≈ₑ_ : {Δ₁ : KEnv} (η₁ η₂ : SemEnv Δ₁ Δ₂) → Set
  _≈ₑ_ {Δ₁ = Δ₁} η₁ η₂ = 
    ∀ {κ} (x : TVar Δ₁ κ) → η₁ x ≈ η₂ x
\end{code}

\Ni  The identity semantic environment relates to itself under the reflection of propositional equality, as witnessed by \Function[Metatheory.Soundness.Relation]{idEnv-≈}. 
\begin{code}[hide]
  module _ {Δ : KEnv} where 
    idEnv = ie {Δ}
\end{code}
\begin{code}
    idEnv-≈ : idEnv ≈ₑ idEnv
    idEnv-≈ _ = reflect-≈ refl
\end{code}

\paragraph{The fundamental lemma}

The fundamental lemma for the soundness relation states that equivalent types evaluate to related semantic objects. The proof of the fundamental lemma is by induction over the type equivalence witness \Var{τ₁} \Datatype{≡ₜ} \Var{τ₂}.
\begin{code}
  fund-≈ : ∀ {η₁ η₂ : SemEnv Δ₁ Δ₂}
           {τ₁ τ₂ : Type Δ₁ κ} → 
           η₁ ≈ₑ η₂ → 
           τ₁ ≡ₜ τ₂ → 
          ⟦ τ₁ ⟧ η₁ ≈ ⟦ τ₂ ⟧ η₂
\end{code}
\begin{code}[hide]
  fund-≈ = Soundness.fund-≈
\end{code}

Soundness follows from the fundamental lemma in the identity semantic environment. Explicitly, reification of the fundamental lemma tells us that \Function{reify} (\Typeclass{⟦} \Var{τ₁} \Typeclass{⟧} \Term{idEnv}) \Datatype{≡} \Function{reify} (\Typeclass{⟦} \Var{τ₂} \Typeclass{⟧} \Term{idEnv}), which is precisely the elaboration of \Typeclass{⇓} \Var{τ₁} \Datatype{≡} \Typeclass{⇓} \Var{τ₂}.

\begin{code}
  soundness : ∀ {τ₁ τ₂ : Type Δ κ} → 
                τ₁ ≡ₜ τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
  soundness = reify-≈ ∘ (fund-≈ idEnv-≈)
\end{code}
\end{AgdaAlign}

\subsection{Consistency}
\label{sec:consistency}

\emph{Consistency} \SourceP{Metatheory.Consistency} states that every type is equivalent to its normalization. Viewing equivalence as reduction, this is equivalently a claim of \emph{(weak) normalization}: each type has \emph{some} reduction sequence to a normal form.

\begin{AgdaAlign} 
\begin{code}[hide]
module ConsistencyStatement where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.NBE
\end{code}
\begin{code}
  consistency : ∀ (τ : Type Δ κ) → τ ≡ₜ ⇑ (⇓ τ)
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.Consistency as Consistency
  consistency = Consistency.consistency
\end{code}
\end{AgdaAlign}


We define a logical relation for consistency (\Function[Metatheory.Consistency.Relation][⟦\Underscore⟧≈\Underscore]{⟦\Dash⟧≈\Dash}) by relating types to semantic objects. The first two cases state the purpose of the relation: $\tau$ relates to $V$ at ground kind when $\tau$ and $V$ are equivalent.

\begin{AgdaAlign}
\begin{code}[hide]
module ConsistencyRelation where
  open import Rome.Prelude
  open import Rome.Kinds
  open import Rome.Kinds.Properties.Decidability
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NBE
  open import Data.Nat.Properties renaming (_≟_ to _≡ℕ?_)  
  open import Rome.Metatheory.Consistency.Relation hiding 
    (⟦_⟧≈_ ; ⟦_⟧≈ᵣ_)
\end{code}
\begin{code}
  ⟦_⟧≈_ : Type Δ κ → SemType Δ κ → Set
  ⟦_⟧≈_ {κ = ★} τ V = τ ≡ₜ ⇑ V
  ⟦_⟧≈_ {κ = L} τ V = τ ≡ₜ ⇑ V
\end{code}

\Ni Two Kripke functions are related when they map related inputs to related outputs under all renamings. That our system reduces modulo $\eta$-equivalence simplifies this definition, which needn't account for when $\phi$ is neutral.

\begin{code}
  ⟦_⟧≈_ {Δ₁} {κ = κ₁ `→ κ₂} f φ = 
      ∀ {Δ₂} (r : Renaming Δ₁ Δ₂) 
      {τ : Type Δ₂ κ₁}
      {V : SemType Δ₂ κ₁} → 
      ⟦ τ ⟧≈ V → 
      ⟦ ren r f · τ ⟧≈ (renKripke r φ ⟨·⟩ V)
\end{code}

That a type $\tau$ is equivalent to an inert map $\Mapp \phi \nu$ requires the identification of some equivalent type $\Mapp f {\Embed\, \nu}$ such that $f$ is related to $\phi$. Of course, $\phi$ is not a \Type{SemType} (its domain is a neutral type), and so the definition \Function[Metatheory.Consistency.Relation]{ConsistentKripkeNE} mirrors the logic above for relating functional types modulo a neutral domain argument.

\begin{code}
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (φ $ ν) = 
    Σ[ f ∈ (Type Δ (_ `→ κ)) ] 
      ((τ ≡ₜ f $ ⇑ ν) × ConsistentKripkeNE f φ)
\end{code}

\Ni The cases for row singletons and row complements follow the same pattern: we identify a type equivalent to the desired semantic form, then assert that form coheres with the relation.

\begin{code}
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = 
    (τ ≡ₜ (⇑ l ▹ ⇑ (reify V))) 
    × ⟦ ⇑ (reify V) ⟧≈ V
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ∖ ρ₁) {nr}) = 
    (τ ≡ₜ (⇑ (reify ((ρ₂ ∖ ρ₁) {nr})))) 
    × ⟦ ⇑ (reify ρ₂) ⟧≈ ρ₂ 
    × ⟦ ⇑ (reify ρ₁) ⟧≈ ρ₁
\end{code}

For semantic rows, we likewise identify a row literal equivalent to $\tau$ (with suitable orderedness evidence) and assert, via \Function[Metatheory.Consistency.Relation][⟦\Underscore⟧≈ᵣ\Underscore]{⟦\Dash⟧≈ᵣ\Dash}, that the contents of the row literal (a list of label-type pairs) is related to the contents of the semantic row (a finite map to semantic types). The helper \Function[Metatheory.Consistency.Relation][⟦\Underscore⟧≈₂\Underscore]{⟦\Dash⟧≈₂\Dash} asserts that the first components of each pair are equal and the second components are related under the consistency relation.

\begin{code}
  ⟦_⟧≈_ {κ = R[ κ ]} τ (row ρ ω) =
    let xs = ⇑ᵣ (reifyRow ρ) in 
    (τ ≡ₜ ⦅ xs ⦆ (fromWitness (⇑ₒ (reifyRowOrdered ω)))) 
    × ⟦ xs ⟧≈ᵣ ρ
    where 
      ⟦_⟧≈ᵣ_ : RowLiteral (Type Δ κ) → 
               Row (SemType Δ κ) → Set
      ⟦ [] ⟧≈ᵣ (zero , P) = ⊤
      ⟦ x ∷ xs ⟧≈ᵣ (suc n , P) = 
        (⟦ x ⟧≈₂ P fzero) × ⟦ xs ⟧≈ᵣ (n , P ∘ fsuc)
\end{code}
\begin{code}[hide]
      ⟦ [] ⟧≈ᵣ (suc n , P) = ⊥
      ⟦ x ∷ ρ ⟧≈ᵣ (zero , P) = ⊥
\end{code}
\end{AgdaAlign}

\paragraph{Properties}

The consistency relation observes properties analogous to the soundness relation. First, types equivalent to neutral types are related to their reflection:

\begin{AgdaAlign}
\begin{code}[hide] 
module FundConsistencyStatement where
  open import Rome.Types ; open import Rome.Kinds 
  open import Rome.NormalTypes
  open import Rome.NBE hiding (idEnv)
  open import Rome.Types.Equivalence
  open import Rome.Types.Properties
  import Rome.Metatheory.Consistency as Consistency
  open Consistency hiding (⊢⟦_⟧≈ ; reflect-⟦⟧≈ ; reify-⟦⟧≈ ; fund-⟦⟧≈  ; consistency)
\end{code}
\begin{code}
  reflect-⟦⟧≈ : {τ : Type Δ κ} {υ :  NeutralType Δ κ} → 
               τ ≡ₜ ⇑ υ → ⟦ τ ⟧≈ reflect υ
\end{code}
\begin{code}[hide]
  reflect-⟦⟧≈ = Consistency.reflect-⟦⟧≈
\end{code}

\Ni Dually, types related to semantic objects are equivalent to their reification:

\begin{code}
  reify-⟦⟧≈ : {τ : Type Δ κ} {V :  SemType Δ κ} → 
              ⟦ τ ⟧≈ V → τ ≡ₜ ⇑ (reify V)
\end{code}
\begin{code}[hide]
  reify-⟦⟧≈ = Consistency.reify-⟦⟧≈
\end{code}

% \paragraph{Logical environments}
% We pointwise relate syntactic substitutions with semantic environments.

% \begin{code}
%   ⟦_⟧≈ₑ_ : Substitution Δ₁ Δ₂ → SemEnv Δ₁ Δ₂ → Set  
%   ⟦_⟧≈ₑ_ {Δ₁ = Δ₁} σ η = 
%     ∀ {κ : Kind} (α : TVar Δ₁ κ) → ⟦ σ α ⟧≈ η α
% \end{code}

% \Ni  As expected, the identity substitution relates to the identity semantic environment (\Function[Metatheory.Consistency.Relation]{idEnv-⟦⟧≈}). The constructor \Constructor[Types.Equivalence][\Underscore≡ₜ\Underscore.eq-refl]{eq-refl} witnesses reflexivity of type equivalence.

% \begin{code}[hide]
%   -- in the def below, either ` or idEnv need to be told what Δ₁ is,
%   -- which is ugly to use an implicit for. This is a small little presentational
%   -- lie---we'll introduce its environment as an implicit of the module.
%   module _ {Δ : KEnv} where
%     open import Rome.NBE renaming (idEnv to ie)
%     idEnv = ie {Δ = Δ}
% \end{code}
% \begin{code}
%     idEnv-⟦⟧≈ : ⟦ ` ⟧≈ₑ idEnv
%     idEnv-⟦⟧≈ _ = reflect-⟦⟧≈ eq-refl
% \end{code}

\paragraph{The fundamental lemma}

The fundamental lemma proves that the substitution of type $\tau$ by $\sigma$ is related to its evaluation in semantic environment $\eta$:

\begin{code}
  fund-⟦⟧≈ : ∀ (τ : Type Δ₁ κ)
            {σ : Substitution Δ₁ Δ₂}
            {η : SemEnv Δ₁ Δ₂} → 
            ⟦ σ ⟧≈ₑ η  → 
            ⟦ τ [ σ ]ₛ ⟧≈ ⟦ τ ⟧ η
\end{code}
\begin{code}[hide]
  fund-⟦⟧≈ = Consistency.fund-⟦⟧≈
\end{code}

\Ni provided a pointwise relation of $\sigma$ and $\eta$:

\begin{code}[hide]
module ConsistencyRest where
  open import Rome.Types ; open import Rome.Kinds 
  open import Rome.NBE
  open import Rome.NormalTypes
  open import Rome.Types.Equivalence
  open import Rome.Types.Properties
  import Rome.Metatheory.Consistency as Consistency
  open Consistency hiding (⊢⟦_⟧≈ ; ⟦_⟧≈ₑ_ ; consistency)
\end{code}
\begin{code}
  ⟦_⟧≈ₑ_ : Substitution Δ₁ Δ₂ → SemEnv Δ₁ Δ₂ → Set  
  ⟦_⟧≈ₑ_ {Δ₁ = Δ₁} σ η = 
    ∀ {κ : Kind} (α : TVar Δ₁ κ) → ⟦ σ α ⟧≈ η α
\end{code}

A natural corollary of the fundamental lemma is that the substitution of \Var{τ} by the identity substitution \Constructor{`} relates to the evaluation of \Var{τ} in the identity environment, or more simply that $\tau$ relates to its evaluation:

\begin{code}
  ⊢⟦_⟧≈ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≈ ⟦ τ ⟧ idEnv
\end{code}
\begin{code}[hide]
  ⊢⟦ τ ⟧≈ = subst (⟦_⟧≈ ⟦ τ ⟧ idEnv) 
    (sub-id τ) (fund-⟦⟧≈ τ idEnv-⟦⟧≈)    
\end{code}

\Ni Consistency follows directly from the reification of this fact.

\begin{code}
  consistency : (τ : Type Δ κ) → τ ≡ₜ ⇑ (⇓ τ) 
  consistency = reify-⟦⟧≈ ∘ ⊢⟦_⟧≈
\end{code}
\end{AgdaAlign}


\paragraph{Completeness}

\emph{Completeness} \SourceP{Metatheory.Completeness} is a simple corollary of consistency. The derivation is given below using custom support (\Record[Types.Equivalence][≡ₜ-Reasoning]{\Dash≡ₜ⟨\Dash⟩\Dash}, \Source{Types.Equivalence}) for equational reasoning over type equivalence. The helper \Function[Types.Equivalence]{inst} reflects propositional equality to type equivalence, and the suffix (\Constructor[Types.Equivalence][≡ₜ-Groupoid]{⁻¹}) witnesses symmetry of type equivalence.

\begin{AgdaAlign}
\begin{code}[hide] 
module Completeness where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.NBE
  open import Rome.Metatheory.Consistency
  open ≡ₜ-Reasoning
\end{code}
\begin{code}
  completeness : {τ υ : Type Δ κ} →
                 ⇓ τ ≡ ⇓ υ → τ ≡ₜ υ 
  completeness {τ = τ} {υ} e = 
   τ        ≡ₜ⟨ consistency τ ⟩ 
   ⇑ (⇓ τ)  ≡ₜ⟨ inst (cong ⇑ e) ⟩ 
   ⇑ (⇓ υ)  ≡ₜ⟨ consistency υ ⁻¹ ⟩ 
   υ ∎ 
\end{code}
\end{AgdaAlign}

\Ni Soundness and completeness together imply, as desired, that $\TEqvJ \Delta \tau \upsilon \kappa$ iff $\Norm\, \tau \equiv\, \Norm \upsilon$.

\subsection{Decidability of Type Conversion}

It is easy enough to implement a syntactic decidability check (\Function[NormalTypes.Properties.Decidability][\Underscore≡?\Underscore]{≡?}) on the shapes of normal forms. Paired with soundness and completeness, we get an effective decision procedure (\Function[Metatheory.Decidability][\Underscore≡ₜ?\Underscore]{≡ₜ?})  to decide the relation $\TEqvJ \Delta \tau \upsilon \kappa$:

\begin{AgdaAlign}
\begin{code}[hide]
module DecTyEquiv where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.Metatheory.Completeness
  open import Rome.Metatheory.Soundness
  open import Rome.NBE 
  open import Rome.Kinds.Properties.Decidability
  open import Rome.NormalTypes.Properties.Decidability
\end{code}
\begin{code}
  _≡ₜ?_ : ∀ (τ₁ τ₂ : Type Δ κ) → Dec (τ₁ ≡ₜ τ₂)
  τ₁ ≡ₜ? τ₂  with (⇓ τ₁) ≡? (⇓ τ₂)
  ... | yes p = yes (completeness p)
  ... | no  p = no (p ∘ soundness)
\end{code}
\end{AgdaAlign}
\fi 

% -----------------------------------------------------------------------------
% Formalization choices & related work

\section{Formalization Choices \& Related Work}
\label{sec:related-work}
\ifrelatedWork

We conclude with a discussion of design decisions, related row calculi, and other formalization efforts.

\subsection{Notable Consequences of Design}
\secref{consistency} claims that consistency is equivalently a claim of weak normalization. However, we do not crucially show that the embedding of a given normal type $\tau$ takes no further steps (i.e., that \Function{¬} \Function{∃[} \Var{υ} \Function{]} (\Function{⇑} \Var{τ} \Datatype{≡ₜ} \Var{υ})). This is a consequence of having mechanized the full equivalence relation, rather than the reflexive, transitive, and symmetric closure of a step relation. A commitment to the latter may have facilitated a stronger discussion of type reduction as a rewrite theory, and other claims thereof (e.g., confluence). 

Another area worth exploration is reusability, \ala{} \citet{AllaisACMM21} or \citet{Saffrich24}. That is, which definitions and claims require induction, and which could instead be module parameters? Future work could provide a modular interface for metatheory, where the user need only supply the definitions of \emph{some} types and theorems.  % Work in progress by the authors seeks to relate denotational and operational semantics of \Rome's term structure, which requires a level-stratification of kinds and types. This results in a massive duplication of data types, begging the question: what may be abstracted? That is, which definitions and claims require induction over the structure of ASTs, and which could instead be parameterized? Future work could provide a modular interface for metatheory, where the user need only supply the definitions of \emph{some} types and theorems. 

\subsection{Other Higher-Order Row Calculi}

Existing formalizations of row calculi with type-level computation differ in both the expressiveness of their row language and in their semantic accounts. We distinguish denotational approaches from elaboration-based approaches, which translate source types into a target calculus with an established metatheory.

\paragraph{Denotational semantics} System \RO (the predecessor to \Rome) is given a denotational semantics by \Citet{HubersM23}, whose soundness result shows that equivalent types have the same denotation, and that well-typed terms inhabit the denotations of their types. This establishes semantic soundness of the equational theory, but does not characterize normal forms or give a complete decision procedure for type equivalence.

\paragraph{Elaboration-based semantics} In contrast, \Citet{Chlipala10} elaborates Ur, a web-programming based language with type-level records, to Rocq~\citep{Rocq}, but only conjectures that a terminating and confluent type-reduction procedure could be given. \Citet{TooheyCJX26} elaborate their system $\LamRho{}$ into $\FOPlus{}$, an extension of System~$\FO$ with products and sums, and formalize normalization of the target calculus in Lean~4~\citep{Lean4}. But, unlike our normalizer, their proof relies on a logical relation that lives in \Datatype{Prop}, and hence provides no constructive algorithm mapping type syntax to normal forms. % In contrast, our normalizer operates directly on higher-order rows and must account explicitly for row computation.

% Existing formalizations of row calculi with type-level computation differ in both the expressiveness of their row language and the way they account for type equivalence. We distinguish denotational approaches from elaboration-based approaches, which translate source types into a target calculus with an established metatheory.

% \paragraph{Denotational approaches}

% \Citet{HubersM23} give a denotational semantics for System \RO's kinds, types, and terms. Their soundness theorem shows that equivalent types have the same denotation, and that well-typed terms inhabit the denotations of their types. This establishes semantic soundness of the equational theory, but does not characterize normal forms or give a complete decision procedure for type equivalence.

% \paragraph{Elaboration-based approaches}
% \Citet{Chlipala10} describes \emph{featherweight Ur}, a language with type-level records and an elaboration into Rocq~\citep{Rocq}. The development does not provide a normalization procedure for Ur's own definitional equality. Instead, the author conjectures that a terminating and confluent procedure could be given. More recently, \Citet{TooheyCJX26} give an elaboration semantics for $\LamRho{}$ into $\FOPlus{}$, an extension of System~$\FO$ with products and sums, and formalize normalization of the target calculus in Lean~4~\citep{Lean4}. In contrast, our normalizer operates directly on higher-order rows and must account explicitly for row computation. Moreover, their proof relies on a logical relation for normalization that lives in \Datatype{Prop}, and hence provides no constructive algorithm mapping type syntax to normal forms.

\subsection{NbE and Intrinsic Mechanization}

\paragraph{Nondependent type theories}
Our NbE construction follows the intrinsic syntax and logical-relation techniques of \Citet{ChapmanKNW19}, who in turn build on \Citet{AllaisBM13}. As in those works, the choice of normal and neutral forms determines whether reflection, reification, and renaming are stable under intrinsic indexing. For $\Rome$, this choice must additionally account for neutral labels, inert maps, ordered row literals, and residual complements.

\paragraph{Dependent type theories}
Normalization by evaluation has also been mechanized in Agda for substantially richer type theories, particularly dependent type theory \citep{Abel13,AbelC14,AbelAHPMSS19}. These developments address challenges that are largely orthogonal to ours, such as explicit substitutions and the transport of context and type indices through dependent syntax. We focus instead on the interaction between higher-order row computation and the semantic invariants required by reification. 

Pinning down a precise treatment of explicit substitutions is still ongoing research. \Citet{AltenkirchK16B} use quotient inductive-inductive types (via postulating constructors and eliminators), while \Citet{ChenNFT26} investigate this approach in Cubical Agda, where higher inductive types are supported by the ambient theory. In $\Rome$, the term--type--kind stratification allows us to retain ordinary inductive syntax and propositional equality throughout the development. This keeps normalization executable and avoids features forbidden by the trusted \emph{--safe} flag.
\fi

% \clearpage
% \appendix


\bibliography{NBE}
\end{document}
%%% Local Variables: 
%%% TeX-command-extra-options: "-shell-escape"
%%% End:
%  LocalWords:  denotational Agda Wadler dPoint sqrt subtyping coercions Intr
%  LocalWords:  RowTypes Bool eval GHC reified HillerstromL Leijen LindleyM RO
%  LocalWords:  ChapmanKNW Aydemir AbelAHPMSS AbelC AbelOV plfa HubersIMM STLC
%  LocalWords:  MorrisM denotationally DenotationalSoundness RowTheories Suc de
%  LocalWords:  ReifyingVariants RowTheory BerthomieuM CardelliMMS HarperP NatF
%  LocalWords:  XueOX GasterJ Sipser SaffrichTM Env Expr Agda's Leivant ChanW
%  LocalWords:  ThiemannW ImpredicativeSet ImpredicativeSetSucks AbelP chapman
%  LocalWords:  AltenkirchK KaposiKK Gaster XieOBS BiXOS Chlipala objTypes Bahr
%  LocalWords:  Garrigue KEnv PEnv Commutativity pygments hyperref
 
