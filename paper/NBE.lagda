\documentclass[sigplan,10pt]{acmart}
\settopmatter{printfolios=true,printccs=true,printacmref=true}

% -----------------------------------------------------------------------------
% Packages 

\usepackage{accents}        % accents below math symbols
\usepackage{amsfonts}       % math fonts and blackboards
\usepackage{amsthm}         % theorem environments
\usepackage{array}          % extended table column types
\usepackage{caption}        % customize figure captions
\usepackage{centernot}      % center negation over symbols
\usepackage{enumitem}       % customize list layouts
\usepackage{ifthen}         % conditional logic in macros
\usepackage{listings}       % source code formatting
\usepackage{minted}         % Pygments syntax highlighting
\usepackage{newunicodechar} % define Unicode chars in TeX
\usepackage{stmaryrd}       % extra math/logic symbols
\usepackage{subcaption}     % subfigures and subcaptions
\usepackage{xspace}         % smart spaces after macros

% -----------------------------------------------------------------------------
% Configured packages

\usepackage[para]{footmisc}                % paragraph-style footnotes
\usepackage[utf8]{inputenc}                % UTF-8 source text encoding
\usepackage[T1]{fontenc}                   % T1 output font encoding
\usepackage[svgnames, dvipsnames]{xcolor}  % named colors and shading
\usepackage[capitalize,noabbrev]{cleveref} % capitalized cross-refs
\usepackage[normalem]{ulem}                % text underlining/striking
\PassOptionsToPackage                      % PDF bookmarks/links
  {unicode,naturalnames}{hyperref}

% -----------------------------------------------------------------------------
% My packages

\usepackage{./sty/mathwidth}
\usepackage{./sty/infer}
\usepackage{./sty/agda}
\usepackage{./sty/NBE}
\usepackage{./sty/commands}
\usepackage{./sty/environments}
\usepackage{./sty/unicode}

% Some configuration
\AgdaNoSpaceAroundCode

% -----------------------------------------------------------------------------
% Set counter to 0 (for abstract)
\setcounter{section}{0}

% -----------------------------------------------------------------------------
% ACM garbage

\setcopyright{none}
\citestyle{acmauthoryear}
\settopmatter{printacmref=false, printfolios=true}
\renewcommand{\footnotetextcopyrightpermission}{} 
% Redefine the \acmDOI command to do nothing 
\pagestyle{empty}
\fancyfoot{}

% -----------------------------------------------------------------------------
% Title and Author

\title{Normalization by Evaluation of Higher-Order Rows}
\author{Alex Hubers}
\orcid{0000-0002-6237-3326}
\affiliation{
  \department{Department of Computer Science}
  \institution{The University of Iowa}
  \streetaddress{14 MacLean Hall}
  \city{Iowa City}
  \state{Iowa}
  \country{USA}}
\email{alexander-hubers@uiowa.edu}

\author{J. Garrett Morris}
\orcid{0000-0002-3992-1080}
\affiliation{
  \department{Department of Computer Science}
  \institution{The University of Iowa}
  \streetaddress{14 MacLean Hall}
  \city{Iowa City}
  \state{Iowa}
  \country{USA}}
\email{garrett-morris@uiowa.edu}

% -----------------------------------------------------------------------------
% Document

\begin{document}
\InlineOn{}

\maketitle

\begin{code}[hide]
{-# OPTIONS -W noUnreachableClauses #-}
module NBE where 
open import Rome.Prelude
\end{code}

% -----------------------------------------------------------------------------
% Abstract

\section*{Abstract}
Row types map labels to types, and are used to \emph{structurally} type records and variants. The presence of higher-order rows, in which labels map to types of higher kind, introduces nontrivial forms of type computation. This paper presents a sound and complete equational theory for types in \Rome (pronounced ``Rome''), a higher-order row type theory. We normalize \Rome types by evaluation in the interactive proof assistant Agda. Moreover, we contribute extensions to logical relation techniques for intrinsic mechanization to prove this procedure is stable, sound, and consistent. As a result, we obtain the first decidable type-conversion algorithm for a higher-order row type theory.

% -----------------------------------------------------------------------------
% Introduction

\section{Introduction}
Row types, as introduced by \citet{wand87}, describe type-level associations of labels to types. Rows can be used dually to type \emph{records} (i.e., classes and objects) and \emph{variants} (i.e., algebraic data types). Recent row type systems~\citep{HubersM23,Chlipala10,Chlipala16, TooheyCJX26} use higher-order rows to describe meta- and generic programs. However, these calculi lack a formal metatheory of type computation.

Systems with type computation typically include a \emph{type conversion} rule, in which a term $M$ at type $\tau$ may be converted to type $\upsilon$ provided that $\tau = \upsilon$. But this rule complicates and impedes the metatheory. For example, type checking is not decidable if type equivalence is not decidable. Consider the judgment $\TypeJ {\Gamma, x : \tau} {x} {\upsilon}$, which is well-typed if $\tau \equiv \upsilon$ and ill-typed otherwise. In addition, type conversion impedes \emph{preservation} and \emph{progress}. For example, when analyzing an application $\TypeJ \Gamma {M\, N} {\upsilon}$, inverting the head term $\TypeJ \Gamma M {\tau \to \upsilon}$  via the inductive hypothesis may yield a conversion rather than a canonical $\lambda$-binding, leaving the proof \emph{stuck}.

Type conversion is typically decided by reducing types to normal forms and performing a syntactic equality check (modulo $\alpha$-equivalence). In fact, the presence of normal forms permits the system to eliminate the type conversion rule entirely: terms may be indexed by types in normal form, and thus any use of the conversion rule would superfluously equate identical types. Eliminating the conversion rule "unstucks" proofs of progress, as the head term in an application must be in canonical form (a $\lambda$-binding).

Type normalization is necessary for important metatheoretic claims, but can be nontrivial. An equational theory for System \FO involves only one nontrivial equation: $\beta$-reduction. The presence of higher-order row types and type operators introduces an abundance of nontrivial type equalities, e.g., the reduction of a map over a row. Likewise, subtle boundary cases arise when constructing record and variant types from nested rows. Consequently, an equational theory with higher-order rows cannot defer to its parent system to inherit a proof of type normalization, nor claim such a proof is an orthogonal triviality. 

This paper closes this metatheoretic gap. We introduce \Rome (pronounced ``Rome''), a novel row calculus extending System \RO~\citep{HubersM23} with row mapping, iso-recursive types, and a novel complement operator on rows. We provide a sound and complete equational theory of types in \Rome and prove that this theory, when viewed as a reduction sequence, is normalizing.

This involves two key contributions. First, we implement a \emph{normalization by evaluation} (NbE) procedure that maps types to normal forms. This procedure is not only responsible for reducing along nontrivial row type equalities, but also for identifying the precise normal and neutral forms of rows and row operations. Second, we prove the equational theory is sound and complete with respect to this normalization function via two Kripke-style logical relations. Our contributions are mechanized in the interactive theorem prover Agda. \Citet{AbelAHPMSS19} highlight the challenge of \emph{Kripke-style logical relations} on \emph{intrinsically well-typed terms}, for which ``developing [logical relation] proofs for realistic languages can require an almost heroic mechanization effort in existing general-purpose proof assistants.'' Our development follows \citet{AllaisBM13} and \citet{ChapmanKNW19} in contributing additional tooling for this known challenge. Our artifact serves as a reference for future NbE and logical-relation proofs of normalization for systems with computation beyond $\beta$-reduction.

In contrast to developments where normalization predicates live in a propositionally irrelevant universe (e.g., that of \citet{TooheyCJX26}), our development is \emph{constructive}: we do not merely assert the existence of normal forms, but rather compute a normal form $\hat{\tau}$ for each type $\tau$. Moreover, decidability of the equational theory is constructive: given types $\KindJ \Gamma \tau \kappa$ and $\KindJ \Gamma \upsilon \kappa$, we can either (i) compute a derivation of $\TEqvJ \Gamma \tau \upsilon \kappa$, or (ii) show no such derivation can exist.   

% -----------------------------------------------------------------------------
% Contributions

In summary, this paper contributes: 

\begin{enumerate}
  \item \Rome{}'s types, kinds, and equational theory \cref{sec:Rome};
  \item a classification of the normal and neutral forms required for higher-order rows, including inert maps, neutral-label rows, and residual row complements \cref{sec:normal-forms};
  \item an NbE algorithm whose semantic operations implement $\beta$-reduction, row mapping and complements, and nested $\Pi$ and $\Sigma$ computation \cref{sec:NbE};  
  \item mechanized proofs of stability, soundness, and completeness in Agda, yielding a decision procedure for \Rome type equivalence \cref{sec:metatheory}; and
  \item a \emph{fully safe} Agda artifact witnessing the computability of normal forms and type equivalence.
\end{enumerate}

% -----------------------------------------------------------------------------
% Rows in Action

\section{Rows in Action}
\label{sec:rows-in-action}

We begin by illustrating some of the novel type computation features in \Rome.


\paragraph{Row types} Rows in \Rome are a type-level representation of record fields and variant constructors.  A \emph{row} is an association of labels to types. The operator $\Pi$ constructs a record from a row, while $\Sigma$ constructs a variant. In the former case, labels describe fields and types describe outputs; in the latter, labels describe constructor names and types describe constructor inputs. To demonstrate, a two dimensional point can be specified as a record type, with \R{{'x ▹ Int , 'y ▹ Int}} as its underlying row:

\begin{rosi} 
Point : Π {'x ▹ Int , 'y ▹ Int}
\end{rosi}

\Ni Dually, a binary tree type can be specified as a recursive variant: 

\begin{rosi}
tree : μ (Σ {'Node   ▹ const Int, 
             'Branch ▹ λ tree → tree × tree})
\end{rosi}

\Ni The row underlying the \R{tree} type is a row of type operators, permitted by \Rome's higher-order capabilities. We can abstract over such rows to do powerful metaprogramming. For example, we can simulate the deriving of a functor typeclass instance: 

\begin{rosi}
type Functor : (⋆ → ⋆) → ⋆
type Functor f = ∀ a b. (a → b) → f a → f b
fmapΣ : ∀ z : R[⋆ → ⋆]. Π (Functor z) → Functor (Σ z)
\end{rosi}

The syntax $\forall z : \RowK {\TypeK \to \TypeK}$ quantifies a \emph{row variable} !z! containing type operators at kind $\TypeK \to \TypeK$. The syntax \R{Functor} \R{＠ z} denotes the mapping of the \R{Functor} type operator over row !z!---that is, the application of \R{Functor} to each operator in !z!. The type of \R{fmapΣ} states that, given a record of \R{fmap} instances at type \R{Π (Functor} \R{＠ z)}, we can give a \R{Functor} instance for \R{Σ z}. This is analogous to components of Haskell's \emph{Deriving Functor} machinery~\citep{Laarhoven07}, but without resort to meta-programming, GHC internals~\citep{GhcAPI}, or Template Haskell~\cite{SheardJ02}.

\paragraph{Reducing rows}
\label{sec:reducing-rows2}

The type of \R{fmapΣ} is \emph{not} in normal form. Expanding the \R{Functor} type synonym and reducing the application \R{Functor} \R{(Sigma z)} yields:


\begin{rosi}
fmapΣ : ∀ z : R[⋆ → ⋆].
        Π ((λ f. ∀ a b. 
            (a → b) → f a → f b) ＠ z) →
        ∀ a b. (a → b) → (Σ z) a → (Σ z) b 
\end{rosi}


What is \R{(Σ z) a}? Intuitively, we expect this to mean ``the variant produced by supplying !a! as an argument to each operator in !z!''. Hence this application reduces in \Rome{} according to an associativity rule. First, for conceptual clarity, let us define some metanotation for a "flipped mapping" helper \Infix{?} (read as "flap"):

\begin{rosi}
type r ? t = (λ f. f t) ＠ r
\end{rosi}

\Ni The flap operator takes a row of type operators and an argument, yielding a row of the applications of each operator to that argument. Now the return type of \R{fmapΣ} is:

\begin{rosi}
fmapΣ : ... → ∀ a b. (a → b) → Σ (z ? a) → Σ (z ? b) 
\end{rosi}

This type is in normal form, but there is \emph{potential} computation waiting: all we need is a proper \emph{value} for the row !z!. Consider when !z! is the row underlying the tree functor. Then the return type is:

\begin{rosi}
fmapΣ : ... → Σ ({'Node ▹ const Nat, 
                   'Branch ▹ λ t. t × t} ? b)
\end{rosi}

\Ni Expanding the flap metanotation yields:
\begin{rosi}
fmapΣ : ... → Σ ((λ f. f b) ＠  
               {'Node ▹ const Nat, 'Branch ▹ λ t. t × t})
\end{rosi}
\Ni which maps then $\beta$-reduces to: 

\begin{rosi}
fmapΣ : ... → Σ {'Node ▹ Nat, 'Branch ▹ b × b}
\end{rosi}

\Ni Similar reduction takes places in the input type.

\paragraph{Desugaring Booleans}

Consider a Boolean AST realized by the (higher-order) row of type operators \R{BoolF}, which has constructors for truth, falsity, conditionals, and disjunction.

\begin{rosi} 
type BoolF = {'T ▹ const ⊤ , 'F ▹ const ⊤ , 
              'If ▹ λ b. b × b × b , 'Or ▹ λ b. b × b}  
\end{rosi}

We specify an evaluation function as taking the least fixed-point of the variant constructed by \R{BoolF} and returning a variant that is either the true or false case.

\begin{rosi}
eval : μ (Σ BoolF) → Σ {'T ▹ ⊤ , 'F ▹ ⊤}
\end{rosi}

Observe first that $\mu$, the least fixed-point type operator in \Rome, expects its input to be canonically $\lambda$-bound, otherwise the types of term constants such as \R{out} \R{:} \R{μ BoolF} \R{→} \R{BoolF (μ BoolF)} cannot compute. As \R{Σ BoolF} has kind $\TypeK \to \TypeK$ in an empty context, this should be the case. But this means that the expression \R{Σ BoolF} must (in-line and) normalize to: 

\begin{rosi}
λ b. \Sigma {'T ▹ ⊤ , 'F ▹ ⊤ , 'If ▹ b × b × b , 'Or ▹ b × b}  
\end{rosi}

Now consider a desugaring pass to replace the \R{Or} constructor with \R{If} statements. Such a pass is typed as follows:

\begin{rosi}
type Or = {'Or ▹ λ b. b × b}
desugarOr : μ (Σ BoolF) → μ (Σ (BoolF ∖ Or))
\end{rosi}

\Ni The syntax \R{(BoolF ∖ Or)} describes the row obtained by removing the \R{Or} row fields from the \R{BoolF} row---hence the type specifies precisely the intent of desugaring. We should expect the following computation:

\begin{rosi}
  BoolF ∖ Or
= {'T  ▹ const Unit, 
   'F  ▹ const Unit, 
   'If ▹ λ b. b × b × b}
\end{rosi}

\paragraph{Predicates and containment}
Perhaps instead we wish to desugar \emph{all} Boolean constructs to the untyped $\lambda$-calculus: 

\begin{rosi}
type LamF  = {'Lam ▹ λ x. x , 
              'App ▹ λ x. x × x , 
              'Var ▹ const Nat}
\end{rosi}

Using row polymorphism and the \emph{row containment} predicates \R{BoolF < y} and \R{LamF < (y  ∖  BoolF)}, we specify that \R{desugar} can operate on any row !y! that includes at least the \R{BoolF} fields and, once those fields are removed, still contains the \R{LambF} fields. This formulation provides a powerful abstraction, enabling \R{desugar} to process any AST that incorporates Boolean constructors.

\begin{rosi}
desugar : ∀ z : R[⋆]. BoolF < z, LamF < (z ∖ BoolF) ⇒
          μ (Σ z) → μ (Σ (z ∖ BoolF))  
\end{rosi}

While this example demonstrates no new forms of \emph{row computation}, it highlights that with each additional row operator comes (possibly many) new \emph{neutral} forms: the types !z! \R{∖ BoolF} and \R{BoolF ∖ z} each may not reduce with a value for !z!.

% \paragraph{Label-generic extension}
% While they incur no forms of type computation, it is nevertheless helpful to highlight that System \RO (and hence \Rome) permits first-class labels~\citep{Leijen04} in the kind, type, and term calculus. For example, with first-class labels we can specify the addition of an arbitrary constructor !l! with type !tau! to \emph{any} variant lacking !{l ▹ tau}!:

% \begin{rosi}
% extend : forall l : L, tau : *, z : R[ * ]. {l ▹ tau} < z => 
%          Sigma (z - {l ▹ tau}) → # l → tau → Sigma z
% \end{rosi}

% Critically, the type variable !l! is quantified with \emph{label kind} !L!, and so we express !{l ▹ tau}! as a row singleton with \emph{variable label}. The type !# l! has kind !*! and permits the label to be a first-class argument to the !extend! function.

% -----------------------------------------------------------------------------
% Rωμ type system

\section{The \Rome{} Type System}
\label{sec:Rome}
 This section defines the \Rome type system. \Cref{fig:kinding} gives the kinding rules for the highlighted \Rome types. We omit the syntax of terms and typing rules, as we are focused purely on type-level computation.

\subsection{Kind Syntax}
\input{figures/syntax-types}

\AH{Check Agda documentation for what the inline command is, again... I imagine I can get a fair bit of mileage at least with the basic examples.}
\Cref{fig:syntax-types} describes the syntax of kinds, predicates, and types in \Rome. We have highlighted the syntax that extends System \Fome in \cref{fig:syntax-types}. Labels (i.e., record field and variant constructor names) live at the type level, and are classified by kind $\LabK$. Rows of kind $\kappa$ are classified by $\RowK \kappa$. When possible, we use $\phi$ for type functions, $\rho$ for types of row kind, and $\xi$ for types of label kind. 


\paragraph{Mechanized representations} The types !Kind! and !KEnv! represent kinds and kinding environments, respectively. Kinding environments are right-growing lists of kinds.

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

Our mechanization employs intrinsically well-scoped De Bruijn variables, meaning variables are effectively indices into a kinding environment $\Delta$. The variables $\kappa$ and $\Delta$ are implicitly quantified kinds and kinding environments.

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

The type $\pi \then \tau$ denotes a qualified type \citep{Jones92}. In essence, the predicate $\pi$ restricts the instantiation of the type variables in $\tau$. The predicate $\LeqP {\rho_1} {\rho_2}$ denotes that $\rho_1$ is \emph{contained} in $\rho_2$. Note that the predicate $\LeqP {\rho_1} {\rho_2}$ relates only row-kinded types (rule \ksrule{$\lesssim$}): it is \emph{not} a full-fledged subtyping relation. The predicate $\PlusP {\rho_{1}} {\rho_{2}} {\rho_{3}}$ denotes that rows $\rho_{1}$ and $\rho_{2}$ concatenate to the row $\rho_{3}$. We index the judgment $\KindJ \Delta \pi {\RowK \kappa}$ by row kind, which expresses that the rows constrained in $\pi$ house types with kind $\kappa$.

We presume a set of \emph{label constants} $\mathcal L$ for which (i) equality is decidable and (ii) $<$ induces a strict, total ordering. Rule \krrule{row} ensures that row literals are ordered accordingly. This avoids the need to identify row literals and their normal forms modulo permutation. We distinguish singleton rows \krrule{rsing}, which have variable (or un-reduced) label $\xi$, from row literals \ksrule{row} with literal labels $\ell_i$. Permitting label variables in row literals permits an opportunity for row labels to overlap upon instantiation. The syntax $\Mapp\phi \rho$ maps the type operator $\phi$ across a row $\rho$. The syntax $\rho_2 \Compl \rho_1$ denotes the \emph{row complement} of $\rho_{2}$ by $\rho_{1}$, analogous to set complements.

\paragraph{Mechanized representations}
Our mechanization is \emph{intrinsic}, meaning types are indexed by context and kind. The shape of predicates does not differ be they constraining a \emph{type} or a \emph{normal form}, and hence the !Pred! type generalizes over both via the !Ty! parameter. For example, predicates on !Type!s are described by !Pred! !(Type! !Delta! !kappa!!)!.

\begin{AgdaAlign}
\begin{code} 
  data Pred (Ty : Set) : Set
  data Type (Δ : KEnv) : Kind → Set
\end{code}

Row literals are defined as lists of label-type associations; like with !Pred!, this definition may be reused for normal forms, and so is parameterized by !Ty!. The predicate !Ordered! !xs! asserts that the row literal !xs! is well-ordered on labels. The function !ordered?! witnesses that this predicate is decidable.

\begin{code}
  RowLiteral : (Ty : Set) → Set 
  RowLiteral Ty = List (Label × Ty)
  Ordered  : ∀ {Ty : Set} → RowLiteral Ty → Set 
  ordered? : ∀ {Ty : Set} → (ρ : RowLiteral Ty) → 
             Dec (Ordered ρ) 
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

Two !Type! constructors are interesting. First, we restrict the formation of $\Pi$ and $\Sigma$ to just kinds that do not yield label-valued rows. % We guard these constructors with the predicate !NotLabel! $\kappa$, which computes to $\bot$ when $\kappa \in \mathcal K$ (see \cref{fig:syntax-types}) and $\top$ otherwise.

\begin{code} 
    Π     : {nl : NotLabel κ} → Type Δ (R[ κ ] `→ κ)
    Σ     : {nl : NotLabel κ} → Type Δ (R[ κ ] `→ κ)
\end{code}
\end{AgdaAlign}

The !NotLabel! $\kappa$ predicate computes to $\bot$ when $\kappa \in \mathcal K$ (see \cref{fig:syntax-types}) and $\top$ otherwise, making it \emph{irrelevant}. Hence congruence over $\Pi$ and $\Sigma$ may be defined without regard for this evidence. That is, we have $\Pi\, \{nl_{1}\}\, \rho_{1} \equiv \Pi\, \{nl_2\}\, \rho_2$ iff $\rho_1 \equiv \rho_2$.

Second, we impose a canonical ordering of row literals via the predicate !Ordered! $\rho$. The following constructs row literal types, and is guarded by the predicate !True (ordered? xs)!.

\begin{code}
    ⦅_⦆ : (xs : RowLiteral (Type Δ κ)) → True (ordered? xs) →
          Type Δ R[ κ ]
\end{code}

% \AH{Space permitting, put (sections of) NotLabel and Ordered into a figure to demonstrate how one needs squashing and the other doesn't.}
\Ni Unlike with !NotLabel !$\kappa$, the !Ordered xs! predicate is not trivially irrelevant, nor does it compute to $\top$ or $\bot$ on closed terms. However, it is decidable, as witnessed by the function !ordered? xs!. In turn, it can be \emph{squashed} via the Agda Standard Library's~\citep{AgdaStdLib} !True! operator, which computes to $\top$ when !xs! is well-ordered and $\bot$ otherwise. This reproduces the same desirable properties of the !NotLabel! predicate. In particular, we have that $\RowLiteral{xs}\, p \equiv \RowLiteral{ys}\, q$ iff $xs \equiv ys$.


\subsection{Type Equivalence and Reduction}
\label{sec:type-equivalence}

\InlineOff{}
\input{figures/equivalence}
\InlineOn{}

We define reduction on types by directing the type equivalence judgment $\TEqvJ \Delta \tau {\upsilon} \kappa$ (\cref{fig:equivalence}) from left to right. The full equivalence relation is the congruence closure of \cref{fig:equivalence} plus rules for reflexivity, symmetry, and transitivity. 

The rules \erule{$\beta$} and \erule{$\eta$} are expected. The rules \erule{map} and \erule{map$_\Labels$} map the type operator $\phi$ over the contents of the row literal $\Row{\LabTy {\ell_i} {\tau_i}}$ and row singleton $\Row{\LabTy \xi \tau}$, respectively.

The rules \erule{map$_\mathsf{id}$} and \erule{map$_{\circ}$} describe functor mapping laws. Normally, the rules \erule{$\eta$} and \erule{map$_{\circ}$} would be presented in the opposite direction (i.e., that $\Mapp {(\lambda \alpha. \alpha)} \rho = \rho$). However, this direction enforces that arrow-kinded variables are canonically $\lambda$-bound and row-kinded variables are canonically maps. Incorporating these rules into the equational theory is not mandatory. For example, \citet{ChapmanKNW19} do not reason modulo $\eta$-equivalence. However it simplifies metatheory, as our mechanization logic may rule out row-kinded and arrow-kinded neutrals, making the definition of semantic types and later logical relations (e.g., in \cref{sec:consistency}) much simpler.

The interesting rules describe row complement computation and the interplay of $\Pi$ and $\Sigma$ with edge cases. The rule \erule{$\Compl$} reduces row complements algorithmically by subtracting the elements of the second operand from the first. The syntax $\{ \LabTy {\ell} {\tau}, \rho\}$ is metanotation, treating rows as lists. The rule \erule{map$_\setminus$} specifies that mapping distributes over complements. The rule \erule{assoc$_\Xi$} reassociates applications of $\Pi$ and $\Sigma$ of the form $(\Pi\, \rho)\, \tau$ to $\Pi\, (\rho \, \Flap \, \tau)$, ensuring that $\Pi$ is the outermost syntax and that reduction may continue by supplying each operator in $\rho$ with the argument $\tau$. The rule \erule{$\Xi$} reveals that the application of $\Pi$ and $\Sigma$ to nested rows is instead mapping. To illustrate, consider the following type with kind $\TypeK \to \TypeK$.

\begin{rosi} 
Π (Σ {'a ▹ {'b ▹ λ x. x}})
\end{rosi}

\Ni The row \R{{'a ▹ {'b ▹ λ x. x}}} has kind $\RowK{\RowK {\TypeK \to \TypeK}}$, and so the application of $\Sigma$ to this row can be "pushed in" to the inner row \R{{'b ▹ λ x. x}}, as so: 

\begin{rosi} 
Π {'a ▹ Σ {'b ▹ λ x. x}}
\end{rosi}

\Ni This process is repeated as many times as necessary. Of note too is that, as this type has arrow kind, normalization must produce a canonical $\lambda$-bound form. We might expect to need the following rule to commute $\Xi \in \{\Pi, \Sigma\}$ over $\lambda$-bindings in rows: 


\begin{small}
\begin{align*}
\ib{\irule[\erule{$\eta\Xi$}]
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
\end{align*}
\end{small}

\Ni but the rules \erule{$\beta$}, \erule{$\eta$}, \erule{map$_\Labels$}, and \errule{assoc$_\Xi$} are in fact sufficient to derive it. 

\paragraph{Mechanized representations}
Equivalence on predicates and types is represented mechanically by the typed relations $\Infix{\TEqv}$ and $\Infix{\PEqv}$.

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

The directed type equivalence relation yields normal forms. The syntax of normal types is given in \cref{fig:type-normalization}. We have highlighted some aspects of the syntax for discussion.

\input{figures/normal-form-judgments}

Normalization reduces applications and maps except when a variable blocks computation, which we represent as a \emph{neutral type}. A neutral type is either a variable or a spine of applications with a variable in head position. We distinguish ground kinds $\gamma$ from functional and row kinds, as neutral types may only be promoted to normal type at ground kind (rule \kruleNF{ne}). Neutral types $n$ at functional kind must be $\eta$-expanded to have an outer-most $\lambda$-binding (e.g., to $\lambda x. \, n\, x$), and neutral types at row kind are expanded to an inert map by the identity function (e.g., to $\Mapp {(\lambda x. x)} {n}$). Likewise, repeated maps are composed: For example, $\Mapp {\phi_{1}} {(\Mapp {\phi_{2}} {n})}$ normalizes by letting $\phi_{1}$ and $\phi_{2}$ compose into $\Mapp {(\phi_{1} \circ \phi_{2})} n$. By design, the former is simply inexpressible in the normal type syntax.

We distinguish singleton rows $\{\LabTy n \Normal \tau\}$ with neutral labels from row literals $\RowIx i 0 m {\LabTy {\ell_i} {\Normal {\tau_i}}}$ with literal labels $\ell_i$. A row is otherwise an inert map $\Mapp \phi n$ or the complement of two rows $\Normal{\tau_2} \Compl \Normal{\tau_1}$. We require in the kinding of normal row complements \kruleNF{$\Compl$} that one (or both) rows are not literal, otherwise the complement would compute. By consequence of $\eta$-expansion, records and variants need only be formed at kind $\TypeK$. The remaining normal type syntax and normal kinding rules do not differ from their counterparts in \cref{fig:syntax-types} and \cref{fig:kinding}.

\paragraph{Mechanized representations} Normal and neutral types are represented intrinsically as the following types.

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

Just as with the !Type! syntax, some constructors require predicate constraints. Promotion of a neutral type $n$ to a normal type via the constructor !ne! is guarded by the predicate !Ground! !kappa!, which computes to $\top$ when $\kappa \in \{ \TypeK , \LabK \}$ and $\bot$ otherwise. Likewise, the construction of the row complement $\rho_{2} \Compl \rho_{1}$ is guarded by a predicate !True! !(! !notRowLiterals?! $\rho_{2}$ $\rho_{1}$ !)! asserting that at most one of the applicands is a row literal. This predicate is designed to avoid the explicit negation $\neg$ (!RowLiteral! $\rho_{2}$ $\wedge$ !RowLiteral! $\rho_{1}$), which does not compute on closed terms to the empty or unit type.

\AH{Clean up squashed evidence logic into a map; add a sentence on typeclasses e.g. "We use a typeclass so that the symbol uparrow embeds types, normaltypes, predicates, and rows alike."}
\Cref{fig:embedding} defines an embedding of the !Normal!\-!Type! syntax back to !Type! syntax, which can be used as a reference for the mechanized constructor names for !Type!s, !NeutralType!s, and !NormalType!s. The definitions !UpPred! and !UpRow! map embedding over the types contained in predicates and row literals. We have an obligation to prove, via !OrderedUp!, that embedding preserves ordering. Some bookkeeping is necessary to convert from squashed evidence to evidence, and vice versa: The function !toWitness! converts !q! !:! !True! !(ordered?! !xs)! into evidence of type !Ordered! !xs!, with !fromWitness! its inverse.


\begin{figure}
\begin{AgdaAlign}
\begin{code}[hide]
module Embedding where
  open import Rome.Types.Syntax 
  open import Rome.NormalTypes.Syntax hiding (⇑ ; ⇑ₙₑ)
  open import Rome.Kinds.GVars
\end{code}
\begin{code}
  ⇑   : NormalType Δ κ  → Type Δ κ
  ⇑ₙₑ : NeutralType Δ κ → Type Δ κ
  ⇑ (ne x)      = ⇑ₙₑ x
  ⇑ (`λ τ)      = `λ (⇑ τ)
  ⇑ (τ₁ `→ τ₂) = ⇑ τ₁ `→ ⇑ τ₂
  ⇑ (`∀ τ)      = `∀ (⇑ τ)
  ⇑ (μ τ)    = μ (⇑ τ)
  ⇑  (lab l)    = lab l
  ⇑  (Π x)      = Π · ⇑ x
  ⇑  (Σ x)      = Σ · ⇑ x
  ⇑  (π ⇒ τ)   = ⇑ₚ π ⇒ ⇑ τ
  ⇑  (⦅ xs ⦆ q)  = ⦅ ⇑ᵣ xs ⦆ 
    (fromWitness (⇑ₒ xs (toWitness q)))
  ⇑  (ρ₂ ∖ ρ₁)  = ⇑ ρ₂ ∖ ⇑ ρ₁
  ⇑  (l ▹ₙ τ)   = ⇑ₙₑ l ▹ ⇑ τ
  ⇑  (F $ ν)  = ⇑ F $ ⇑ₙₑ ν
  ⇑ₙₑ (` x)     = ` x
  ⇑ₙₑ (τ₁ · τ₂) = ⇑ₙₑ τ₁ · ⇑ τ₂
\end{code}
\end{AgdaAlign}
\caption{Embedding}
\label{fig:embedding}
\end{figure}

% -----------------------------------------------------------------------------
% Design choices, renaming, substitution

\section{Design Choices in Formalized Metatheory}

Our development occupies a sweet-spot in intrinsically well-typed syntax. Because variables are well-scoped and types are well-kinded, relations and functions defined on types preserve kind and context definitionally. This reduces the overhead of tedious well-formedness predicates and preservation lemmas. 

Reaping the benefits of intrinsic syntax while dodging the downfalls is largely thanks to the \Rome calculus's stratification of types from kinds. Intrinsic syntax is notoriously prone to "transport hell" \citep{SaffrichTM24, ChenNFT26}, in which effectively equivalent terms are indexed by unfortunately unequal indices. Notably absent from our mechanized representations are inductively-defined renamings and substitutions, which in turn prevents constructors for \emph{explicit substitution} in the syntax of types. Because \Rome enjoys a stratification of types from kinds, no substitution calculus is necessary, as substitution and renaming may be defined functionally without unpleasant circularity. Instead, following \citet{ChapmanKNW19}, we use a higher-order representation of renamings and substitutions. Hence we inherit the benefits of functions (e.g., associativity of composition) without encumbering definitions with the painful transports on indices that comes from explicit substitutions.

\subsection{Renamings}

A !Renaming! is a function mapping type variables in environment !Delta_1! to environment !Delta_2!. The function !ren!$_{k}$ renames an input !Type! !tau! according to an input !Renaming!.

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
  renₜ : Renaming Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
\end{code}
\begin{code}[hide]
  import Rome.Types.Renaming as Renaming
  renₜ = Renaming.renₜ
\end{code}
\end{AgdaAlign}

Renaming is defined for row literals, predicates, normal types, and neutral types; we use a typeclass to permit the name !ren! to operate over each.

\subsection{Substitutions} 

A !Substitution! renames in parallel and maps type variables in environment !Delta_1! to types in !Delta_2!. The function !sub!$_{k}$ substitutes all type variables in input !Type! !tau! according to an input !Substitution!. Like with renaming, we introduce a typeclass so that the name !sub! operates over types, rows, predicates, neutral and normal types.

\AH{Also comment on infix syntax for substitution... Or, actually, don't even talk about the sub$_t$ syntax, just discuss the infix notation.}

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
  subₜ : Substitution Δ₁ Δ₂ → Type Δ₁ κ → Type Δ₂ κ
\end{code}
\begin{code}[hide]
  import Rome.Types.Substitution as Substitution 
  subₜ = Substitution.subₜ
\end{code}
\end{AgdaAlign}

\Ni While each !Substitution! is a total function, not all variables are changed. In particular, the !Type! constructor !`! constructs a !Type! from a !TVar!, fixing each type variable. This constructor forms the \emph{identity substitution} over types.

\begin{code}[hide]
module SubId where
  open import Rome.Kinds ; open import Rome.Types ; open import Rome.NormalTypes
\end{code} 
\begin{code}
  sub-id : ∀ (τ : Type Δ κ) → sub ` τ ≡ τ
\end{code}
\begin{code}[hide]
  import Rome.Types.Properties.Substitution as Substitution
  sub-id = Substitution.sub-id
\end{code}

% -----------------------------------------------------------------------------
% Normalization by Evaluation

\section{Normalization by Evaluation}
\label{sec:NbE}

Normalization by evaluation consists of three key domains and three functions over these domains. We declare !Type!, the syntax of types; !NormalType! and !NeutralType!, the syntax of normal and neutral types; and !SemType!, an embedded domain of semantic types. From there we produce a \emph{reflection} from neutral types to semantic types, a \emph{reification} from semantic types to normal types, and an \emph{evaluation} from types to semantic types. It follows that normalization of a type $\tau$ is the composition of reification after evaluation of $\tau$.

\subsection{Residualizing Semantics}

We define our semantic domain in Agda recursively over the syntax of kinds. Our semantics is \emph{residualizing}~\citep{Lindley05} because we distinguish \emph{values} in the semantic domain (functions and rows) from \emph{residual values} (unbound variables, applications with a variable in head position, and normal forms) at ground kind. Hence semantic types are residual values at type and label kind.

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


\paragraph{Functions} We interpret arrow-kinded types as \emph{Kripke function spaces} \citep{JungT93, Abel13}, which permit the application of interpreted function $\KindJ {\Delta_1} \phi {\kappa_1 \to \kappa_2}$ at any environment !Delta_2! provided a renaming from !Delta_1! into !Delta_2!. The Kripke flavor here is that environments may be viewed as \emph{worlds}, and so each Kripke function returns a type in any \emph{reachable} environment.

\begin{code}[hide]
  module _ where private
    SemType : KEnv → Kind → Set
\end{code}
\begin{code}
    KripkeFunction : KEnv → Kind → Kind → Set
    KripkeFunction Δ₁ κ₁ κ₂ =  
      ∀ {Δ₂} → Renaming Δ₁ Δ₂ → 
                SemType Δ₂ κ₁ → SemType Δ₂ κ₂
    SemType Δ₁ (κ₁ `→ κ₂) = KripkeFunction Δ₁ κ₁ κ₂
\end{code}
\begin{code}[hide]
    SemType _ _ = ⊥
\end{code}

Because we choose to reason modulo $\eta$-equivalence, arrow-kinded types are canonically $\lambda$-bound, and hence our definition of !SemType! needn't account for the evaluation of arrow-kinded variables. Contrast our definition with that of \citet{ChapmanKNW19}, for which the evaluation of e.g. variable $v : \TypeK \to \TypeK$ is !left (` v)!: 

\begin{code}
    SemType Δ₁ (κ₁ `→ κ₂) = 
        NeutralType Δ₁ (κ₁ `→ κ₂) 
     or KripkeFunction Δ₁ κ₁ κ₂
\end{code} 


\paragraph{Row literals} We define the interpretation of row literals ${\RowIx i 0 n {\LabTy {\ell_i} {\tau_i}}}$ as the type !Row! !(SemType! !Delta! !kappa)!, which is defined generically over arbitrary type !A : Set! below. The !Row! type is a finitely indexed map. We choose this representation because operations like row mapping can be expressed as function composition. We will commonly refer to the empty row and cons case on !Row!s as $\epsilon$ and !_::_!, respectively.

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
  open import Rome.NormalTypes.NBE hiding (SemType ; SemRow)
\end{code}
\begin{code}[hide]
\end{code}

Not all row-kinded semantic types are row literals. We must account for \emph{inert} row kinded types for which neutral types halt reduction to row literals. For example, the singleton $\Row {\LabTy n \tau}$ is not a row literal because its label is neutral. In summary, a semantic row is either: a row literal, a neutral-labeled row singleton, an inert map, or an inert row complement.  In order to enforce rule \erule{map$_\circ$}---that the nested map $\Mapp{\phi_{1}}{(\Mapp{\phi_{2}}{\rho})}$ be recomposed to $\Mapp{(\phi_{1} \circ \phi_{2})}{\rho}$---we want to represent the type operator in inert maps functionally. However, a direct attempt in doing so runs afoul of Agda's positivity checker. Consider the following definition of !SemRow! for an inert map constructor:
\begin{code} 
  data SemRow (Δ : KEnv) : Kind → Set where
    _$_ : KripkeFunction Δ κ₁ κ₂ → 
            NeutralType Δ R[ κ₁ ] → SemRow Δ R[ κ₂ ]
\end{code}

The Kripke function argument has both a negative occurence and a non-strictly positive occurence of !SemType!, and so Agda rejects this definition (correctly) as ill-founded. We recover a well-founded definition following a subtle encoding trick found in \citet{AllaisBM13}. For the negative occurrence, it is sufficient to instead quantify over \emph{neutral type} arguments; for the non-strictly positive occurrence, we parameterize !SemRow! by a functor $\mathcal T$ !: KEnv! $\to$ !Set!, which serves as a placeholder for !SemType! $(\text{--})$ !kappa!. 

\begin{figure}
\begin{code}[hide]
module Caveat where
  open import Rome.Kinds
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE.Syntax hiding (SemRow ; SemType)

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
\label{fig:SemRow}
\end{figure}

The constructors in \cref{fig:SemRow} specify inert maps, singleton rows with neutral label, row literals, and inert row complements. As in the syntax, we require predicates that row literals are well-ordered and row complements have at most one row literal. Finally, we adjust the definition of !SemType! !Delta! !R[! !kappa! !]! accordingly so that $\mathcal T =$ !SemType! $(\text{--})$ $\kappa$.
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
  open import Rome.NormalTypes.NBE.Syntax ; open import Rome.NormalTypes.NBE.Renaming
\end{code}
\begin{figure}
\begin{code}
  reflect : NeutralType Δ κ → SemType Δ κ
  reify : SemType Δ κ → NormalType Δ κ
  
  reflect {κ = ★} τ            = ne τ
  reflect {κ = L} τ            = ne τ
  reflect {κ = κ₁ `→ κ₂} φ = λ r v → reflect (ren r φ · reify v)
  reflect {κ = R[ κ ]} ρ       = (λ r ν → reflect ν) $ ρ 
\end{code}
\caption{Reflection}
\label{fig:reflection}
\end{figure}



Reflection asserts that neutral forms have semantic representations. We define reflection (\cref{fig:reflection}) mutually recursively with reification (\cref{fig:reification}). Types at kind $\TypeK$ and $\LabK$ can be promoted straightforwardly with the !ne! constructor. Neutral types at arrow kind must be expanded into Kripke functions: The input !v! has type !SemType Delta_2 kappa_1! and must be reified, while The function !phi! is kinded in environment !Delta_1! and so must be renamed to !Delta_2!, the environment of !v!. Finally, a neutral row (e.g., a row variable) must be expanded into an inert mapping by !(\! !r! !n! $\to$ !reflect! !n)!. This equation implements the expansion of \erule{map$_\mathsf{id}$} for neutral types.

\subsection{Reification}
\label{sec:reification}

\begin{figure}
\begin{code}[hide]
  reifyNRL : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ′ → SemType Δ′ κ) R[ κ ]) → 
                     (nr : notRowLiteral ρ₁ or notRowLiteral ρ₂) → notRowLiteralNF (reify ρ₁) or notRowLiteralNF (reify ρ₂)
  reifyNRL′ : ∀ (ρ₁ ρ₂ : SemRow Δ (λ Δ′ → SemType Δ′ κ) R[ κ ]) → 
                     (nr : notRowLiteral ρ₁ or notRowLiteral ρ₂) → notRowLiteralNF (reify ((ρ₁ ∖ ρ₂) {nr}))
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
  reifyRowOrdered : ∀ {Δ : KEnv} {κ : Kind} (ρ : Row (SemType Δ κ)) → OrderedRow ρ →  Ordered (reifyRow ρ)
\end{code}
\begin{code}
  reify {κ = ★} τ = τ
  reify {κ = L} τ = τ
  reify {κ = κ₁ `→ κ₂} φ = `λ (reify (φ S (reflect {κ = κ₁} ((` Z)))))
  reify {κ = R[ κ ]} (l ▹ τ) = (l ▹ₙ (reify τ))
  reify {κ = R[ κ ]} (φ $ τ) =  (`λ (reify (φ S (` Z))) $ τ)
  reify {κ = R[ κ ]} ((ρ₂ ∖ ρ₁) {q}) = 
    (reify ρ₂ ∖ reify ρ₁) {fromWitness (reifyNRL ρ₂ ρ₁ q)}
  reify {κ = R[ κ ]} (row ρ q) = 
    ⦅ reifyRow ρ ⦆ (fromWitness (reifyRowOrdered ρ q))

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
  reifyRowOrdered (n , P) q = reifyRowOrdered⃗ n P q

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

Reification asserts that semantic values have syntactic representations. The definition of reification is a little more involved (\cref{fig:reification}). The first two equations are expected (!tau! is already in normal form). Functions are reified effectively by $\eta$\--expan\-sion. Here we see why we choose to interpret functions with a Kripke flavor, as the weakening renaming !S! is crucial to permitting !phi! to operate over the just-introduced type variable !` Z!. The remaining equations describe the reification of the four row cases. In the $\Mapp \phi \tau$ case, we must reify the neutral Kripke function $\phi$ analogously to the reification of type operators. We reify row literals effectively by mapping reification over the contents of each semantic row, reconstructing a list as we go along. A straightforward definition of !reifyRow! migh attempt to induct over the !Row! argument's length (its first component), which Agda's termination checker rejects. This is because the recursive call in the successor case will be over $(n , P \circ \text{fsuc})$, where the second component is not structurally smaller. We bypass this restriction by instead recursing over the curried form !reify!!Row!$^{\to}$. In both the row literal and row complement case, some bookkeeping is necessary to ensure that (respectively) reification respects row orderedness and reification does not produce row literals from inert rows.

Finally, The !NormalType! constructor !ne! stipulates that we may only promote neutral derivations to normal derivations at \emph{ground kind} (rule \kruleNF{ne}). Hence the composition of reflection and reification effectively $\eta$-expands neutral types.

\begin{code}[hide]
module ηNorm where 
  open import Rome.Types
  open import Rome.NormalTypes ; open import Rome.Kinds 
  open import Rome.NormalTypes.NBE hiding (η-norm)
\end{code}
\begin{code}
  η-norm : NeutralType Δ κ → NormalType Δ κ 
  η-norm = reify ∘ reflect
\end{code}

\Ni This function forms the \emph{identity substitution} on normal types:

\begin{code}
  subNF-id : ∀ (τ : NormalType Δ κ) → sub (η-norm ∘ `) τ ≡ τ 
\end{code}
\begin{code}[hide]
  import Rome.NormalTypes.Properties.Substitution as Substitution
  subNF-id = Substitution.subₜNF-id
\end{code}

% -----------------------------------------------------------------------------
% Evaluation

\section{Evaluation}
\label{sec:Evaluation}
Our next task is to \emph{evaluate} terms of type !Type Delta kappa! into the semantic domain at type !SemType Delta kappa!. This component of the normalization algorithm implements row computation. We proceed by defining semantic helpers that reduce !SemType! arguments.

\begin{code}[hide]
module Evaluation where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE.Syntax hiding (ε)
  open import Rome.NormalTypes.NBE.Normalization using (reflect ; reify ; lifte ; extende ; _∈Row?_)
  open import Rome.NormalTypes.NBE.Renaming
  open import Rome.Kinds
  open import Data.Bool
  open SemTypes using (ε)
\end{code}

\paragraph{Semantic application}

We define semantic application straightforwardly as Agda application under the identity renaming.

\begin{code}
  _⟨·⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ κ₁ → 
         SemType Δ κ₂
  F ⟨·⟩ V = F id V
\end{code}


\Ni Semantic application implements $\beta$-reduction. 

\paragraph{Semantic mapping}
We define the mapping $\Mapp {\phi} {\rho}$ over the four cases a semantic row may take. The functions !ordered!!Map!$_{2}$ and !not!!Row!!Literal!!.map.! are bookkeeping that assert our orderedness and row literal predicates are preserved by semantic mapping.

\begin{AgdaAlign}
\begin{code}
  _⟨$⟩_ : SemType Δ (κ₁ `→ κ₂) → SemType Δ R[ κ₁ ] → 
           SemType Δ R[ κ₂ ]
\end{code}
\begin{code}[hide]
  notRowLiteral$ : ∀ {Δ : KEnv} {κ₁ : Kind} {κ₂ : Kind} {F : SemType Δ (κ₁ `→ κ₂)} {ρ₂ ρ₁ : SemRow Δ (λ Δ′ → SemType Δ′ κ₁) R[ κ₁ ]} → 
                notRowLiteral ρ₂ or notRowLiteral ρ₁ → notRowLiteral (F ⟨$⟩ ρ₂) or notRowLiteral (F ⟨$⟩ ρ₁)
\end{code}
\begin{code}
  _⟨$⟩_ {κ₁ = κ₁} {κ₂ = κ₂} F (l ▹ τ) = l ▹ (F ⟨·⟩ τ)
  F ⟨$⟩ row (n , P) q = row (n , map₂ (F id) ∘ P) 
    (orderedMap₂ (F id) q)
  F ⟨$⟩ ((ρ₂ ∖ ρ₁) {nr}) = ((F ⟨$⟩ ρ₂) ∖ (F ⟨$⟩ ρ₁)) 
    {notRowLiteral$ nr}
  F ⟨$⟩ (G $ n) = (λ {Δ′} r → F r ∘ G r) $ n
\end{code}
\begin{code}[hide]
  notRowLiteral$ {F = F} {x₁ ▹ x₂} {ρ₁} (left x) = left tt
  notRowLiteral$ {F = F} {ρ₂ ∖ ρ₃} {ρ₁} (left x) = left tt
  notRowLiteral$ {F = F} {φ $ n} {ρ₁} (left x) = left tt
  
  notRowLiteral$ {F = F} {ρ₂} {x ▹ x₁} (right y) = right tt
  notRowLiteral$ {F = F} {ρ₂} {ρ₁ ∖ ρ₃} (right y) = right tt
  notRowLiteral$ {F = F} {ρ₂} {φ $ n} (right y) = right tt
\end{code}
\end{AgdaAlign}

\Ni The case where !rho! is a row literal is interesting in that our choice of representation for row literals as finite maps pays off: we express the mapping of !phi! across the row !(n , P)! by composing !P! with !F!. (The function !map!$_{2}$ maps over a tuple's second component.) This equation, and line 3, implement the equational rule \errule{map}. 

The mapping of !phi! over a complement is distributive, following rule \errule{map$_{\setminus}$}. Likewise, we follow rule \errule{map$_\circ$} in grouping the nested map !phi_1! !.map.! !(phi_2 .map. n)! into a composed map. Here again a functional representation pays off by permitting composition in the semantic domain.

\paragraph{Semantic complement} The complement of two row-kinded semantic types is always inert when one (or both) are not row literals, and thus constructed simply by the !_COMPL_! constructor. The interesting case is when we must reduce two row literals to another row literal.

\begin{AgdaAlign}
\begin{code}
  _In?_ : Label → Row (SemType Δ κ) → Bool
\end{code}
\begin{code}[hide]
  l In? (n , P) = isYes (l ∈Row? P)
  {-# TERMINATING #-}
\end{code}
\begin{code}
  _∖V_ : (ρ₂ ρ₁ : Row (SemType Δ κ)) → Row (SemType Δ κ)
  (zero , P) ∖V ρ = ε 
  (suc n , P) ∖V ρ with P fzero
  ... | (l , τ) = if l In? ρ then 
                  (n , P ∘ fsuc) ∖V ρ else
                  (l , τ) ⨾⨾ ((n , P ∘ fsuc) ∖V ρ)
\end{code}
\begin{code}[hide]
  import Rome.NormalTypes.NBE.Normalization as Normalization
  _⟨∖⟩′_ : SemType Δ R[ κ ] → SemType Δ R[ κ ] → SemType Δ R[ κ ]
  _⟨∖⟩′_ = Normalization._∖V_
\end{code}
\end{AgdaAlign}

The semantic helper above implements the subtract function given in \cref{fig:equivalence}, and is effectively identical logic. In the interest of concision, we present this helper by induction over the !Row! input's first component, which Agda's termination checker rejects. Like with !reifyRow! (\cref{fig:reification}), our artifact instead recurses over a curried form. This nuisance highlights a shortcoming in Agda's strictly syntactic termination checking, and could be avoided with type-based alternatives~\citep{AbelP16, AbreuDHJMS23}.

\paragraph{Semantic flap}
We define a semantic version of the flap operator as follows. This definition is auxiliary but helpful in tidying code.

\begin{code}
  apply : SemType Δ κ₁ → SemType Δ ((κ₁ `→ κ₂) `→ κ₂)
  apply a = λ ρ F → F ⟨·⟩ (renSem ρ a)
  _⟨?⟩_ : SemType Δ R[ κ₁ `→ κ₂ ] → 
           SemType Δ κ₁ → SemType Δ R[ κ₂ ]
  f ⟨?⟩ a = apply a ⟨$⟩ f 
\end{code}

\paragraph{Semantic $\Pi$ and $\Sigma$} 
\label{sec:semantic-Pi}
The defining equations for the reduction of $\Pi$ is given below. The logic for $\Sigma$ is identical and omitted.

\begin{code}
  ⟨Π⟩ : SemType Δ R[ κ ] → SemType Δ κ 
  ⟨Π⟩ {κ = ★} x = Π (reify x)
  ⟨Π⟩ {κ = κ₁ `→ κ₂} F = λ ρ v → ⟨Π⟩ (renSem ρ F ⟨?⟩ v)
  ⟨Π⟩ {κ = R[ κ ]} ρ = const ⟨Π⟩ ⟨$⟩ ρ
\end{code}
\begin{code}[hide]
  ⟨Π⟩ {κ = L} x = lab "impossible"
  ⟨Σ⟩ : SemType Δ R[ κ ] → SemType Δ κ 
  ⟨Σ⟩ {κ = ★} x = Σ (reify x)
  ⟨Σ⟩ {κ = κ₁ `→ κ₂} F = λ ρ v → ⟨Σ⟩ (renSem ρ F ⟨?⟩ v)
  ⟨Σ⟩ {κ = R[ κ ]} ρ = (λ _ v → ⟨Σ⟩ v) ⟨$⟩ ρ  
  ⟨Σ⟩ {κ = L} _ = lab "impossible"
\end{code}
 
Recall that we may only construct record types in normal form at kind $\TypeK$, and so for the case that $\kappa = \TypeK$ we simply reify the input and construct the record via the !NormalType! constructor !Pi!. We exclude the case that $\kappa = \LabK$ because it is impossible (recall that in the !Type! syntax, we restrict the formation of the $\Pi$ constructor to just non-label kinds.) 

Next, when applying !Pi'V! to a function, we expand the semantic $\lambda$-binding outwards. Thereafter, we apply rule \errule{assoc$_\Pi$} to explain how !Pi'V! operates on a single operand. We implement rule \errule{$\Pi$} directly in the last equation: the application of !Pi'V! to a row-kinded input $\rho$ is simply the mapping of !Pi'V!  over $\rho$.

These two rules characterize the computational interaction of $\Pi$ and $\Sigma$ with higher-order and nested rows. We implement row computation via our semantic helpers. The fact that the semantic helpers resemble their syntactic equational rules, modulo some plumbing, is a desirable feature of our implementation.

\paragraph{Evaluation}
A semantic environment maps type variables to semantic types. The identity environment, which fixes the meaning of variables, is given as the composition of reflection and !`!. Evaluation (\cref{fig:evaluation}) maps !Type!s to semantic types, given a suitable semantic environment.


\begin{code}
  SemEnv : KEnv → KEnv → Set
  SemEnv Δ₁ Δ₂ = ∀ {κ} → TVar Δ₁ κ → SemType Δ₂ κ
  idEnv : SemEnv Δ Δ
  idEnv = reflect ∘ `
\end{code}

\begin{figure}
\begin{AgdaAlign}
\begin{code}[hide]
  {-# TERMINATING #-}
\end{code}
\begin{code}
  ⟦_⟧ₜ : Type Δ₁ κ → SemEnv Δ₁ Δ₂ → SemType Δ₂ κ
\end{code}
\begin{code}[hide]
  ⟦_⟧ₚ : Pred (Type Δ₁ R[ κ ]) → SemEnv Δ₁ Δ₂ → Pred (NormalType Δ₂ R[ κ ])
  ⟦_⟧ₚ (ρ₁ · ρ₂ ~ ρ₃) η = reify (⟦ ρ₁ ⟧ₜ η) · reify (⟦ ρ₂ ⟧ₜ η) ~ reify (⟦ ρ₃ ⟧ₜ η)
  ⟦_⟧ₚ (ρ₁ ≲ ρ₂) η = reify (⟦ ρ₁ ⟧ₜ η) ≲ reify (⟦ ρ₂ ⟧ₜ η)
\end{code}
\begin{code}
  ⟦ ` v ⟧ₜ η       = η v
  ⟦ τ₁ · τ₂ ⟧ₜ η   = (⟦ τ₁ ⟧ₜ η) ⟨·⟩ (⟦ τ₂ ⟧ₜ η)
  ⟦ ρ₂ ∖ ρ₁ ⟧ₜ η = ⟦ ρ₂ ⟧ₜ η ⟨∖⟩′ ⟦ ρ₁ ⟧ₜ η
  ⟦ Π ⟧ₜ η         = λ _ v → ⟨Π⟩ v
  ⟦ Σ ⟧ₜ η         = λ _ v → ⟨Σ⟩ v
  ⟦ f $ a ⟧ₜ η     = ⟦ f ⟧ₜ η ⟨$⟩ ⟦ a ⟧ₜ η
  ⟦ ξ ▹ τ ⟧ₜ η with ⟦ ξ ⟧ₜ η 
  ... | ne ν       = (ν ▹ ⟦ τ ⟧ₜ η)
  ... | lab l      = row (1 , λ { fzero → (l , ⟦ τ ⟧ₜ η) }) tt
  ⟦ ⦅ ρ ⦆ ω ⟧ₜ η   = row 
    (⟦ ρ ⟧ᵣ η) 
    (⟦ toWitness ω ⟧ₒ η)
    where
      ⟦_⟧ᵣ : RowLiteral (Type Δ₁ κ) → 
            SemEnv Δ₁ Δ₂ → 
            Row (SemType Δ₂ κ)
      ⟦ [] ⟧ᵣ η          = ε
      ⟦ (l , τ) ∷ ρ ⟧ᵣ η = (l , ⟦ τ ⟧ₜ η) ⨾⨾ ⟦ ρ ⟧ᵣ η
      ⟦_⟧ₒ : {ρ : RowLiteral (Type Δ₁ κ)} → 
             Ordered ρ → 
             (η : SemEnv Δ₁ Δ₂) → 
             OrderedRow (⟦ ρ ⟧ᵣ η)      
\end{code}
\begin{code}[hide]
      import Rome.NormalTypes.NBE.Normalization as Normalization
      ⟦_⟧ₒ {ρ = []} ω η = tt
      ⟦_⟧ₒ {ρ = _ ∷ []} ω η = tt
      ⟦_⟧ₒ {ρ = (l₁ , τ₁) ∷ (l₂ , τ₂) ∷ ρ} (l₁<l₂ , ω) η with 
            ⟦ ρ ⟧ᵣ η  | ⟦ ω ⟧ₒ η 
      ... | zero , P  | ih = l₁<l₂ , tt
      ... | suc n , P | ih₁ , ih₂ =  l₁<l₂ , ih₁ , ih₂

  ⟦ (π ⇒ τ) ⟧ₜ η = ⟦ π ⟧ₚ η ⇒ ⟦ τ ⟧ₜ η
  ⟦ (`∀ τ) ⟧ₜ η = `∀ (⟦ τ ⟧ₜ (lifte η)) 
  ⟦ (μ τ) ⟧ₜ η = μ (reify (⟦ τ ⟧ₜ η))
  ⟦ (lab l) ⟧ₜ η = lab l
  ⟦ (τ₁ `→ τ₂) ⟧ₜ η = (⟦ τ₁ ⟧ₜ η) `→ (⟦ τ₂ ⟧ₜ η)
  ⟦ (`λ τ) ⟧ₜ η = λ ρ v → ⟦ τ ⟧ₜ (extende (renSem ρ ∘ η) v)
\end{code}
\end{AgdaAlign}
\caption{Evaluation}
\label{fig:evaluation}
\end{figure}


We describe only the interesting cases of evaluation. The first equation states that variables evaluate to their meaning in environment !eta!. As desired, the equations for application !_cdot_!, row complement !_COMPL_!, record and variant operators !Pi! and !Sigma!, and mapping !_.map._! defer to the semantic helpers defined in this section. (The operation $\setminus\text{V}'$ is the semantic complement operator for row literals lifted to !SemRow!s.) Evaluation of labeled singletons must check if the label is a neutral variable !n! or label literal !ell!, making sure to only construct row literals with literal labels. The function !evalRow! is effectively inverse to !reifyRow! (\cref{fig:reification}). In each case, we employ our smart constructors for semantic row literals. We have an obligation to prove that evaluation preserves the ordering evidence !q!, which is performed by the auxiliary lemma !evalRowOrdered!.


\paragraph{Normalization} Finally, normalization in the NbE approach is simply the composition of reification after evaluation. 

\begin{code}
  ⇓ : Type Δ κ → NormalType Δ κ 
  ⇓ τ = reify (⟦ τ ⟧ₜ idEnv)
\end{code}

% -----------------------------------------------------------------------------
% Metatheory

\section{Metatheory}
\label{sec:metatheory}

This section describes the metatheory of \Rome. For historical reasons \citep{Friedman75,Statman82,BergerS91}, \emph{soundness} and \emph{consistency} are elsewhere in the NbE literature referred to as \emph{completeness} and \emph{soundness}, respectively. Our nomenclature is instead borrowed from \citet{Lindley05} as a matter of preference.

\subsection{Canonicity of Normal Types}
\begin{AgdaAlign}
\begin{code}[hide]
module Canonicity where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds 
\end{code}
In any context an arrow-kinded type is canonically $\lambda$-bound:
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
  open import Rome.NormalTypes.NBE
\end{code}
\emph{Stability} asserts that $\Norm$ behaves as a normalization function ought to. That is, normal forms are fixed points of normalization.

\begin{code}
  stability : ∀ (τ : NormalType Δ κ) → ⇓ (⇑ τ) ≡ τ 
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.NBE.Stability as Stability
  stability = Stability.stability
\end{code}

\Ni Stability implies idempotency:
\begin{code}
  idempotency : ∀ (τ : Type Δ κ) → 
                ((⇑ ∘ ⇓) ∘ (⇑ ∘ ⇓)) τ ≡ (⇑ ∘ ⇓) τ 
  idempotency τ = cong ⇑ (stability (⇓ τ)) 
\end{code} 

\Ni and surjectivity:

\begin{code}
  surjectivity : ∀ (τ : NormalType Δ κ) → 
                 Σ[ υ ∈ Type Δ κ ] (⇓ υ ≡ τ)
  surjectivity τ = ⇑ τ , stability τ
\end{code}
\end{AgdaAlign}

\subsection{Soundness}
\label{sec:soundness} 
\emph{Soundness} of the equational theory states that if $\TEqvJ \Delta \tau \upsilon \kappa$, then $\tau$ and $\upsilon$ normalize to the same form.
\begin{AgdaAlign}
\begin{code}[hide]
module SoundnessStatement where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds ; open import Rome.NormalTypes.NBE
\end{code} 
\begin{code}
  soundness : ∀ {τ υ : Type Δ κ} → τ ≡ₜ υ → ⇓ τ ≡ ⇓ υ
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.NBE.Soundness as Soundness
  soundness = Soundness.soundness
\end{code}
\end{AgdaAlign}

We prove soundness via a logical relation $(\approx)$ on semantic types that specifies when two semantic objects are partial-equivalent modulo \emph{uniformity} and functional extensionality.

\begin{figure}
\begin{AgdaAlign}
\begin{code}[hide]
module Uniformity where
  open import Rome.Prelude
  open import Rome.Kinds
  open import Rome.Kinds.Properties.Decidability
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE hiding (renKripke)
  open import Rome.Metatheory.NBE.Soundness.Relation hiding 
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
  open import Rome.NormalTypes.NBE
  open import Data.Nat.Properties renaming (_≟_ to _≡ℕ?_)  
  open import Rome.Metatheory.NBE.Soundness.Relation hiding 
    (_≈_ ; _≈₂_ ; _≈ᵣ_)
\end{code}
\begin{code}
  _≈_ : SemType Δ κ → SemType Δ κ → Set
  _≈_ {κ = ★} τ₁ τ₂ = τ₁ ≡ τ₂
  _≈_ {κ = L} τ₁ τ₂ = τ₁ ≡ τ₂
  _≈_ {κ = R[ κ ]} (l₁ ▹ τ₁) (l₂ ▹ τ₂) = (l₁ ≡ l₂) × τ₁ ≈ τ₂
  _≈_ {κ = R[ κ ]} (ρ₁ ∖ ρ₂) (ρ₃ ∖ ρ₄) = ρ₁ ≈ ρ₃ × ρ₂ ≈ ρ₄
\end{code}

\Ni In the arrow case, we assert that the Kripke functions $\phi$ and $\psi$ are \emph{uniform} and \emph{extensionally equivalent} to one another (\cref{fig:uniformity-and-PE}). 

\begin{code}
  _≈_ {Δ₁} {κ = κ₁ `→ κ₂} φ ψ = 
    Uniform φ × Uniform ψ × PointEqual-≈ {Δ₁} φ ψ 
\end{code}

\Ni Uniformity states that passing a renaming $r_2$ to a Kripke function is equivalent to renaming it algorithmically---that is, semantic renaming (!renSem!) commutes with Kripke renaming. The uniformity property is attributable to \citet{AllaisBM13} but simplified by \citet{ChapmanKNW19}. The !PointEqual!!-!!~~! predicate circumvents any need to postulate functional extensionality. Rather, we assert that two Kripke functions $\phi$ and $\psi$ map equivalent inputs to equivalent outputs under all renamings.

Some plumbing is necessary in the case that we are equating two inert maps $\Mapp {\phi} {n}$ and $\Mapp {\psi} {m}$: 

\begin{code}
  _≈_ {κ = R[ κ₂ ]} (_$_ {κ₁} φ n) (_$_ {κ₁′} ψ m) with 
    κ₁ ≡k? κ₁′ 
  ... | yes refl = UniformNE φ × UniformNE ψ × 
                   PointEqualNE-≈ φ ψ × n ≡ m
\end{code}
\begin{code}[hide]
  ... | no _ = ⊥   
\end{code}

\Ni Kind equality is decidable !(.=.k?)!, which lets us relate inert maps only when the domains of $\phi$ and $\psi$ (that is, $\kappa_{1}$ and $\kappa_1'$) are equivalent. The predicates !UniformNE! and !PointEqualNE! are entirely analogous to !Uniform! and !PointEqual! except that they describe Kripke functions in which the domain is a !NeutralType! rather than !SemType!. 

Finally, we relate row literals of equal length by a pointwise relation of their contents.

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
  open import Rome.NormalTypes.NBE
  open import Rome.Types.Equivalence
  import Rome.Metatheory.NBE.Soundness as Soundness
  open Soundness hiding (fund-≈ ; reflect-≈ ; reify-≈ ; idEnv-≈ ; _≈e_ ; soundness)
\end{code}
\begin{code}
  reflect-≈  : {ν₁ ν₂ : NeutralType Δ κ} →
               ν₁ ≡ ν₂ → reflect ν₁ ≈ reflect ν₂
\end{code}
\begin{code}[hide]
  reflect-≈ = Soundness.reflect-≈
\end{code}

\Ni Dually, equivalent semantic objects reify to propositionally equal types. 

\begin{code}
  reify-≈ : {V₁ V₂ : SemType Δ κ} → 
            V₁ ≈ V₂ → reify V₁ ≡ reify V₂ 
\end{code}
\begin{code}[hide]
  reify-≈ = Soundness.reify-≈
\end{code}

\paragraph{Logical environments}
We lift the soundness relation to a pointwise equivalence on semantic environments.

\begin{code}
  _≈e_ : {Δ₁ : KEnv} (η₁ η₂ : SemEnv Δ₁ Δ₂) → Set
  _≈e_ {Δ₁ = Δ₁} η₁ η₂ = 
    ∀ {κ} (x : TVar Δ₁ κ) → (η₁ x) ≈ (η₂ x)
\end{code}

\Ni  The identity semantic environment relates to itself under the reflection of propositional equality, as witnessed by !idEnv-~~!. 

\begin{code}
  idEnv-≈ : ∀ {Δ} → (idEnv {Δ = Δ}) ≈e idEnv
  idEnv-≈ _ = reflect-≈ refl
\end{code}

\paragraph{The fundamental lemma}

The fundamental lemma for the soundness relation states that equivalent types evaluate to related semantic objects. The proof of the fundamental lemma is by induction over the type equivalence witness !tau_1 .=.t tau_2!.
\begin{code}
  fund-≈ : ∀ {η₁ η₂ : SemEnv Δ₁ Δ₂}
           {τ₁ τ₂ : Type Δ₁ κ} → 
           η₁ ≈e η₂ → 
           τ₁ ≡ₜ τ₂ → 
          ⟦ τ₁ ⟧ₜ η₁ ≈ ⟦ τ₂ ⟧ₜ η₂
\end{code}
\begin{code}[hide]
  fund-≈ = Soundness.fund-≈
\end{code}

Soundness follows from the fundamental lemma in the identity semantic environment. Explicitly, the fundamental lemma tells us that $\text{eval}\, \tau_1 \, \text{idEnv} \approx \text{eval}\, \tau_2 \, \text{idEnv}$. After reification, we have that $\text{reify (eval}\, \tau_1 \, \text{idEnv)} \equiv \text{reify (eval}\, \tau_2 \, \text{idEnv)}$, which is precisely the elaboration of $\Norm \, \tau_1 \equiv \, \Norm \, \tau_2$.

\begin{code}
  soundness : ∀ {τ₁ τ₂ : Type Δ κ} → 
                τ₁ ≡ₜ τ₂ → ⇓ τ₁ ≡ ⇓ τ₂
  soundness = reify-≈ ∘ (fund-≈ idEnv-≈)
\end{code}
\end{AgdaAlign}

\subsection{Consistency}
\label{sec:consistency}

\emph{Consistency} states that every type is equivalent to its normalization. Or, equivalently, \emph{consistency} states that $\Infix{\TEqv}$ is \emph{normalizing}.

\begin{AgdaAlign} 
\begin{code}[hide]
module ConsistencyStatement where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.NormalTypes.NBE
\end{code}
\begin{code}
  consistency : ∀ (τ : Type Δ κ) → τ ≡ₜ ⇑ (⇓ τ)
\end{code}
\begin{code}[hide]
  import Rome.Metatheory.NBE.Consistency as Consistency
  consistency = Consistency.consistency
\end{code}
\end{AgdaAlign}


We define a logical relation for consistency $\llbracket \tau \rrbracket{\approx}\, V$ by relating types to semantic objects. The first two cases state the purpose of the relation: $\tau$ relates to $V$ at ground kind when $\tau$ is equivalent to the embedding of $V$. In other words, $\tau$ and $V$ are identified up to type equivalence.

\begin{AgdaAlign}
\begin{code}[hide]
module ConsistencyRelation where
  open import Rome.Prelude
  open import Rome.Kinds
  open import Rome.Kinds.Properties.Decidability
  open import Rome.Types
  open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE
  open import Data.Nat.Properties renaming (_≟_ to _≡ℕ?_)  
  open import Rome.Metatheory.NBE.Consistency.Relation hiding 
    (⟦_⟧≈_ ; ⟦_⟧≈ᵣ_)
\end{code}
\begin{code}
  ⟦_⟧≈_ : Type Δ κ → SemType Δ κ → Set
  ⟦_⟧≈_ {κ = ★} τ V = τ ≡ₜ ⇑ V
  ⟦_⟧≈_ {κ = L} τ V = τ ≡ₜ ⇑ V
\end{code}

\Ni Two kripke functions are related when they map related inputs to related outputs under all renamings. That our system reduces modulo $\eta$-equivalence simplifies this definition, which needn't account for when $\phi$ is neutral.

\begin{code}
  ⟦_⟧≈_ {Δ₁} {κ = κ₁ `→ κ₂} f φ = 
      ∀ {Δ₂} (r : Renaming Δ₁ Δ₂) 
      {τ : Type Δ₂ κ₁}
      {V : SemType Δ₂ κ₁} → 
      ⟦ τ ⟧≈ V → 
      ⟦ ren r f · τ ⟧≈ (renKripke r φ ⟨·⟩ V)
\end{code}

That a type $\tau$ is equivalent to an inert map requires the identification of some equivalent type $\Mapp f {\EmbedNE\, n}$ such that $f$ is related to $\phi$. Of course, $\phi$ is not a !SemType! (its domain is a neutral type), and so the definition !SoundKripkeNE! mirrors the logic above for relating functional types modulo a neutral domain argument.

\begin{code}
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (φ $ n) = 
    Σ[ f ∈ (Type Δ (_ `→ κ)) ] 
      ((τ ≡ₜ f $ ⇑ₙₑ n) × SoundKripkeNE f φ)
\end{code}

\Ni The cases for row singletons and row complements follow the same pattern: we identify a type equivalent to the desired semantic form, then assert that form coheres with the relation.

\begin{code}
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ (l ▹ V) = 
    (τ ≡ₜ (⇑ₙₑ l ▹ ⇑ (reify V))) 
    × ⟦ ⇑ (reify V) ⟧≈ V
  ⟦_⟧≈_ {Δ} {κ = R[ κ ]} τ ((ρ₂ ∖ ρ₁) {nr}) = 
    (τ ≡ₜ (⇑ (reify ((ρ₂ ∖ ρ₁) {nr})))) 
    × ⟦ ⇑ (reify ρ₂) ⟧≈ ρ₂ 
    × ⟦ ⇑ (reify ρ₁) ⟧≈ ρ₁
\end{code}

For semantic rows, we likewise identify a row literal equivalent to $\tau$ (with suitable orderedness evidence) and assert, via ![[_]]r~~!, that the contents of the row literal (a list of label-type pairs) is related to the contents of the semantic row (a finite map to semantic types). The helper ![[_]]~~!$_2$ asserts that the first components of each pair are equal and the second components are related under ![[_]]~~!.

\begin{code}
  ⟦_⟧≈_ {κ = R[ κ ]} τ (row ρ q) =
    let xs = ⇑ᵣ (reifyRow ρ) in 
    (τ ≡ₜ ⦅ xs ⦆ 
      (fromWitness 
        (⇑ₒ (reifyRow ρ) (reifyRowOrdered ρ q)))) 
    × ⟦ xs ⟧≈ᵣ ρ
    where 
      ⟦_⟧≈ᵣ_ : RowLiteral (Type Δ κ) → 
               Row (SemType Δ κ) → Set
      ⟦ [] ⟧≈ᵣ (zero , P) = ⊤
      ⟦ x ∷ ρ ⟧≈ᵣ (suc n , P) = 
        (⟦ x ⟧≈₂ P fzero) × ⟦ ρ ⟧≈ᵣ (n , P ∘ fsuc)
\end{code}
\begin{code}[hide]
      ⟦ [] ⟧≈ᵣ (suc n , P) = ⊥
      ⟦ x ∷ ρ ⟧≈ᵣ (zero , P) = ⊥
\end{code}
\end{AgdaAlign}

\paragraph{The fundamental lemma}

\begin{AgdaAlign}
\begin{code}[hide] 
module FundConsistencyStatement where
  open import Rome.Types ; open import Rome.Kinds 
  open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE
  open import Rome.Types.Equivalence
  open import Rome.Types.Properties
  import Rome.Metatheory.NBE.Consistency as Consistency
  open Consistency hiding (⊢⟦_⟧≈ ; fund-⟦⟧≈ ; consistency)
\end{code}

The fundamental lemma proves that the substitution of type $\tau$ by $\sigma$ is related to its evaluation in semantic environment $\eta$:

\begin{code}
  fund-⟦⟧≈ : ∀ (τ : Type Δ₁ κ)
            {σ : Substitution Δ₁ Δ₂}
            {η : SemEnv Δ₁ Δ₂} → 
            ⟦ σ ⟧≈e η  → 
            ⟦ sub σ τ ⟧≈ (⟦ τ ⟧ₜ η)
\end{code}
\begin{code}[hide]
  fund-⟦⟧≈ = Consistency.fund-⟦⟧≈
\end{code}

\Ni provided a pointwise relation of $\sigma$ and $\eta$:

\begin{code}[hide] 
module FundConsistency where
  open import Rome.Types ; open import Rome.Kinds 
  open import Rome.NormalTypes
  open import Rome.NormalTypes.NBE
  open import Rome.Types.Equivalence
  open import Rome.Types.Properties
  import Rome.Metatheory.NBE.Consistency as Consistency
  open Consistency hiding (⊢⟦_⟧≈ ; ⟦_⟧≈e_ ; consistency)
\end{code}
\begin{code}
  ⟦_⟧≈e_ : Substitution Δ₁ Δ₂ → SemEnv Δ₁ Δ₂ → Set  
  ⟦_⟧≈e_ {Δ₁ = Δ₁} σ η = 
    ∀ {κ} (α : TVar Δ₁ κ) → ⟦ σ α ⟧≈ (η α)
\end{code}

A natural corollary of the fundamental lemma is that each type $\tau$, propositionally equal to itself under the identity substitution, is related to its evaluation in the identity environment.

\begin{code}
  ⊢⟦_⟧≈ : ∀ (τ : Type Δ κ) → ⟦ τ ⟧≈ ⟦ τ ⟧ₜ idEnv
\end{code}
\begin{code}[hide]
  ⊢⟦ τ ⟧≈ = tr (⟦_⟧≈ ⟦ τ ⟧ₜ idEnv) 
    (sub-id τ) (fund-⟦⟧≈ τ idEnv-⟦⟧≈)
\end{code}

\Ni Consistency follows from reification, which asserts that $\tau$ is equivalent to $\Embed (\text{reify} V)$ if $\tau$ is related to ⟨$⟩$.

\begin{code}
  consistency : (τ : Type Δ₁ κ) → τ ≡ₜ ⇑ (⇓ τ) 
  consistency = reify-⟦⟧≈ ∘ ⊢⟦_⟧≈
\end{code}
\end{AgdaAlign}

\paragraph{Completeness}

\AH{Comment on equational reasoning, transitivity, and symmetry.}
Consistency implies \emph{completeness}, which is dual to soundness. The helper !inst! reflects propositional equality to type equivalence, while !eq-trans! and !eq-sym! construct transitivity and symmetry of the type equivalence relation.

\begin{AgdaAlign}
\begin{code}[hide] 
module Completeness where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.NormalTypes.NBE
  open import Rome.Metatheory.NBE.Consistency
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

It is easy enough to implement a syntactic decidability check ($\equiv?$) on the shapes of normal forms. Paired with soundness and completeness, we get an effective decision procedure to decide the relation $\TEqvJ \Delta \tau \upsilon \kappa$ as follows:

\begin{AgdaAlign}
\begin{code}[hide]
module DecTyEquiv where
  open import Rome.Types ; open import Rome.NormalTypes
  open import Rome.Kinds
  open import Rome.Metatheory.NBE.Completeness
  open import Rome.Metatheory.NBE.Soundness
  open import Rome.NormalTypes.NBE 
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

% -----------------------------------------------------------------------------
% Formalization choices & related work

\section{Formalization Choices \& Related Work}
\label{sec:related-work}

We conclude with a discussion of related row calculi and formalization efforts.

\subsection{Higher-Order Row Calculi}

Existing formalizations of row calculi with type-level computation differ in both the expressiveness of their row language and the way they account for type equivalence. We distinguish denotational approaches from elaboration-based approaches, which translate source types into a target calculus with an established metatheory.

\paragraph{Denotational approaches}

\Citet{HubersM23} give a denotational semantics for System \RO's kinds, types, and terms. Their soundness theorem shows that equivalent types have the same denotation, and that well-typed terms inhabit the denotations of their types. This establishes semantic soundness of the equational theory, but does not characterize normal forms or give a complete decision procedure for type equivalence.

\paragraph{Elaboration-based approaches}

\Citet{Chlipala10} describes \emph{featherweight Ur}, a language with type-level records and an elaboration into Coq. The development does not provide a normalization procedure for Ur's own definitional equality. Instead, the author conjectures that a terminating and confluent procedure could be given. More recently, \Citet{TooheyCJX26} give an elaboration semantics for $\LamRho{}$ into $\FOPlus{}$, an extension of System~$\FO$ with products and sums, and formalize normalization of the target calculus in Lean~4~\citep{Lean4}. In contrast, our normalizer operates directly on higher-order rows and must account explicitly for row computation. Moreover, their proof relies on a logical relation for normalization that lives in !Prop!, and hence provides no constructive algorithm mapping type syntax to normal forms.

\subsection{NbE and Intrinsic Mechanization}

\paragraph{Nondependent type theories}
Our NbE construction follows the intrinsic syntax and logical-relation techniques of \Citet{ChapmanKNW19}, who in turn build on \Citet{AllaisBM13}. As in those works, the choice of normal and neutral forms determines whether reflection, reification, and renaming are stable under intrinsic indexing. For $\Rome$, this choice must additionally account for neutral labels, inert maps, ordered row literals, and residual complements.

\paragraph{Dependent type theories}
Normalization by evaluation has also been mechanized in Agda for substantially richer type theories, particularly dependent type theory \citep{Abel13,AbelC14,AbelAHPMSS19}. These developments address challenges that are largely orthogonal to ours, such as explicit substitutions and the transport of context and type indices through dependent syntax. We focus instead on the interaction between higher-order row computation and the semantic invariants required by reification. Pinning down a precise treatment of explicit substitutions is still ongoing research. \Citet{AltenkirchK16B} use quotient inductive-inductive types (via postulating constructors and eliminators), while \Citet{ChenNFT26} investigate this approach in Cubical Agda, where higher inductive types are supported by the ambient theory. In $\Rome$, the term--type--kind stratification allows us to retain ordinary inductive syntax and propositional equality throughout the development. This keeps normalization executable and avoids features forbade by the trusted !--safe! flag.

% \clearpage
% \appendix


\bibliographystyle{ACM-Reference-Format}
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
%  LocalWords:  Garrigue KEnv PEnv
 
