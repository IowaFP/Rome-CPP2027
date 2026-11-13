\section{The \Rome{} type system}
\label{sec:Rome-calculus}

This section declaratively defines the \Rome type system. 

\subsection{Syntax}
\input{figures/syntax-types}
The syntax of \Rome kinds, predicates, and types are given in \cref{fig:syntax-types}. We have highlighted the syntax
that extends system \Fome. 

% Two subtleties warrant explanation. 

% \begin{itemize}
% \item We distinguish row literals from \emph{row singletons} $\Row {\LabTy {\xi} {\tau}}$, which are of length one but permitted to have unreduced and/or variable label $\xi$. It is imperative that we distinguish row literals from row singletons, as permitting label variables in row literals permits an opportunity for row labels to overlap upon instantiation.
% \item We exclude the application of $\Pi$ and $\Sigma$ to any kind $\kappa$ that would yield a label-valued row, e.g. $\RowK \LabK$. This ensures that labels are canonically literal when in normal form. (Consider the nonsensical but otherwise permitted label $\Pi {\Row {\LabTy {\ell} {\ell}}}$, which would have kind $\LabK$.)
% \end{itemize}



\subsection{Kinding}
\input{figures/kinding}
\Cref{fig:kinding} describes the kind system of \Rome. RowLiteral (Type literals are) 


\subsection{Type Equivalence and Reduction}
\InlineOff{}
\input{figures/equivalence}
\InlineOn{}

We define reduction on types $\tau \RedT \tau'$ by directing the type equivalence judgment $\TEqvJ \Delta \tau {\tau'} \kappa$ (\cref{fig:equivalence}) from left to right. The full equivalence relation is the congruence closure of \cref{fig:equivalence} plus rules for reflexivity, symmetry, and transitivity.

\subsection{Normal forms}
\label{sec:normal-forms}
\input{figures/normal-form-judgments}

The syntax and kinding of normal and neutral types is given in \cref{fig:type-normalization}. % We have highlighted some subtle aspects of the syntax and kinding for discussion:

% \begin{itemize}
% \item we distinguish ground kinds $\gamma$ from functional and row kinds, as neutral types may only be promoted to normal type at ground kind (rule \kruleNF{ne});
% \item neutral types at row kind are expanded to an inert map by the identity function (e.g., to $\Mapp {(\lambda x. x)} {n}$);
% \item the syntax $\{\LabTy n \Normal \tau\}$ separates singleton rows (with neutral label $n$) from row literals $\Normal \rho$ (with literal labels $\ell_i$); rule \kruleNF{$\triangleright$} ensures that $n$ is a well-kinded neutral label;
% \item we restrict the formation of $\Pi$ and $\Sigma$ types to just kind $\TypeK$, as this enforces arrow-kinded types are canonically $\lambda$-bound; and
% \item  the complement of two row literals should compute to another row literal; we thus require in the kinding of normal row complements \kruleNF{$\Compl$} that one (or both) rows are not literal.
% \end{itemize}
