%include is-jfp.lagda

%if jfpstyle
\documentclass{jfp}
%else
\documentclass[submission,copyright,creativecommons]{eptcs}
\providecommand{\event}{LFMTP 2025}
%endif

% \documentclass[a4paper,UKenglish,cleveref, autoref, thm-restate]{lipics-v2021}
% \documentclass[sigplan,10pt,natbib]{acmart}
%\documentclass[sigplan,10pt,natbib,anonymous,review]{acmart}

%if not jfpstyle
\usepackage{underscore}
\usepackage[T1]{fontenc}
%endif

\usepackage{graphicx}
\usepackage{caption}
\usepackage{amsmath}

% \setlength{\abovedisplayskip}{2pt}
% \setlength{\belowdisplayskip}{2pt}
% \setlength{\abovedisplayshortskip}{2pt}
% \setlength{\belowdisplayshortskip}{2pt}
\usepackage{etoolbox}
% \makeatletter
% \patchcmd{\hscode}{\par}{\vspace{-15pt}\par}{}{}
% \makeatother


% \settopmatter{printfolios=true,printccs=false,printacmref=false}
% \citestyle{acmauthoryear}
%\usepackage{tipa}
%\usepackage{fontspec}
\usepackage{graphicx}
\usepackage{ragged2e}
\usepackage{tikz-cd}
\let\Bbbk\relax % to avoid conflict
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt

% \renewcommand{\hscodestyle}{\setlength{\baselineskip}{0.3\baselineskip}}

% From https://tex.stackexchange.com/questions/325297/how-to-scale-a-tikzcd-diagram
\tikzcdset{scale cd/.style={every label/.append style={scale=#1},
    cells={nodes={scale=#1}}}}

\tikzcdset{scaleedge cd/.style={every label/.append style={scale=#1}}}
\tikzcdset{scalecell cd/.style={cells={nodes={scale=#1}}}}

% From https://tex.stackexchange.com/questions/235118/making-a-thicker-cdot-for-dot-product-that-is-thinner-than-bullet
\makeatletter
\newcommand*\bigcdot{\mathpalette\bigcdot@@{3.0}}
\newcommand*\bigcdot@@[2]{\mathbin{\vcenter{\hbox{\scalebox{#2}{$\m@@th#1\cdot$}}}}}
\makeatother

%if jfpstyle
\bibliographystyle{./jfplike}
%else
\bibliographystyle{./eptcs}
%endif

\begin{document}

%if jfpstyle
\journaltitle{JFP}
\cpr{Cambridge University Press}
\doival{10.1017/xxxxx}

\lefttitle{T. Altenkirch, N. Burke and P. Wadler}
\righttitle{Substitution Without Copy and Paste}

\totalpg{\pageref{lastpage01}}
\jnlDoiYr{2025}
%else
\def\titlerunning{Substitution Without Copy and Paste}
\def\authorrunning{T. Altenkirch, N. Burke \& P. Wadler}
%endif

\title{Substitution Without Copy and Paste}

%if jfpstyle
\begin{authgrp}
\author{Thorsten Altenkirch}
\affiliation{University of Nottingham, Nottingham, UK\\
        (\email{thorsten.altenkirch@@nottingham.ac.uk})}
\author{Nathaniel Burke}
\affiliation{Imperial College London, London, UK\\
% I am going to lose access to my Imperial email address when I graduate so
% I think giving a gmail probably makes more sense...
        (\email{nathanielrburke3@@gmail.com})}
\author{Philip Wadler}
\affiliation{University of Edinburgh and Input Output, Edinburgh, UK\\
        (\email{wadler@@inf.ed.ac.uk})}
\end{authgrp}
%else
\author{Thorsten Altenkirch
\institute{University of Nottingham\\Nottingham, UK}
\email{thorsten.altenkirch@@nottingham.ac.uk}
\and
Nathaniel Burke
\institute{Imperial College London\\London, UK}
\email{nathanielrburke3@@gmail.com}
\and 
Philip Wadler
\institute{University of Edinburgh and Input Output\\Edinburgh, UK}
\email{wadler@@inf.ed.ac.uk}
}
%endif

% \author{Thorsten Altenkirch}
% \affiliation{%
%   \institution{University of Nottingham}
%   \city{Nottingham}
%   \country{United Kingdom}
%   }
% \email{thorsten.altenkirch@@nottingham.ac.uk}
% 
% \author{Nathaniel Burke}
% \affiliation{
%   \institution{Imperial College London}
%   \city{London}
%   \country{United Kingdom}
%   }
% \email{nathaniel.burke21@@imperial.ac.uk}
% 
% \author{Philip Wadler}
% \affiliation{
%   \institution{University of Edinburgh}
%   \city{Edinburgh}
%   \country{United Kingdom}
%   }
% \email{wadler@@inf.ed.ac.uk}

%TODO Add ORCIDs?
% \author{Thorsten Altenkirch}{University of Nottingham, Nottingham, United Kingdom}{thorsten.altenkirch@@nottingham.ac.uk}{}{}
% \author{Nathaniel Burke}{Imperial College London, London, United Kingdom}{nathaniel.burke21@@imperial.ac.uk}{}{}
% \author{Philip Wadler}{University of Edinburgh, Edinburgh, United Kingdom}{wadler@@inf.ed.ac.uk}{}{}

% \authorrunning{T. Altenkirch, N. Burke and P. Wadler}
% \Copyright{Thorsten Altenkirch, Nathaniel Burke and Philip Wadler}
 
% TODO Maybe tweak/add more keywords
% \ccsdesc{Theory of computation~Type theory}
% \keywords{Substitution, Metatheory, Agda}

% \begin{document}

%if not jfpstyle
\AtBeginEnvironment{hscode}{\setlength{\parskip}{0pt} \vspace{-1.5ex}}
\AtEndEnvironment{hscode}{\vspace{-1.5ex}}
%endif

%if jfpstyle
\maketitle[T]
%else
\maketitle
%endif

\begin{abstract}
Defining substitution for a language with binders
like the simply typed $\lambda$-calculus requires repetition,
defining substitution and renaming separately. To verify the
categorical properties of this calculus, we must repeat the same
argument many times. We present a lightweight method
that avoids repetition and that 
gives rise to a simply typed category with families (CwF)
isomorphic to the initial simply typed CwF.
Our paper is a literate Agda script.
\end{abstract}

\section{Introduction}
\label{sec:introduction}

\begin{quote}
Some half dozen persons have written technically on combinatory logic,
and most of these, including ourselves, have published something
erroneous. \cite{curry1958combinatory}
\end{quote}

% [PHIL: Begin alternative introduction.]

% It is notoriously difficult to define substitution correctly
% in the presence of binding operators. A pleasing solution is
% suggested by \cite{debruijn1972lambda}, which not only
% introduces his eponymous indices but also the notion of
% simultaneous substitution. However, to make the recursive
% definition well-founded there is a necessary
% trick: one must first define renaming (mapping variables
% to variables), and then use this in turn to define
% substitution (mapping variables to terms). The two
% definitions are quite similar, and hence coding substitution
% in this way violates a fundamental tenet of software
% engineering: \emph{do not write code by copy and paste}.
% Worse, one needs not just two versions of composition
% (one for renaming and one for substitution) but \emph{four}
% (one may have either a renaming or substitution on
% the left, and again on the right); and this leads to
% fundamental properties that require four proofs, closely
% related by cut and paste. There are techniques for factoring
% these definitions and proofs, for instance as suggested by \cite{allais2017type},
% but these are far from elementary.

% [PHIL: End alternative introduction. Having written it, I think
% I like the below better!]

% OLD INTRO
% The first author was writing lecture notes for an introduction to
% category theory for functional programmers. A nice example of a
% category is that of simply typed $\lambda$-terms and
% substitutions; hence it seemed a good idea to give the definition and
% ask the students to prove the category laws. When writing the answer,
% they realised that it is not as easy as they thought, and to make sure that
% there were no mistakes, they started to formalize the problem in Agda.
% The main setback was that the same proofs got repeated many times. 
% If there is one guideline of good software engineering then it is to
% \textbf{not write code by copy and paste} and this applies even more so to 
% formal proofs.
% % Horrible hack: Remind LaTeX that "\\[<LENGTH>]" is a thing, because apparently
% % it can sometimes forget...
% \phantom{a} \\[0.0ex] \indent
% This paper is the result of the effort to refactor the proof. We think
% that the method used is interesting also for other problems. In
% particular the current construction can be seen as a warmup for the
% recursive definition of substitution for dependent type theory which
% may have interesting applications for the coherence problem,
% i.e. interpreting dependent types in higher categories. 

% NEW INTRO
% (shorter)

The first author was writing an introduction to
category theory for functional programmers. One example
was the category of simply-typed $\lambda$-terms and
substitutions, and proving the expected category laws
seemed a suitable exercise.
We attempted to mechanise the
solution in Agda \cite{agda}, and hit a setback: multiple proofs had to be
repeated multiple times. A guideline of
good software engineering is to \textbf{not write code
by copy and paste}, and this applies doubly to
formal proofs.

This paper is the result of our effort to refactor the proof.
The method used also applies to other problems; in
particular, we see the current construction as a warmup for the
definition of substitution for dependent type theory, which
may have interesting applications for interpreting dependent types in
higher categories.

\subsection{In a nutshell}
\label{sec:nutshell}

When working with substitution for a calculus with binders,
you have to differentiate between renamings (|Δ ⊩v Γ|),
where variables are substituted only for variables (|Γ ∋ A|),
and proper substitutions (|Δ ⊩ Γ|),
where variables are replaced with terms (|Γ ⊢ A|).
This results in several similar operations:
\begin{center}
\begin{minipage}{0.5\textwidth}
\begin{spec}
  _v[_]v  : Γ ∋ A  → Δ ⊩v Γ  → Δ ∋ A
  _v[_]   : Γ ∋ A  → Δ ⊩ Γ   → Δ ⊢ A
\end{spec}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{spec}
  _[_]v   : Γ ⊢ A  → Δ ⊩v Γ  → Δ ⊢ A
  _[_]    : Γ ⊢ A  → Δ ⊩ Γ   → Δ ⊢ A
\end{spec}
\end{minipage}
\end{center}
%The operations on terms depend on the operations on variables.
\noindent The duplication gets worse when we prove properties
of substitution such as the functor law,
\begin{spec}
x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]
\end{spec}
All components |x|, |xs|, |ys| can be either variables/renamings
or terms/substitutions, so we must prove eight combinations;
and the repetition extends to the intermediary lemmas. 

Our solution is to introduce a type of sorts with |V : Sort| for
variables/renamings and |T : Sort| for terms/substitutions, leading
to a single substitution operation 
|_[_] : Γ ⊢[ q ] A → Δ ⊩[ r ] Γ → Δ ⊢[ q ⊔ r ] A|
where |q, r : Sort| and |q ⊔ r| is the least upper bound in the
lattice of sorts with |V ⊑ T|.
Now we need only prove one variant of the
functor law, relying on the fact that |_⊔_| is associative.
Our mutually recursive definitions are accepted by Agda,
as we can convince its termination checker that |V| is
structurally smaller than |T| (see Section~\ref{sec:fact-with-sorts}).
% \begin{spec}
% data Sort : Set 
% data IsV : Sort → Set
% data Sort where
%   V : Sort
%   T>V : (s : Sort) → IsV s → Sort
% data IsV where
%   isV : IsV V
% pattern T = T>V V isV
% \end{spec}

We also formulate our specification
with a quotient-inductive-inductive type, or QIIT (a mutual 
inductive type with equations)
using explicit substitutions
(where substitution is itself a term former).
In our specification 
the substitution laws correspond to the equations of a simply-typed
category with families (CwF)---a variant of a CwF
where the types do not depend on a context.
Our definition of leads to a simply typed CwF
isomorphic to the initial one, giving
a normalisation result where $\lambda$-terms without explicit
substitutions are \emph{substitution normal forms}.

\subsection{Related work}
\label{sec:related-work}

De Bruijn introduced his eponymous indices and
simultaneous substitution in \cite{bruijn1972lambda}. 
Here we use typed de Bruijn indices as in \cite{alti:csl99},
where they showed termination of 
substitution using
well-founded recursion. Our approach is
simpler and scales better, avoiding well-founded recursion.
Andreas Abel used a similar technique to ours to implement \cite{alti:csl99},
in an unpublished Agda proof \cite{abel:subst11}.

The duplication between renamings and substitutions is factored into 
\emph{kits} in \cite{mcbride2006type}. The structure of the proofs is explained in
\cite{allais2017type} from a monadic perspective. Indeed this example
is one of the motivations for relative monads
\cite{altenkirch2015monads}. In the monadic approach, we represent substitutions 
as functions;
however, it is not clear how to extend this to dependent types without
``very dependent'' \cite{hickey1996formal, altenkirch2023munchhausen} types.
% TODO PLW: I don't know what "monadic perspective" means here.

% We avoid the monadic perspective which here for two reasons: first we want
% to give a simple self-contained proof avoiding too many advanced
% categorical constructions; second, we are interested in the application to 
% dependent types where it is not clear how the monadic approach can be applied
% without using very dependent types.

There are a number of publications on mechanising substitution.
Stark~\emph{et al}~\cite{stark2019autosubst} develop a Rocq library which automatically derives
substitution lemmas, but the proofs are repeated for renamings and
substitutions. Their equational theory is similar to the simply
typed CwFs in Section \ref{sec:initiality}.
% TODO PLW: why is 'autosubst 2' cited, but not the original autosubst?
Saffrich~\cite{saffrich2024abstractions} uses Agda with an \emph{extrinsic}
formulation (with preterms and typing separate), and applies
\cite{allais2017type} to factor the construction using kits.
In contrast, Saffrich~\cite{saffrich2024intrinsically} uses Agda with
an \emph{intrinsic} formulation (as here, indexing terms by types),
but with renamings and substitutions defined separately, and relevant 
substitution lemmas repeated for all required combinations.


% \subsection{Using Agda}
% \label{sec:using-agda}
% 
% For details of Agda see the online documentation
% \cite{agda}. We use inductive definitions with
% structurally recursive programs/proofs.
% Agda's termination checker \cite{alti:jfp02} investigates all
% possible recursive paths to find a lexical termination ordering.
% We make heavy use of mutual recursion.
% 
% Agda permits turning propositional equations into rewrite rules.
% We exploit this to make the statement of some theorems more readable
% (avoiding manual transports with |subst|), but this is not essential.
% 
% Implicit arguments are indicated by using |{..}| instead of |(..)|,
% and instantiated using the syntax |f {x = ..}|.
%TODO PLW: I think the explanation of implicit's is too compact to be helpful.
% Agda supports |variable| declarations to introduce implicit quantification.
% Instead of |{Γ : Con} → ..| we write |∀ {Γ} → ..|.
%TODO PLW: deleted above line as too mystifying.

% Agda allows mixfix notation using `|_|'s  to indicate where parameters go.
% The standard library's definitions for equational derivations exploit this flexibility.
%TODO PLW: deleted above line as too mystifying.

% This document is a literate Agda file. Different chapters are in different modules to
% avoid name clashes, e.g. preliminary definitions from Section~\ref{sec:naive-approach}
% are redefined later.

%include naive.lagda
%include subst.lagda
%include laws.lagda
%include init.lagda

\section{Conclusions and further work}
\label{sec:concl-furth-work}

The subject of the paper is a problem we expect everybody (including
ourselves) would have thought trivial.
As it turns out, it isn't, and 
we spent quite some time 
going down alleys that didn't work, 
and getting to grips with the subtleties of Agda's termination checking.

% With hindsight, the main idea seems rather
% obvious: introduce sorts as a datatype with the structure of a boolean
% algebra. To implement the solution in Agda, we managed to
% convince the termination checker that |V| is structurally smaller than
% |T| and so left the actual work determining and verifying the termination 
% ordering to Agda. This greatly simplifies the formal development. 

% We could, however, simplify our development slightly further if we were able to 
% instrument the termination checker, for example with an ordering on 
% constructors (i.e. removing the need for the |T>V| encoding). 
% We also ran into issues with Agda only examining direct arguments to function
% calls for identifying termination order. The solutions to these problems were
% all quite mechanical, which perhaps implies there is room for Agda's termination
% checking to be extended.
% Finally, it would be nice if the termination checker
% provided independently-checkable evidence that its non-trivial reasoning is 
% sound (being able to print termination matrices with |-v term:5| is a
% useful feature, but is not quite as convincing as actually elaborating 
% to well-founded induction like e.g. Lean).
The convenience of our solution relies on Agda's built-in 
support for lexicographic termination \cite{alti:jfp02}.
In contrast, Rocq's |Fixpoint| command merely supports structural recursion on a
single argument and Lean has only raw elimination principles as
primitive. Luckily, both of these proof assistants layer on additional
tactics to support more natural use of non-primitive 
induction, making our approach somewhat 
transferable. Indeed, Lean can be convinced that our substitution 
operations
terminate after specifying measures similar to those in
Section~\ref{sec:termination}, via the |termination_by| tactic.

% For example, Lean features a pair of tactics |termination_by| and 
% |decreasing_by| for specifying per-function termination measures and
% proving that these measures strictly decrease, similarly to our
% approach to justifying termination in \ref{sec:termination}. 
% The slight extra complication is
% that Lean requires the provided measures to strictly decrease along 
% every
% mutual function call as opposed to over every cycle in the call graph.
% In the case of our substitution operations, adapting for this is not to onerous,
% requiring e.g. replacing the measures for |id| and |_⁺_| from
% |(r₂ , Γ₂)| and |(r₃ , σ₃)| to |(r₂ , Γ₂ , 0)| and |(r₃ , 0 , σ₃)|, ensuring
% a strict decrease when calling |_⁺_| in |id {Γ = Γ ▷ A}|.

% Conveniently, after specifying the correct measures, Lean is able to
% automatically solve the |decreasing_by| proof obligations, and so our
% approach to defining substitution remains concise even without quite-as-robust 
% support
% for lexicographic termination\footnote{In fact, specifying termination
% measures manually has some advantages: we no longer need to use a
% complicated |Sort| datatype to make the ordering on constructors
% explicit.}.
%  Of course, doing the analysis to work out which
% termination measures were appropriate took some time, and one could imagine
% an expanded Lean tactic being able to infer termination
% with no assistance, using a similar algorithm to Agda.

% We could avoid a recursive definition of substitution altogether and
% only work with the initial simply typed CwF as a QIIT. 
% However, this is
% unsatisfactory for two reasons: first of all, we would like to relate
% the quotiented view of $\lambda$-terms to the their definitional
% presentation, and, 
% second, when proving properties of $\lambda$-terms it is preferable to do so
% by induction over terms rather than use quotients (i.e. no need to consider
% cases for non-canonical elements or prove that equations are preserved).

% PLW: added following
One reviewer asked about another alternative: since we are merging |_∋_| and
|_⊢_|
why not go further and merge them entirely? Instead of a separate type for
variables, one could have a term corresponding to de Bruijn index zero
(written |●  : Γ ▷ A ⊢ A| and an explicit weakening operator on
terms (written
|_↑ : Γ ⊢ B → Γ ▷ A ⊢ B|).
% \begin{spec}
% data _⊢′_ : Con → Ty → Set where
%   ●    : Γ ▷ A ⊢′ A
%   _↑   : Γ ⊢′ B → Γ ▷ A ⊢′ B
%   _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
%   ƛ_   : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
% \end{spec}
This has the unfortunate property that there is now more than one way to
write terms that used to be identical. For instance, the terms
|● ↑ ↑ · ● ↑ · ●| and |(● ↑ · ●) ↑ · ●| are equivalent, where |● ↑ ↑|
corresponds to the variable with de Bruijn index two. A development
along these lines is explored in \cite{wadler2024explicit}.

% It
% leads to a compact development, but one where the
% natural normal form appears to be to push weakening to the outside
% (such as in \cite{mcbride2018everybody}),
% so that the second of the two terms above is considered normal rather
% than the first. 
% It may be a useful alternative, but we think it is
% also interesting to pursue the development given here, where
% terms retain their familiar normal form.

We see the current construction as a warmup for the
definition of substitution for dependent type theory
This is harder,
because then the typing of the constructors actually depends on the
substitution laws. Such a M\"unchhausian \cite{altenkirch2023munchhausen} 
construction should be possible in Agda (the reference is to Baron Münchhausen, who allegedly 
pulled himself 
out of a swamp by his own hair).
% PLW: deleted the following as redundant
% We call definitions in type theory whose typing depends on equations about 
% themselves \emph{M\"unchhausian}.
However, the theoretical underpinning of
inductive-inductive-recursive definitions is mostly unexplored, with
the exception of \cite{kaposi2023towards}.
There are
potential interesting applications: strictifying substitution laws is
essential to prove coherence of models of type theory in higher types,
in the sense of HoTT.

Hence an apparently trivial
problem isn't so easy after all, and it is a stepping stone to more
exciting open questions. But before you can run you need to walk and
we believe that the construction here can be useful to others.

% PLW: We should be sure to cite the following as related work.

% Schäfer, Steven, Tobias Tebbi, and Gert Smolka. ‘Autosubst: Reasoning
% with de Bruijn Terms and Parallel Substitutions’. In Interactive
% Theorem Proving, edited by Christian Urban and Xingyuan Zhang,
% 359–74. Lecture Notes in Computer Science. Cham: Springer
% International Publishing,
% 2015. https://doi.org/10.1007/978-3-319-22102-1_24.

% Saffrich, Hannes. ‘Abstractions for Multi-Sorted Substitutions’. In
% DROPS-IDN/v2/Document/10.4230/LIPIcs.ITP.2024.32. Schloss Dagstuhl –
% Leibniz-Zentrum für Informatik,
% 2024. https://doi.org/10.4230/LIPIcs.ITP.2024.32.

% Saffrich, Hannes, Peter Thiemann, and Marius Weidner. ‘Intrinsically
% Typed Syntax, a Logical Relation, and the Scourge of the Transfer
% Lemma’. In Proceedings of the 9th ACM SIGPLAN International Workshop
% on Type-Driven Development, 2–15. TyDe 2024. New York, NY, USA:
% Association for Computing Machinery,
% 2024. https://doi.org/10.1145/3678000.3678201.

%if jfpstyle
\section*{Conflicts of Interest}

% I assume?
None.
%endif

\bibliography{./local}

%if jfpstyle
\label{lastpage01}
%endif

\end{document}
