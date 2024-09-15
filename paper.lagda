\documentclass[sigplan,10pt,natbib,anonymous,review]{acmart}
\settopmatter{printfolios=true,printccs=false,printacmref=false}
\citestyle{acmauthoryear}
%\usepackage{tipa}
%\usepackage{fontspec}
\let\Bbbk\relax % to avoid conflict
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt

\title{Substitution without copy and paste}

\author{Thorsten Altenkirch}
\affiliation{%
  \institution{University of Nottingham}
  \city{Nottingham}
  \country{United Kingdom}}
\email{thorsten.altenkirch@@nottingham.ac.uk}

\author{Nathaniel Burke}
\affiliation{
  \institution{Imperial College London}
  \city{London}
  \country{United Kingdom}}
\email{nathaniel.burke21@@imperial.ac.uk}

\author{Phil Wadler}

\begin{abstract}
When defining substitution recursively for a language with binders
like the simply typed $\lambda$-calculus we need to define
substitution and renaming separately. When we want to verify the
categorical properties of this calculus we end up repeating the same
argument many times. In this paper we present a lightweight method
that avoids this repetition and is implemented in Agda.

We use our setup to also show that the recursive definition of
substitution gives rise to a simply typed category with families (CwF)
and indeed that it is isomorphic to the initial simply typed CwF.
\end{abstract}

\begin{document}
\maketitle

\section{Introduction}
\label{sec:introduction}

% [PHIL: Begin alternative introduction.]

\begin{quote}
Some half dozen persons have written technically on combinatory logic,
and most of these, including ourselves, have published something
erroneous. \citet{curry1958combinatory}
\end{quote}

% It is notoriously difficult to define substitution correctly
% in the presence of binding operators. A pleasing solution is
% suggested by \citet{debruijn1972lambda}, which not only
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
% these definitions and proofs, for instance as suggested by \citet{allais2017type},
% but these are far from elementary.

% [PHIL: End alternative introduction. Having written it, I think
% I like the below better!]


The first author was writing lecture notes for an introduction to
category theory for functional programmers. A nice example of a
category is the category of simply typed $\lambda$-terms and
substitutions hence it seemed a good idea to give the definition and
ask the students to prove the category laws. When writing the answer
they realised that it is not as easy as they thought. To make sure that
there are no mistakes they started to formalize the problem in Agda.
The main setback was that the same proofs got repeated many times. 
If there is one guideline of good software engineering then it is 
\textbf{Do not write code by copy and paste} and this applies even more so to 
formal proofs.

This paper is the result of the effort to refactor the proof. We think
that the method used is interesting also for other problems, in
particular the current construction can be seen as a warmup for the
recursive definition of substitution for dependent type theory which
may have interesting applications for the coherence problem,
i.e. interpreting dependent types in higher categories. 

\subsection{Related work}
\label{sec:related-work}

\citet{de_bruijn_lambda_1972} introduces his eponymous indices and also
the notion of simultaneous substitution. We are here using a typed
version of de Bruijn indices, e.g. see \cite{alti:csl99} where the
problem of showing termination of a simple definition of substitution
(for the untyped $\lambda$-calculus) is addressed using a well-founded
recursion. However, this is only applied to the definition and the
categorical laws (which follow from the monad laws) were not formally
verified. Also the present approach seems to be simpler and scales
better avoiding well-founded recursion.  The monadic approach has been
further investigated in \cite{mcbride2006type}. The structure of the
proofs is explained in \cite{allais2017type} from a monadic
perspective. Indeed this example is one of the motivations for
relative monads \cite{altenkirch2015monads}.

We avoid the monadic perspective here for two reasons: first we want
to give a simple self-contained proof avoiding too many advanced
categorical constructions as mentioned in the introduction as a
motivation; second we are interested in the application to dependent
types where it is not clear how the monadic approach can be applied
without using very dependent types.

There are a number of publications on formalising substitution laws.
Just to mention a few recent ones: 
\cite{stark2019autosubst} develops a Coq library which automatically derives
substitution lemmas, but the proofs are simply repeated for renamings and
substitutions. Their equational theory is similar to the simply
typed CwFs we are using in section \ref{sec:initiality}.
\cite{saffrich2024abstractions} is also using Agda but extrinsically
(i.e. separating preterms and typed syntax). Here the approach from 
\cite{allais2017type}  is used to factor the construction using
\emph{kits}.  In \cite{saffrich2024intrinsically} this is further
developed, this time using intrinsic syntax, but with renamings and 
substitutions defined separately and relevant lemmas repeated for all required 
combinations.

\subsection{Using Agda}
\label{sec:using-agda}

For the technical details of Agda we refer to the online documentation
\cite{agda}. We only use plain Agda, inductive definitions and
structurally recursive programs and proofs.  Termination is checked by
Agda's termination checker \cite{alti:jfp02} which uses a lexical
combination of structural descent that is inferred by the termination
checker by investigating all possible recursive paths. We will define
mutually recursive proofs which heavily rely on each other.

The only recent
feature we use even though sparingly is the possibility to turn propositional
equations into rewriting rules (i.e. definitional equalities). This
makes the statement of some theorems more readable because we can avoid
using |subst| but this is not essential.

We extensively use variable declarations to introduce implicit
quantification (we summarize the variables conventions in passing in
the text). We also use $\forall{}$-prefix so we can elide types of function
parameters where they can be inferred, i.e. instead of |{Γ : Con} → ..| we just 
write |∀ {Γ} → ..|.

Implicit variables, which are indicated by using |{..}| instead of
|(..)| in dependent function types,  can be instantiated using the syntax
|a {x = b}| which we use in the proofs. Agda syntax is very flexible
allowing mixfix syntax declarations using |_| to indicate where the
parameters go.

In the proofs we also use the Agda standard library's definitions for equational 
derivations, which exploit Agda's flexible syntax.

The source of this document contains the actual Agda code, i.e. it is
a literate Agda file. Different chapters are in different modules to
avoid name clashes, e.g. preliminary definitions from section \ref{sec:naive-approach}
are redefined later.

%include naive.lagda
%include subst.lagda
%include laws.lagda
%include init.lagda

\section{Conclusions and further work}
\label{sec:concl-furth-work}

The subject of the paper is a problem which everybody including
ourselves would have thought to be trivial. As it turns out, it isn't. 
We spent some time going down alleys that didn't work. 
In the end with hindsight the main idea seems rather
obvious: introduce sorts as a datatype with the structure of a boolean
algebra. To implement the solution in Agda we managed to
convince the termination checker that |V| is structurally smaller than
|T| and so leave the actual work determining and verifying the termination 
ordering to Agda.
This greatly simplifies the formal development. 

We could, however, simplify our development slightly further if we were able to 
instrument the termination checker, for example with an ordering on 
constructors. 
We also ran into issues with Agda only examining direct arguments to function
calls when doing termination checking. The solutions to these problems were
all quite mechanical, which perhaps implies there is room for Agda's termination
checker to be extended.
Finally, it would be nice if the termination checker
provided independently-checkable evidence that its non-trivial reasoning is 
sound. 

This paper can also be seen as a preparation for the harder problem to
implement recursive substitution for dependent types. This is harder
because here the typing of the constructors actually depends on the
substitution laws. While such a M\"unchhausian \cite{altenkirch2023munchhausen} 
construction
\footnote{The reference is to Baron Münchhausen who allegedly pulled himself on 
his own hair out of a swamp.
We call definitions in type theory whose typing depends on equations about them 
\emph{M\"unchhausian}.
}
should actually be possible in Agda, the theoretical underpinning of
inductive-inductive-recursive definitions is mostly unexplored (with
the exception of the proposal by \cite{kaposi2023towards}). However, there are
potential interesting applications: strictifying substitution laws is
essential to prove coherence of models of type theory in higher types
in the sense of HoTT.

Hence this paper has two aspects: it turns out that an apparently trivial
problem isn't so hard after all, and it is a stepping stone to more
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






\bibliographystyle{ACM-Reference-Format}
\bibliography{local}


\end{document}
