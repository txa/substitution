%if False
\begin{code}
{-# OPTIONS --rewriting #-}
module init where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}
\end{code}
%endif

\section{Initiality}
\label{sec:initiality}

We can do more than just prove that we have got a category, indeed we
can verify the laws of a simply typed category with families
(CwF). CwFs are mostly known as models of dependent type theory but
they can be specialised to simple types \cite{castellan2021categories}.

For the categorically minded we can summarize:
\footnote{It is not necessary to know the categorical definition to
  understand the rest of the paper.}
a CwF is given by
\begin{itemize}
\item a category of contexts,
\item a presheaf to model types (i.e. a contravariant functor from the
  category of context to Set),
\item a dependent presheaf for terms over the type presheaf (i.e. a presheaf
  over the category of elements of the type presheaf),
\item A terminal object (empty context) and context extension.
  Context extension corresponds to demanding that the term presheaf is
  locally representable.  
\end{itemize}
To this we can add further constructors, e.g. $\Pi$-types. If we are
only interested in a substitution calculus like in our current work, we
only add the type and term formers and the condition that they are
natural, i.e. commute with substitution.

In the simply typed case the type
presheaf is constant since the set of types doesn't vary over the
context and the dependent presheaf of terms becomes an ordinary
presheaf over the category of contexts.

We start with a precise definition of a simply typed CwF with
additional structure to model simply typed $\lambda$-calculus (section
\ref{sec:simply-typed-cwfs}) and then we show that the recursive
definition of substitution gives rise to a simply typed CwF (section
\ref{sec:cwf-recurs-subst}). We can define the initial CwF as a
Quotient Inductive Type in Cubical Agda but to simplify our
development
\footnote{Cubical Agda still lacks some essential automation,
  e.g. integrating no-confusion properties into pattern matching.}
we just postulate the existence of this QIIT in Agda (with
the associated rewriting rules). By initiality there is an evaluation
functor from the initial CwF to the recursively defined CwF (defined
in section \ref{sec:cwf-recurs-subst}). On the
other hand we can embed the recursive CwF into the initial CwF ---
this corresponds to the embedding of normal forms into
$\lambda$-terms, only that here we talk about \emph{substitution normal
forms}. We then show that these two structure maps are inverse to each
other and
hence that the recursively defined CwF is indeed initial (section
\ref{sec:proving-initiality}). The two identities correspond to
completeness and stability in the language of normalisation functions.  

\subsection{Simply Typed CwFs}
\label{sec:simply-typed-cwfs}

We define a record to capture simply typed CWFs:
\begin{code}
record CwF-simple : Set₁ where
\end{code}

%if False
\begin{code}
  infix   3  _⊢_
  infix   3  _⊨_
  infixl  4  _▷_
  infixl  4  _,_
  infix   5  _∘_
  infix   5  ƛ_
  infixr  6  _⇒_
  infixl  6  _·_
  infix   8  _[_]
\end{code}
%endif


We start with the category of contexts using the same names as
introduced previously:
\begin{code}
  field
    Con : Set
    _⊨_ : Con → Con → Set

    id : {Γ : Con} → Γ ⊨ Γ
    _∘_ : {Γ Δ Θ : Con}
        → Δ ⊨ Θ → Γ ⊨ Δ → Γ ⊨ Θ
    id∘ : ∀ {Γ Δ}{δ : Γ ⊨ Δ}
       → id ∘ δ ≡ δ
    ∘id : ∀ {Γ Δ}{δ : Γ ⊨ Δ}
       → δ ∘ id ≡ δ
    ∘∘ : ∀ {Γ Δ Θ Ξ}
          {ξ : Θ ⊨ Ξ}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)  
\end{code}
We introduce the set of types and associate a presheaf with each type:
\begin{code}
    Ty : Set           
    _⊢_ : Con → Ty → Set         
    _[_] : ∀ {Γ Δ A}
        → Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
    [id] : ∀ {Γ A}{t : Γ ⊢ A}
        →  (t [ id ]) ≡ t
    [∘] : ∀ {Γ Δ Θ A}
          {t : Θ ⊢ A}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ} →
          t [ θ ] [ δ ] ≡ t [ θ ∘ δ ] 
\end{code}
The category of contexts has a terminal object (the empty context):
\begin{code}
    • : Con
    ε : ∀ {Γ} → Γ ⊨ • 
    •-η : ∀ {Γ}{δ : Γ ⊨ •}
        → δ ≡ ε  
\end{code}
Context extension resembles categorical products but mixing contexts
and types:
\begin{code}
    _▷_ : Con → Ty → Con
    _,_ : ∀ {Γ Δ A}
        → Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ (Δ ▷ A)
    π₀ : ∀ {Γ Δ A}
        → Γ ⊨ (Δ ▷ A) → Γ ⊨ Δ
    π₁ : ∀ {Γ Δ A}
        → Γ ⊨ (Δ ▷ A) → Γ ⊢ A
    ▷-β₀ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₀ (δ , t) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₁ (δ , t) ≡ t
    ▷-η : ∀ {Γ Δ A}{δ : Γ ⊨ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ A}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ A}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₁ (θ ∘ δ) ≡ (π₁ θ) [ δ ]  
\end{code}
We can define the morphism part of the context extension functor as
before:
\begin{code}
  _^_ : ∀ {Γ Δ} → Γ ⊨ Δ → ∀ A → Γ ▷ A ⊨ Δ ▷ A
  δ ^ A = (δ ∘ (π₀ id)) , π₁ id
\end{code}
We need to add the specific components for simply typed
$\lambda$-calculus: we add the type constructors and the term
constructors and the corresponding naturality laws:
\begin{code}
  field
    o : Ty
    _⇒_ : Ty → Ty → Ty
    _·_  : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    ƛ_   : ∀ {Γ A B} → Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
    ·[]  : ∀ {Γ Δ A B}
           {t : Γ ⊢ A ⇒ B}{u : Γ ⊢ A}{δ : Δ ⊨ Γ}
           → (t · u) [ δ ] ≡ (t [ δ ]) · (u [ δ ])
    ƛ[] :  ∀ {Γ Δ A B}{t : Γ ▷ A ⊢ B}{δ : Δ ⊨ Γ}
           → (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ _ ])  
\end{code}

\subsection{The CwF of recursive substitutions}
\label{sec:cwf-recurs-subst}

\subsection{Proving initiality}
\label{sec:proving-initiality}
