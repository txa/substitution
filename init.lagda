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
  category of contexts to |Set|),
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
  e.g. integrating no-confusion properties with pattern matching.}
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

We now want to show that our recursive substitution syntax obeys the CwF laws,
or in other words, that any CwF can be interpreted into our syntax.

%if False
\begin{code}
open import subst
open import laws

\end{code}
%endif

\begin{code}
module CwF = CwF-simple

\end{code}
\begin{spec}
stlc : CwF-simple
stlc .CwF.Con = Con
\end{spec}

We now need to decide how to interpret morphisms/substitutions. In our first 
attempt, we tried to pair renamings/substitutions with their sorts and stay 
polymorphic:
\begin{spec}
record _⊨_ (Δ : Con) (Γ : Con) : Set where
  field
    sort : Sort
    tms  : Δ ⊨[ sort ] Γ

stlc .CwF._⊨_ = _⊨_
stlc .CwF.id  = record {sort = V; tms = id}
\end{spec}

Unfortunately, this approach quickly breaks. The CwF laws force us to provide a 
unique morphism to the terminal object/weakening-from-the-empty-context.
\begin{spec}
stlc .CwF.• = •
stlc .CwF.ε = record {sort = ?; tms = ε}
stlc .CwF.•-η {δ = record {sort = q; tms = ε}} = ?
\end{spec}
Our |_⊨_| record is simply too flexible here. It allows two distinct 
implementations: |record {sort = V; tms = ε}| and |record {sort = T; tms = ε}|. 
We are stuck!

To avoid this, we instead must fix the sort to |T|.

\begin{code}
_⊨_ = _⊨[ T ]_ 

\end{code}
%if False
\begin{code}
_⊢_ = _⊢[ T ]_

π₀ : Δ ⊨[ q ] (Γ ▷ A) → Δ ⊨[ q ] Γ
π₀ (δ , M) = δ

π₁ : Δ ⊨[ q ] (Γ ▷ A) → Δ ⊢[ q ] A
π₁ (δ , M) = M

tm*⊑ : q ⊑ s → Γ ⊨[ q ] Δ → Γ ⊨[ s ] Δ
tm*⊑ q⊑s ε = ε
tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x

interleaved mutual
  ⊑∘ : tm*⊑ v⊑t xs ∘ ys ≡ xs ∘ ys
  ∘⊑ : ∀ {xs : Δ ⊨[ T ] Γ} {ys : Θ ⊨[ V ] Δ} → xs ∘ tm*⊑ v⊑t ys ≡ xs ∘ ys
  v[⊑] : i [ tm*⊑ v⊑t ys ] ≡ tm⊑ v⊑t i [ ys ]
  t[⊑] : t [ tm*⊑ v⊑t ys ] ≡ t [ ys ]
  ⊑⁺ : tm*⊑ ⊑t xs ⁺ A ≡ tm*⊑ v⊑t (xs ⁺ A)
  ⊑^ : tm*⊑ v⊑t xs ^ A ≡ tm*⊑ v⊑t (xs ^ A)

\end{code}
%endif

\end{code}
\begin{code}
  stlc : CwF-simple
  stlc .CwF.Con = Con
  stlc .CwF._⊨_ = _⊨_

  stlc .CwF.•           = •
  stlc .CwF.ε           = ε
  stlc .CwF.•-η {δ = ε} = refl 

  stlc .CwF._∘_ = _∘_
  stlc .CwF.∘∘  = sym ∘∘
\end{code}

The lack of flexibility to choose the sort does, however, make identity a little 
trickier. |id| doesn't fit directly as it produces
renamings |Γ ⊨[ V ] Γ| - we need the equivalent substitution |Γ ⊨[ T ] Γ|. 
Technically, |id-poly| would suit this purpose but for reasons that will become 
clear soon, we take a slightly more indirect approach.
\footnote{Also, |id-poly| was ultimately just an implementation detail 
to satisfy the termination checker, so we'd rather not rely on it here.}

We first extend |tm⊑| to sequences of variables/terms:
\begin{spec}
  tm*⊑ : q ⊑ s → Γ ⊨[ q ] Δ → Γ ⊨[ s ] Δ
  tm*⊑ q⊑s ε = ε
  tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x
\end{spec}
And prove various lemmas about how |tm*⊑| coercions can be lifted outside of
our substitution operators:
\begin{spec}
  ⊑∘   : tm*⊑ v⊑t xs ∘ ys ≡ xs ∘ ys
  ∘⊑   : xs ∘ tm*⊑ v⊑t ys ≡ xs ∘ ys
  v[⊑] : i [ tm*⊑ v⊑t ys ] ≡ tm⊑ v⊑t i [ ys ]
  t[⊑] : t [ tm*⊑ v⊑t ys ] ≡ t [ ys ]
  ⊑⁺   : tm*⊑ ⊑t xs ⁺ A ≡ tm*⊑ v⊑t (xs ⁺ A)
  ⊑^   : tm*⊑ v⊑t xs ^ A ≡ tm*⊑ v⊑t (xs ^ A)
\end{spec}
Most of these are proofs come out easily by induction on terms and 
substitutions and we skip over them.
Perhaps worth noting though is that |⊑⁺| requires one new law relating our two
ways of weakening variables.
\begin{code}
  suc[id⁺] : i [ id ⁺ A ] ≡ suc i A
  suc[id⁺] {i = i} {A = A} =
    i [ id ⁺ A ]
    ≡⟨ ⁺-nat[]v {i = i} ⟩ 
    suc (i [ id ]) A
    ≡⟨ cong (λ j → suc j A) [id] ⟩
    suc i A ∎

  ⊑⁺ {xs = ε}      = refl
  ⊑⁺ {xs = xs , x} = cong₂ _,_ ⊑⁺ (cong (`_) suc[id⁺])

\end{code}

%if False
\begin{code}
  ⊑∘ {xs = ε} = refl
  ⊑∘ {xs = xs , x} = cong₂ _,_ ⊑∘ refl

  ∘⊑ {xs = ε} = refl
  ∘⊑ {xs = xs , x} = cong₂ _,_ ∘⊑ (t[⊑] {t = x})

  v[⊑] {i = zero}    {ys = ys , y} = refl
  v[⊑] {i = suc i _} {ys = ys , y} = v[⊑] {i = i}

  ⊑^ = cong₂ _,_ ⊑⁺ refl

  t[⊑] {t = ` i}           = v[⊑] {i = i}
  t[⊑] {t = t · u}         = cong₂ _·_ (t[⊑] {t = t}) (t[⊑] {t = u})
  t[⊑] {t = ƛ t} {ys = ys} =
    ƛ t [ tm*⊑ ⊑t ys ^ _ ]
    ≡⟨ cong (λ ρ → ƛ t [ ρ ]) ⊑^ ⟩
    ƛ t [ tm*⊑ ⊑t (ys ^ _) ] 
    ≡⟨ cong ƛ_ (t[⊑] {t = t}) ⟩
     ƛ t [ ys ^ _ ] ∎
\end{code}
%endif

We can now build an identity substitution by applying this coercion to the 
identity renaming.
\begin{code}
  stlc .CwF.id = tm*⊑ v⊑t id
\end{code}
Our left and right identity laws now take the form |tm*⊑ v⊑t id ∘ δ ≡ δ|
and |δ ∘ tm*⊑ v⊑t id ≡ δ|. This is where we can take full advantage of the 
|tm*⊑| machinery: the lemmas let us reuse our existing |id∘|/|∘id| proofs!
\begin{code}
  stlc .CwF.id∘ {δ = δ} = 
    tm*⊑ v⊑t id ∘ δ
    ≡⟨ ⊑∘ ⟩
    id ∘ δ
    ≡⟨ id∘ ⟩
    δ ∎
  stlc .CwF.∘id {δ = δ} =
    δ ∘ tm*⊑ v⊑t id
    ≡⟨ ∘⊑ ⟩
    δ ∘ id
    ≡⟨ ∘id ⟩
    δ ∎
\end{code}

Similarly to substitutions, we must fix the sort of our presheaf on contexts/
terms to |T| (in this case, so we can prove the identity law: applying the
identity substitution to a variable |i| produces the distinct term |` i|).

\begin{spec}
  _⊢_ = _⊢[ T ]_
\end{spec}
\begin{code}
  stlc .CwF.Ty           = Ty
  stlc .CwF._⊢_          = _⊢_
  stlc .CwF._[_]         = _[_]
  stlc .CwF.[∘] {t = t}  = sym ([∘] {x = t})
  stlc .CwF.[id] {t = t} =
    t [ tm*⊑ v⊑t id ]
    ≡⟨ t[⊑] {t = t} ⟩
    t [ id ]
    ≡⟨ [id] ⟩
    t ∎
\end{code}

Context extension and the associated laws are easy. We define projections 
|π₀ (δ , t) = δ| and |π₁ (δ , t) = t| standalone as these will be useful in the 
next section also.

\begin{code}
  stlc .CwF._▷_ = _▷_
  stlc .CwF._,_ = _,_
  stlc .CwF.π₀ = π₀
  stlc .CwF.π₁ = π₁
  stlc .CwF.▷-β₀ = refl
  stlc .CwF.▷-β₁ = refl
  stlc .CwF.▷-η {δ = xs , x} = refl
  stlc .CwF.π₀∘ {θ = xs , x} = refl
  stlc .CwF.π₁∘ {θ = xs , x} = refl
\end{code}

Finally, we can deal with the cases specific to simply typed $\lambda$-calculus.
Interestingly, the beta-rule for substitutions applied to lambdas is somewhat
non-trivial due to differing implementations of |_^_|.

\begin{code}
  stlc .CwF.o = o
  stlc .CwF._⇒_ = _⇒_
  stlc .CwF._·_ = _·_
  stlc .CwF.ƛ_ = ƛ_
  stlc .CwF.·[] = refl
  stlc .CwF.ƛ[] {A = A} {t = x} {δ = ys} =
    ƛ x [ ys ^ A ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ ^ A ]) (sym ∘id) ⟩
    ƛ x [ (ys ∘ id) ^ A ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym ⁺-nat∘) ⟩ 
    ƛ x [ ys ∘ id ⁺ A , ` zero ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym (∘⊑ {xs = ys}  {ys = id ⁺ _})) ⟩
    ƛ x [ ys ∘ tm*⊑ v⊑t (id ⁺ A) , ` zero ] ∎
\end{code}

\subsection{Proving initiality}
\label{sec:proving-initiality}

We have now proved that we can interpret any model of a simply-typed CwF into
our syntax with recursive substitutions, but this is not yet sufficient for 
proving initiality (that our syntax is isomorphic to the initial CwF).

To show this isomorphism, we must first define the initial CwF. We use
postulates and rewrite rules instead of a Cubical Agda QIIT because of 
technical limitations mentioned previously.

% TODO
 