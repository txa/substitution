%if False
\begin{code}
{-# OPTIONS --rewriting --injective-type-constructors #-}
module init where

open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Unit
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
\item A category of contexts,
\item A presheaf to model types (i.e. a contravariant functor from the
  category of contexts to |Set|),
\item A dependent presheaf for terms over the type presheaf (i.e. a presheaf
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
Quotient Inductive Type. To simplify our development, rather than using a
Cubical Agda HIT,
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

We now aim to show that our recursive substitution syntax obeys the CwF laws.
As we shall see later, this will also be more-or-less enough to implement the 
"normalisation" direction of our initial CwF |≃| recursive sub syntax 
isomorphism.

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
is-cwf : CwF-simple
is-cwf .CwF.Con = Con
\end{spec}

We now need to decide which type family to interpret substitutions into. 
In our first attempt, we tried to pair renamings/substitutions with their sorts 
and stay polymorphic:

\begin{spec}
record _⊨_ (Δ : Con) (Γ : Con) : Set where
  field
    sort : Sort
    tms  : Δ ⊨[ sort ] Γ

is-cwf .CwF._⊨_ = _⊨_
is-cwf .CwF.id  = record {sort = V; tms = id}
\end{spec}

Unfortunately, this approach quickly breaks. The CwF laws force us to provide a 
unique morphism to the terminal context (i.e. a unique weakening from the empty 
context).

\begin{spec}
is-cwf .CwF.• = •
is-cwf .CwF.ε = record {sort = ?; tms = ε}
is-cwf .CwF.•-η {δ = record {sort = q; tms = ε}} = ?
\end{spec}

Our |_⊨_| record is simply too flexible here. It allows two distinct 
implementations: |record {sort = V; tms = ε}| and |record {sort = T; tms = ε}|. 
We are stuck!

To avoid this, we instead fix the sort to |T|.

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

\begin{code}
  is-cwf : CwF-simple
  is-cwf .CwF.Con = Con
  is-cwf .CwF._⊨_ = _⊨_

  is-cwf .CwF.•           = •
  is-cwf .CwF.ε           = ε
  is-cwf .CwF.•-η {δ = ε} = refl 

  is-cwf .CwF._∘_ = _∘_
  is-cwf .CwF.∘∘  = sym ∘∘
\end{code}

The lack of flexibility to choose the sort does, however, make identity a little 
trickier. |id| doesn't fit directly as it produces
renamings |Γ ⊨[ V ] Γ|; we need the equivalent substitution |Γ ⊨[ T ] Γ|. 
Technically, |id-poly| would suit this purpose but for reasons that will become 
clear soon, we take a slightly more indirect approach.
\footnote{Also, |id-poly| was ultimately just an implementation detail 
to satisfy the termination checker, so we'd rather not rely on it.}

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
  is-cwf .CwF.id = tm*⊑ v⊑t id
\end{code}

The left and right identity CwF laws now take the form |tm*⊑ v⊑t id ∘ δ ≡ δ|
and |δ ∘ tm*⊑ v⊑t id ≡ δ|. This is where we can take full advantage of the 
|tm*⊑| machinery; these lemmas let us reuse our existing |id∘|/|∘id| proofs!

\begin{code}
  is-cwf .CwF.id∘ {δ = δ} = 
    tm*⊑ v⊑t id ∘ δ
    ≡⟨ ⊑∘ ⟩
    id ∘ δ
    ≡⟨ id∘ ⟩
    δ ∎
  is-cwf .CwF.∘id {δ = δ} =
    δ ∘ tm*⊑ v⊑t id
    ≡⟨ ∘⊑ ⟩
    δ ∘ id
    ≡⟨ ∘id ⟩
    δ ∎
\end{code}

Similarly to substitutions, we must fix the sort of our terms to |T| 
(in this case, so we can prove the identity law - note that applying the 
identity substitution to a variable |i| produces the distinct term |` i|).

\begin{spec}
  _⊢_ = _⊢[ T ]_
\end{spec}
\begin{code}
  is-cwf .CwF.Ty           = Ty
  is-cwf .CwF._⊢_          = _⊢_
  is-cwf .CwF._[_]         = _[_]
  is-cwf .CwF.[∘] {t = t}  = sym ([∘] {x = t})
  is-cwf .CwF.[id] {t = t} =
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
  is-cwf .CwF._▷_ = _▷_
  is-cwf .CwF._,_ = _,_
  is-cwf .CwF.π₀ = π₀
  is-cwf .CwF.π₁ = π₁
  is-cwf .CwF.▷-β₀ = refl
  is-cwf .CwF.▷-β₁ = refl
  is-cwf .CwF.▷-η {δ = xs , x} = refl
  is-cwf .CwF.π₀∘ {θ = xs , x} = refl
  is-cwf .CwF.π₁∘ {θ = xs , x} = refl
\end{code}

Finally, we can deal with the cases specific to simply typed $\lambda$-calculus.
Only the beta-rule for substitutions applied to lambdas is non-trivial due to 
differing implementations of |_^_|.

\begin{code}
  is-cwf .CwF.o = o
  is-cwf .CwF._⇒_ = _⇒_
  is-cwf .CwF._·_ = _·_
  is-cwf .CwF.ƛ_ = ƛ_
  is-cwf .CwF.·[] = refl
  is-cwf .CwF.ƛ[] {A = A} {t = x} {δ = ys} =
    ƛ x [ ys ^ A ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ ^ A ]) (sym ∘id) ⟩
    ƛ x [ (ys ∘ id) ^ A ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym ⁺-nat∘) ⟩ 
    ƛ x [ ys ∘ id ⁺ A , ` zero ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym (∘⊑ {xs = ys}  {ys = id ⁺ _})) ⟩
    ƛ x [ ys ∘ tm*⊑ v⊑t (id ⁺ A) , ` zero ] ∎
\end{code}

We have shown our recursive substitution syntax satisfies the CwF laws, but we
want to go a step further and show initiality: that our syntax is isomoprhic to
the initial CwF.

An important first step is to actually define the initial CwF (and its
eliminator). We use postulates and rewrite rules instead of a Cubical 
Agda QIIT because of technical limitations mentioned previously.
We also reuse our existing datatypes for contexts and types because terms do not 
occur inside types in STLC.

To state the dependent equations between outputs of the eliminator, we need
dependent identity types, which we can define by matching on the identity
between the LHS and RHS types.

%if False
\begin{code}
open import Level hiding (suc)

infix 4 _≡[_]≡_

private variable
  ℓ ℓ₁ ℓ₂ : Level
\end{code}
%endif

\begin{code}
_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ refl ]≡ y = x ≡ y
\end{code}

%if False
\begin{code}
infix   3  _⊢ᴵ_
infix   3  _⊨ᴵ_
infix   5  _∘ᴵ_
infix   5  ƛᴵ_
infixl  6  _·ᴵ_
infix   8  _[_]ᴵ
\end{code}
%endif

\begin{code}
postulate
  _⊢ᴵ_ : Con → Ty → Set
  _⊨ᴵ_ : Con → Con → Set

variable
  tᴵ uᴵ vᴵ : Γ ⊢ᴵ A
  δᴵ σᴵ ξᴵ : Δ ⊨ᴵ Γ

postulate
  idᴵ  : Γ ⊨ᴵ Γ
  _∘ᴵ_ : Δ ⊨ᴵ Γ → Θ ⊨ᴵ Δ → Θ ⊨ᴵ Γ
  id∘ᴵ : idᴵ ∘ᴵ δᴵ ≡ δᴵ
  ∘idᴵ : δᴵ ∘ᴵ idᴵ ≡ δᴵ
  ∘∘ᴵ  : (ξᴵ ∘ᴵ σᴵ) ∘ᴵ δᴵ ≡ ξᴵ ∘ᴵ (σᴵ ∘ᴵ δᴵ)

  _[_]ᴵ : Γ ⊢ᴵ A → Δ ⊨ᴵ Γ → Δ ⊢ᴵ A
  [id]ᴵ : tᴵ [ idᴵ ]ᴵ ≡ tᴵ
  [∘]ᴵ  : tᴵ [ σᴵ ]ᴵ [ δᴵ ]ᴵ ≡ tᴵ [ σᴵ ∘ᴵ δᴵ ]ᴵ

  εᴵ   : Δ ⊨ᴵ •
  _,ᴵ_ : Δ ⊨ᴵ Γ → Δ ⊢ᴵ A → Δ ⊨ᴵ (Γ ▷ A)
  π₀ᴵ : Δ ⊨ᴵ Γ ▷ A → Δ ⊨ᴵ Γ
  π₁ᴵ : Δ ⊨ᴵ Γ ▷ A → Δ ⊢ᴵ A

  •-ηᴵ  : δᴵ ≡ εᴵ
  ▷-β₀ᴵ : π₀ᴵ (δᴵ ,ᴵ tᴵ) ≡ δᴵ
  ▷-β₁ᴵ : π₁ᴵ (δᴵ ,ᴵ tᴵ) ≡ tᴵ
  ▷-ηᴵ  : (π₀ᴵ δᴵ ,ᴵ π₁ᴵ δᴵ) ≡ δᴵ
  π₀∘ᴵ  : π₀ᴵ (σᴵ ∘ᴵ δᴵ) ≡ π₀ᴵ σᴵ ∘ᴵ δᴵ
  π₁∘ᴵ  : π₁ᴵ (σᴵ ∘ᴵ δᴵ) ≡ π₁ᴵ σᴵ [ δᴵ ]ᴵ

wkᴵ : Γ ▷ A ⊨ᴵ Γ
wkᴵ = π₀ᴵ idᴵ

zeroᴵ : Γ ▷ A ⊢ᴵ A 
zeroᴵ = π₁ᴵ idᴵ

_^ᴵ_ : Δ ⊨ᴵ Γ → ∀ A → Δ ▷ A ⊨ᴵ Γ ▷ A
δ ^ᴵ A = (δ ∘ᴵ wkᴵ) ,ᴵ zeroᴵ

postulate
  _·ᴵ_ : Γ ⊢ᴵ A ⇒ B → Γ ⊢ᴵ A → Γ ⊢ᴵ B
  ƛᴵ_  : Γ ▷ A ⊢ᴵ B → Γ ⊢ᴵ A ⇒ B
  ·[]ᴵ : (tᴵ ·ᴵ uᴵ) [ δᴵ ]ᴵ ≡ tᴵ [ δᴵ ]ᴵ ·ᴵ uᴵ [ δᴵ ]ᴵ
  ƛ[]ᴵ : (ƛᴵ tᴵ) [ δᴵ ]ᴵ ≡ ƛᴵ (tᴵ [ δᴵ ^ᴵ A ]ᴵ)

sucᴵ : Γ ⊢ᴵ B → ∀ A → Γ ▷ A ⊢ᴵ B
sucᴵ x A = x [ π₀ᴵ idᴵ ]ᴵ

record Motive : Set₁ where
  field
    Conᴱ : Con → Set
    Tyᴱ  : Ty → Set
    Tmᴱ  : Conᴱ Γ → Tyᴱ A → Γ ⊢ᴵ A → Set
    Tmsᴱ : Conᴱ Δ → Conᴱ Γ → Δ ⊨ᴵ Γ → Set

module _ (𝕄 : Motive) where
  open Motive 𝕄

  variable
    Γᴱ Δᴱ θᴱ Ξᴱ : Conᴱ Γ
    Aᴱ Bᴱ Cᴱ Dᴱ : Tyᴱ A
    tᴱ uᴱ vᴱ : Tmᴱ Γᴱ Aᴱ tᴵ
    δᴱ σᴱ ξᴱ : Tmsᴱ Δᴱ Γᴱ δᴵ

  record Branches : Set₁ where
    infixl  4  _▷ᴱ_
    infixl  4  _,ᴱ_
    infix   5  _∘ᴱ_
    infix   5  ƛᴱ_
    infixr  6  _⇒ᴱ_
    infixl  6  _·ᴱ_
    infix   8  _[_]ᴱ
    field
      idᴱ  : Tmsᴱ Γᴱ Γᴱ idᴵ 
      _∘ᴱ_ : Tmsᴱ Δᴱ Γᴱ σᴵ → Tmsᴱ θᴱ Δᴱ δᴵ → Tmsᴱ θᴱ Γᴱ (σᴵ ∘ᴵ δᴵ)
      
      id∘ᴱ : idᴱ ∘ᴱ δᴱ ≡[ cong (Tmsᴱ Δᴱ Γᴱ) id∘ᴵ ]≡ δᴱ
      ∘idᴱ : δᴱ ∘ᴱ idᴱ ≡[ cong (Tmsᴱ Δᴱ Γᴱ) ∘idᴵ ]≡ δᴱ
      ∘∘ᴱ  : (ξᴱ ∘ᴱ σᴱ) ∘ᴱ δᴱ ≡[ cong (Tmsᴱ Ξᴱ Γᴱ) ∘∘ᴵ ]≡ ξᴱ ∘ᴱ (σᴱ ∘ᴱ δᴱ) 

      _[_]ᴱ : Tmᴱ Γᴱ Aᴱ tᴵ → Tmsᴱ Δᴱ Γᴱ δᴵ → Tmᴱ Δᴱ Aᴱ (tᴵ [ δᴵ ]ᴵ)
      
      [id]ᴱ : tᴱ [ idᴱ ]ᴱ ≡[ cong (Tmᴱ Γᴱ Aᴱ) [id]ᴵ ]≡ tᴱ
      [∘]ᴱ  : tᴱ [ σᴱ ]ᴱ [ δᴱ ]ᴱ ≡[ cong (Tmᴱ θᴱ Aᴱ) [∘]ᴵ ]≡ tᴱ [ σᴱ ∘ᴱ δᴱ ]ᴱ

      •ᴱ : Conᴱ •
      εᴱ : Tmsᴱ Δᴱ •ᴱ εᴵ

      •-ηᴱ : δᴱ ≡[ cong (Tmsᴱ Δᴱ •ᴱ) •-ηᴵ ]≡ εᴱ

      _▷ᴱ_ : Conᴱ Γ → Tyᴱ A → Conᴱ (Γ ▷ A)
      _,ᴱ_ : Tmsᴱ Δᴱ Γᴱ δᴵ → Tmᴱ Δᴱ Aᴱ tᴵ → Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) (δᴵ ,ᴵ tᴵ)
      π₀ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δᴵ → Tmsᴱ Δᴱ Γᴱ (π₀ᴵ δᴵ)
      π₁ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δᴵ → Tmᴱ Δᴱ Aᴱ (π₁ᴵ δᴵ)

      ▷-β₀ᴱ : π₀ᴱ (δᴱ ,ᴱ tᴱ) ≡[ cong (Tmsᴱ Δᴱ Γᴱ) ▷-β₀ᴵ ]≡ δᴱ
      ▷-β₁ᴱ : π₁ᴱ (δᴱ ,ᴱ tᴱ) ≡[ cong (Tmᴱ Δᴱ Aᴱ) ▷-β₁ᴵ ]≡ tᴱ
      ▷-ηᴱ  : (π₀ᴱ δᴱ ,ᴱ π₁ᴱ δᴱ) ≡[ cong (Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ)) ▷-ηᴵ ]≡ δᴱ
      π₀∘ᴱ  : π₀ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ cong (Tmsᴱ θᴱ Γᴱ) π₀∘ᴵ ]≡ π₀ᴱ σᴱ ∘ᴱ δᴱ
      π₁∘ᴱ  : π₁ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ cong (Tmᴱ θᴱ Aᴱ) π₁∘ᴵ ]≡ π₁ᴱ σᴱ [ δᴱ ]ᴱ
    
    wkᴱ : Tmsᴱ (Γᴱ ▷ᴱ Aᴱ) Γᴱ wkᴵ
    wkᴱ = π₀ᴱ idᴱ

    zeroᴱ : Tmᴱ (Γᴱ ▷ᴱ Aᴱ) Aᴱ zeroᴵ
    zeroᴱ = π₁ᴱ idᴱ

    _^ᴱ_ : Tmsᴱ Δᴱ Γᴱ δᴵ → ∀ Aᴱ → Tmsᴱ (Δᴱ ▷ᴱ Aᴱ) (Γᴱ ▷ᴱ Aᴱ) (δᴵ ^ᴵ A)
    δᴱ ^ᴱ Aᴱ = (δᴱ ∘ᴱ wkᴱ) ,ᴱ zeroᴱ

    field
      oᴱ   : Tyᴱ o
      _⇒ᴱ_ : Tyᴱ A → Tyᴱ B → Tyᴱ (A ⇒ B)
      
      _·ᴱ_ : Tmᴱ Γᴱ (Aᴱ ⇒ᴱ Bᴱ) tᴵ → Tmᴱ Γᴱ Aᴱ uᴵ → Tmᴱ Γᴱ Bᴱ (tᴵ ·ᴵ uᴵ)
      ƛᴱ_  : Tmᴱ (Γᴱ ▷ᴱ Aᴱ) Bᴱ tᴵ → Tmᴱ Γᴱ (Aᴱ ⇒ᴱ Bᴱ) (ƛᴵ tᴵ)
      
      ·[]ᴱ : (tᴱ ·ᴱ uᴱ) [ δᴱ ]ᴱ 
          ≡[ cong (Tmᴱ Δᴱ Bᴱ) ·[]ᴵ 
          ]≡ tᴱ [ δᴱ ]ᴱ ·ᴱ uᴱ [ δᴱ ]ᴱ
      ƛ[]ᴱ : (ƛᴱ tᴱ) [ δᴱ ]ᴱ 
          ≡[ cong (Tmᴱ Δᴱ (Aᴱ ⇒ᴱ Bᴱ)) ƛ[]ᴵ 
          ]≡ ƛᴱ (tᴱ [ δᴱ ^ᴱ Aᴱ ]ᴱ)  

module Eliminator {𝕄} (𝔹 : Branches 𝕄) where
  open Motive 𝕄
  open Branches 𝔹

  elim-con : ∀ Γ → Conᴱ Γ
  elim-ty  : ∀ A → Tyᴱ  A

  elim-con • = •ᴱ
  elim-con (Γ ▷ A) = (elim-con Γ) ▷ᴱ (elim-ty A)

  elim-ty o = oᴱ
  elim-ty (A ⇒ B) = (elim-ty A) ⇒ᴱ (elim-ty B) 

  postulate
    elim-cwf  : ∀ tᴵ → Tmᴱ (elim-con Γ) (elim-ty A) tᴵ
    elim-cwf* : ∀ δᴵ → Tmsᴱ (elim-con Δ) (elim-con Γ) δᴵ

    elim-cwf*-idβ : elim-cwf* (idᴵ {Γ}) ≡ idᴱ
    elim-cwf*-∘β  : elim-cwf* (σᴵ ∘ᴵ δᴵ) ≡ elim-cwf* σᴵ ∘ᴱ elim-cwf* δᴵ

    elim-cwf*-[]β : elim-cwf (tᴵ [ δᴵ ]ᴵ) ≡ elim-cwf tᴵ [ elim-cwf* δᴵ ]ᴱ

    elim-cwf*-εβ  : elim-cwf* (εᴵ {Δ = Δ}) ≡ εᴱ
    elim-cwf*-,β  : elim-cwf* (δᴵ ,ᴵ tᴵ) ≡ (elim-cwf* δᴵ ,ᴱ elim-cwf tᴵ)
    elim-cwf*-π₀β : elim-cwf* (π₀ᴵ δᴵ) ≡ π₀ᴱ (elim-cwf* δᴵ)
    elim-cwf*-π₁β : elim-cwf (π₁ᴵ δᴵ) ≡ π₁ᴱ (elim-cwf* δᴵ)

    elim-cwf-·β : elim-cwf (tᴵ ·ᴵ uᴵ) ≡ elim-cwf tᴵ ·ᴱ elim-cwf uᴵ
    elim-cwf-ƛβ : elim-cwf (ƛᴵ tᴵ) ≡ ƛᴱ elim-cwf tᴵ
\end{code}

%if False
\begin{code}
  {-# REWRITE elim-cwf*-idβ elim-cwf*-∘β elim-cwf*-[]β elim-cwf*-εβ elim-cwf*-,β 
              elim-cwf*-π₀β elim-cwf*-π₁β elim-cwf-·β elim-cwf-ƛβ #-}

open Motive public
open Branches public
open Eliminator public
\end{code}
%endif

\begin{spec}
TODO: Insert REWRITE rule transformed into LaTeX characters here!
\end{spec}

Normalisation from the initial CwF into substitution normal forms now only
needs a way to connect our notion of "being a CwF" with our initial CwF's 
eliminator: specifically, that any set of type families obeying the CwF laws
gives rise to a |Motive| and associated set of |Branches|.

The one extra ingredient we need to make this work out neatly is to introduce
a new reduction for |cong|:
\footnote{This identity also holds definitionally in Cubical.}

\begin{code}
cong-const : ∀ {A : Set ℓ₁} {B : Set ℓ₂} {x : A} {y z : B} {p : y ≡ z} 
           → cong (λ _ → x) p ≡ refl
cong-const {p = refl} = refl

\end{code}

\begin{spec}
% TODO: REWRITE rule
\end{spec}

%if False
\begin{code}
{-# REWRITE cong-const #-}
\end{code}
%endif

This is enables the no-longer-dependent |_≡[_]≡_|s to collapse to |_≡_|s 
automatically.

\begin{code}
module Recursor (cwf : CwF-simple) where
  rec-con : Con → cwf .CwF.Con
  rec-ty  : Ty  → cwf .CwF.Ty
  rec-tms : Δ ⊨ᴵ Γ → cwf .CwF._⊨_ (rec-con Δ) (rec-con Γ)
  rec-tm  : Γ ⊢ᴵ A → cwf .CwF._⊢_ (rec-con Γ) (rec-ty A)

  cwf-to-motive : Motive
  cwf-to-motive .Conᴱ _     = cwf .CwF.Con
  cwf-to-motive .Tyᴱ  _     = cwf .CwF.Ty
  cwf-to-motive .Tmᴱ Γ A _  = cwf .CwF._⊢_ Γ A
  cwf-to-motive .Tmsᴱ Δ Γ _ = cwf .CwF._⊨_ Δ Γ
  
  cwf-to-branches : Branches cwf-to-motive
  cwf-to-branches .idᴱ   = cwf .CwF.id
  cwf-to-branches ._∘ᴱ_  = cwf .CwF._∘_
  cwf-to-branches .id∘ᴱ  = cwf .CwF.id∘
  -- etc...
\end{code}

%if False
\begin{code}
  cwf-to-branches .∘idᴱ  = cwf .CwF.∘id
  cwf-to-branches .∘∘ᴱ   = cwf .CwF.∘∘
  cwf-to-branches ._[_]ᴱ = cwf .CwF._[_]
  cwf-to-branches .[id]ᴱ = cwf .CwF.[id]
  cwf-to-branches .[∘]ᴱ  = cwf .CwF.[∘]
  cwf-to-branches .•ᴱ    = cwf .CwF.•
  cwf-to-branches .εᴱ    = cwf .CwF.ε
  cwf-to-branches .•-ηᴱ  = cwf .CwF.•-η
  cwf-to-branches ._▷ᴱ_  = cwf .CwF._▷_
  cwf-to-branches ._,ᴱ_  = cwf .CwF._,_
  cwf-to-branches .π₀ᴱ   = cwf .CwF.π₀
  cwf-to-branches .π₁ᴱ   = cwf .CwF.π₁
  cwf-to-branches .▷-β₀ᴱ = cwf .CwF.▷-β₀
  cwf-to-branches .▷-β₁ᴱ = cwf .CwF.▷-β₁
  cwf-to-branches .▷-ηᴱ  = cwf .CwF.▷-η
  cwf-to-branches .π₀∘ᴱ  = cwf .CwF.π₀∘
  cwf-to-branches .π₁∘ᴱ  = cwf .CwF.π₁∘
  cwf-to-branches .oᴱ    = cwf .CwF.o
  cwf-to-branches ._⇒ᴱ_  = cwf .CwF._⇒_
  cwf-to-branches ._·ᴱ_  = cwf .CwF._·_
  cwf-to-branches .ƛᴱ_   = cwf .CwF.ƛ_
  cwf-to-branches .·[]ᴱ  = cwf .CwF.·[]
  cwf-to-branches .ƛ[]ᴱ  = cwf .CwF.ƛ[]
\end{code}
%endif

\begin{code}
  rec-con = elim-con cwf-to-branches
  rec-ty  = elim-ty  cwf-to-branches
  rec-tm  = elim-cwf  cwf-to-branches
  rec-tms = elim-cwf* cwf-to-branches

open Recursor public
\end{code}

%if False
\begin{code}
{-# INLINE rec-con #-}
{-# INLINE rec-ty #-}
\end{code}
%endif

Normalisation into to our substitution-normal forms can now be achieved by with:
\begin{spec}
norm : Γ ⊢ᴵ A → rec-con is-cwf Γ ⊢ rec-ty is-cwf A
norm = rec-tm is-cwf 
\end{spec}

Of course, normalisation doesn't affect contexts or types so we might hope for a
simpler signature |Γ ⊢ᴵ A → Γ ⊢ A| and, luckily, rewrite rules can get us there!
\begin{code}

Con≡ : rec-con is-cwf Γ ≡ Γ
Ty≡  : rec-ty is-cwf A ≡ A

Con≡ {Γ = •} = refl
Con≡ {Γ = Γ ▷ A} = cong₂ _▷_ Con≡ Ty≡

Ty≡ {A = o} = refl
Ty≡ {A = A ⇒ B} = cong₂ _⇒_ Ty≡ Ty≡

\end{code}

\begin{spec}
%TODO: REWRITE RULE

\end{spec}

%if False
\begin{code}
{-# REWRITE Con≡ Ty≡ #-}
\end{code}
%endif

\begin{code}
norm : Γ ⊢ᴵ A → Γ ⊢ A
norm = rec-tm is-cwf 

norm* : Δ ⊨ᴵ Γ → Δ ⊨ Γ
norm* = rec-tms is-cwf
\end{code}

The inverse operation to inject our syntax back into the initial CwF comes out
easily be recursing on our substitution-normal forms.

\begin{code}
⌜_⌝ : Γ ⊢[ q ] A → Γ ⊢ᴵ A
⌜ zero ⌝    = zeroᴵ
⌜ suc i B ⌝ = sucᴵ ⌜ i ⌝ B
⌜ ` i ⌝     = ⌜ i ⌝
⌜ t · u ⌝   = ⌜ t ⌝ ·ᴵ ⌜ u ⌝
⌜ ƛ t ⌝     = ƛᴵ ⌜ t ⌝

⌜_⌝* : Δ ⊨[ q ] Γ → Δ ⊨ᴵ Γ
⌜ ε ⌝*     = εᴵ
⌜ δ , x ⌝* = ⌜ δ ⌝* ,ᴵ ⌜ x ⌝
\end{code}

\subsection{Proving initiality}
\label{sec:proving-initiality}

We have implemented both directions of the isomorphism. Now to show this truly
is an isomorphism and not just a pair of functions, we must prove that |norm| 
and |⌜_⌝| are mutual inverses - i.e. stability |norm ⌜ t ⌝ ≡ t| and 
completeness |⌜ norm t ⌝ ≡ t|.

We start with stability, as it is considerably easier. There are just a couple
details worth mentioning:
\begin{itemize}
  \item To deal with variables in the |`_| case, we phrase the lemma is a 
  slightly more general way, taking expressions of any sort and coercing them up 
  to sort |T| on the RHS.
  \item The case for variables relies on a bit of coercion manipulation and our 
  earlier lemma relating |suc i B| and |i [ id ⁺ B ]|.
\end{itemize}

\begin{code}
stab : norm ⌜ x ⌝ ≡ tm⊑ ⊑t x
stab {x = zero} = refl
stab {x = suc i B} =
  norm ⌜ i ⌝ [ tm*⊑ v⊑t (id ⁺ B) ]
  ≡⟨ t[⊑] {t = norm ⌜ i ⌝} ⟩
  norm ⌜ i ⌝ [ id ⁺ B ]
  ≡⟨ cong (λ j → suc[ _ ] j B) (stab {x = i}) ⟩
  ` i [ id ⁺ B ]
  ≡⟨ cong `_ suc[id⁺] ⟩
  ` suc i B ∎
stab {x = ` i} = stab {x = i}
stab {x = t · u} = cong₂ _·_ (stab {x = t}) (stab {x = u})
stab {x = ƛ t} = cong ƛ_ (stab {x = t})
\end{code}

To prove completeness, we must instead induct on the initial CwF itself, which
means there are many more cases. We start with the motive:

\begin{code}
compl-𝕄 : Motive
compl-𝕄 .Conᴱ _ = ⊤
compl-𝕄 .Tyᴱ  _ = ⊤
compl-𝕄 .Tmᴱ _ _ tᴵ = ⌜ norm tᴵ ⌝ ≡ tᴵ
compl-𝕄 .Tmsᴱ _ _ δᴵ = ⌜ norm* δᴵ ⌝* ≡ δᴵ
\end{code}

To show these identities, we need to prove that our various recursively-defined
syntax operations are preserved by |⌜_⌝|.

Preservation of projections out of sequences of terms reduce to the associated 
beta-laws of the initial CwF.

\begin{code}
⌜π₀⌝ : ∀ {δ : Δ ⊨ (Γ ▷ A)}
     → ⌜ π₀ δ ⌝* ≡ π₀ᴵ ⌜ δ ⌝*
⌜π₀⌝ {δ = δ , x} = sym ▷-β₀ᴵ

⌜π₁⌝ : ∀ {δ : Δ ⊨ (Γ ▷ A)}
     → ⌜ π₁ δ ⌝ ≡ π₁ᴵ ⌜ δ ⌝*
⌜π₁⌝ {δ = δ , x} = sym ▷-β₁ᴵ
\end{code}

\begin{code}
⌜zero⌝ : ⌜ zero[_] {Γ = Γ} {A = A} q ⌝ ≡ zeroᴵ
⌜zero⌝ {q = V} = refl
⌜zero⌝ {q = T} = refl
\end{code}

Preservation proofs for |_[_]|, |_^_|, |_⁺_|, |id| and |suc[_]| are all mutually 
inductive, mirroring their original recursive definitions. We must stay
polymorphic over sorts and again use our dummy |Sort| argument trick in |⌜id⌝| 
to keep Agda's termination checker happy.

\begin{code}
⌜[]⌝  : ⌜ x [ ys ] ⌝ ≡ ⌜ x ⌝ [ ⌜ ys ⌝* ]ᴵ
⌜^⌝   : ∀ {xs : Δ ⊨[ q ] Γ} → ⌜ xs ^ A ⌝* ≡ ⌜ xs ⌝* ^ᴵ A
⌜⁺⌝   : ⌜ xs ⁺ A ⌝* ≡ ⌜ xs ⌝* ∘ᴵ wkᴵ
⌜id⌝  : ⌜ id {Γ = Γ} ⌝* ≡ idᴵ
⌜suc⌝ : ⌜ suc[ q ] x B ⌝ ≡ ⌜ x ⌝ [ wkᴵ ]ᴵ

⌜id⌝′ : Sort → ⌜ id {Γ = Γ} ⌝* ≡ idᴵ
⌜id⌝ = ⌜id⌝′ V

\end{code}
\begin{spec}
%TODO: INLINE pragma!
\end{spec}


%if False
\begin{code}
{-# INLINE ⌜id⌝ #-}
\end{code}
%endif

To complete these proofs, we also need beta-laws about our initial CwF
substitutions, so we derive these now.

\begin{code}
zero[]ᴵ : zeroᴵ [ δᴵ ,ᴵ tᴵ ]ᴵ ≡ tᴵ
zero[]ᴵ {δᴵ = δᴵ} {tᴵ = tᴵ} =
  zeroᴵ [ δᴵ ,ᴵ tᴵ ]ᴵ
  ≡⟨ sym π₁∘ᴵ ⟩
  π₁ᴵ (idᴵ ∘ᴵ (δᴵ ,ᴵ tᴵ))
  ≡⟨ cong π₁ᴵ id∘ᴵ ⟩
  π₁ᴵ (δᴵ ,ᴵ tᴵ)
  ≡⟨ ▷-β₁ᴵ ⟩
  tᴵ ∎

suc[]ᴵ : sucᴵ tᴵ B [ δᴵ ,ᴵ uᴵ ]ᴵ ≡ tᴵ [ δᴵ ]ᴵ
suc[]ᴵ {tᴵ = tᴵ} {B = B} {δᴵ = δᴵ} {uᴵ = uᴵ} =
  sucᴵ tᴵ B [ δᴵ ,ᴵ uᴵ ]ᴵ
  ≡⟨ [∘]ᴵ ⟩
  tᴵ [ wkᴵ ∘ᴵ δᴵ ,ᴵ uᴵ ]ᴵ
  ≡⟨ cong (tᴵ [_]ᴵ) (sym π₀∘ᴵ) ⟩
  tᴵ [ π₀ᴵ (idᴵ ∘ᴵ (δᴵ ,ᴵ uᴵ)) ]ᴵ
  ≡⟨ cong (λ ρ → tᴵ [ π₀ᴵ ρ ]ᴵ) id∘ᴵ ⟩
  tᴵ [ π₀ᴵ (δᴵ ,ᴵ uᴵ) ]ᴵ
  ≡⟨ cong (tᴵ [_]ᴵ) ▷-β₀ᴵ ⟩
  tᴵ [ δᴵ ]ᴵ ∎ 

,[]ᴵ : (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ ≡ (δᴵ ∘ᴵ σᴵ) ,ᴵ (tᴵ [ σᴵ ]ᴵ)
,[]ᴵ {δᴵ = δᴵ} {tᴵ = tᴵ} {σᴵ = σᴵ} =
  (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ
  ≡⟨ sym (▷-ηᴵ {δᴵ = (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ}) ⟩
  π₀ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong (_,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)) π₀∘ᴵ ⟩
  (π₀ᴵ (δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong (λ ρ → (ρ ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)) ▷-β₀ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ π₁ᴵ ((δᴵ ,ᴵ tᴵ) ∘ᴵ σᴵ)
  ≡⟨ cong ((δᴵ ∘ᴵ σᴵ) ,ᴵ_) π₁∘ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ (π₁ᴵ (δᴵ ,ᴵ tᴵ) [ σᴵ ]ᴵ)
  ≡⟨ cong (λ ρ → (δᴵ ∘ᴵ σᴵ) ,ᴵ (ρ [ σᴵ ]ᴵ)) ▷-β₁ᴵ ⟩
  (δᴵ ∘ᴵ σᴵ) ,ᴵ (tᴵ [ σᴵ ]ᴵ) ∎
\end{code}

We also need a couple lemmas about how |⌜_⌝| ignores sort coercions.

\begin{code}
⌜⊑⌝ : ∀ {x : Γ ⊢[ q ] A} → ⌜ tm⊑ ⊑t x ⌝ ≡ ⌜ x ⌝
⌜⊑⌝ {q = V} = refl
⌜⊑⌝ {q = T} = refl

⌜⊑⌝* : ⌜ tm*⊑ ⊑t xs ⌝* ≡ ⌜ xs ⌝*
⌜⊑⌝* {xs = ε} = refl
⌜⊑⌝* {xs = xs , x} = cong₂ _,ᴵ_ ⌜⊑⌝* (⌜⊑⌝ {x = x})
\end{code}

We can now (finally) proceed with the proofs:

\begin{code}
⌜[]⌝ {x = zero} {ys = ys , y} = sym (zero[]ᴵ {δᴵ = ⌜ ys ⌝*})
⌜[]⌝ {x = suc i B} {ys = ys , y} =
  ⌜ i [ ys ] ⌝
  ≡⟨ ⌜[]⌝ {x = i} ⟩
  ⌜ i ⌝ [ ⌜ ys ⌝* ]ᴵ
  ≡⟨ sym suc[]ᴵ ⟩
  sucᴵ ⌜ i ⌝ B [ ⌜ ys ⌝* ,ᴵ ⌜ y ⌝ ]ᴵ ∎
⌜[]⌝ {x = ` i} {ys = ys} = 
  ⌜ tm⊑ ⊑t (i [ ys ]) ⌝
  ≡⟨ ⌜⊑⌝ {x = i [ ys ]} ⟩
  ⌜ i [ ys ] ⌝
  ≡⟨ ⌜[]⌝ {x = i} ⟩
  ⌜ i ⌝ [ ⌜ ys ⌝* ]ᴵ ∎
⌜[]⌝ {x = t · u} {ys = ys} = 
  ⌜ t [ ys ] ⌝ ·ᴵ ⌜ u [ ys ] ⌝
  ≡⟨ cong₂ _·ᴵ_ (⌜[]⌝ {x = t}) (⌜[]⌝ {x = u}) ⟩
  ⌜ t ⌝ [ ⌜ ys ⌝* ]ᴵ ·ᴵ ⌜ u ⌝ [ ⌜ ys ⌝* ]ᴵ
  ≡⟨ sym ·[]ᴵ ⟩
  (⌜ t ⌝ ·ᴵ ⌜ u ⌝) [ ⌜ ys ⌝* ]ᴵ ∎
⌜[]⌝ {x = ƛ t} {ys = ys} = 
  ƛᴵ ⌜ t [ ys ^ _ ] ⌝
  ≡⟨ cong ƛᴵ_ (⌜[]⌝ {x = t}) ⟩
  ƛᴵ ⌜ t ⌝ [ ⌜ ys ^ _ ⌝* ]ᴵ
  ≡⟨ cong (λ ρ → ƛᴵ ⌜ t ⌝ [ ρ ]ᴵ) ⌜^⌝ ⟩
  ƛᴵ ⌜ t ⌝ [ ⌜ ys ⌝* ^ᴵ _ ]ᴵ
  ≡⟨ sym ƛ[]ᴵ ⟩
  (ƛᴵ ⌜ t ⌝) [ ⌜ ys ⌝* ]ᴵ ∎

⌜^⌝ {q = q} = cong₂ _,ᴵ_ ⌜⁺⌝ (⌜zero⌝ {q = q})

⌜⁺⌝ {xs = ε} = sym •-ηᴵ
⌜⁺⌝ {xs = xs , x} {A = A} = 
  ⌜ xs ⁺ A ⌝* ,ᴵ ⌜ suc[ _ ] x A ⌝
  ≡⟨ cong₂ _,ᴵ_ ⌜⁺⌝ (⌜suc⌝ {x = x}) ⟩
  (⌜ xs ⌝* ∘ᴵ wkᴵ) ,ᴵ (⌜ x ⌝ [ wkᴵ ]ᴵ)
  ≡⟨ sym ,[]ᴵ ⟩
  (⌜ xs ⌝* ,ᴵ ⌜ x ⌝) ∘ᴵ wkᴵ ∎

⌜id⌝′ {Γ = •} _ = sym •-ηᴵ
⌜id⌝′ {Γ = Γ ▷ A} _ = 
  ⌜ id ⁺ A ⌝* ,ᴵ zeroᴵ
  ≡⟨ cong (_,ᴵ zeroᴵ) ⌜⁺⌝ ⟩
  ⌜ id ⌝* ^ᴵ A
  ≡⟨ cong (_^ᴵ A) ⌜id⌝ ⟩
  idᴵ ^ᴵ A
  ≡⟨ cong (_,ᴵ zeroᴵ) id∘ᴵ ⟩
  wkᴵ ,ᴵ zeroᴵ
  ≡⟨ ▷-ηᴵ ⟩
  idᴵ ∎

⌜suc⌝ {q = V} = refl
⌜suc⌝ {q = T} {x = t} {B = B} =
  ⌜ t [ id ⁺ B ] ⌝
  ≡⟨ ⌜[]⌝ {x = t} ⟩
  ⌜ t ⌝ [ ⌜ id ⁺ B ⌝* ]ᴵ
  ≡⟨ cong (⌜ t ⌝ [_]ᴵ) ⌜⁺⌝ ⟩
  ⌜ t ⌝ [ ⌜ id ⌝* ∘ᴵ wkᴵ ]ᴵ
  ≡⟨ cong (λ ρ → ⌜ t ⌝ [ ρ ∘ᴵ wkᴵ ]ᴵ) ⌜id⌝ ⟩
  ⌜ t ⌝ [ idᴵ ∘ᴵ wkᴵ ]ᴵ
  ≡⟨ cong (⌜ t ⌝ [_]ᴵ) id∘ᴵ ⟩
  ⌜ t ⌝ [ wkᴵ ]ᴵ ∎
\end{code}

We also prove preservation of substitution composition.

\begin{code}
⌜∘⌝ : ⌜ xs ∘ ys ⌝* ≡ ⌜ xs ⌝* ∘ᴵ ⌜ ys ⌝*
⌜∘⌝ {xs = ε} = sym •-ηᴵ
⌜∘⌝ {xs = xs , x} {ys = ys} = 
  ⌜ xs ∘ ys ⌝* ,ᴵ ⌜ x [ ys ] ⌝
  ≡⟨ cong₂ _,ᴵ_ ⌜∘⌝ (⌜[]⌝ {x = x}) ⟩
  (⌜ xs ⌝* ∘ᴵ ⌜ ys ⌝*) ,ᴵ (⌜ x ⌝ [ ⌜ ys ⌝* ]ᴵ)
  ≡⟨ sym ,[]ᴵ ⟩
  (⌜ xs ⌝* ,ᴵ ⌜ x ⌝) ∘ᴵ ⌜ ys ⌝* ∎
\end{code}

The main cases of |Branches compl-𝕄| can now be proved by just applying the 
preservation lemmas and the IHs.

%if False
\begin{code}
duip : ∀ {A B : Set ℓ} {x y : A} {z w : B} {p q} {r : (x ≡ y) ≡ (z ≡ w)}
      → p ≡[ r ]≡ q
duip {p = refl} {q = refl} {r = refl} = refl
\end{code}
%endif

\begin{code}
compl-𝔹 : Branches compl-𝕄
compl-𝔹 .idᴱ = 
  ⌜ tm*⊑ v⊑t id ⌝*
  ≡⟨ ⌜⊑⌝* ⟩
  ⌜ id ⌝*
  ≡⟨ ⌜id⌝ ⟩
  idᴵ ∎
compl-𝔹 ._∘ᴱ_ {σᴵ = σᴵ} {δᴵ = δᴵ} σᴱ δᴱ = 
  ⌜ norm* σᴵ ∘ norm* δᴵ ⌝*
  ≡⟨ ⌜∘⌝ ⟩
  ⌜ norm* σᴵ ⌝* ∘ᴵ ⌜ norm* δᴵ ⌝*
  ≡⟨ cong₂ _∘ᴵ_ σᴱ δᴱ ⟩
  σᴵ ∘ᴵ δᴵ ∎
compl-𝔹 ._[_]ᴱ {tᴵ = tᴵ} {δᴵ = δᴵ} tᴱ δᴱ = 
  ⌜ norm tᴵ [ norm* δᴵ ] ⌝
  ≡⟨ ⌜[]⌝ {x = norm tᴵ} ⟩
  ⌜ norm tᴵ ⌝ [ ⌜ norm* δᴵ ⌝* ]ᴵ
  ≡⟨ cong₂ _[_]ᴵ tᴱ δᴱ ⟩
  tᴵ [ δᴵ ]ᴵ ∎
compl-𝔹 .•ᴱ = tt
compl-𝔹 .εᴱ = refl
compl-𝔹 ._▷ᴱ_ _ _ = tt
compl-𝔹 ._,ᴱ_ δᴱ tᴱ = cong₂ _,ᴵ_ δᴱ tᴱ
compl-𝔹 .π₀ᴱ {δᴵ = δᴵ} δᴱ = 
  ⌜ π₀ (norm* δᴵ) ⌝*
  ≡⟨ ⌜π₀⌝ ⟩
  π₀ᴵ ⌜ norm* δᴵ ⌝*
  ≡⟨ cong π₀ᴵ δᴱ ⟩
  π₀ᴵ δᴵ ∎
compl-𝔹 .π₁ᴱ {δᴵ = δᴵ} δᴱ = 
  ⌜ π₁ (norm* δᴵ) ⌝
  ≡⟨ ⌜π₁⌝ ⟩
  π₁ᴵ ⌜ norm* δᴵ ⌝*
  ≡⟨ cong π₁ᴵ δᴱ ⟩
  π₁ᴵ δᴵ ∎
compl-𝔹 .oᴱ = tt
compl-𝔹 ._⇒ᴱ_ _ _ = tt
compl-𝔹 ._·ᴱ_ tᴱ uᴱ = cong₂ _·ᴵ_ tᴱ uᴱ
compl-𝔹 .ƛᴱ_ tᴱ = cong (ƛᴵ_) tᴱ
\end{code}

The remaining cases correspond to the CwF equations, which are required to hold 
for whatever type family we eliminate the initial CwF into so congruence of 
|_≡_| is retained. For our completeness proof, all of these cases become
higher-dimensional identities, equating different proof trees for completeness
instantiated with the LHS/RHS terms/substitutions. 

In a univalent type theory we might try and carefully introduce additional 
coherences to our initial CwF to try and make these identities provable without 
the sledgehammer of set truncation (which would prevent eliminating the initial 
CwF into any non-set).

As we are working in vanilla Agda, we'll take a simpler approach, and rely on 
UIP.

\begin{spec}
duip : ∀ {A B : Set ℓ} {x y : A} {z w : B} {p q} {r : (x ≡ y) ≡ (z ≡ w)}
      → p ≡[ r ]≡ q
duip {p = refl} {q = refl} {r = refl} = refl
\end{spec}

It is probably worth noting that this implementation of (dependent) UIP relies 
on type constructor injectivity (specifically, injectivity of |_≡_|). 
We could use a weaker version which takes an additional proof of |x ≡ z| 
instead, but this would be clunkier to use; Agda has no hope of inferring such a
proof by unification.

\begin{code}
compl-𝔹 .id∘ᴱ  = duip
compl-𝔹 .∘idᴱ  = duip
compl-𝔹 .∘∘ᴱ   = duip
compl-𝔹 .[id]ᴱ = duip
compl-𝔹 .[∘]ᴱ  = duip
compl-𝔹 .•-ηᴱ  = duip
compl-𝔹 .▷-β₀ᴱ = duip
compl-𝔹 .▷-β₁ᴱ = duip
compl-𝔹 .▷-ηᴱ  = duip
compl-𝔹 .π₀∘ᴱ  = duip
compl-𝔹 .π₁∘ᴱ  = duip
compl-𝔹 .·[]ᴱ  = duip
compl-𝔹 .ƛ[]ᴱ  = duip
\end{code}

And completeness is just call to the eliminator away.

\begin{code}
compl : ⌜ norm tᴵ ⌝ ≡ tᴵ
compl {tᴵ = tᴵ} = elim-cwf compl-𝔹 tᴵ
\end{code}
 