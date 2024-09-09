\documentclass[sigplan,10pt,anonymous,review]{acmart}\settopmatter{printfolios=true,printccs=false,printacmref=false}
%\usepackage{tipa}
%\usepackage{fontspec}
\let\Bbbk\relax % to avoid conflict
%include lhs2TeX.fmt
%include agda.fmt
%include lib.fmt

%if False
\begin{code}
{-# OPTIONS --rewriting #-}
module paper where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

--infix   3  _∋_
--infix   3  _⊢_
infix   3  _⊢[_]_
infix   3  _⊨[_]_
infixl  4  _▷_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixr  6  _⇒_
infixl  6  _·_
infix   7  `_
infix   8  _^_
infix   8  _⁺_
infix   8  _[_]
\end{code}
%endif


\title{Substitution without cut and paste}

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
\email{nathaniel.burke21@imperial.ac.uk}

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

The first author was writing lecture notes for an introduction to
category theory for functional programmers. A nice example of a
category is the category of simply typed $\lambda$-terms and
substitutions hence it seemed a good idea to give the definition and
ask the students to prove the category laws. When writing the answer
they realised that it  is not as easy as they thought. To make sure that
there are no mistakes they started to formalize the problem in agda.
Now this wasn't as easy as they thought but the main setback was that the
same proofs got repeated many times. If there is one guideline of good
software engineering then it is \textbf{Do not write code by copy and
  paste} and this applies even more so to formal proofs.

This paper is the result of the effort to refactor the proof. We think
that the method used is interesting also for other problems, in
particular the current construction can be seen as a warmup for the
recursive definition of substitution for dependent type theory which
may have interesting applications for the coherence problem,
i.e. interpreting dependent types in higher categories. 

\subsection{Related work}
\label{sec:related-work}

In \cite{alti:csl99} the problem of showing termination of a simple
definition of substitution (for the untyped $\lambda$-calculus) is
adressed using a well-founded recursion. However, this is only applied
to the definition and the categorical laws (which follow from the
monad laws) were not formally verified. Also the present approach
seems to be simpler and scales better avoiding well-founded recursion.
The monadic approach has been further investigated in \cite{mcbride2006type}. The
structure of the proofs is explained in \cite{allais2017type} from a
monadic perspective. Indeed this example is one of the motivations for
relative monads \cite{altenkirch2015monads}.

We avoid the monadic perspective here for two reasons: first we want
to give a simple self-contained proof avoiding too much advanced
categorical constructions as mentioned in the introduction as a
motivation; second we are interested in the application to dependent
types where it is not clear how the monadic approach can be applied
without using very dependent types.

\subsection{Using agda}
\label{sec:using-agda}

For the technical details of agda we refer to the online documentation
\cite{agda}. We only use plain agda and inductive definitions and
structurally recursive programs and proofs.  Termination is checked by
agda's termination checker \cite{alti:jfp02} which uses a lexical
combination of structural descent which is inferred by the termination
checker by investigating all possible recursive paths. We will define
mutually recursive proofs which heavily rely on each other.

The only recent
feature we use even though sparingly is the possibility to turn
equations into rewriting rules (i.e. definitional equalities). This
makes the statement of some theorems more readable because we can avoid
using |subst| but this is not essential.

We extensively use variable declarations to introduce implicit
quantification (we summarize the variables conventions in passing in
the text). Implicit variables can be instantiated using the syntax
|a{x = b}| which we use in the proofs. Agda syntax is very flexible
allowing general syntax declarations using |_| to indicate where the
parameters go.

In the proofs we also use agda's syntax for equational derivations,
which exploiting agda's general syntax is just an ordinary agda
definition in the standard library.

The source of this document contains the actual agda code, i.e. it is a
literate agda file. Some parts of the displayed code are not checked,
e.g. most of section \ref{sec:naive-approach} to avoid clashes. 

\section{The naive approach}
\label{sec:naive-approach}

Let us first review the naive approach which leads to the
copy-and-paste proof. We define types (|A,B,C|) and contexts (|Γ , Δ ,
Θ|):
\begin{code}
data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

data Con : Set where
  • : Con
  _▷_ : Con → Ty → Con
\end{code}
%if False
\begin{code}
variable
  A B C : Ty
  Γ Δ Θ : Con  
\end{code}
%endif

Next we introduce intrinsically typed de Bruijn variables (|i,j,k|) and
$\lambda$-terms (|t,u,v|) :
\begin{spec}
data _∋_ : Con → Ty → Set where 
  zero : Γ ▷ A ∋ A
  suc  : Γ ∋ A → (B : Ty) → Γ ▷ B ∋ A
  
data _⊢_ : Con → Ty → Set where 
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
\end{spec}
Here the constructor |`_| corresponds to \emph{variables are
  $\lambda$-terms}; we write applications as |t  · u|, since we use de
Bruijn variables lambda abstraction |ƛ_| doesn't use a name but
refers to the variable |zero|. We also define substitutions as
sequences of terms:
\begin{spec}
data _⊨_ : Con → Con → Set where
  ε   : Γ ⊨ •
  _,_ : Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ Δ , A  
\end{spec}
Now to define the categorical structure (|_∘_|,|id|) we first need to define
substitution for terms and variables:
\begin{spec}
_v[_] : Γ ∋ A → Δ ⊨ Γ → Δ ⊢ A
zero    v[ ts , t ]    =  t
(suc i _) v[ ts , t ]  =  i v[ ts ]


_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
(ƛ t)   [ ts ]       =  ƛ ?
\end{spec}
As usual we have a problem with the binder |ƛ_| we are given a
substitution |ts : Δ ⊨ Γ| but our term lives in the extended context
|t : Γ , A ⊢ B|. We need to exploit the fact that context extension
|_▷_| is functorial:
\begin{spec}
_^_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ ▷ A
\end{spec}
Using |_^_| we can complete |_[_]|
\begin{spec}
  (ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])
\end{spec}
However, now we have to define |_^_|. This is easy, isn't it but we
need weakening on substitutions:
\begin{spec}
_⁺_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ
\end{spec}
And now we can define |_^_|:
\begin{spec}
ts ^ A = ts ⁺ A , ` zero 
\end{spec}
but we need to define |_⁺_ | which is nothing but a fold of weakening
of terms
\begin{spec}
suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B

ε         ⁺ A  = •
(ts , t)  ⁺ A  = ts ⁺ A , suc-tm t A  
\end{spec}
But how to define |suc-tm| we only have weakening for variables? If we
already had identity and substitution we could say:
\begin{spec}
suc-tm t A = t [ suc-tm* id A ] 
\end{spec}
but this is certainly not structurally recursive (and hence rejected
by agda's termination checker).

Actually we realize that |id| is a renaming, i.e. it is a substitution
only containing variables and we can easily define |suc*| for
renamings. This leads to a structurally recursive definition but we
also have to repeat the definition of substitutions for renamings.

This may not sound too bad to obtain structural termination we have to
duplicate a definition but it gets even worse when proving the
laws. To prove associativity we need to prove functoriality of
substitution first:
\begin{spec}
[∘] : t [ us ∘ vs ] ≡ t [ us ] [ vs ]
\end{spec}
Since |t , us , vs| can be variables/renamings or terms/substitutions
there are in principle 8 combinations of which we need 5. And each
time we need to prove a number of lemmas again in a different
setting.

In the rest of the paper we describe a technique how this proof can be
factored only relying on the agda termination checker to validate that
the recursion is structurally terminating.

\section{Factorising with sorts}
\label{sec:fact-with-sorts}

Our main idea is that we have to turn the distinction between
variables and terms into a parameter. The first approximation is to
define a type |Sort| (|q , r , s|) :
\begin{spec}
data Sort : Set where
   V T : Sort  
 \end{spec}
but this is not exactly what we want because we want agda to know that
the sort of variables |V| is \emph{easier} that the sort of terms
|T|. Agda's termination checker only knows about the structural
ordering of an inductive type, and with the following definition we
can make |V| structurally smaller than |T| maintaining that |V| and
|T| are the only elements of |Sort|.
\begin{code}
data Sort : Set 
data IsV : Sort → Set
data Sort where
  V : Sort
  T>V : (s : Sort) → IsV s → Sort
data IsV where
  isV : IsV V
\end{code}
%if False
\begin{code}
variable
  q r s    : Sort
\end{code}
%endif

Here the predicate |isV| only holds for |V|. We can avoid this mutual
definition by using equality |_≡_|.

We can now define |T : Sort| but even better we can tell agda that
this is a derived pattern
\begin{code}
pattern T = T>V V isV
\end{code}
this means we can pattern match over |Sort| just with |V| and |T|,
which are indeed the only elements of |Sort| but now |V| is
structurally smaller than |T|.

We can now define terms and variables in one go (|x , y , z|) ~:
\begin{code}
data _⊢[_]_ : Con → Sort → Ty → Set where
  zero : Γ ▷ A ⊢[ V ] A
  suc  : Γ  ⊢[ V ]  A → (B : Ty) → Γ ▷ B  ⊢[ V ]  A
  `_   : Γ  ⊢[ V ]  A → Γ  ⊢[ T ]  A
  _·_  : Γ ⊢[ T ] A ⇒ B → Γ ⊢[ T ] A → Γ ⊢[ T ] B
  ƛ_   : Γ ▷ A ⊢[ T ] B → Γ ⊢[ T ] A ⇒ B
\end{code}

While almost identical to the previous definition (|Γ ⊢[ V ] A| corresponds to
|Γ ∋ A| and |Γ  ⊢[ T ]  A| to |Γ ⊢ A|)
we can now
parametrize all definitions and theorems explicitly. As a first step
we can generalize renamings and substitutions (|xs , ys , zs|):
\begin{code}
data _⊨[_]_ : Con → Sort → Con → Set where
  ε   : Γ ⊨[ q ] •
  _,_ : Γ ⊨[ q ] Δ → Γ ⊢[ q ] A → Γ ⊨[ q ] Δ ▷ A  
\end{code}
%if False
\begin{code}
variable
  i j k    : Γ ⊢[ V ] A
  t u v    : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  xs ys zs : Γ ⊨[ q ] Δ  
\end{code}
%endif

To account for the non-uniform behaviour of substitution and
composition (the result is |V| only of both inputs are |V|) we define
a least upper bound on |Sort|:
\begin{code}
_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T
\end{code}
We also need the order to insert a coercion when necessary:
\begin{code}
data _⊑_ : Sort → Sort → Set where
  rfl : s ⊑ s
  v⊑t : V ⊑ T
\end{code}
Yes, this is just boolean algebra. We need a number of laws:
\begin{code}
⊑t : s ⊑ T
v⊑ : V ⊑ s
⊑q⊔ : q ⊑ (q ⊔ r)
⊑⊔r : r ⊑ (q ⊔ r)
⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔v : q ⊔ V ≡ q
\end{code}
which are easy to prove by case analysis, e.g.
\begin{code}
⊑t {V} = v⊑t
⊑t {T} = rfl
\end{code}
%if False
\begin{code}
v⊑ {V} = rfl
v⊑ {T} = v⊑t

⊑q⊔ {V} = v⊑
⊑q⊔ {T} = rfl

⊑⊔r {q = V} = rfl
⊑⊔r {q = T} = ⊑t

⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v {V} = refl
⊔v {T} = refl

{-# REWRITE ⊔⊔ ⊔v  #-}
\end{code}
%endif

To improve readability we turn the equations  (|⊔⊔| , |⊔v|) into rewrite rules. 
The order gives rise to a functor which is witnessed by
\begin{code}
tm⊑ : q ⊑ s → Γ ⊢[ q ] A → Γ ⊢[ s ]  A
tm⊑ rfl x = x
tm⊑ v⊑t i = ` i
\end{code}
Using a parametric version of |_^_|
\begin{code}
_^_ : Γ ⊨[ q ] Δ → ∀ A → Γ ▷ A ⊨[ q ] Δ ▷ A   
\end{code}
we are ready to define substitution and renaming in one operation
\begin{code}
_[_] : Γ ⊢[ q ] A → Δ ⊨[ r ] Γ → Δ ⊢[ q ⊔ r ] A
  
zero    [ xs , x ]   =  x
(suc i _) [ xs , x ] =  i [ xs ]
(` i)   [ xs ]       =  tm⊑  ⊑t  (i [ xs ])
(t · u) [ xs ]       =  (t [ xs ]) · (u [ xs ])
(ƛ t)   [ xs ]       =  ƛ (t [ xs ^ _ ]) 
\end{code}
To take care of the fact that substitution will only return a variable
if both inputs are variables / renamings we use |_⊔_| here. We alo
need to use |tm⊑| to take care of the two cases when substituting for
a variable. We can also define |id| using |_^_|:
\begin{code}
id : Γ ⊨[ q ] Γ
id {Γ = •}     =  ε
id {Γ = Γ ▷ A} =  id ^ A
\end{code}
To define |_^_| we need parametric versions of |zero|, |suc| and
|suc*|. |zero| is very easy:

\begin{code}
zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ]      =  zero
zero[ T ]      =  ` zero
\end{code}

However, |suc| is more subtle since the case for |T| depends on its
fold for substitutions (|_⁺_|):
\begin{code}
_⁺_ : Γ ⊨[ q ] Δ → (A : Ty) → Γ ▷ A ⊨[ q ] Δ

suc[_] :  ∀ q → Γ ⊢[ q ] B → (A : Ty) → Γ ▷ A ⊢[ q ] B
suc[ V ] i  A   =  suc i A
suc[ T ] t  A   =  t [ id {q = V} ⁺  A ]

ε ⁺ A = ε
(xs , x) ⁺ A = xs ⁺ A , suc[ _ ] x A 
\end{code}
And now we define:
\begin{code}
xs ^ A                 =  xs ⁺ A , zero[ _ ]
\end{code}

Finally, we define composition by folding substitution:
\begin{code}
_∘_ : Γ ⊨[ q ] Θ → Δ ⊨[ r ] Γ → Δ ⊨[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
\end{code}

Clearly, the definitions are very recursive and exploits the structural
ordering on terms and the order on sorts. We can leave the details to
the termination checker.

\section{Proving the laws}
\label{sec:proving-laws}

We now present a formal proof of the categorical laws proving each
lemma only once and we only use structural recursion. Indeed the
termination isn't completely trivial but inferred by the termination
checker.

\subsection{The left identity law}
\label{sec:left-identity-law}

Let's get the easy case out of the way : this is identity left (|xs ∘
id ≡ xs|). It is easy because it doesn't depend on any other
property.

The main lemma is the identity law for the substitution functor:
\begin{code}
[id] : x [ id {q = V} ] ≡ x
\end{code}
To prove the successor case we need naturality of |suc[ q ]| but here
only in the case where the term is a variable which can be shown by a
simple induction over the variable:
% ⁺-nat[]v : {i : Γ  ⊢[ V ] B}{xs : Δ ⊨[ q ] Γ}
%   → i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
\begin{code}
⁺-nat[]v : i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
⁺-nat[]v {i = zero}      {xs = xs , x} = refl
⁺-nat[]v {i = suc j A}  {xs = xs , _} = ⁺-nat[]v {i = j}
\end{code}

The identity law is now easily provable by structural induction:

\begin{code}
[id] {x = zero} = refl
[id] {x = suc i A} = 
   i [ id ⁺ A ] 
   ≡⟨ ⁺-nat[]v {i = i} ⟩
   suc (i [ id ]) A
   ≡⟨ cong (λ j → suc j A) ([id] {x = i}) ⟩      
   suc i A ∎
[id] {x = ` i} =
   cong `_ ([id] {x = i})
[id] {x = t · u} =
   cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {x = ƛ t} =
   cong ƛ_ ([id] {x = t})
\end{code}
Note that the |ƛ_|-case is easy here: we need the law for
|t :  Γ , A ⊢[ T ] B| but this is just another instance because
|id {Γ = Γ , A}  =  id ^ A|.

This is the first time we use Agda's syntax for equational derivations
which is just syntactic sugar for constructing an equational
derivation using transitivity and reflexivity exploiting Agda's
flexible syntax. Here |e ≡⟨ p ⟩ e'| means that |p| is the proof that
|e ≡ e'|. Later we will also use the special case |e ≡⟨⟩ e'| which
means that |e| and |e'| are definitionally equal (this corresponds to
|e ≡⟨ refl ⟩ e'|), this is just used to make the proof more
readable.  The proof is terminated with |∎| which inserts |refl|.
We use the congruence proof |cong f : a ≡ b → f a ≡ f b|
and a version for binary functions
|cong₂ g : a ≡ b → c ≡ d → g a c ≡ g b d|.

The category law now is a fold of the functor law:
\begin{code}
∘id : xs ∘ (id {q = V}) ≡ xs
∘id {xs = ε}         = refl
∘id {xs = xs , x}  =
   cong₂ _,_ (∘id {xs = xs}) ([id] {x = x})
\end{code}

\subsection{Right identity}
\label{sec:right-ident}

We need to prove the right identity law mutually with the second
functor law for substitution which is the main lemma for
associativity. 

Let's state the functor law but postpone the proof to the next section

\begin{code}
[∘] :
  {x : Θ ⊢[ q ] A}{xs : Γ ⊨[ r ] Θ}{ys : Δ ⊨[ s ] Γ}
  → x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]
\end{code}
This actually uses the strict equality
\footnote{We use agda's rewrite here.
Alternatively we would have to insert a transport using |subst|.}
\begin{spec}
 ⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
\end{spec}
because the left hand side has the type
\begin{spec}
Δ ⊢[  q ⊔ (r ⊔ s) ] A
\end{spec}
while the right hand side has type
\begin{spec}
Δ ⊢[  (q ⊔ r) ⊔ ) ] A.
\end{spec}

% actually the coercion wouldn't be necessary if we restrict to
%|id {q = V}| but this seems to break the proof?
We also need to adopt the left identity law because given
|xs : Γ ⊨[ r ] Δ| the left hand side has a different type
\begin{spec}
(id {q = q}) ∘ xs :  Γ ⊨[ q ⊔ r ] Δ 
\end{spec}
We use the extension of |tm⊑|
to substitutions:
\begin{code}
tm*⊑ : q ⊑ s → Γ ⊨[ q ] Δ → Γ ⊨[ s ] Δ
\end{code}
%if False
\begin{code}
tm*⊑ q⊑s ε = ε
tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x
\end{code}
%endif
and |⊑⊔r : r ⊑ (q ⊔ r| to state the law:
\begin{code}
id∘ : {xs : Γ ⊨[ r ] Δ}
  → (id {q = q}) ∘ xs ≡ tm*⊑ (⊑⊔r {q = q}) xs
\end{code}
To prove it we need the $\beta$-laws for |zero[_]| and |_⁺_|:
\begin{code}
zero[] : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x 
⁺∘ : xs ⁺ A  ∘ (ys , x) ≡ xs ∘ ys
\end{code}
Now |id∘| can be shown easily:
\begin{code}
id∘ {xs = ε} = refl
id∘ {q = q} {xs = xs , x} = cong₂ _,_ (
   id ⁺ _ ∘ (xs , x)
     ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs
     ≡⟨ id∘ {xs = xs} ⟩
   tm*⊑ (⊑⊔r {q = q}) xs ∎)
   (zero[] {q = q})
\end{code}

Now we show the $\beta$-laws. |zero[]| is just a simple case analysis over the sort
%if False
\begin{code}
zero[] {q = V} = refl
zero[] {q = T} = refl
\end{code}
%endif
while |suc*∘| relies on a corresponding property for substitution:
\begin{code}
suc[] : {ys : Γ ⊨[ r ] Δ}
    → (suc[ q ] x _) [ ys , y ] ≡ x [ ys ] 
\end{code}
%if False
\begin{code}
tm*rfl : {q⊑q : q ⊑ q} → tm*⊑ q⊑q xs ≡ xs
tm*rfl {xs = ε} {q⊑q = rfl} = refl
tm*rfl {xs = xs , x} {q⊑q = rfl} = cong₂ _,_ (tm*rfl {xs = xs}) refl
\end{code}
%endif

The case for |q = V| is just definitional:
\begin{code}
suc[] {q = V} = refl
\end{code}
while |q = T| is surprisingly complicated and in particular relies on the functor law |[∘]|
and the first functor law for |tm*⊑|: |tm*rfl : {q⊑q : q ⊑ q} → tm*⊑ q⊑q xs ≡ xs|:

\begin{code}
suc[] {q = T} {x = x} {y = y} {ys = ys} =
  (suc[ T ] x _) [ ys , y ]
  ≡⟨⟩
  x [(id {q = V}) ⁺ _ ] [ ys , y ]
  ≡⟨ sym ([∘] {x = x}) ⟩
  x [ ((id {q = V}) ⁺ _) ∘  (ys , y) ]
  ≡⟨ cong (λ ρ → x [ ρ ]) ⁺∘  ⟩
  x [ (id {q = V}) ∘  ys  ]
  ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
  x [ tm*⊑ (⊑⊔r {q = V}) ys ]
  ≡⟨ cong (λ ρ → x [ ρ ]) tm*rfl ⟩
  x [ ys ]  ∎
\end{code}
Now the $\beta$-law |⁺∘| is just a simple fold. You may note that
|⁺∘| relies on itself  but on an easier instance in the ordering of
sorts.  It also uses |id∘| and |[∘]| which recursively use it.
%if False
\begin{code}
⁺∘ {xs = ε} = refl
⁺∘ {xs = xs , x} = cong₂ _,_ (⁺∘ {xs = xs}) (suc[] {x = x})
\end{code}
%endif

\subsection{Associativity}
\label{sec:associativity}
We finally get to the proof of the 2nd functor law
(|[∘] : x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]|) which is the main lemma for
associativity. The main obstacle is that for the |ƛ_| case we need the
second functor law for context extension:
\begin{code}
^∘ :  {xs : Γ ⊨[ r ] Θ}{ys : Δ ⊨[ s ] Γ}{A : Ty}
      → (xs ∘ ys) ^ A ≡ (xs ^ A) ∘ (ys ^ A)
\end{code}
To verify the variable case we also need that |tm| commutes with substitution,
which is easy to prove by case analysis
\begin{spec}
tm[] : tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]
\end{spec}
%if False
\begin{code}
tm[] : {x : Θ ⊢[ q ] A}{xs : Γ ⊨[ r ] Θ}
     → tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]
tm[] {q = V} = refl
tm[] {q = T} = refl
\end{code}
%endif
We are now ready to prove |[∘]| by structural induction:
\begin{code}
[∘] {x = zero} {ys , y} = refl
[∘] {x = suc i _} {ys , y} = [∘] {x = i}
[∘] {x = ` x}{xs = xs}{ys = ys} = 
   tm⊑ ⊑t (x [ xs ∘ ys ])
    ≡⟨ cong (tm⊑ ⊑t) ([∘] {x = x}) ⟩
   tm⊑ ⊑t (x [ xs ] [ ys ])
    ≡⟨ tm[] {x = x [ xs ]} ⟩        
   (tm⊑ ⊑t (x [ xs ])) [ ys ] ∎
[∘] {x = t · u} =
   cong₂ _·_ ([∘] {x = t}) ([∘] {x = u})
[∘] {x = ƛ t}{xs = xs}{ys = ys} =
   cong ƛ_ (
     t [ (xs ∘ ys) ^ _ ]
     ≡⟨ cong (λ zs → t [ zs ]) ^∘  ⟩
     t [ (xs ^ _) ∘ (ys ^ _)  ]
     ≡⟨ [∘] {x = t} ⟩           
     (t [ xs ^ _ ]) [ ys ^ _ ] ∎)
\end{code}
From here we prove associativity by a fold:
\begin{code}
∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs
∘∘ {xs = ε} = refl
∘∘ {xs = xs , x} =
   cong₂ _,_ (∘∘ {xs = xs}) ([∘] {x = x})
\end{code}

However, we are not done yet we still need to prove
the 2nd functor law for |^| (|^∘|). It turns out that this depends on
the naturality of  weakening:
\begin{code}
⁺-nat∘ : xs ∘ (ys ⁺ A) ≡ (xs ∘ ys) ⁺ A  
\end{code}
which unsurprisingly hs to be shown by establishing a corresponding
property for substitution:
\begin{code}
⁺-nat[] : {x : Γ  ⊢[ q ] B}{xs : Δ ⊨[ r ] Γ}
     → x [ xs ⁺ A ] ≡ suc[ _ ] (x [ xs ]) A
\end{code}
The case |q = V| is just the naturality for variables which we have
already proven :
\begin{code}
⁺-nat[] {q = V}{x = i} = ⁺-nat[]v {i = i}
\end{code}
The case for |q = T| is more interesting and relies again on |[∘]| and
|∘id|:
\begin{code}
⁺-nat[] {q = T} {A = A} {x = x} {xs} = 
   x [ xs ⁺ A ]
   ≡⟨ cong (λ zs → x [ zs ⁺ A ]) (sym ∘id) ⟩
   x [ (xs ∘ id {q = V}) ⁺ A ]     
   ≡⟨ cong (λ zs → x [ zs ]) (sym (⁺-nat∘ {xs = xs})) ⟩
   x [ xs ∘ (id ⁺ A) ]   
   ≡⟨ [∘] {x = x} ⟩
   x [ xs ] [ id ⁺ A ] ∎
\end{code}

%if False
\begin{code}
⁺-nat∘ {xs = ε} = refl
⁺-nat∘ {xs = xs , x} =
  cong₂ _,_ (⁺-nat∘ {xs = xs}) (⁺-nat[] {x = x})

tm⊑zero : (q⊑r : q ⊑ r) → zero[_] {Γ = Γ}{A = A} r ≡ tm⊑ q⊑r zero[ q ]
tm⊑zero rfl = refl
tm⊑zero v⊑t = refl
\end{code}
%endif

Finally we have all the ingredients to prove the 2nd functor law |^∘|:
\footnote{Actually we also need that zero commutes with |tm⊑|: that is for any
|q⊑r : q ⊑ r| we have that |tm⊑zero q⊑r : zero[ r ] ≡ tm⊑ q⊑r zero[ q ]|.}
\begin{code}
^∘ {r = r}{s = s}{xs = xs}{ys = ys} {A = A} = 
    (xs ∘ ys) ^ A
    ≡⟨⟩
    (xs ∘ ys) ⁺ A , zero[ r ⊔ s ]    
    ≡⟨ cong₂ _,_ (sym (⁺-nat∘ {xs = xs})) refl ⟩
    xs ∘ (ys ⁺ A) , zero[ r ⊔ s ]
    ≡⟨ cong₂ _,_ refl (tm⊑zero (⊑⊔r {r = s}{q = r})) ⟩        
    xs ∘ (ys ⁺ A) , tm⊑ (⊑⊔r {q = r}) zero[ s ]
    ≡⟨ cong₂ _,_
         (sym (⁺∘ {xs = xs}))
         (sym (zero[] {q = r}{x = zero[ s ]}))  ⟩    
    (xs ⁺ A) ∘  (ys ^ A) , zero[ r ] [ ys ^ A ]
    ≡⟨⟩  
    (xs ^ A) ∘ (ys ^ A) ∎
\end{code}

\section{Initiality}
\label{sec:initiality}

We can do more than just prove that we have got a category, indeed we
can verify the laws of a simply typed category with families
(CwF). CwFs ar mostly known as models of dependent type theory but
they can be specialised to simple types. In a general CwF we have a
category of contexts, a presheaf to model types and a\emph{ dependent
presheaf} over the type presheaf (that is a presheaf over the category
of elements of the type presheaf). In the simply typed case the type
presheaf is constant since the set of types doesn't vary over the
context and the dependent presheaf of terms becomes an ordinary
presheaf over the category of contexts.

We start with a precise definition of a simply typed CwF with
additional structure to model simply typed $\lambda$-calculus (section
\ref{sec:simply-typed-cwfs}) and then we show that the recursive
definition of substitution gives rise to a simply typed CwF (section
\ref{sec:cwf-recurs-subst}). We can define the initial CwF as a
Quotient Inductive Type in cubical agda but to simplify our
development
\footnote{Cubical agda still lacks some essential automatisation,
  eg. integrating no-confusion properties into pattern matching.}
we just postulate the existence of this QIIT in agda (with
the associated rewriting rules). By initiality there is an evaluation
functor form the initial CwF to the recursively defined CwF. On the
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

% using Spec to avoid name clashes. How can we dea with this?
% Another question is how to use variable defs in a record?

We define a record to capture simply typed CWFs:
\begin{spec}
record CwF-simple : Set₁ where
\end{spec}

%if False
\begin{spec}
  infix   3  _⊢_
  infix   3  _⊨_
  infixl  4  _▷_
  infixl  4  _,_
  infix   5  _∘_
  infix   5  ƛ_
  infixr  6  _⇒_
  infixl  6  _·_
  infix   8  _[_]  
\end{spec}
%endif
We start with the category of contexts using the same names as
introduced previously:
\begin{spec}
  field
    Con : Set
    _⊨_ : Con → Con → Set

    id : {Γ : Con} → Γ ⊨ Γ
    _∘_ : {Γ Δ Θ : Con} → Δ ⊨ Θ → Γ ⊨ Δ → Γ ⊨ Θ
    id∘ : ∀ {Γ Δ}{δ : Γ ⊨ Δ} → id ∘ δ ≡ δ
    ∘id : ∀ {Γ Δ}{δ : Γ ⊨ Δ} → δ ∘ id ≡ δ
    ∘∘ : ∀ {Γ Δ Θ Ξ}{ξ : Θ ⊨ Ξ}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)  
\end{spec}
We introduce the set of types and associate a presheaf with each type:
\begin{spec}
    Ty : Set           
    _⊢_ : Con → Ty → Set         
    _[_] : ∀ {Γ Δ A} → Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
    [id] : ∀ {Γ A}{t : Γ ⊢ A} →  (t [ id ]) ≡ t
    [∘] : ∀ {Γ Δ Θ}{A : Ty}{t : Θ ⊢ A}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ} →
            t [ θ ] [ δ ] ≡ t [ θ ∘ δ ] 
\end{spec}
The category of contexts has a terminal object (the empty context):
\begin{spec}
    • : Con
    ε : {Γ : Con} → Γ ⊨ • 
    •-η : {Γ : Con}{δ : Γ ⊨ •} → δ ≡ ε  
\end{spec}
Context extension resembles categorical products but mixing contexts
and types:
\begin{spec}
    _▷_ : Con → Ty → Con
    _,_ : ∀ {Γ Δ A} → Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ (Δ ▷ A)
    π₀ : ∀ {Γ Δ A} → Γ ⊨ (Δ ▷ A) → Γ ⊨ Δ
    π₁ : ∀ {Γ Δ A} → Γ ⊨ (Δ ▷ A) → Γ ⊢ A
    ▷-β₀ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₀ (δ , t) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₁ (δ , t) ≡ t
    ▷-η : ∀ {Γ Δ A}{δ : Γ ⊨ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₁ (θ ∘ δ) ≡ (π₁ θ) [ δ ]  
\end{spec}
We can define the morphism part of the context extension functor as
before:
\begin{spec}
  _^_ : ∀ {Γ Δ} → Γ ⊨ Δ → ∀ A → Γ ▷ A ⊨ Δ ▷ A
  δ ^ A = (δ ∘ (π₀ id)) , π₁ id
\end{spec}
We need to add the specific components for simply typed
$\lambda$-calculus: we add the type constructors and the term
constructors and the corresponding naturality laws:
\begin{spec}
  field
    o : Ty
    _⇒_ : Ty → Ty → Ty
    _·_  : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    ƛ_   : ∀ {Γ A B} → Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
    ·[]  : ∀ {Γ Δ A B}{t : Γ ⊢ A ⇒ B}{u : Γ ⊢ A}{δ : Δ ⊨ Γ}
           → (t · u) [ δ ] ≡ (t [ δ ]) · (u [ δ ])
    ƛ[] :  ∀ {Γ Δ A B}{t : Γ ▷ A ⊢ B}{δ : Δ ⊨ Γ}
           → (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ _ ])  
\end{spec}

\subsection{The CwF of recursive substitutions}
\label{sec:cwf-recurs-subst}

\subsection{Proving initiality}
\label{sec:proving-initiality}

\section{Conclusions and further work}
\label{sec:concl-furth-work}

The subject of the paper is a problem which everybody including
ourselves would have thought to be trivial. As it turns out it isn't
and we are not the only one who noticed this, in
particular if you don't want to prove it using copy-and-paste. 
We spend some time going down alleys that didn't work find clever
parametrisation. In the end with hindsight the main idea seems rather
obvious: introduce sorts as a datatype with the structure of a boolean
algebra. To be able to implement the solution in agda we managed to
convince the termination checker that |V| is structurally smaller than
|T| which means that the actual work determining and verifying the
termination ordering is left to agda. This greatly simplifies the
formal development. In a way one would like to be able to instrument
the termination checker for example with an ordering on
constructors. Also it would be nice if the termination checker
provides evidence that its actual non-trivial reasoning is sound and
can be checked independently. 

This paper can also be seen as a preparation for the harder problem to
implement recursive substitution for dependent types. This is harder
because here the typing oof the constructors actually depends on the
substitution laws. While such a M\"unchhausian \cite{altenkirch2023munchhausen} construction should
actually be possible in agda, the theoretical underpinning of
inductive-inductive-recursive definitions is mostly unexplored (with
the exception of the proposal by \cite{kaposi2023towards}. However, there are
potential interesting applications: strictifying substitution laws is
essential to prove coherence of models of type theory in higher types
in the sense of HoTT.

Hence this paper has two aspects: it turns out that an apparently trivial
problem isn't so hard after all, and it is a stepping stone to more
exciting open questions. But before you can run you need to walk and
we also believe that the construction here can be useful to others.

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
