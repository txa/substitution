%if full
\begin{code}
{-# OPTIONS --rewriting --local-confluence-check #-}
module subst where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import naive using (Ty ;  o ; _⇒_ ; • ; _▷_ ; Con) public 

variable
  A B C : Ty
  Γ Δ Θ : Con  

infix   3  _⊢[_]_
infix   3  _⊩[_]_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixl  6  _·_
infix   7  `_
infix   8  _^_
infix   8  _⁺_
infix   8  _[_]
\end{code}
%endif

\section{Factorising with sorts}
\label{sec:fact-with-sorts}

%if False
\begin{code}
module Subst where
\end{code}
%endif

Our main idea is to turn the distinction between
variables and terms into a parameter. The first approximation of this idea is to
define a type |Sort| (|q, r, s|):
\begin{spec}
data Sort : Set where
   V T : Sort  
 \end{spec}
But this is not quite what we want.
Agda's termination checker uses structural orderings.
Following our intuition that variable weakening is trivial but
term weakening requires renaming, we want to make the sort
of variables |V| structurally smaller than the sort of terms |T|.

With the following definition, we
make |V| structurally smaller than |T>V V isV|,
while maintaining that |Sort| has only two elements.

%if false
\begin{code}
mutual
\end{code}
%endif
\noindent
\begin{minipage}{0.55\textwidth}
\begin{code}
  data Sort : Set where
    V    : Sort
    T>V  : (s : Sort) → IsV s → Sort
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
  data IsV : Sort → Set where
    isV : IsV V
\end{code}
\end{minipage}
%if False
\begin{code}
variable
  q r s    : Sort
\end{code}
%endif

\noindent
The predicate |isV| only holds for |V|. This encoding makes
use of Agda's support for inductive-inductive datatypes (IITs), but a
pair of a natural number |n| and a proof |n ≤ 1| would also work, i.e.
|Sort = Σ ℕ (_≤ 1)|.
We make |T : Sort| an abbreviation for |T>V V isV| with a pattern declaration.
\begin{code}
pattern T = T>V V isV
\end{code}
Now we can pattern match over |Sort| with |V| and |T|,
while Agda's termination checker treats |V| as structurally 
smaller than |T|.

It is now possible to define terms and variables (|x, y, z|) in one go:
\begin{code}
data _⊢[_]_ : Con → Sort → Ty → Set where
  zero  : Γ ▷ A ⊢[ V ] A
  suc   : Γ  ⊢[ V ]  A → (B : Ty) → Γ ▷ B  ⊢[ V ]  A
  `_    : Γ  ⊢[ V ]  A → Γ  ⊢[ T ]  A
  _·_   : Γ ⊢[ T ] A ⇒ B → Γ ⊢[ T ] A → Γ ⊢[ T ] B
  ƛ_    : Γ ▷ A ⊢[ T ] B → Γ ⊢[ T ] A ⇒ B
\end{code}
This recapitulates our previous definition, where
|Γ ⊢[ V ] A| corresponds to |Γ ∋ A| and |Γ  ⊢[ T ]  A| to |Γ ⊢ A|.
Now we can parametrize our previous development.
As a first step, we generalize renamings and substitutions (|xs, ys, zs|):
\begin{code}
data _⊩[_]_ : Con → Sort → Con → Set where
  ε    : Γ ⊩[ q ] •
  _,_  : Γ ⊩[ q ] Δ → Γ ⊢[ q ] A → Γ ⊩[ q ] Δ ▷ A  
\end{code}
%if False
\begin{code}
variable
  i j k    : Γ ⊢[ V ] A
  t u v    : Γ ⊢[ T ] A
  x y z : Γ ⊢[ q ] A
  xs ys zs : Γ ⊩[ q ] Δ  
\end{code}
%endif

We model the structural order on sorts as
an explicit relation with a least upper bound.
The latter will help with substitution and composition,
where the result is |V| only if both inputs are |V|.

\noindent
\begin{minipage}{0.55\textwidth}
\begin{code}
data _⊑_ : Sort → Sort → Set where
  rfl : s ⊑ s
  v⊑t : V ⊑ T
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T
\end{code}
\end{minipage}

\noindent
This is just boolean algebra. We need a number of laws:

\noindent
\begin{minipage}{0.55\textwidth}
\begin{code}
⊑t : s ⊑ T
v⊑ : V ⊑ s
⊑q⊔ : q ⊑ (q ⊔ r)
⊑⊔r : r ⊑ (q ⊔ r)
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔v : q ⊔ V ≡ q
⊔t : q ⊔ T ≡ T
\end{code}
\end{minipage}

\noindent
These are easy to prove by case analysis,
e.g. |⊑t {V} = v⊑t| and |⊑t {T} = rfl|.
%if False
\begin{code}
⊑t {V} = v⊑t
⊑t {T} = rfl

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

⊔t {V} = refl
⊔t {T} = refl
\end{code}
%endif
Further, we turn the equations
($\sqcup\sqcup$, $\sqcup\Varid{v}$, $\sqcup\Varid{t}$) into rewrite rules.
% \begin{code}
% {-# REWRITE ⊔⊔ ⊔v ⊔t #-} 
% \end{code}
This introduces new definitional equalities, allowing the
type checker to directly exploit e.g. associativity of |_⊔_| 
(effectively, this feature allows a selective use of 
extensional Type Theory).

Functoriality of context extension is now parametric
\begin{code}
_^_ : Γ ⊩[ q ] Δ → ∀ A → Γ ▷ A ⊩[ q ] Δ ▷ A
\end{code}
We'll derive this later. Meanwhile,
the order on sorts gives rise to another functor.
\begin{code}
tm⊑ : q ⊑ s → Γ ⊢[ q ] A → Γ ⊢[ s ] A
tm⊑ rfl x  = x
tm⊑ v⊑t i  = ` i
\end{code}
Now we can define substitution and renaming in one go:

\noindent
\begin{minipage}{0.55\textwidth}
\begin{code}
_[_] : Γ ⊢[ q ] A → Δ ⊩[ r ] Γ → Δ ⊢[ q ⊔ r ] A
zero       [ xs , x ]  = x
(suc i _)  [ xs , x ]  = i [ xs ]
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
(` i)      [ xs ]      = tm⊑  ⊑t  (i [ xs ])
(t · u)    [ xs ]      = (t [ xs ]) · (u [ xs ])
(ƛ t)      [ xs ]      = ƛ (t [ xs ^ _ ]) 
\end{code}
\end{minipage}

\noindent
Here |_⊔_| ensures substitution returns a variable
only if both inputs are variables/renamings.
We use |tm⊑| because |i [ xs ]| will be a variable if
|xs| is a renaming, but |(` i) [ xs ]| is always a term.

We define |id| using |_^_|, recursing over contexts.
To define |_^_| itself, we need parametric versions of |zero| and |suc|.
Defining |zero| is easy.

\noindent
\begin{minipage}{0.55\textwidth}
\begin{spec}
id : Γ ⊩[ V ] Γ
id {Γ = •}      =  ε
id {Γ = Γ ▷ A}  =  id ^ A
\end{spec}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{code}
zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ]      =  zero
zero[ T ]      =  ` zero
\end{code}
\end{minipage}

%if False
\begin{code}
id-poly : Γ ⊩[ q ] Γ 
id-poly {Γ = •} = ε
id-poly {Γ = Γ ▷ A} = id-poly ^ A

id : Γ ⊩[ V ] Γ 
id = id-poly
{-# INLINE id #-}

-- Alternative:

-- id′ : Sort → Γ ⊩[ V ] Γ

-- id : Γ ⊩[ V ] Γ
-- id = id′ V
-- {-# INLINE id #-}

-- id′ {Γ = •}     _ =  ε
-- id′ {Γ = Γ ▷ A} _ = id ^ A
\end{code}
%endif

However, |suc| is more subtle since the case for |T| depends on
weakening over substitutions:

%if false
\begin{code}
_⁺_ : Γ ⊩[ q ] Δ → (A : Ty) → Γ ▷ A ⊩[ q ] Δ
\end{code}
%endif
\noindent
\begin{minipage}{0.55\textwidth}
\begin{code}
suc[_]  :  ∀ q → Γ ⊢[ q ] B → ∀ A 
        →  Γ ▷ A ⊢[ q ] B
suc[ V ] i  A  = suc i A
suc[ T ] t  A  = t [ id ⁺  A ]
\end{code}
\end{minipage}
\begin{minipage}{0.4\textwidth}
\begin{spec}
_⁺_  :  Γ ⊩[ q ] Δ → ∀ A 
     →  Γ ▷ A ⊩[ q ] Δ
ε         ⁺ A = ε
(xs , x)  ⁺ A = xs ⁺ A , suc[ _ ] x A 
\end{spec}
\end{minipage}\\
%if False
\begin{code}
ε ⁺ A = ε
(xs , x) ⁺ A = xs ⁺ A , suc[ _ ] x A 
\end{code}
%endif
And finally we can define |_^_| and |_∘_|.

\noindent
\begin{minipage}{0.4\textwidth}
\begin{code}
xs ^ A =  xs ⁺ A , zero[ _ ]
\end{code}
\end{minipage}
\begin{minipage}{0.55\textwidth}
\begin{code}
_∘_ : Γ ⊩[ q ] Θ → Δ ⊩[ r ] Γ → Δ ⊩[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
\end{code}
\end{minipage}



\subsection{Termination}
\label{sec:termination}

Unfortunately (as of Agda 2.7.0.1) we now hit a termination error.
\begin{spec}
Termination checking failed for the following functions:
  _^_, _[_], id, _⁺_, suc[_]
\end{spec}
The cause turns out to be |id|.
Termination here hinges on weakening for terms
(|suc[ T ] t A|) applying a renaming rather than a full substitution.
Note that if instead we had |id : Γ ⊩[ T ] Γ|, or if
weakening for variables (|suc[ V ] i A|) was implemented by |i [ id ⁺ A ]|,
our operations would still be type-correct but would genuinely loop,
so perhaps Agda is right to be careful.

Why doesn't Agda accept our program? The limitation is ultimately
technical: Agda only looks at direct arguments to function calls when 
building the call graph from which it identifies termination order 
\cite{alti:jfp02}. Because |id| is not passed a sort, the sort cannot be 
considered as decreasing in the case of term weakening (|suc[ T ] t A|).

\noindent
\begin{minipage}{0.675\textwidth}
\begin{tikzcd}[scaleedge cd=1.1, sep=large]
& |suc[ q₄ ] t₄q₄Γ₄|
\arrow[dd, bend left, "\substack{|r₃ < q₄|}"]
\arrow[ldd, bend right, swap, "\substack{|r₂ < q₄|}"]
\arrow[rdd, bend left, "|r₁ < q₄|"]
\\
\\
|idr₂Γ₂| 
\arrow[r, swap, "\substack{|r₃ = r₂|}"]
\arrow[in=300, out=240, loop, swap, "\substack{|r₂′ = r₂| \\ |Γ₂′ < Γ₂|}"]
& |σ₃r₃Δ₃Γ₃ ⁺ A| 
\arrow[uu, bend left, "\substack{|q₄ = r₃|}"]
\arrow[in=300, out=240, loop, swap, "\substack{|r₃′ = r₃| \\ |σ₃′ < σ₃|}"]
& |t₁q₁Γ₁ [ σ₁r₁Δ₁Γ₁ ]|
\arrow[l, "|r₃ = r₁|"]
\arrow[in=300, out=240, loop, swap, "\substack{|r₁′ = r₁| \\ |t₁′ < t₁|}"]
\end{tikzcd}
\captionof{figure}{Call graph of substitution operations}
\label{figure:termination}
\end{minipage}
\begin{minipage}{0.3\textwidth}
\renewcommand{\arraystretch}{1.2}
\begin{center}
\begin{tabular}{ ||c||c||c|| }
\hline
Function & Measure \\
\hline \hline
|t₁q₁Γ₁ [ σ₁r₁Δ₁Γ₁ ]| & |(r₁ , t₁)| \\ [0.2ex]
\hline
|idr₂Γ₂| & |(r₂ , Γ₂)| \\ [0.2ex]
\hline
|σ₃r₃Δ₃Γ₃ ⁺ A| & |(r₃ , σ₃)| \\ [0.2ex]
\hline
|suc[ q₄ ] t₄q₄Γ₄| & |(q₄)| \\ [0.2ex]
\hline
\end{tabular}
\end{center}
\captionof{table}{Per-function termination measures}
\label{table:termination}
\end{minipage}
\\[2.0ex]

Luckily, there is an easy solution: making |id| polymorphic in its |Sort|
and instantiating with |V| at the call-sites
enables the decrease
to be tracked and termination to be correctly inferred by Agda.
We present the call graph diagrammatically (inlining |_^_|), 
in the style of \cite{keller2010hereditary} (Figure~\ref{figure:termination}).

To justify termination, we note that along all cycles in the graph,
either the |Sort| strictly decreases,
or the |Sort| is preserved and some other argument
(the context, substitution, or term) decreases. Following this, we can
assign lexicographically-decreasing measures to each of the functions
(\textsf{Table \ref{table:termination}}).

In practice, we will generally require identity renamings, rather than
substitutions. We define |Sort|-polymorphic |id-poly|, and then define
our original |id| by instantiating it at |V| and ensuring it is always
inlined.

\noindent
\begin{minipage}{0.45\textwidth}
\begin{spec}
id-poly : Γ ⊩[ q ] Γ 
id-poly {Γ = •} = ε
id-poly {Γ = Γ ▷ A} = id-poly ^ A
\end{spec}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{spec}
id : Γ ⊩[ V ] Γ 
id = id-poly
{-# INLINE id #-}
\end{spec}
\end{minipage}

(All this fuss with |Sort|-polymorphic |id| may be unnecessary.
At a cost in performance, it is possible to extend Agda's 
termination checker so that our original definitions are accepted directly.
See \href{https://github.com/agda/agda/pull/7695}{\#7695}.)

% Dummy argument explanation (unnecessary)

% We now have a working implementation of substitution. In preparation for
% a similar termination issue we will encounter later though, we note that, 
% perhaps surprisingly, adding a ``dummy argument'' to |id| of
% a completely unrelated type, such as |Bool| also satisfies Agda.
% That is, we can write
% 
% \begin{minipage}{0.45\textwidth}
% \begin{spec}
% id′ : Bool → Γ ⊩[ V ] Γ
% id′ {Γ = •}      d = ε
% id′ {Γ = Γ ▷ A}  d = id′ d ^ A
% \end{spec}
% \end{minipage}
% \begin{minipage}{0.45\textwidth}
% \begin{spec}
% id : Γ ⊩[ V ] Γ 
% id = id′ true
% {-#  \Keyword{INLINE} $\Varid{id}$ #-} 
% \end{spec}
% \end{minipage}
% 
% This result was a little surprising at first, but Agda's
% implementation reveals answers. It turns out that Agda considers
% ``base constructors'' (data constructors
% taking with arguments) to be structurally smaller-than-or-equal-to all
% parameters of the caller. This enables Agda to infer |true ≤ T| in 
% |suc[ T ] t A| and |V ≤ true| in
% |id′ {Γ = Γ ▷ A}|; we do not get a strict decrease in |Sort| like before,
% but the size is at least preserved, and it turns out
% (making use of some slightly more complicated termination measures) this is
% enough.

% Call graph diagram for the "dummy argument" approach (commented out because
% it takes up a lot of space and I don't think it is really necessary):
% \begin{tikzcd}[scaleedge cd=1.1, sep=large]
% & |suc[ q₄ ] t₄q₄Γ₄|
% \arrow[dd, bend left, "\substack{|r₃ < q₄|}"]
% \arrow[ldd, bend right, swap, "\substack{|d₂ ≤ q₄| \\ |Γ₂ = Γ₄|}"]
% \arrow[rdd, bend left, "\substack{|r₁ < q₄|}"]
% \\
% \\
% |id′Γ₂ d₂| 
% \arrow[r, swap, "\substack{|q₃ ≤ d₂| \\ |Δ₃ < Γ₂|}"]
% \arrow[in=300, out=240, loop, swap, "\substack{|d₂′ = d₂| \\ |Γ₂′ < Γ₂|}"]
% & |σ₃r₃Δ₃Γ₃ ⁺ A| 
% \arrow[uu, bend left, "\substack{|q₄ = r₃| \\ |Γ₄ = Δ₃|}"]
% \arrow[in=300, out=240, loop, swap, "\substack{|r₃′ = r₃| \\ |Δ₃′ = Δ₃| \\ |σ₃′ < σ₃|}"]
% & |t₁q₁Γ₁ [ σ₁r₁Δ₁Γ₁ ]|
% \arrow[l, "|r₃ = r₁|"]
% \arrow[in=300, out=240, loop, swap, "\substack{|r₁′ = r₁| \\ |t₁′ < t₁|}"]
% \end{tikzcd}

% TODO: Should we link to the PR?
% https://github.com/agda/agda/pull/7695
% This ``dummy argument'' approach perhaps is interesting because one could 
% imagine automating this process (i.e. via elaboration, or
% directly during termination checking). In fact, a
% PR featuring exactly this extension is currently open on the Agda
% GitHub repository.

% Ultimately the details behind how termination is ensured do not matter here 
% though: both approaches provide effectively the same
% interface.
% \footnote{Technically, a |Sort|-polymorphic |id| provides a direct
% way to build identity \textit{substitutions} as well as identity
% \textit{renamings}, which are useful for implementing single substitutions 
% (|< t > = id , t|), 
% but we can easily recover this with a monomorphic |id| by extending |tm⊑| to 
% lists of terms (see \ref{sec::cwf-recurs-subst}). For the rest of the paper, 
% we will use |id : Γ ⊩[ V ] Γ| without assumptions about how it is 
% implemented.}

