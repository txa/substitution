%if full
\begin{code}
{-# OPTIONS --rewriting #-}
module subst where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import naive using (Ty ;  o ; _⇒_ ; • ; _▷_ ; Con) public 

variable
  A B C : Ty
  Γ Δ Θ : Con  

infix   3  _⊢[_]_
infix   3  _⊨[_]_
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
variables and terms into a parameter. The first approximation is to
define a type |Sort| (|q, r, s|) :
\begin{spec}
data Sort : Set where
   V T : Sort  
 \end{spec}
but this is not exactly what we want because we want Agda to know that
the sort of variables |V| is \emph{smaller} than the sort of terms
|T| (following intuition that variable weakening is trivial, but to 
weaken a term we must construct a renaming). 
Agda's termination checker only knows about the structural
orderings. With the following definition, we
can make |V| structurally smaller than |T>V V isV|, while maintaining that 
|Sort| has only two elements.
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

Here the predicate |isV| only holds for |V|. We could avoid this mutual
definition by using equality |_≡_|:
\begin{spec}
data Sort where
  V : Sort
  T>V : (s : Sort) → s ≡ V → Sort
\end{spec}

We can now define |T = T>V V isV : Sort| but, even better, we can tell Agda that
this is a derived pattern
\begin{code}
pattern T = T>V V isV
\end{code}
This means we can pattern match over |Sort| just with |V| and |T|,
but now |V| is visibly (to Agda's termination checker) structurally smaller than
|T|.

We can now define terms and variables in one go (|x, y, z|):
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
parametrize all definitions and theorems explicitly. As a first step,
we can generalize renamings and substitutions (|xs, ys, zs|):
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
composition (the result is |V| only if both inputs are |V|) we define
a least upper bound on |Sort|:
\begin{code}
_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T
\end{code}
We also need this order as a relation, for inserting coercions when necessary:
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
\end{code}
%endif

To improve readability we turn the equations ($\sqcup\sqcup$, 
$\sqcup\mathrm{v}$) into rewrite rules: by declaring

\begin{spec}
{-# \Keyword{REWRITE} $\sqcup\!\sqcup \; \sqcup\mathrm{v} \;$ #-}
\end{spec}

%if False
\begin{code}
{-# REWRITE ⊔⊔ ⊔v #-} 
\end{code}
%endif

This introduces new definitional equalities, i.e.
|q ⊔ (r ⊔ s) = (q ⊔ r) ⊔ s| and |q ⊔ V = q| are now used by the type
checker.
\footnote{Effectively, this feature allows a selective use of extensional
  Type Theory.}
The order gives rise to a functor which is witnessed by
\begin{code}
tm⊑ : q ⊑ s → Γ ⊢[ q ] A → Γ ⊢[ s ] A
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
We use |_⊔_| here to take care of the fact that substitution will only return a 
variable if both inputs are variables / renamings. We also
need to use |tm⊑| to take care of the two cases when substituting for
a variable. 

We can also define |id| using |_^_|:
\begin{spec}
id : Γ ⊨[ V ] Γ
id {Γ = •}     =  ε
id {Γ = Γ ▷ A} =  id ^ A
\end{spec}

%if False
\begin{code}
id-poly : Γ ⊨[ q ] Γ 
id-poly {Γ = •} = ε
id-poly {Γ = Γ ▷ A} = id-poly ^ A

id : Γ ⊨[ V ] Γ 
id = id-poly
{-# INLINE id #-}

-- Alternative:

-- id′ : Sort → Γ ⊨[ V ] Γ

-- id : Γ ⊨[ V ] Γ
-- id = id′ V
-- {-# INLINE id #-}

-- id′ {Γ = •}     _ =  ε
-- id′ {Γ = Γ ▷ A} _ = id ^ A
\end{code}
%endif

To define |_^_|, we need parametric versions of |zero|, |suc| and
|suc*|. |zero| is very easy:

\begin{code}
zero[_] : ∀ q → Γ ▷ A ⊢[ q ] A
zero[ V ]      =  zero
zero[ T ]      =  ` zero
\end{code}

However, |suc| is more subtle since the case for |T| depends on its
fold over substitutions (|_⁺_|):
\begin{code}
_⁺_ : Γ ⊨[ q ] Δ → (A : Ty) → Γ ▷ A ⊨[ q ] Δ

suc[_] : ∀ q → Γ ⊢[ q ] B → (A : Ty) 
       → Γ ▷ A ⊢[ q ] B
suc[ V ] i  A   =  suc i A
suc[ T ] t  A   =  t [ id ⁺  A ]

ε ⁺ A = ε
(xs , x) ⁺ A = xs ⁺ A , suc[ _ ] x A 
\end{code}
And now we define:
\begin{code}
xs ^ A                 =  xs ⁺ A , zero[ _ ]
\end{code}

Unfortunately (as of Agda 2.7.0.1), we now hit a termination error.
\begin{spec}
Termination checking failed for the following functions:
  _^_, _[_], id, _⁺_, suc[_]
\end{spec}

The cause turns out to be |id|. Termination here hinges on weakening for terms
(|suc[ T ] t A|) building
and applying a renaming (i.e. a sequence of variables, for which weakening is
trivial) rather than a full substutution. Note that if |id| produced
|Tms[ T ] Γ Γ|s, or if we implemented 
weakening for variables (|suc[ V ] i A|) with |i [ id ⁺ A ]|, our operations
would still be
type-correct, but would genuinely loop, so perhaps Agda is right to be
careful.

Of course, we have specialised weakening for variables, so we now must ask 
why Agda still doesn't accept our program. The limitation is ultimately a 
technical one: Agda only looks at the direct arguments to function calls when 
building the call graph from which it identifies termination order 
\cite{alti:jfp02}. Because |id| is not passed a sort, the sort cannot be 
considered as decreasing in the case of term weakening (|suc[ T ] t A|).

Luckily, there is an easy solution here: making |id| |Sort|-polymorphic and
instantiating with |V| at the call-sites
adds new rows/columns (corresponding to the |Sort| argument) to the call
matrices
involving |id|, enabling the decrease
to be tracked and termination to be correctly inferred by Agda.
We present the call graph diagramatically (inlining |_^_|), 
in the style of \cite{keller2010hereditary}.

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

To justify termination formally, we note that along all cycles in the graph,
either the 
|Sort| strictly decreases
in size, or the size of the |Sort| is preserved and some other argument
(the context, substitution or term) gets smaller. We can therefore
assign decreasing measures as 
follows:

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

We now have a working implementation of substitution. In preparation for
a similar termination issue we will encounter later though, we note that, 
perhaps surprisingly, adding a ``dummy argument'' to |id| of
a completely unrelated type, such as |Bool| also satisfies Agda.
That is, we can write

\begin{spec}
id′ : Bool → Γ ⊨[ V ] Γ
id′ {Γ = •}      d = ε
id′ {Γ = Γ ▷ A}  d = id′ d ^ A

id : Γ ⊨[ V ] Γ 
id = id′ true
{-# INLINE id #-} 
\end{spec}

This result was a little surprising at first, but Agda's
implementation reveals answers. It turns out that Agda considers
``base constructors'' (data constructors
taking with arguments) to be structurally smaller-than-or-equal-to all
parameters of the caller. This enables Agda to infer |true ≤ T| in 
|suc[ T ] t A| and |V ≤ true| in
|id′ {Γ = Γ ▷ A}|; we do not get a strict decrease in |Sort| like before,
but it is at least preserved, and it turns out
(making use of some slightly more complicated termination measures) this is
enough:

\begin{tikzcd}[scaleedge cd=1.1, sep=large]
& |suc[ q₄ ] t₄q₄Γ₄|
\arrow[dd, bend left, "\substack{|r₃ < q₄|}"]
\arrow[ldd, bend right, swap, "\substack{|d₂ ≤ q₄| \\ |Γ₂ = Γ₄|}"]
\arrow[rdd, bend left, "\substack{|r₁ < q₄|}"]
\\
\\
|id′Γ₂ d₂| 
\arrow[r, swap, "\substack{|q₃ ≤ d₂| \\ |Δ₃ < Γ₂|}"]
\arrow[in=300, out=240, loop, swap, "\substack{|d₂′ = d₂| \\ |Γ₂′ < Γ₂|}"]
& |σ₃r₃Δ₃Γ₃ ⁺ A| 
\arrow[uu, bend left, "\substack{|q₄ = r₃| \\ |Γ₄ = Δ₃|}"]
\arrow[in=300, out=240, loop, swap, "\substack{|r₃′ = r₃| \\ |Δ₃′ = Δ₃| \\ |σ₃′ < σ₃|}"]
& |t₁q₁Γ₁ [ σ₁r₁Δ₁Γ₁ ]|
\arrow[l, "|r₃ = r₁|"]
\arrow[in=300, out=240, loop, swap, "\substack{|r₁′ = r₁| \\ |t₁′ < t₁|}"]
\end{tikzcd}

% TODO: Should we link to the PR?
% https://github.com/agda/agda/pull/7695
This ``dummy argument'' approach perhaps is interesting because one could 
imagine automating this process (i.e. via elaboration or
directly inside termination checking). In fact, a
PR featuring exactly this extension is currently open on the Agda
GitHub repository.

Ultimately the details behind how termination is ensured do not matter
though here though: both appaoraches provide effectively the same
interface.\sidenote{Technically, a |Sort|-polymorphic |id| provides a direct
way to build identity substitutions as well as identity
renamings, which are useful to build single substitutions (|< t > = id , t|), 
but we can easily recover this for a monomorphic |id| by extending |tm⊑| to 
lists of terms.}

Finally, we define composition by folding substitution:
\begin{code}
_∘_ : Γ ⊨[ q ] Θ → Δ ⊨[ r ] Γ → Δ ⊨[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
\end{code}
