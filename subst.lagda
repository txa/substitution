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
definition by using equality |_≡_|.

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
a variable. We can also define |id| using |_^_|:
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

Unfortunately, we now hit a termination error.
\begin{spec}
Termination checking failed for the following functions:
  _^_, _[_], id, _⁺_, suc[_]
\end{spec}

The cause turns out to be |id|. 
Termination here hinges on the fact that |id| is a renaming - i.e. a sequences 
of variables, for which weakening is trivial. Note that if we implemented 
weakening for variables as |i [ id ⁺ A ]|, this would be type-correct, but our
substitutions would genuinely loop, so perhaps Agda is right to be careful.

Of course, we have specialised our weakening for variables, so we now must ask 
why Agda still doesn't accept our program. The limitation is ultimately a 
technical one: Agda only looks at the direct arguments to function calls when 
building the call graph from which it identifies termination order 
\cite{alti:jfp02}. Because |id| is not passed a sort, the sort cannot be 
considered as decreasing in the case of term weakening (|suc[ T ] t A|).

Luckily, working around this is not difficult. We can implement |id| 
sort-polymorphically and then define an abbreviation which specialises this to 
variables.

\begin{spec}
id-poly : Γ ⊨[ q ] Γ 
id-poly {Γ = •} = ε
id-poly {Γ = Γ ▷ A} = id-poly ^ A

id : Γ ⊨[ V ] Γ 
id = id-poly
{-# \Keyword{INLINE} id #-}
\end{spec}

Finally, we define composition by folding substitution:
\begin{code}
_∘_ : Γ ⊨[ q ] Θ → Δ ⊨[ r ] Γ → Δ ⊨[ q ⊔ r ] Θ
ε ∘ ys         = ε
(xs , x) ∘ ys  = (xs ∘ ys) , x [ ys ]
\end{code}

Clearly, the definitions are very recursive and exploit the structural
ordering on terms and the order on sorts. We can leave the details to
the termination checker.
