%if False
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