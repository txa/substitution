%if False
\begin{code}
module naive where

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊨_
infixl  4  _,_
infix   3  _⊨v_
infix   8  _[_]
infix   8  _[_]v
\end{code}
%endif

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
\begin{code}
data _∋_ : Con → Ty → Set where 
  zero : Γ ▷ A ∋ A
  suc  : Γ ∋ A → (B : Ty) → Γ ▷ B ∋ A

data _⊢_ : Con → Ty → Set where 
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
\end{code}
Here the constructor |`_| corresponds to \emph{variables are
  $\lambda$-terms}; we write applications as |t  · u|, since we use de
Bruijn variables lambda abstraction |ƛ_| doesn't use a name but
refers to the variable |zero|. We also define substitutions as
sequences of terms:
\begin{code}
data _⊨_ : Con → Con → Set where
  ε   : Γ ⊨ •
  _,_ : Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ Δ ▷ A  
\end{code}
Now to define the categorical structure (|_∘_|,|id|) we first need to define
substitution for terms and variables:
%if False
\begin{code}
_^_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ ▷ A
\end{code}
%endif

\begin{code}
_v[_] : Γ ∋ A → Δ ⊨ Γ → Δ ⊢ A
zero    v[ ts , t ]    =  t
(suc i _) v[ ts , t ]  =  i v[ ts ]


_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
\end{code}


\begin{spec}
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
\begin{code}
(ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])
\end{code}

However, now we have to define |_^_|. This is easy, isn't it but we
need weakening on substitutions:
\begin{code}
_⁺_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ
\end{code}
And now we can define |_^_|:
\begin{code}
ts ^ A = ts ⁺ A , ` zero 
\end{code}
but we need to define |_⁺_ | which is nothing but a fold of weakening
of terms
\begin{code}
suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B

ε         ⁺ A  = ε
(ts , t)  ⁺ A  = ts ⁺ A , suc-tm t A  
\end{code}
But how to define |suc-tm| we only have weakening for variables? If we
already had identity |id : Γ  ⊨ Γ| and substitution we could say:
\begin{spec}
suc-tm t A = t [ id ⁺ A ] 
\end{spec}
but this is certainly not structurally recursive (and hence rejected
by agda's termination checker).

Actually we realize that |id| is a renaming, i.e. it is a substitution
only containing variables and we can easily define |_⁺v_| for
renamings. This leads to a structurally recursive definition but we
also have to repeat the definition of substitutions for renamings.
\begin{code}
data _⊨v_ : Con → Con → Set where
  ε   : Γ ⊨v •
  _,_ : Γ ⊨v Δ → Γ ∋ A → Γ ⊨v Δ ▷ A

_⁺v_ : Γ ⊨v Δ → (A : Ty) → Γ ▷ A ⊨v Δ
ε         ⁺v A  = ε
(is , i)  ⁺v A  = is ⁺v A , suc i A

_^v_ : Γ ⊨v Δ → (A : Ty) → Γ ▷ A ⊨v Δ ▷ A
is ^v A = is ⁺v A , zero 

_v[_]v : Γ ∋ A → Δ ⊨v Γ → Δ ∋ A
zero    v[ is , i ]v    =  i
(suc i _) v[ is , j ]v  =  i v[ is ]v

_[_]v : Γ ⊢ A → Δ ⊨v Γ → Δ ⊢ A
(` i)   [ is ]v       =  ` (i v[ is ]v)
(t · u) [ is ]v       =  (t [ is ]v) · (u [ is ]v)
(ƛ t)   [ is ]v       =  ƛ (t [ is ^v _ ]v)

idv : Γ ⊨v Γ
idv {Γ = •}     =  ε
idv {Γ = Γ ▷ A} =  idv ^v A

suc-tm t A = t [ idv ⁺v A ]v
\end{code}

This may not sound too bad to obtain structural termination we have to
duplicate a definition but it gets even worse when proving the
laws. To prove associativity we need to prove functoriality of
substitution first:
\begin{spec}
[∘] : t [ us ∘ vs ] ≡ t [ us ] [ vs ]
\end{spec}
Since |t , us , vs| can be variables/renamings or terms/substitutions
there are in principle 8 combinations of which we need 4. And each
time we need to prove a number of lemmas again in a different
setting.

In the rest of the paper we describe a technique how the definition
and thr proof can be
factored only relying on the agda termination checker to validate that
the recursion is structurally terminating.
