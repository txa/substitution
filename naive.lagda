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
copy-and-paste proof. We define types (|A, B, C|) and contexts (|Γ, Δ, Θ|):

\begin{minipage}{0.45\textwidth}
\begin{code}
data Ty : Set where
  o    : Ty
  _⇒_  : Ty → Ty → Ty
\end{code}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{code}
data Con : Set where
  •    : Con
  _▷_  : Con → Ty → Con
\end{code}
\end{minipage}
%if False
\begin{code}
variable
  A B C : Ty
  Γ Δ Θ : Con  
\end{code}
%endif
\\Next we introduce intrinsically typed de Bruijn variables (|i, j, k|) and
$\lambda$-terms (|t, u, v|):

\noindent
\begin{minipage}{0.4\textwidth}
\begin{code}
data _∋_ : Con → Ty → Set where 
  zero  : Γ ▷ A ∋ A
  suc   : Γ ∋ A → (B : Ty) → Γ ▷ B ∋ A
\end{code}
\end{minipage}
\hfill
\begin{minipage}{0.5\textwidth}
\begin{code}
data _⊢_ : Con → Ty → Set where 
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
\end{code}
\end{minipage}

Here the constructor |`_| corresponds to \emph{variables are
  $\lambda$-terms}. We write applications as |t · u|. Since we use de
Bruijn variables, lambda abstraction |ƛ_| doesn't bind a name explicitly
(instead, variables count the number of binders between them and their 
actual binding site). 
We also define substitutions as sequences of terms:
\begin{code}
data _⊨_ : Con → Con → Set where
  ε   : Γ ⊨ •
  _,_ : Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ Δ ▷ A  
\end{code}
Now to define the categorical structure (|_∘_|, |id|) we first need to define
substitution for terms and variables:
%if False
\begin{code}
_^_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ ▷ A
\end{code}
%endif

\begin{minipage}{0.45\textwidth}
\begin{code}
_v[_] : Γ ∋ A → Δ ⊨ Γ → Δ ⊢ A
zero       v[ ts , t ] = t
(suc i _)  v[ ts , t ] = i v[ ts ]
\end{code}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{spec}
_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` i)    [ ts ] = i v[ ts ]
(t · u)  [ ts ] = (t [ ts ]) · (u [ ts ])
(ƛ t)    [ ts ] = ƛ ?
\end{spec}
\end{minipage}

As usual, we encounter a problem with the case for binders |ƛ_|. We are given a
substitution |ts : Δ ⊨ Γ| but the body |t| lives in the extended context
|t : Γ , A ⊢ B|. We need to exploit the fact that context extension
|_▷_| is functorial: |_^_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ ▷ A|.
Using |_^_| we can complete |_[_]|
%if false
\begin{code}
_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
\end{code}
%endif
\begin{code}
(ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])
\end{code}
However, now we have to define |_^_|. This is easy (isn't it?) but we
need weakening on substitutions: |_⁺_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ|:
%if False
\begin{code}
_⁺_ : Γ ⊨ Δ → (A : Ty) → Γ ▷ A ⊨ Δ
\end{code}
%endif
\begin{code}
ts ^ A = ts ⁺ A , ` zero 
\end{code}
Now we need to define |_⁺_|, which is nothing but a fold of weakening
of terms:

%if false
\begin{code}
suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B
\end{code}
%endif
\noindent
\begin{minipage}{0.45\textwidth}
\begin{code}
ε         ⁺ A  = ε
(ts , t)  ⁺ A  = ts ⁺ A , suc-tm t A  
\end{code}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{spec}
suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B
\end{spec}
\end{minipage}\\
But how can we define |suc-tm| when we only have weakening for variables? If we
already had identity |id : Γ ⊨ Γ| and substitution we could write:
|suc-tm t A = t [ id ⁺ A ] |, 
but this is certainly not structurally recursive (and hence rejected
by Agda's termination checker).

Actually, we realise that |id| is a renaming, i.e. it is a substitution
only containing variables, and we can easily define |_⁺v_| for
renamings. This leads to a structurally recursive definition, but we
have to repeat the definition of substitutions for renamings.

\centering
\begin{code}
data _⊨v_ : Con → Con → Set where
  ε   : Γ ⊨v •
  _,_ : Γ ⊨v Δ → Γ ∋ A → Γ ⊨v Δ ▷ A
\end{code}
\noindent
\justifying
\begin{minipage}{0.45\textwidth}
\begin{code}
_v[_]v : Γ ∋ A → Δ ⊨v Γ → Δ ∋ A
zero       v[ is , i ]v  = i
(suc i _)  v[ is , j ]v  = i v[ is ]v

_⁺v_ : Γ ⊨v Δ → ∀ A → Γ ▷ A ⊨v Δ
ε         ⁺v A           = ε
(is , i)  ⁺v A           = is ⁺v A , suc i A

_^v_ : Γ ⊨v Δ → ∀ A → Γ ▷ A ⊨v Δ ▷ A
is ^v A                  = is ⁺v A , zero 
\end{code}
\end{minipage}
\hfill
\begin{minipage}{0.45\textwidth}
\begin{code}
_[_]v : Γ ⊢ A → Δ ⊨v Γ → Δ ⊢ A
(` i)   [ is ]v  =  ` (i v[ is ]v)
(t · u) [ is ]v  =  (t [ is ]v) · (u [ is ]v)
(ƛ t)   [ is ]v  =  ƛ (t [ is ^v _ ]v)

idv : Γ ⊨v Γ
idv {Γ = •}      = ε
idv {Γ = Γ ▷ A}  = idv ^v A

suc-tm t A       = t [ idv ⁺v A ]v
\end{code}
\end{minipage}

This may not seem too bad: to obtain structural termination we just have to
duplicate a few definitions, but it gets even worse when proving the
laws. For example, to prove associativity, we first need to prove functoriality 
of substitution: |[∘] : t [ us ∘ vs ] ≡ t [ us ] [ vs ]|.
Since |t, us, vs| can be variables/renamings or terms/substitutions,
there are in principle eight combinations (though it turns out that four is 
enough). 
Each time, we must to prove a number of lemmas again in a different setting.

In the rest of the paper we describe a technique for factoring these definitions
and the proofs, only relying on the Agda termination checker to validate that
the recursion is structurally terminating.
 