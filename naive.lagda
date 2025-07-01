%if False
\begin{code}
module naive where

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊩_
infixl  4  _,_
infix   3  _⊩v_
infix   8  _[_]
infix   8  _[_]v
\end{code}
%endif

\section{The naive approach}
\label{sec:naive-approach}

First, we review the copy-and-paste approach. 
We define types (|A, B, C|) and contexts (|Γ, Δ, Θ|):

\noindent
\begin{minipage}{0.45\textwidth}
\begin{code}
data Ty : Set where
  o    : Ty
  _⇒_  : Ty → Ty → Ty
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
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

\noindent
Next, we introduce intrinsically typed de Bruijn variables (|i, j, k|) and
$\lambda$-terms (|t, u, v|):

\noindent
%if jfpstyle
\begin{minipage}{0.45\textwidth}
%else
\begin{minipage}{0.45\textwidth}
%endif
\begin{code}
data _∋_ : Con → Ty → Set where 
  zero  :  Γ ▷ A ∋ A
  suc   :  Γ ∋ A → (B : Ty) 
        →  Γ ▷ B ∋ A
\end{code}
\end{minipage}
%\hfill
%if jfpstyle
\begin{minipage}{0.5\textwidth}
%else
\begin{minipage}{0.5\textwidth}
%endif
\begin{code}
data _⊢_ : Con → Ty → Set where 
  `_   :  Γ ∋ A → Γ ⊢ A
  _·_  :  Γ ⊢ A ⇒ B → Γ ⊢ A →  Γ ⊢ B
  ƛ_   :  Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
\end{code}
\end{minipage}

\noindent
The constructor |`_| embeds variables in
$\lambda$-terms and we write applications as |t · u|.
Following de~Bruijn, lambda abstraction |ƛ_| doesn't bind a name explicitly.
Instead, variables count the number of binders between them and their binding site. 
Substitutions (|ts, us, vs|) are sequences of terms:
\begin{code}
data _⊩_ : Con → Con → Set where
  ε    : Γ ⊩ •
  _,_  : Γ ⊩ Δ → Γ ⊢ A → Γ ⊩ Δ ▷ A  
\end{code}
% To define the categorical structure (|_∘_|, |id|) we first must
% define substitution for terms and variables:
Now we attempt to define the action of substitution for terms and variables:

%if False
\begin{code}
_^_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ ▷ A
\end{code}
%endif
\noindent
%if jfpstyle
\begin{minipage}{0.5\textwidth}
%else
\begin{minipage}{0.45\textwidth}
%endif
\begin{code}
_v[_] : Γ ∋ A → Δ ⊩ Γ → Δ ⊢ A
zero       v[ ts , t ] = t
(suc i _)  v[ ts , t ] = i v[ ts ]
\end{code}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{spec}
_[_] : Γ ⊢ A → Δ ⊩ Γ → Δ ⊢ A
(` i)    [ ts ] = i v[ ts ]
(t · u)  [ ts ] = (t [ ts ]) · (u [ ts ])
(ƛ t)    [ ts ] = ƛ ?
\end{spec}
\end{minipage}

\noindent
We encounter a problem with the case for binders |ƛ_|. We are given a
substitution |ts : Δ ⊩ Γ| but the body lives in the extended context
|t : Γ , A ⊢ B|. We exploit functoriality of context extension (|_▷_|),
|_^_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ ▷ A|, and write 
|(ƛ t) [ ts ] =  ƛ (t [ ts ^ _ ])|.

%if false
\begin{code}
_[_] : Γ ⊢ A → Δ ⊩ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
(ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])
\end{code}
%endif

Now, we must define |_^_|. This is easy (isn't it?), but we
need weakening of substitutions (|_⁺_|):

\noindent
\begin{minipage}{0.45\textwidth}
\begin{spec}
ts ^ A = ts ⁺ A , ` zero 
\end{spec}
\end{minipage}
\begin{minipage}{0.5\textwidth}
\begin{spec}
_⁺_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ
\end{spec}
\end{minipage}

%if False
\begin{code}
_⁺_ : Γ ⊩ Δ → (A : Ty) → Γ ▷ A ⊩ Δ
ts ^ A = ts ⁺ A , ` zero 
\end{code}
%endif

\noindent
Which, in turn, is just a fold of term-weakening (|suc-tm|) over substitutions:

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
\begin{minipage}{0.5\textwidth}
\begin{spec}
suc-tm : Γ ⊢ B → (A : Ty) → Γ ▷ A ⊢ B
\end{spec}
\end{minipage}

\noindent
But how can we define |suc-tm| when we only have weakening for variables (|vs|)? 
If we
already had identity |id : Γ ⊩ Γ| and substitution we could write:
|suc-tm t A = t [ id ⁺ A ] |, 
but this is not structurally recursive (and is rejected
by Agda's termination checker).

To fix this, we use that |id| is a renaming, i.e.
a substitution only containing variables,
and defining |_⁺v_| for renamings is easy.
This leads to a structurally recursive definition,
though with some repetition.
\vspace{-3ex}
%\centering
\noindent
\begin{code}
data _⊩v_ : Con → Con → Set where
  ε   : Γ ⊩v •
  _,_ : Γ ⊩v Δ → Γ ∋ A → Γ ⊩v Δ ▷ A
\end{code}
\noindent
%\justifying
%if jfpstyle
\begin{minipage}{0.45\textwidth}
%else
\begin{minipage}{0.5\textwidth}
% \vspace{-2ex}
%endif
\begin{code}
_v[_]v : Γ ∋ A → Δ ⊩v Γ → Δ ∋ A
zero       v[ is , i ]v  = i
(suc i _)  v[ is , j ]v  = i v[ is ]v

_⁺v_ : Γ ⊩v Δ → ∀ A → Γ ▷ A ⊩v Δ
ε         ⁺v A           = ε
(is , i)  ⁺v A           = is ⁺v A , suc i A

_^v_ : Γ ⊩v Δ → ∀ A → Γ ▷ A ⊩v Δ ▷ A
is ^v A                  = is ⁺v A , zero 
\end{code}
\end{minipage}
\hfill
%if jfpstyle
\begin{minipage}{0.5\textwidth}
\begin{code}
_[_]v : Γ ⊢ A → Δ ⊩v Γ → Δ ⊢ A
(` i)    [ is ]v  =  ` (i v[ is ]v)
(t · u)  [ is ]v  =  
  (t [ is ]v) · (u [ is ]v)
(ƛ t)    [ is ]v  =  ƛ (t [ is ^v _ ]v)

idv : Γ ⊩v Γ
idv {Γ = •}      = ε
idv {Γ = Γ ▷ A}  = idv ^v A

suc-tm t A       = t [ idv ⁺v A ]v
\end{code}
%else
\begin{minipage}{0.45\textwidth}
% \vspace{-2ex}
\begin{spec}
_[_]v : Γ ⊢ A → Δ ⊩v Γ → Δ ⊢ A
(` i)    [ is ]v  =  ` (i v[ is ]v)
(t · u)  [ is ]v  =  (t [ is ]v) · (u [ is ]v)
(ƛ t)    [ is ]v  =  ƛ (t [ is ^v _ ]v)

idv : Γ ⊩v Γ
idv {Γ = •}      = ε
idv {Γ = Γ ▷ A}  = idv ^v A

suc-tm t A       = t [ idv ⁺v A ]v
\end{spec}
%endif
\end{minipage}

\noindent
This may not seem too bad, but it gets worse when proving the laws.
Let |_∘_| be composition of substitutions.
To prove associativity, we first need functoriality,
|[∘] : t [ us ∘ vs ] ≡ t [ us ] [ vs ]| but to prove this, we also need
to cover all variations where |t, us, vs| are variables/renamings rather than 
terms/substitutions. This leads to eight combinations, with the cases for
each constructor of |t| reading near-identically.
This repetition is emblematic of many prior attempts at mechanising
substitution
\cite{adams2004formal, benton2012strongly, schafer2015autosubst, 
stark2019autosubst, saffrich2024intrinsically}.

The rest of the paper shows how to factor these definitions
and proofs, using only (lexicographic) structural recursion.
