%if False
\begin{code}
{-# OPTIONS --rewriting --local-confluence-check #-}
module laws where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import subst public 
\end{code}
%endif


\section{Proving the laws}
\label{sec:proving-laws}

We now present a formal proof of the categorical laws, proving each
lemma only once while only using structural induction. Indeed 
termination isn't completely trivial but is still inferred by the termination
checker.

\subsection{The right identity law}
\label{sec:right-identity-law}

Let's get the easy case out of the way: the right-identity law 
(|xs ∘ id ≡ xs|). It is easy because it doesn't depend on any other
categorical equations.

The main lemma is the identity law for the substitution functor 
|[id] : x [ id ] ≡ x|.
%if False
\begin{code}
[id] : x [ id ] ≡ x
\end{code}
%endif
To prove the successor case, we need naturality of |suc[ q ]| applied to a 
variable, which can be shown by simple induction over said variable:
\footnote{We are using the naming conventions introduced in sections
  \ref{sec:naive-approach} and \ref{sec:fact-with-sorts}, e.g.
  |i : Γ ∋ A|.}
% ⁺-nat[]v : {i : Γ  ⊢[ V ] B}{xs : Δ ⊩[ q ] Γ}
%   → i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
\begin{code}
⁺-nat[]v : i [ xs ⁺ A ] ≡ suc[ q ] (i [ xs ]) A
⁺-nat[]v {i = zero}     {xs = xs , x} = refl
⁺-nat[]v {i = suc j A}  {xs = xs , x} = ⁺-nat[]v {i = j}
\end{code}
The identity law is now easily provable by structural induction:

\noindent
\begin{minipage}{0.5\textwidth}
\begin{code}
[id] {x = zero}     = refl
[id] {x = suc i A}  = 
   i [ id ⁺ A ]  ≡⟨ ⁺-nat[]v {i = i} ⟩
   suc (i [ id ]) A
   ≡⟨ cong (λ j → suc j A) ([id] {x = i}) ⟩      
   suc i A       ∎
\end{code}
\end{minipage}
\begin{minipage}{0.45\textwidth}
\begin{code}
[id] {x = ` i}    =
   cong `_ ([id] {x = i})
[id] {x = t · u}  =
   cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {x = ƛ t}    =
   cong ƛ_ ([id] {x = t})
\end{code}
\end{minipage}

Note that the |ƛ_| case is easy here: we need the law to hold for
|t :  Γ , A ⊢[ T ] B|, but this is still covered by the inductive hypothesis 
because |id {Γ = Γ , A}  =  id ^ A|.

Note also that is the first time we use Agda's syntax for equational derivations.
This is just syntactic sugar for constructing an equational
derivation using transitivity, exploiting Agda's
flexible syntax. Here |e ≡⟨ p ⟩ e'| means that |p| is a proof of
|e ≡ e'|. Later we will also use the special case |e ≡⟨⟩ e'| which
means that |e| and |e'| are definitionally equal (this corresponds to
|e ≡⟨ refl ⟩ e'| and is just used to make the proof more
readable).  The proof is terminated with |∎| which inserts |refl|.
We also make heavy use of congruence |cong f : a ≡ b → f a ≡ f b|
and a version for binary functions
|cong₂ g : a ≡ b → c ≡ d → g a c ≡ g b d|.

The category law |∘id : xs ∘ id ≡ xs| is now simply a fold of the functor law
(|[id]|).

%if False
\begin{code}
∘id : xs ∘ id ≡ xs
∘id {xs = ε}       = refl
∘id {xs = xs , x}  = cong₂ _,_ (∘id {xs = xs}) ([id] {x = x})
\end{code}
%endif

\subsection{The left identity law}
\label{sec:right-ident}

We need to prove the left identity law mutually with the second
functor law for substitution. This is the main lemma for
associativity. 

Let's state the functor law but postpone the proof until the next section:
|[∘] : x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]|. 
%if False
\begin{code}
[∘] : x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]
\end{code}
%endif
This implicitly relies on the
definitional  equality\footnote{We rely on Agda's 
rewrite rules here.
Alternatively we would have to insert a transport using |subst|.}
|⊔⊔ : q ⊔ (r ⊔ s) = (q ⊔ r) ⊔ s| because the left hand side has the type
|Δ ⊢[  q ⊔ (r ⊔ s) ] A| while the right hand side has type
|Δ ⊢[ (q ⊔ r) ⊔ s ] A|.

Of course, we must also state the left-identity law |id∘ : id ∘ xs ≡ xs|. 
%if False
\begin{code}
id∘ : id ∘ xs ≡ xs
\end{code}
%endif
Similarly to |id|, Agda will not accept a direct implementation of |id∘| as 
structurally recursive. Unfortunately, adapting the law to deal with a
|Sort|-polymorphic |id| complicates matters: when |xs| is a renaming 
(i.e. at sort |V|)
composed with an identity substition (i.e. at sort |T|), its sort must be lifted
on
the RHS (e.g. by extending the |tm⊑| functor to lists of terms) to
obey |_⊔_|. 

Accounting for this lifting is certainly do-able, but in keeping with the
single-responsibility principle of software design, we argue it is neater
to consider only |V|-sorted |id| here and worry about equations involving
|Sort|-coercions later (in \ref{sec:cwf-recurs-subst}).
Therefore, we instead add a ``dummy'' |Sort| argument
(i.e. |id∘′ : Sort → id ∘ xs ≡ xs|) to track the size
decrease (such that we can eventually just use |id∘ = id∘′ V|).
\footnote{Perhaps surprisingly, this ``dummy'' argument does not even need to
be of type |Sort| to satisfy Agda here. More discussion on this trick 
can be found at Agda issue
\href{https://github.com/agda/agda/issues/7693}{\#7693}, but in summary:
\begin{itemize} 
   \item \vspace{-2ex} Agda considers all base constructors (constructors with no parameters) 
   to be of minimal size structurally, so their presence can track size
   preservation of other base-constructor arguments across function calls.
   \item \vspace{-2ex} It turns out that
   a strict decrease in |Sort| is not necessary everywhere for termination: 
   note that the context also gets structurally smaller in the call to |_⁺_| 
   from |id|.
\end{itemize}
}

%if False
\begin{code}
id∘′ : Sort → id ∘ xs ≡ xs
id∘ = id∘′ V
{-# INLINE id∘ #-}
\end{code}
%endif

To prove |id∘′|, we need the $\beta$-law for |_⁺_|,
|xs ⁺ A  ∘ (ys , x) ≡ xs ∘ ys|, which can be shown with a fold over a
corresponding property for |suc[_]|.

%if False
\begin{code}
⁺∘ : xs ⁺ A ∘ (ys , x) ≡ xs ∘ ys
\end{code}
%endif

\noindent
\begin{minipage}{0.5\textwidth}
\begin{code}
suc[] : (suc[ q ] x _) [ ys , y ] ≡ x [ ys ] 
suc[] {q = V} = refl
suc[] {q = T} {x = x} {ys = ys} {y = y} =
  (suc[ T ] x _) [ ys , y ]  ≡⟨⟩
  x [ id ⁺ _ ] [ ys , y ]    
  ≡⟨ sym ([∘] {x = x}) ⟩
  x [ (id ⁺ _) ∘ (ys , y) ]  
  ≡⟨ cong (λ ρ → x [ ρ ]) ⁺∘  ⟩
  x [ id ∘ ys  ]             
  ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
  x [ ys ]  ∎
\end{code}
\end{minipage}
\hfill
\begin{minipage}{0.45\textwidth}
\begin{spec}
⁺∘ : xs ⁺ A ∘ (ys , x) ≡ xs ∘ ys
⁺∘ {xs = ε}       = refl
⁺∘ {xs = xs , x}  = 
   cong₂ _,_  (⁺∘ {xs = xs}) 
              (suc[] {x = x})

id∘′ {xs = ε}       _ = refl
id∘′ {xs = xs , x}  _ = cong₂ _,_
   (id ⁺ _ ∘ (xs , x)  ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs             ≡⟨ id∘ ⟩
   xs                  ∎)
   refl
\end{spec}
\end{minipage}

%if False
\begin{code}
⁺∘ {xs = ε}       = refl
⁺∘ {xs = xs , x}  = 
   cong₂ _,_ (⁺∘ {xs = xs}) (suc[] {x = x})

id∘′ {xs = ε}       _ = refl
id∘′ {xs = xs , x}  _ = cong₂ _,_
   (id ⁺ _ ∘ (xs , x)  ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs             ≡⟨ id∘ ⟩
   xs                  ∎)
   refl
\end{code}
%endif

One may note that
|⁺∘| relies on itself indirectly via |suc[]|. Like with the substitution
operations, termination is justified here by 
the |Sort| decreasing.
%if False
\begin{code}
-- ⁺∘ {xs = ε} = refl
-- ⁺∘ {xs = xs , x} = cong₂ _,_ (⁺∘ {xs = xs}) (suc[] {x = x})
\end{code}
%endif

\subsection{Associativity}
\label{sec:associativity}
We finally get to the proof of the second functor law
(|[∘] : x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]|), the main lemma for
associativity. The main obstacle is that for the |ƛ_| case; we need the
second functor law for context extension:
|^∘ : (xs ∘ ys) ^ A ≡ (xs ^ A) ∘ (ys ^ A)|.
%if False
\begin{code}
^∘ :  {xs : Γ ⊩[ r ] Θ}{ys : Δ ⊩[ s ] Γ}{A : Ty}
      → (xs ∘ ys) ^ A ≡ (xs ^ A) ∘ (ys ^ A)
\end{code}
%endif

To verify the variable case we also need that |tm⊑| commutes with substitution,
|tm[] : tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]|,
which is easy to prove by case analysis.
%if False
\begin{code}
tm[] : {x : Θ ⊢[ q ] A}{xs : Γ ⊩[ r ] Θ}
     → tm⊑ ⊑t (x [ xs ]) ≡ (tm⊑ ⊑t x) [ xs ]
tm[] {q = V} = refl
tm[] {q = T} = refl
\end{code}
%endif

We are now ready to prove |[∘]| by structural induction:

\begin{code}
[∘] {x = zero}     {xs = xs , x}         = refl
[∘] {x = suc i _}  {xs = xs , x}         = [∘] {x = i}
[∘] {x = ` x}      {xs = xs}  {ys = ys}  = 
   tm⊑ ⊑t (x [ xs ∘ ys ])      ≡⟨ cong (tm⊑ ⊑t) ([∘] {x = x}) ⟩
   tm⊑ ⊑t (x [ xs ] [ ys ])    ≡⟨ tm[] {x = x [ xs ]} ⟩        
   (tm⊑ ⊑t (x [ xs ])) [ ys ]  ∎
[∘] {x = t · u}                           = cong₂ _·_ ([∘] {x = t}) ([∘] {x = u})
[∘] {x = ƛ t}      {xs = xs}  {ys = ys}   = cong ƛ_ (
   t [ (xs ∘ ys) ^ _ ]         ≡⟨ cong (λ zs → t [ zs ]) ^∘  ⟩
   t [ (xs ^ _) ∘ (ys ^ _)  ]  ≡⟨ [∘] {x = t} ⟩           
   (t [ xs ^ _ ]) [ ys ^ _ ]   ∎)
\end{code}

% \noindent
% \begin{minipage}{0.5\textwidth}
% \begin{code}
% [∘] {x = zero}     {xs = xs , x}       = 
%    refl
% [∘] {x = suc i _}  {xs = xs , x}       = 
%    [∘] {x = i}
% [∘] {x = ` x}      {xs = xs}{ys = ys}  = 
%    tm⊑ ⊑t (x [ xs ∘ ys ])
%     ≡⟨ cong (tm⊑ ⊑t) ([∘] {x = x}) ⟩
%    tm⊑ ⊑t (x [ xs ] [ ys ])
%     ≡⟨ tm[] {x = x [ xs ]} ⟩        
%    (tm⊑ ⊑t (x [ xs ])) [ ys ] ∎
% \end{code}
% \end{minipage}
% \begin{minipage}{0.35\textwidth}
% \begin{code}
% [∘] {x = t · u}                  =
%    cong₂ _·_ ([∘] {x = t}) ([∘] {x = u})
% [∘] {x = ƛ t}{xs = xs}{ys = ys}  =
%    cong ƛ_ (
%      t [ (xs ∘ ys) ^ _ ]
%      ≡⟨ cong (λ zs → t [ zs ]) ^∘  ⟩
%      t [ (xs ^ _) ∘ (ys ^ _)  ]
%      ≡⟨ [∘] {x = t} ⟩           
%      (t [ xs ^ _ ]) [ ys ^ _ ] ∎)
% \end{code}
% \end{minipage}

Associativity |∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs| can be proven merely by a 
fold of |[∘]| over substitutions.
%if False
\begin{code}
∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs
∘∘ {xs = ε} = refl
∘∘ {xs = xs , x} =
   cong₂ _,_ (∘∘ {xs = xs}) ([∘] {x = x})
\end{code}
%endif

However, we are not done yet. We still need to prove
the second functor law for |_^_| (|^∘|). It turns out that this depends on
the naturality of weakening |⁺-nat∘ : xs ∘ (ys ⁺ A) ≡ (xs ∘ ys) ⁺ A|,
%if False
\begin{code}
⁺-nat∘ : xs ∘ (ys ⁺ A) ≡ (xs ∘ ys) ⁺ A
\end{code}
%endif
which unsurprisingly must be shown by establishing a corresponding
property for substitutions: |⁺-nat[] : x [ xs ⁺ A ] ≡ suc[ _ ] (x [ xs ]) A|.
%if False
\begin{code}
⁺-nat[] : ∀ {x : Γ ⊢[ q ] B} {xs : Δ ⊩[ r ] Γ} 
        → x [ xs ⁺ A ] ≡ suc[ _ ] (x [ xs ]) A
\end{code}
%endif
The case |q = V| is just the naturality for variables which we have
already proven (|⁺-nat[]v|).
%if False
\begin{code}
⁺-nat[] {q = V}{x = i} = ⁺-nat[]v {i = i}
\end{code}
%endif
The case for |q = T| is more interesting and relies again on |[∘]| and
|∘id|:
\begin{code}
⁺-nat[] {q = T} {A = A} {x = x} {xs = xs} = 
   x [ xs ⁺ A ]         ≡⟨ cong (λ zs → x [ zs ⁺ A ]) (sym ∘id) ⟩
   x [ (xs ∘ id) ⁺ A ]  ≡⟨ cong (λ zs → x [ zs ]) (sym (⁺-nat∘ {xs = xs})) ⟩
   x [ xs ∘ (id ⁺ A) ]  ≡⟨ [∘] {x = x} ⟩
   x [ xs ] [ id ⁺ A ]  ∎
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

It also turns out we need 
|zero[]  : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x|, the $\beta$-law for 
|zero[_]|, which holds
definitionally in the case for either |Sort|.

%if False
\begin{code}
zero[]  : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x 
zero[] {q = V} = refl
zero[] {q = T} = refl
\end{code}
%endif 

\noindent
Finally, we have all the ingredients to prove the second functor law |^∘|:
\footnote{Actually, we also need that zero commutes with |tm⊑|: that is for any
|q⊑r : q ⊑ r| we have that |tm⊑zero q⊑r : zero[ r ] ≡ tm⊑ q⊑r zero[ q ]|.}
%if jfpstyle
\begin{code}
^∘ {r = r}{s = s}{xs = xs}{ys = ys} {A = A} = 
    (xs ∘ ys) ^ A                  ≡⟨⟩
    (xs ∘ ys) ⁺ A , zero[ r ⊔ s ]  ≡⟨ cong₂ _,_ (sym (⁺-nat∘ {xs = xs})) refl ⟩
    xs ∘ (ys ⁺ A) , zero[ r ⊔ s ]                
      ≡⟨ cong₂ _,_ refl (tm⊑zero (⊑⊔r {r = s}{q = r})) ⟩        
    xs ∘ (ys ⁺ A) , tm⊑ (⊑⊔r {q = r}) zero[ s ]  
      ≡⟨ cong₂ _,_ (sym (⁺∘ {xs = xs})) (sym (zero[] {q = r}{x = zero[ s ]}))  ⟩    
    (xs ⁺ A) ∘  (ys ^ A) , zero[ r ] [ ys ^ A ]  ≡⟨⟩  
    (xs ^ A) ∘ (ys ^ A)                          ∎
\end{code}
%else
\begin{spec}
^∘ {r = r}{s = s}{xs = xs}{ys = ys} {A = A} = 
    (xs ∘ ys) ^ A                  ≡⟨⟩
    (xs ∘ ys) ⁺ A , zero[ r ⊔ s ]  ≡⟨ cong₂ _,_ (sym (⁺-nat∘ {xs = xs})) refl ⟩
    xs ∘ (ys ⁺ A) , zero[ r ⊔ s ]  ≡⟨ cong₂ _,_ refl (tm⊑zero (⊑⊔r {r = s}{q = r})) ⟩        
    xs ∘ (ys ⁺ A) , tm⊑ (⊑⊔r {q = r}) zero[ s ]  
      ≡⟨ cong₂ _,_ (sym (⁺∘ {xs = xs})) (sym (zero[] {q = r}{x = zero[ s ]}))  ⟩    
    (xs ⁺ A) ∘  (ys ^ A) , zero[ r ] [ ys ^ A ]  ≡⟨⟩  
    (xs ^ A) ∘ (ys ^ A)                          ∎
\end{spec}
%endif
