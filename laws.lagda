%if False
\begin{code}
{-# OPTIONS --rewriting #-}
module laws where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

open import subst public 
\end{code}
%endif


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
[id] : x [ id ] ≡ x
\end{code}
To prove the successor case we need naturality of |suc[ q ]| but here
only in the case where the term is a variable which can be shown by a
simple induction over the variable:
\footnote{We are using the conventions introduced in sections
  \ref{sec:naive-approach} and \ref{sec:fact-with-sorts}, e.g.
  |i : Γ ∋ A|.}
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
∘id : xs ∘ id ≡ xs
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
This actually uses the definitional equality
\footnote{We use Agda's rewrite here.
Alternatively we would have to insert a transport using |subst|.}
\begin{spec}
⊔⊔ : q ⊔ (r ⊔ s) = (q ⊔ r) ⊔ s
\end{spec}
because the left hand side has the type
\begin{spec}
Δ ⊢[  q ⊔ (r ⊔ s) ] A
\end{spec}
while the right hand side has type
\begin{spec}
Δ ⊢[ (q ⊔ r) ⊔ s ] A.
\end{spec}

Of course, we must also state the left-identity law:

\begin{code}
id∘ : {xs : Γ ⊨[ r ] Δ}
  → id ∘ xs ≡ xs
\end{code}

Similarly to |id|, Agda will not accept a direct implementation of |id∘| as 
structurally recursive, though we solve this error in a slightly more hacky way.
We declare a version of |id∘| which takes an unused |Sort| argument, and then
implement our desired right-identity law by instantiating this unused sort with 
|V|.
\footnote{Alternatively, we could extend sort coercions, |tm⊑|, to 
renamings/substitutions. The proofs end up a bit clunkier this way 
(requiring explicit insertion and removal of these coercions).}

\begin{code}
id∘′ : Sort → {xs : Γ ⊨[ r ] Δ}
  → id ∘ xs ≡ xs

id∘ = id∘′ V
\end{code}

\begin{spec}
{-# INLINE id \circ \; #-}
\end{spec}

%if False
\begin{code}
{-# INLINE id∘ #-}
\end{code}
%endif

To prove it we need the $\beta$-laws for |zero[_]| and |_⁺_|:
\begin{code}
zero[] : zero[ q ] [ xs , x ] ≡ tm⊑ (⊑⊔r {q = q}) x 
⁺∘ : xs ⁺ A  ∘ (ys , x) ≡ xs ∘ ys
\end{code}
As before we state the laws but prove them later.
Now |id∘| can be shown easily:
\begin{code}
id∘′ _ {xs = ε} = refl
id∘′ _ {xs = xs , x} = cong₂ _,_
   (id ⁺ _ ∘ (xs , x)
     ≡⟨ ⁺∘ {xs = id} ⟩
   id ∘ xs 
     ≡⟨ id∘ ⟩
   xs ∎)
   refl
\end{code}

Now we show the $\beta$-laws. |zero[]| is just a simple case analysis over the sort
%if False
\begin{code}
zero[] {q = V} = refl
zero[] {q = T} = refl
\end{code}
%endif
while |⁺∘| relies on a corresponding property for substitution:
\begin{code}
suc[] : {ys : Γ ⊨[ r ] Δ}
    → (suc[ q ] x _) [ ys , y ] ≡ x [ ys ] 
\end{code}

The case for |q = V| is just definitional:
\begin{code}
suc[] {q = V} = refl
\end{code}
% It is simpler now - does it still count as "surprisingly complicated"?
while |q = T| is surprisingly complicated and in particular relies on the functor law |[∘]|.
Using them we can prove:
\begin{code}
suc[] {q = T} {x = x} {y = y} {ys = ys} =
  (suc[ T ] x _) [ ys , y ]
  ≡⟨⟩
  x [ id ⁺ _ ] [ ys , y ]
  ≡⟨ sym ([∘] {x = x}) ⟩
  x [ (id ⁺ _) ∘ (ys , y) ]
  ≡⟨ cong (λ ρ → x [ ρ ]) ⁺∘  ⟩
  x [ id ∘ ys  ]
  ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
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
which unsurprisingly has to be shown by establishing a corresponding
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
   x [ (xs ∘ id) ⁺ A ]     
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
