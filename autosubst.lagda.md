A version of substitution inspired by
  Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution
  Seven Schäfer, Tobias Tebbi, Gert Smolka
  Proc. of ITP 2015, Nanjing, China, Springer LNAI

```
{-# OPTIONS --prop --rewriting #-}
module autosubst where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊢[_]_
infix   3  _⊨[_]_
infixl  4  _,_
infix   5  _⨾_
infix   5  ƛ_
infixr  6  _⇒_
infixl  6  _·_
infix   7  `_
infix   8  _↑
infix   8  _⇑
infix   8  _[_]
```

Types and contexts
```
data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

variable
  A B C : Ty

data Con : Set where
  ∅ : Con
  _,_ : Con → Ty → Con

variable
  Γ Δ Θ Ξ : Con
```

Sorts
```
data Sort : Set where
  V : Sort
  T⊐V : (q : Sort) → q ≡ V → Sort

pattern T = T⊐V V refl

variable
  q r s : Sort
```

Kits, variables, and terms
```
data _⊢[_]_ : Con → Sort → Ty → Set

_∋_ : Con → Ty → Set
Γ ∋ A  =  Γ ⊢[ V ] A

_⊢_ : Con → Ty → Set
Γ ⊢ A  =  Γ ⊢[ T ] A

data _⊢[_]_ where
  zero : Γ , A ∋ A
  suc  : Γ ∋ A → Γ , B ∋ A
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ , A ⊢ B → Γ ⊢ A ⇒ B

variable
  x y z : Γ ∋ A
  L M N : Γ ⊢ A
  P Q R : Γ ⊢[ q ] A

data _⊨[_]_ : Con → Sort → Con → Set where
  ∅   : Γ ⊨[ q ] ∅
  _,_ : Γ ⊨[ q ] Δ → Γ ⊢[ q ] A → Γ ⊨[ q ] Δ , A

variable
  ρ σ τ    : Γ ⊨[ q ] Δ
```

Basic properties of sorts
```
data _⊑_ : Sort → Sort → Set where
  rfl : q ⊑ q
  V⊏T : V ⊑ T

⊔-tran : q ⊑ r → r ⊑ s → q ⊑ s
⊔-tran rfl r⊑s = r⊑s
⊔-tran V⊏T rfl = V⊏T

_⊔_ : Sort → Sort → Sort
V ⊔ q  =  q
T ⊔ q  =  T

⊔-right : q ⊔ V ≡ q
⊔-right {V} = refl
⊔-right {T} = refl

⊔-top : q ⊔ T ≡ T
⊔-top {V} = refl
⊔-top {T} = refl

⊔-sym : q ⊔ r ≡ r ⊔ q
⊔-sym {V} {r} rewrite ⊔-right {r} = refl
⊔-sym {T} {r} rewrite ⊔-top   {r} = refl

⊔-assoc : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔-assoc {V} = refl
⊔-assoc {T} = refl

⊑T : q ⊑ T
⊑T {V} = V⊏T
⊑T {T} = rfl

V⊑ : V ⊑ q
V⊑ {V} = rfl
V⊑ {T} = V⊏T

⊑⊔₁ : q ⊑ (q ⊔ r)
⊑⊔₁ {q = V} = V⊑
⊑⊔₁ {q = T} = rfl

⊑⊔₂ : r ⊑ (q ⊔ r)
⊑⊔₂ {q = V} = rfl
⊑⊔₂ {q = T} = ⊑T

{-# REWRITE ⊔-assoc ⊔-right ⊔-top #-}
```

Promotions
```
lift : q ⊑ r → Γ ⊢[ q ] A → Γ ⊢[ r ]  A
lift rfl P = P
lift V⊏T x = ` x

lift* : q ⊑ r → Γ ⊨[ q ] Δ → Γ ⊨[ r ] Δ
lift* q⊑r ∅ = ∅
lift* q⊑r (σ , xL) = lift* q⊑r σ , lift q⊑r xL

vr : Γ ∋ A → Γ ⊢[ q ] A
vr = lift V⊑

tm : Γ ⊢[ q ] A → Γ ⊢ A
tm = lift ⊑T
```

Shift, instantiation, id, composition to be defined later
```
⤊  : {q : Sort} {Γ : Con} {A : Ty} → Γ , A ⊨[ q ] Γ -- (a)
id : {q : Sort} {Γ : Con} → Γ ⊨[ q ] Γ              -- (a)
_⇑ : Δ ⊨[ q ] Γ → Δ , A ⊨[ q ] Γ
_[_] : Γ ⊢[ q ] A → Δ ⊨[ r ] Γ → Δ ⊢[ q ⊔ r ] A
_⨾_ : Θ ⊨[ q ] Γ → Δ ⊨[ r ] Θ → Δ ⊨[ q ⊔ r ] Γ
```

QUESTION: If I change the signature of the marked lines to

    ⤊ : {Γ : Con} {A : Ty} → Γ , A ⊨[ V ] Γ  -- (a)
    id : {Γ : Con} → Γ ⊨[ V ] Γ              -- (a)

and remove the {V} parameters below, then Agda complains of
non-termination. Why? Is there a fix? (Error message reported at end.)

Zero and successor, generalised
```
● : {q : Sort} {Γ : Con} {A : Ty} → Γ , A ⊢[ q ] A
● {V}  =  zero
● {T}  =  ` zero

_↑ : Γ ⊢[ q ] A → Γ , B ⊢[ q ] A
_↑ {q = V} x  =  suc x
_↑ {q = T} M  =  M [ ⤊ {V} ]
```

Identity and composition
```
id {Γ = ∅}      =  ∅
id {Γ = Γ , A}  =  ⤊ , ●

∅       ⨾ τ  =  ∅
(σ , P) ⨾ τ  =  (σ ⨾ τ) , (P [ τ ])
```

Shift and instantiation
```
∅       ⇑  =  ∅
(σ , P) ⇑  =  σ ⇑ , P ↑

⤊ = id ⇑

zero    [ σ , P ]  =  P
(suc x) [ σ , P ]  =  x [ σ ]
(` x)   [ σ ]      =  tm (x [ σ ])
(ƛ N)   [ σ ]      =  ƛ (N [ σ ⇑ , ● ])  -- (b)
(L · M) [ σ ]      =  (L [ σ ]) · (M [ σ ])
```

QUESTION (b): If the equation for ƛ is instead written

    (ƛ N) [ σ ] =  ƛ (N [ σ ⨾ ⤊ {V} , ● ])

then Agda complains about termination. Why? Is there a fix?
(Error message reported at end.)

Other equations to prove.
Apart from the first postulate, these correspond to Figure 1 of the Autosubst paper.
Four of the rules in that paper are not listed, because they are definitional equalities.
```
postulate
  ⇑→⤊    :   {σ : Δ ⊨[ q ] Γ} → σ ⇑ ≡ σ ⨾ ⤊ {V} {Δ} {A} -- (c)
  ⤊⨾     :   ⤊ {V} ⨾ (σ , P) ≡ σ
  [id]   :   P [ id {V} ] ≡ P
  ⤊⨾,●[] :   (⤊ {V} ⨾ σ , ● {V} [ σ ]) ≡ σ
  id⨾    :   id {V} ⨾ σ ≡ σ
  ⨾id    :   σ ⨾ id {V} ≡ σ
  ⨾⨾     :   {ρ : Θ ⊨[ q ] Γ} {σ : Ξ ⊨[ r ] Θ} {τ : Δ ⊨[ s ] Ξ} → -- (c)
               (ρ ⨾ σ) ⨾ τ ≡ ρ ⨾ (σ ⨾ τ)
  [][]   :   {P : Γ ⊢[ q ] A} {σ : Θ ⊨[ r ] Γ} {τ : Δ ⊨[ s ] Θ} → -- (c)
               (P [ σ ]) [ τ ] ≡ P [ σ ⨾ τ ]
  ⤊,●     :   (⤊ {V} {Γ} {A} , ●) ≡ id

{-# REWRITE ⇑→⤊ ⤊⨾ [id] ⤊⨾,●[] id⨾ ⨾id ⨾⨾ [][] ⤊,● #-}
```

QUESTION (c): Is there a way to get rid of the implicit parameters
required for these three rules?

------------------------------------------------------------------------
ERROR (a):

Termination checking failed for the following functions:
  ⤊, _⇑, _[_], _↑
Problematic calls:
  M [ ⤊ ]
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:179,20-25)
  ⤊ (at /Users/wadler/papers-substitution/autosubst.lagda.md:179,22-23)
  P ↑
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:194,23-24)
  id ⇑
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:196,8-9)
  σ ⇑
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:201,32-33)
  L [ σ ]
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:202,26-31)

------------------------------------------------------------------------
ERROR (b):

/Users/wadler/papers-substitution/autosubst.lagda.md:156,1-194,44
Termination checking failed for the following functions:
  _[_], _⨾_
Problematic calls:
  P [ τ ]
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:180,30-35)
  N [ σ ⨾ ⤊ , ● ]
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:193,28-45)
  σ ⨾ ⤊
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:193,32-33)
  L [ σ ]
    (at /Users/wadler/papers-substitution/autosubst.lagda.md:194,26-31)
------------------------------------------------------------------------
