A version of substitution inspired by
  Autosubst: Reasoning with de Bruijn Terms and Parallel Substitution
  Seven Schäfer, Tobias Tebbi, Gert Smolka
  Proc. of ITP 2015, Nanjing, China, Springer LNAI

This version modified to use π₀ and π₁ as in cwf.

```
{-# OPTIONS --prop --rewriting #-}
module autosubst-pi where

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
```

Substitutions
```
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

π₀ and π₁
```
π₀ : Δ ⊨[ q ] Γ , A → Δ ⊨[ q ] Γ
π₀ (σ , P)  =  σ

π₁ : Δ ⊨[ q ] Γ , A → Δ ⊢[ q ] A
π₁ (σ , P)  =  P
```

Identity
```
suc* : Δ ⊨[ V ] Γ → Δ , A ⊨[ V ] Γ
suc* ∅        =  ∅
suc* (σ , x)  =  suc* σ , suc x

`* : Δ ⊨[ V ] Γ → Δ ⊨[ T ] Γ
`* ∅        =  ∅
`* (σ , x)  =  `* σ , ` x

id : {q : Sort} {Γ : Con} → Γ ⊨[ q ] Γ
id {V} {∅} = ∅
id {V} {Γ , A} = suc* (id {V} {Γ}) , zero
id {T} = `* (id {V})
```

Composition, functoriality, instantiation
```
_[_] : Γ ⊢[ q ] A → Δ ⊨[ r ] Γ → Δ ⊢[ q ⊔ r ] A

_⨾_ : Θ ⊨[ q ] Γ → Δ ⊨[ r ] Θ → Δ ⊨[ q ⊔ r ] Γ
∅       ⨾ τ  =  ∅
(σ , P) ⨾ τ  =  (σ ⨾ τ) , (P [ τ ])

_^ : Δ ⊨[ q ] Γ → Δ , A ⊨[ q ] Γ , A
σ ^ = (σ ⨾ π₀ (id {V})) , (π₁ id)

zero    [ σ , P ]     =  P
(suc x) [ σ , P ]     =  x [ σ ]
(` x)   [ σ ]         =  tm (x [ σ ])
_[_] {r = V} (ƛ N) σ  =  ƛ (_[_] {r = V} N (σ ^))
_[_] {r = T} (ƛ N) σ  =  ƛ (_[_] {r = T} N (σ ^))
(L · M) [ σ ]         =  (L [ σ ]) · (M [ σ ])
```

