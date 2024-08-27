```
{-# OPTIONS --prop --rewriting #-}
module stlc-proof-naive where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊨_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixr  6  _⇒_
infixl  6  _·_
infixl  6 _,→_
infix   7  `_
infix   8  _^_
infix   8  _↑_
infix   8  _[_]

data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

variable
  A B C : Ty

data Con : Set where
  ∅ : Con
  _,_ : Con → Ty → Con

variable
  Γ Δ Θ : Con

data _∋_ : Con → Ty → Set where 
  zero : Γ , A ∋ A
  suc  : Γ ∋ A → (B : Ty) → Γ , B ∋ A
  
data _⊢_ : Con → Ty → Set where 
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ , A ⊢ B → Γ ⊢ A ⇒ B

data _⊨_ : Con → Con → Set where
  ∅   : Γ ⊨ ∅
  _,_ : Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ Δ , A

_v[_] : Γ ∋ A → Δ ⊨ Γ → Δ ⊢ A
zero    v[ ts , t ]  =  t
(suc i _) v[ ts , t ]  =  i v[ ts ]

{-# TERMINATING #-}
suc-tm : Γ ⊢ B → (A : Ty) → Γ , A ⊢ B

suc-tm* : Γ ⊨ Δ → (A : Ty) → Γ , A ⊨ Δ
suc-tm* ∅ A = ∅
suc-tm* (ts , t) A = suc-tm* ts A , suc-tm t A

id : Γ ⊨ Γ


_^_ : Γ ⊨ Δ → (A : Ty) → Γ , A ⊨ Δ , A
ts ^ A = suc-tm* ts A , ` zero 

_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` i)   [ ts ]       =  i v[ ts ]
(t · u) [ ts ]       =  (t [ ts ]) · (u [ ts ])
(ƛ t)   [ ts ]       =  ƛ (t [ ts ^ _ ])

suc-tm t A = t [ suc-tm* id A ] 

id {∅} = ∅
id {Γ , A} = id ^ A
