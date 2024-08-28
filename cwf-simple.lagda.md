```
{-# OPTIONS --rewriting #-}
module cwf-simple where

open import Relation.Binary.PropositionalEquality hiding ([_])

record CwF-simple : Set₁ where
  infix   3  _⊢_
  infix   3  _⊨_
  infixl  4  _▷_
  infixl  4  _,_
  infix   5  _∘_
  infix   5  ƛ_
  infixr  6  _⇒_
  infixl  6  _·_
  infix   8  _[_]
  field
    Con : Set
    Ty : Set
    _⊢_ : Con → Ty → Set
    _⊨_ : Con → Con → Set
    -- category laws
    id : {Γ : Con} → Γ ⊨ Γ
    _∘_ : {Γ Δ Θ : Con} → Δ ⊨ Θ → Γ ⊨ Δ → Γ ⊨ Θ
    id∘ : ∀ {Γ Δ}{δ : Γ ⊨ Δ} → id ∘ δ ≡ δ
    ∘id : ∀ {Γ Δ}{δ : Γ ⊨ Δ} → δ ∘ id ≡ δ
    ∘∘ : ∀ {Γ Δ Θ Ξ}{ξ : Θ ⊨ Ξ}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ}
          → (ξ ∘ θ) ∘ δ ≡ ξ ∘ (θ ∘ δ)
    -- _ ⊢ A is a presheaf
    _[_] : ∀ {Γ Δ A} → Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
    [id] : ∀ {Γ A}{t : Γ ⊢ A} →  (t [ id ]) ≡ t
    [∘] : ∀ {Γ Δ Θ}{A : Ty}{t : Θ ⊢ A}{θ : Δ ⊨ Θ}{δ : Γ ⊨ Δ} →
            t [ θ ] [ δ ] ≡ t [ θ ∘ δ ]
    -- empty context
    • : Con
    ε : {Γ : Con} → Γ ⊨ • 
    •-η : {Γ : Con}{δ : Γ ⊨ •} → δ ≡ ε
    -- context extension
    _▷_ : Con → Ty → Con
    _,_ : ∀ {Γ Δ A} → Γ ⊨ Δ → Γ ⊢ A → Γ ⊨ (Δ ▷ A)
    π₀ : ∀ {Γ Δ A} → Γ ⊨ (Δ ▷ A) → Γ ⊨ Δ
    π₁ : ∀ {Γ Δ A} → Γ ⊨ (Δ ▷ A) → Γ ⊢ A
    ▷-β₀ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₀ (δ , t) ≡ δ
    ▷-β₁ : ∀ {Γ Δ A}{δ : Γ ⊨ Δ}{t : Γ ⊢ A}
           → π₁ (δ , t) ≡ t
    ▷-η : ∀ {Γ Δ A}{δ : Γ ⊨ (Δ ▷ A)}
           → (π₀ δ , π₁ δ) ≡ δ
    π₀∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₀ (θ ∘ δ) ≡ π₀ θ ∘ δ
    π₁∘ : ∀ {Γ Δ Θ}{A : Ty}{θ : Δ ⊨ (Θ ▷ A)}{δ : Γ ⊨ Δ}
           → π₁ (θ ∘ δ) ≡ (π₁ θ) [ δ ]
  _^_ : ∀ {Γ Δ} → Γ ⊨ Δ → ∀ A → Γ ▷ A ⊨ Δ ▷ A
  δ ^ A = (δ ∘ (π₀ id)) , π₁ id
  field
    --- specific for λ-calculus
    o : Ty
    _⇒_ : Ty → Ty → Ty
    _·_  : ∀ {Γ A B} → Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
    ƛ_   : ∀ {Γ A B} → Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B  
    ·[]  : ∀ {Γ Δ A B}{t : Γ ⊢ A ⇒ B}{u : Γ ⊢ A}{δ : Δ ⊨ Γ}
           → (t · u) [ δ ] ≡ (t [ δ ]) · (u [ δ ])
    ƛ[] :  ∀ {Γ Δ A B}{t : Γ ▷ A ⊢ B}{δ : Δ ⊨ Γ}
           → (ƛ t) [ δ ] ≡ ƛ (t [ δ ^ _ ])
    
```

```
open import paper

record _⊢_ (Γ : Con)(A : Ty) : Set where
  field
    qq : Sort
    xx : Γ ⊢[ qq ] A

record _⊨_ (Γ Δ : Con) : Set where
  field
    qq : Sort
    xss : Γ ⊨[ qq ] Δ

variable
  xx yy : Γ ⊢ A 
  xss yss : Γ ⊨ Δ 

idx : Γ ⊨ Γ
idx = record { qq = V ; xss = id }

_∘x_ : Γ ⊨ Θ → Δ ⊨ Γ → Δ ⊨ Θ
record { qq = pp ; xss = xs } ∘x record { qq = qq ; xss = ys } =
  record { qq = pp ⊔ qq ; xss = xs ∘ ys }

tm*⊑rfl : tm*⊑ rfl xs ≡ xs 
tm*⊑rfl {xs = ε} = refl
tm*⊑rfl {xs = xs , x} = cong₂ _,_ (tm*⊑rfl {xs = xs}) refl

{-# REWRITE tm*⊑rfl  #-}

idx∘x : idx ∘x xss ≡ xss
idx∘x {xss = record { qq = qq ; xss = xss }} =
  cong (λ xss → record { qq = qq ; xss = xss }) (id∘ {q = V}{xs = xss})

stlc : CwF-simple
stlc = record
         { Con = Con
         ; Ty = Ty
         ; _⊢_ = _⊢_
         ; _⊨_ = _⊨_
         ; id = idx
         ; _∘_ = _∘x_
         ; id∘ = idx∘x
         ; ∘id = {!!}
         ; ∘∘ = {!!}
         ; _[_] = {!!}
         ; [id] = {!!}
         ; [∘] = {!!}
         ; • = {!!}
         ; ε = {!!}
         ; •-η = {!!}
         ; _▷_ = {!!}
         ; _,_ = {!!}
         ; π₀ = {!!}
         ; π₁ = {!!}
         ; ▷-β₀ = {!!}
         ; ▷-β₁ = {!!}
         ; ▷-η = {!!}
         ; π₀∘ = {!!}
         ; π₁∘ = {!!}
         ; o = {!!}
         ; _⇒_ = {!!}
         ; _·_ = {!!}
         ; ƛ_ = {!!}
         ; ·[] = {!!}
         ; ƛ[] = {!!}
         }

```
