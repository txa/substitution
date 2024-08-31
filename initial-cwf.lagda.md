```
{-# OPTIONS --cubical --rewriting #-}

open import Level
open import Agda.Primitive.Cubical
open import Relation.Binary.PropositionalEquality using (refl; erefl) 
  renaming (_≡_ to _≡ᵢ_)

module initial-cwf where

-- Utilities

private variable
  ℓ : Level

_≡_ : ∀ {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} x y = PathP (λ _ → A) x y

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ p ]≡ y = PathP (λ i → p i) x y

infix 4 _≡_ _≡[_]≡_

≡ᵢ→≡ : ∀ {A : Set ℓ} {x y : A} → x ≡ᵢ y → x ≡ y
≡ᵢ→≡ {x = x} refl = λ _ → x

≡→≡ᵢ : ∀ {A : Set ℓ} {x y : A} → x ≡ y → x ≡ᵢ y
≡→≡ᵢ {x = x} p = primTransp (λ i → x ≡ᵢ p i) i0 (erefl x)

-- End utilities

infix   3  _⊢_
infix   3  _⊨_
infixl  4  _▷_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixr  6  _⇒_
infixl  6  _·_
infix   8  _[_]

data Con : Set
data Ty  : Set

data Con where
  •   : Con
  _▷_ : Con → Ty → Con

data Ty where
  o : Ty
  _⇒_ : Ty → Ty → Ty

data Code : Set where
  tm  : Con → Ty → Code
  tms : Con → Con → Code

data Syn : Code → Set

_⊢_ : Con → Ty → Set
Γ ⊢ A = Syn (tm Γ A)

_⊨_ : Con → Con → Set
Δ ⊨ Γ = Syn (tms Δ Γ)

variable
  Γ Δ θ Ξ : Con
  A B C D : Ty
  M N L : Γ ⊢ A
  δ σ ξ : Δ ⊨ Γ

_^_ : Δ ⊨ Γ → ∀ A → Δ ▷ A ⊨ Γ ▷ A

data Syn where
  id  : Γ ⊨ Γ
  _∘_ : Δ ⊨ Γ → θ ⊨ Δ → θ ⊨ Γ
  id∘ : id ∘ δ ≡ δ
  ∘id : δ ∘ id ≡ δ
  ∘∘  : (ξ ∘ σ) ∘ δ ≡ ξ ∘ (σ ∘ δ)

  _[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
  [id] : M [ id ] ≡ M
  [∘]  : M [ σ ] [ δ ] ≡ M [ σ ∘ δ ]

  ε   : Δ ⊨ •
  _,_ : Δ ⊨ Γ → Δ ⊢ A → Δ ⊨ (Γ ▷ A)
  π₀ : Δ ⊨ Γ ▷ A → Δ ⊨ Γ
  π₁ : Δ ⊨ Γ ▷ A → Δ ⊢ A

  •-η  : δ ≡ ε
  ▷-β₀ : π₀ (δ , M) ≡ δ
  ▷-β₁ : π₁ (δ , M) ≡ M
  ▷-η  : (π₀ δ , π₁ δ) ≡ δ
  π₀∘  : π₀ (σ ∘ δ) ≡ π₀ σ ∘ δ
  π₁∘  : π₁ (σ ∘ δ) ≡ (π₁ σ) [ δ ]

  _·_ : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_  : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B
  ·[] : (M · N) [ δ ] ≡ M [ δ ] · N [ δ ]
  ƛ[] : (ƛ M) [ δ ] ≡ ƛ (M [ δ ^ A ])

wk : Γ ▷ A ⊨ Γ
wk = π₀ id

vz : Γ ▷ A ⊢ A 
vz = π₁ id

δ ^ A = (δ ∘ wk) , vz
```

```
open import cwf-simple renaming (CwF-simple to CwF)

module initial-cwf-is-cwf where
  initial-cwf-is-cwf : CwF
  initial-cwf-is-cwf = record {
    Con = Con;
    Ty = Ty;
    _⊢_ = _⊢_;
    _⊨_ = _⊨_;
    id = id;
    _∘_ = _∘_;
    id∘ = ≡→≡ᵢ id∘;
    ∘id = ≡→≡ᵢ ∘id;
    ∘∘ = ≡→≡ᵢ ∘∘;
    _[_] = _[_];
    [id] = ≡→≡ᵢ [id];
    [∘] = ≡→≡ᵢ [∘];
    • = •;
    ε = ε;
    •-η = ≡→≡ᵢ •-η;
    _▷_ = _▷_;
    _,_ = _,_;
    π₀ = π₀;
    π₁ = π₁;
    ▷-β₀ = ≡→≡ᵢ ▷-β₀;
    ▷-β₁ = ≡→≡ᵢ ▷-β₁;
    ▷-η = ≡→≡ᵢ ▷-η;
    π₀∘ = ≡→≡ᵢ π₀∘;
    π₁∘ = ≡→≡ᵢ π₁∘;
    o = o;
    _⇒_ = _⇒_;
    _·_ = _·_;
    ƛ_ = ƛ_;
    ·[] = ≡→≡ᵢ ·[];
    ƛ[] = ≡→≡ᵢ ƛ[]
    }

module Recursor (cwf : CwF) where
  rec-con : Con → cwf .CwF.Con
  rec-ty  : Ty  → cwf .CwF.Ty
  rec-tms : Δ ⊨ Γ → cwf .CwF._⊨_ (rec-con Δ) (rec-con Γ)
  rec-tm  : Γ ⊢ A → cwf .CwF._⊢_ (rec-con Γ) (rec-ty A)

  -- Directly implementing 'rec-tm' or 'rec-tms' by pattern matching relies on 
  -- injectivity/no confusion, which Cubical Agda does not support. 
  -- Luckily though, if we stay parametric over 'Code' then everything works out
  -- nicely!

  rec-code : Code → Set
  rec-code (tm Γ A) = cwf .CwF._⊢_ (rec-con Γ) (rec-ty A)
  rec-code (tms Δ Γ) = cwf .CwF._⊨_ (rec-con Δ) (rec-con Γ)

  rec-syn : ∀ {c} → Syn c → rec-code c

  rec-con • = cwf .CwF.•
  rec-con (Γ ▷ A) = cwf .CwF._▷_ (rec-con Γ) (rec-ty A)

  rec-ty o = cwf .CwF.o
  rec-ty (A ⇒ B) = cwf .CwF._⇒_ (rec-ty A) (rec-ty B)

  rec-syn id = cwf .CwF.id
  rec-syn (σ ∘ δ) = cwf .CwF._∘_ (rec-tms σ) (rec-tms δ)
  rec-syn (id∘ {δ = δ} i) = ≡ᵢ→≡ (cwf .CwF.id∘ {δ = rec-tms δ}) i
  rec-syn (∘id {δ = δ} i) = ≡ᵢ→≡ (cwf .CwF.∘id {δ = rec-tms δ}) i
  rec-syn (∘∘ {ξ = ξ} {σ = σ} {δ = δ} i) 
    = ≡ᵢ→≡ (cwf .CwF.∘∘ {ξ = rec-tms ξ} {θ = rec-tms σ}  {δ = rec-tms δ}) i
  rec-syn (M [ δ ]) = cwf .CwF._[_] (rec-tm M) (rec-tms δ)
  rec-syn ([id] {M = M} i) = ≡ᵢ→≡ (cwf .CwF.[id] {t = rec-tm M}) i
  rec-syn ([∘] {M = M} {σ = σ} {δ = δ} i) 
    = ≡ᵢ→≡ (cwf .CwF.[∘] {t = rec-tm M} {θ = rec-tms σ} {δ = rec-tms δ}) i
  rec-syn ε = cwf .CwF.ε
  rec-syn (δ , M) = cwf .CwF._,_ (rec-tms δ) (rec-tm M)
  rec-syn (•-η {δ = δ} i) = ≡ᵢ→≡ (cwf .CwF.•-η {δ = rec-tms δ}) i
  rec-syn (π₀ δ) = cwf .CwF.π₀ (rec-tms δ)
  rec-syn (π₁ δ) = cwf .CwF.π₁ (rec-tms δ)
  rec-syn (▷-β₀ {δ = δ} {M = M} i) 
    = ≡ᵢ→≡ (cwf .CwF.▷-β₀ {δ = rec-tms δ} {t = rec-tm M}) i
  rec-syn (▷-β₁ {δ = δ} {M = M} i) 
    = ≡ᵢ→≡ (cwf .CwF.▷-β₁ {δ = rec-tms δ} {t = rec-tm M}) i
  rec-syn (▷-η {δ = δ} i) = ≡ᵢ→≡ (cwf .CwF.▷-η {δ = rec-tms δ}) i
  rec-syn (π₀∘ {σ = σ} {δ = δ} i) 
    = ≡ᵢ→≡ (cwf .CwF.π₀∘ {θ = rec-tms σ} {δ = rec-tms δ}) i
  rec-syn (π₁∘ {σ = σ} {δ = δ} i)
    = ≡ᵢ→≡ (cwf .CwF.π₁∘ {θ = rec-tms σ} {δ = rec-tms δ}) i
  rec-syn (M · N) = cwf .CwF._·_ (rec-tm M) (rec-tm N)
  rec-syn (ƛ M) = cwf .CwF.ƛ_ (rec-tm M)
  rec-syn (·[] {M = M} {N = N} {δ = δ} i) 
    = ≡ᵢ→≡ (cwf .CwF.·[] {t = rec-tm M} {u = rec-tm N} {δ = rec-tms δ}) i
  rec-syn (ƛ[] {M = M} {δ = δ} i) 
    = ≡ᵢ→≡ (cwf .CwF.ƛ[] {t = rec-tm M} {δ = rec-tms δ}) i

  rec-tms = rec-syn
  rec-tm  = rec-syn
```   