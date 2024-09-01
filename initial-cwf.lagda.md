```
{-# OPTIONS --cubical --rewriting #-}

open import Level
open import Agda.Primitive.Cubical
open import Relation.Binary.PropositionalEquality using (refl; erefl) 
  renaming (_≡_ to _≡ᵢ_)

module initial-cwf where

-- Utilities

private variable
  ℓ ℓ₁ ℓ₂ : Level

_≡_ : ∀ {A : Set ℓ} → A → A → Set ℓ
_≡_ {A = A} x y = PathP (λ _ → A) x y

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ p ]≡ y = PathP (λ i → p i) x y

infix 4 _≡_ _≡[_]≡_

≡ᵢ→≡ : ∀ {A : Set ℓ} {x y : A} → x ≡ᵢ y → x ≡ y
≡ᵢ→≡ {x = x} refl = λ _ → x

≡→≡ᵢ : ∀ {A : Set ℓ} {x y : A} → x ≡ y → x ≡ᵢ y
≡→≡ᵢ {x = x} p = primTransp (λ i → x ≡ᵢ p i) i0 (erefl x)

ap : ∀ {A : Set ℓ₁} {B : Set ℓ₂} (f : A → B) {x y} → x ≡ y → f x ≡ f y
ap f p = λ i → f (p i)

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
  π₁∘  : π₁ (σ ∘ δ) ≡ π₁ σ [ δ ]

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

-- We index by the type constructors so we can generalise over variables of
-- those types
module _ (Conᴱ : Con → Set) (Tyᴱ : Ty → Set) 
         (Tmᴱ : ∀ {Γ A} → Conᴱ Γ → Tyᴱ A → Γ ⊢ A → Set) 
         (Tmsᴱ : ∀ {Δ Γ} → Conᴱ Δ → Conᴱ Γ → Δ ⊨ Γ → Set) 
         where

  variable
    Γᴱ Δᴱ θᴱ Ξᴱ : Conᴱ Γ
    Aᴱ Bᴱ Cᴱ Dᴱ : Tyᴱ A
    Mᴱ Nᴱ Lᴱ : Tmᴱ Γᴱ Aᴱ M
    δᴱ σᴱ ξᴱ : Tmsᴱ Δᴱ Γᴱ δ

  record Motive : Set₁ where
    infixl  4  _▷ᴱ_
    infixl  4  _,ᴱ_
    infix   5  _∘ᴱ_
    infix   5  ƛᴱ_
    infixr  6  _⇒ᴱ_
    infixl  6  _·ᴱ_
    infix   8  _[_]ᴱ
    field
      idᴱ  : Tmsᴱ Γᴱ Γᴱ id 
      _∘ᴱ_ : Tmsᴱ Δᴱ Γᴱ σ → Tmsᴱ θᴱ Δᴱ δ → Tmsᴱ θᴱ Γᴱ (σ ∘ δ)
      
      id∘ᴱ : idᴱ ∘ᴱ δᴱ ≡[ ap (Tmsᴱ Δᴱ Γᴱ) id∘ ]≡ δᴱ
      ∘idᴱ : δᴱ ∘ᴱ idᴱ ≡[ ap (Tmsᴱ Δᴱ Γᴱ) ∘id ]≡ δᴱ
      ∘∘ᴱ  : (ξᴱ ∘ᴱ σᴱ) ∘ᴱ δᴱ ≡[ ap (Tmsᴱ Ξᴱ Γᴱ) ∘∘ ]≡ ξᴱ ∘ᴱ (σᴱ ∘ᴱ δᴱ) 

      _[_]ᴱ : Tmᴱ Γᴱ Aᴱ M → Tmsᴱ Δᴱ Γᴱ δ → Tmᴱ Δᴱ Aᴱ (M [ δ ])
      
      [id]ᴱ : Mᴱ [ idᴱ ]ᴱ ≡[ ap (Tmᴱ Γᴱ Aᴱ) [id] ]≡ Mᴱ
      [∘]ᴱ  : Mᴱ [ σᴱ ]ᴱ [ δᴱ ]ᴱ ≡[ ap (Tmᴱ θᴱ Aᴱ) [∘] ]≡ Mᴱ [ σᴱ ∘ᴱ δᴱ ]ᴱ

      •ᴱ : Conᴱ •
      εᴱ : Tmsᴱ Δᴱ •ᴱ ε

      •-ηᴱ : δᴱ ≡[ ap (Tmsᴱ Δᴱ •ᴱ) •-η ]≡ εᴱ

      _▷ᴱ_ : Conᴱ Γ → Tyᴱ A → Conᴱ (Γ ▷ A)
      _,ᴱ_ : Tmsᴱ Δᴱ Γᴱ δ → Tmᴱ Δᴱ Aᴱ M → Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) (δ , M)
      π₀ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δ → Tmsᴱ Δᴱ Γᴱ (π₀ δ)
      π₁ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δ → Tmᴱ Δᴱ Aᴱ (π₁ δ)

      ▷-β₀ᴱ : π₀ᴱ (δᴱ ,ᴱ Mᴱ) ≡[ ap (Tmsᴱ Δᴱ Γᴱ) ▷-β₀ ]≡ δᴱ
      ▷-β₁ᴱ : π₁ᴱ (δᴱ ,ᴱ Mᴱ) ≡[ ap (Tmᴱ Δᴱ Aᴱ) ▷-β₁ ]≡ Mᴱ
      ▷-ηᴱ  : (π₀ᴱ δᴱ ,ᴱ π₁ᴱ δᴱ) ≡[ ap (Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ)) ▷-η ]≡ δᴱ
      π₀∘ᴱ  : π₀ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ ap (Tmsᴱ θᴱ Γᴱ) π₀∘ ]≡ π₀ᴱ σᴱ ∘ᴱ δᴱ
      π₁∘ᴱ  : π₁ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ ap (Tmᴱ θᴱ Aᴱ) π₁∘ ]≡ π₁ᴱ σᴱ [ δᴱ ]ᴱ
    
    wkᴱ : Tmsᴱ (Γᴱ ▷ᴱ Aᴱ) Γᴱ wk
    wkᴱ = π₀ᴱ idᴱ

    vzᴱ : Tmᴱ (Γᴱ ▷ᴱ Aᴱ) Aᴱ vz
    vzᴱ = π₁ᴱ idᴱ

    _^ᴱ_ : Tmsᴱ Δᴱ Γᴱ δ → ∀ Aᴱ → Tmsᴱ (Δᴱ ▷ᴱ Aᴱ) (Γᴱ ▷ᴱ Aᴱ) (δ ^ A)
    δᴱ ^ᴱ Aᴱ = (δᴱ ∘ᴱ wkᴱ) ,ᴱ vzᴱ

    field
      oᴱ   : Tyᴱ o
      _⇒ᴱ_ : Tyᴱ A → Tyᴱ B → Tyᴱ (A ⇒ B)
      
      _·ᴱ_ : Tmᴱ Γᴱ (Aᴱ ⇒ᴱ Bᴱ) M → Tmᴱ Γᴱ Aᴱ N → Tmᴱ Γᴱ Bᴱ (M · N)
      ƛᴱ_  : Tmᴱ (Γᴱ ▷ᴱ Aᴱ) Bᴱ M → Tmᴱ Γᴱ (Aᴱ ⇒ᴱ Bᴱ) (ƛ M)
      
      ·[]ᴱ : (Mᴱ ·ᴱ Nᴱ) [ δᴱ ]ᴱ 
          ≡[ ap (Tmᴱ Δᴱ Bᴱ) ·[] 
          ]≡ Mᴱ [ δᴱ ]ᴱ ·ᴱ Nᴱ [ δᴱ ]ᴱ
      ƛ[]ᴱ : (ƛᴱ Mᴱ) [ δᴱ ]ᴱ 
          ≡[ ap (Tmᴱ Δᴱ (Aᴱ ⇒ᴱ Bᴱ)) ƛ[] 
          ]≡ ƛᴱ (Mᴱ [ δᴱ ^ᴱ Aᴱ ]ᴱ)

module Eliminator {Conᴱ Tyᴱ} 
                  {Tmᴱ : ∀ {Γ A} → Conᴱ Γ → Tyᴱ A → Γ ⊢ A → Set} 
                  {Tmsᴱ : ∀ {Δ Γ} → Conᴱ Δ → Conᴱ Γ → Δ ⊨ Γ → Set} 
                  (M : Motive Conᴱ Tyᴱ Tmᴱ Tmsᴱ) 
  where
  open Motive M

  elim-con : ∀ Γ → Conᴱ Γ
  elim-ty  : ∀ A → Tyᴱ  A
  elim-tm  : ∀ M → Tmᴱ (elim-con Γ) (elim-ty A) M
  elim-tms : ∀ δ → Tmsᴱ (elim-con Δ) (elim-con Γ) δ

  elim-con • = •ᴱ
  elim-con (Γ ▷ A) = (elim-con Γ) ▷ᴱ (elim-ty A)

  elim-ty o = oᴱ
  elim-ty (A ⇒ B) = (elim-ty A) ⇒ᴱ (elim-ty B)  

  elim-code : ∀ c → Syn c → Set
  elim-code (tm Γ A) M = Tmᴱ (elim-con Γ) (elim-ty A) M
  elim-code (tms Δ Γ) δ = Tmsᴱ (elim-con Δ) (elim-con Γ) δ

  elim-syn : ∀ {c} s → (elim-code c s)
  
  elim-tm M  = elim-syn M
  elim-tms δ = elim-syn δ

  elim-syn id = idᴱ
  elim-syn (δ ∘ σ) = elim-tms δ ∘ᴱ elim-tms σ
  elim-syn (id∘ {δ = δ} i) = id∘ᴱ {δᴱ = elim-tms δ} i
  elim-syn (∘id {δ = δ} i) = ∘idᴱ {δᴱ = elim-tms δ} i
  elim-syn (∘∘ {ξ = ξ} {σ = σ} {δ = δ} i) 
    = ∘∘ᴱ {ξᴱ = elim-tms ξ} {σᴱ = elim-tms σ} {δᴱ = elim-tms δ} i
  elim-syn (M [ δ ]) = elim-tm M [ elim-tms δ ]ᴱ
  elim-syn ([id] {M = M} i) = [id]ᴱ {Mᴱ = elim-tm M} i
  elim-syn ([∘] {M = M} {σ = σ} {δ = δ} i) 
    = [∘]ᴱ {Mᴱ = elim-tm M} {σᴱ = elim-tms σ} {δᴱ = elim-tms δ} i
  elim-syn ε = εᴱ
  elim-syn (δ , M) = elim-tms δ ,ᴱ elim-tm M
  elim-syn (π₀ δ) = π₀ᴱ (elim-tms δ)
  elim-syn (π₁ δ) = π₁ᴱ (elim-tms δ)
  elim-syn (•-η {δ = δ} i) = •-ηᴱ {δᴱ = elim-tms δ} i
  elim-syn (▷-β₀ {δ = δ} {M = M} i) 
    = ▷-β₀ᴱ {δᴱ = elim-tms δ} {Mᴱ = elim-tm M} i
  elim-syn (▷-β₁ {δ = δ} {M = M} i)
    = ▷-β₁ᴱ {δᴱ = elim-tms δ} {Mᴱ = elim-tm M} i
  elim-syn (▷-η {δ = δ} i) 
    = ▷-ηᴱ {δᴱ = elim-tms δ} i
  elim-syn (π₀∘ {σ = σ} {δ = δ} i) = π₀∘ᴱ {σᴱ = elim-tms σ} {δᴱ = elim-tms δ} i
  elim-syn (π₁∘ {σ = σ} {δ = δ} i) = π₁∘ᴱ {σᴱ = elim-tms σ} {δᴱ = elim-tms δ} i
  elim-syn (M · N) = elim-tm M ·ᴱ elim-tm N
  elim-syn (ƛ M) = ƛᴱ (elim-tm M)
  elim-syn (·[] {M = M} {N = N} {δ = δ} i) 
    = ·[]ᴱ {Mᴱ = elim-tm M} {Nᴱ = elim-tm N} {δᴱ = elim-tms δ} i
  elim-syn (ƛ[] {M = M} {δ = δ} i) = ƛ[]ᴱ {Mᴱ = elim-tm M} {δᴱ = elim-tms δ} i
``` 
