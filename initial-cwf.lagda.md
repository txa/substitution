```
{-# OPTIONS --rewriting #-}

import Agda.Builtin.Equality.Rewrite

open import Level
open import Relation.Binary.PropositionalEquality hiding ([_])

module initial-cwf where

-- Utilities
 
private variable
  ℓ : Level

infix 4 _≡[_]≡_

_≡[_]≡_ : ∀ {A B : Set ℓ} → A → A ≡ B → B → Set ℓ
x ≡[ refl ]≡ y = x ≡ y

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

postulate
  _⊢_ : Con → Ty → Set
  _⊨_ : Con → Con → Set

variable
  Γ Δ θ Ξ : Con
  A B C D : Ty
  M N L : Γ ⊢ A
  δ σ ξ : Δ ⊨ Γ

postulate
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

wk : Γ ▷ A ⊨ Γ
wk = π₀ id

vz : Γ ▷ A ⊢ A 
vz = π₁ id

_^_ : Δ ⊨ Γ → ∀ A → Δ ▷ A ⊨ Γ ▷ A
δ ^ A = (δ ∘ wk) , vz

postulate
  _·_ : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_  : Γ ▷ A ⊢ B → Γ ⊢ A ⇒ B
  ·[] : (M · N) [ δ ] ≡ M [ δ ] · N [ δ ]
  ƛ[] : (ƛ M) [ δ ] ≡ ƛ (M [ δ ^ A ])

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
    id∘ = id∘;
    ∘id = ∘id;
    ∘∘ = ∘∘;
    _[_] = _[_];
    [id] = [id];
    [∘] = [∘];
    • = •;
    ε = ε;
    •-η = •-η;
    _▷_ = _▷_;
    _,_ = _,_;
    π₀ = π₀;
    π₁ = π₁;
    ▷-β₀ = ▷-β₀;
    ▷-β₁ = ▷-β₁;
    ▷-η = ▷-η;
    π₀∘ = π₀∘;
    π₁∘ = π₁∘;
    o = o;
    _⇒_ = _⇒_;
    _·_ = _·_;
    ƛ_ = ƛ_;
    ·[] = ·[];
    ƛ[] = ƛ[]
    }

module Recursor (cwf : CwF) where
  rec-con : Con → cwf .CwF.Con
  rec-ty  : Ty  → cwf .CwF.Ty

  rec-con • = cwf .CwF.•
  rec-con (Γ ▷ A) = cwf .CwF._▷_ (rec-con Γ) (rec-ty A)

  rec-ty o = cwf .CwF.o
  rec-ty (A ⇒ B) = cwf .CwF._⇒_ (rec-ty A) (rec-ty B)

  postulate
    rec-tms : Δ ⊨ Γ → cwf .CwF._⊨_ (rec-con Δ) (rec-con Γ)
    rec-tm  : Γ ⊢ A → cwf .CwF._⊢_ (rec-con Γ) (rec-ty A)

    rec-tms-idβ : rec-tms (id {Γ}) ≡ cwf .CwF.id
    rec-tms-∘β  : rec-tms (σ ∘ δ) ≡ cwf .CwF._∘_ (rec-tms σ) (rec-tms δ)

    rec-tms-[]β : rec-tm (M [ δ ]) ≡ cwf .CwF._[_] (rec-tm M) (rec-tms δ)

    rec-tms-εβ  : rec-tms (ε {Δ = Δ}) ≡ cwf .CwF.ε
    rec-tms-,β  : rec-tms (δ , M) ≡ cwf .CwF._,_ (rec-tms δ) (rec-tm M)
    rec-tms-π₀β : rec-tms (π₀ δ) ≡ cwf .CwF.π₀ (rec-tms δ)
    rec-tms-π₁β : rec-tm (π₁ δ) ≡ cwf .CwF.π₁ (rec-tms δ)

    rec-tm-·β : rec-tm (M · N) ≡ cwf .CwF._·_ (rec-tm M) (rec-tm N)
    rec-tm-ƛβ : rec-tm (ƛ M) ≡ cwf .CwF.ƛ_ (rec-tm M)


  {-# REWRITE rec-tms-idβ rec-tms-∘β rec-tms-[]β rec-tms-εβ rec-tms-,β 
              rec-tms-π₀β rec-tms-π₁β rec-tm-·β rec-tm-ƛβ #-}

record Motive : Set₁ where
  field
    Conᴱ : Con → Set
    Tyᴱ  : Ty → Set
    Tmᴱ  : Conᴱ Γ → Tyᴱ A → Γ ⊢ A → Set
    Tmsᴱ : Conᴱ Δ → Conᴱ Γ → Δ ⊨ Γ → Set

-- We index by the type constructors so we can generalise over variables of
-- those types
module _ (𝕄 : Motive) where
  open Motive 𝕄

  variable
    Γᴱ Δᴱ θᴱ Ξᴱ : Conᴱ Γ
    Aᴱ Bᴱ Cᴱ Dᴱ : Tyᴱ A
    Mᴱ Nᴱ Lᴱ : Tmᴱ Γᴱ Aᴱ M
    δᴱ σᴱ ξᴱ : Tmsᴱ Δᴱ Γᴱ δ


  record Cases : Set₁ where
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
      
      id∘ᴱ : idᴱ ∘ᴱ δᴱ ≡[ cong (Tmsᴱ Δᴱ Γᴱ) id∘ ]≡ δᴱ
      ∘idᴱ : δᴱ ∘ᴱ idᴱ ≡[ cong (Tmsᴱ Δᴱ Γᴱ) ∘id ]≡ δᴱ
      ∘∘ᴱ  : (ξᴱ ∘ᴱ σᴱ) ∘ᴱ δᴱ ≡[ cong (Tmsᴱ Ξᴱ Γᴱ) ∘∘ ]≡ ξᴱ ∘ᴱ (σᴱ ∘ᴱ δᴱ) 

      _[_]ᴱ : Tmᴱ Γᴱ Aᴱ M → Tmsᴱ Δᴱ Γᴱ δ → Tmᴱ Δᴱ Aᴱ (M [ δ ])
      
      [id]ᴱ : Mᴱ [ idᴱ ]ᴱ ≡[ cong (Tmᴱ Γᴱ Aᴱ) [id] ]≡ Mᴱ
      [∘]ᴱ  : Mᴱ [ σᴱ ]ᴱ [ δᴱ ]ᴱ ≡[ cong (Tmᴱ θᴱ Aᴱ) [∘] ]≡ Mᴱ [ σᴱ ∘ᴱ δᴱ ]ᴱ

      •ᴱ : Conᴱ •
      εᴱ : Tmsᴱ Δᴱ •ᴱ ε

      •-ηᴱ : δᴱ ≡[ cong (Tmsᴱ Δᴱ •ᴱ) •-η ]≡ εᴱ

      _▷ᴱ_ : Conᴱ Γ → Tyᴱ A → Conᴱ (Γ ▷ A)
      _,ᴱ_ : Tmsᴱ Δᴱ Γᴱ δ → Tmᴱ Δᴱ Aᴱ M → Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) (δ , M)
      π₀ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δ → Tmsᴱ Δᴱ Γᴱ (π₀ δ)
      π₁ᴱ  : Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ) δ → Tmᴱ Δᴱ Aᴱ (π₁ δ)

      ▷-β₀ᴱ : π₀ᴱ (δᴱ ,ᴱ Mᴱ) ≡[ cong (Tmsᴱ Δᴱ Γᴱ) ▷-β₀ ]≡ δᴱ
      ▷-β₁ᴱ : π₁ᴱ (δᴱ ,ᴱ Mᴱ) ≡[ cong (Tmᴱ Δᴱ Aᴱ) ▷-β₁ ]≡ Mᴱ
      ▷-ηᴱ  : (π₀ᴱ δᴱ ,ᴱ π₁ᴱ δᴱ) ≡[ cong (Tmsᴱ Δᴱ (Γᴱ ▷ᴱ Aᴱ)) ▷-η ]≡ δᴱ
      π₀∘ᴱ  : π₀ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ cong (Tmsᴱ θᴱ Γᴱ) π₀∘ ]≡ π₀ᴱ σᴱ ∘ᴱ δᴱ
      π₁∘ᴱ  : π₁ᴱ (σᴱ ∘ᴱ δᴱ) ≡[ cong (Tmᴱ θᴱ Aᴱ) π₁∘ ]≡ π₁ᴱ σᴱ [ δᴱ ]ᴱ
    
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
          ≡[ cong (Tmᴱ Δᴱ Bᴱ) ·[] 
          ]≡ Mᴱ [ δᴱ ]ᴱ ·ᴱ Nᴱ [ δᴱ ]ᴱ
      ƛ[]ᴱ : (ƛᴱ Mᴱ) [ δᴱ ]ᴱ 
          ≡[ cong (Tmᴱ Δᴱ (Aᴱ ⇒ᴱ Bᴱ)) ƛ[] 
          ]≡ ƛᴱ (Mᴱ [ δᴱ ^ᴱ Aᴱ ]ᴱ)  

module Eliminator {𝕄} (C : Cases 𝕄) where
  open Motive 𝕄
  open Cases C

  elim-con : ∀ Γ → Conᴱ Γ
  elim-ty  : ∀ A → Tyᴱ  A

  elim-con • = •ᴱ
  elim-con (Γ ▷ A) = (elim-con Γ) ▷ᴱ (elim-ty A)

  elim-ty o = oᴱ
  elim-ty (A ⇒ B) = (elim-ty A) ⇒ᴱ (elim-ty B) 

  postulate
    elim-tm  : ∀ M → Tmᴱ (elim-con Γ) (elim-ty A) M
    elim-tms : ∀ δ → Tmsᴱ (elim-con Δ) (elim-con Γ) δ

    elim-tms-idβ : elim-tms (id {Γ}) ≡ idᴱ
    elim-tms-∘β  : elim-tms (σ ∘ δ) ≡ elim-tms σ ∘ᴱ elim-tms δ

    elim-tms-[]β : elim-tm (M [ δ ]) ≡ elim-tm M [ elim-tms δ ]ᴱ

    elim-tms-εβ  : elim-tms (ε {Δ = Δ}) ≡ εᴱ
    elim-tms-,β  : elim-tms (δ , M) ≡ (elim-tms δ ,ᴱ elim-tm M)
    elim-tms-π₀β : elim-tms (π₀ δ) ≡ π₀ᴱ (elim-tms δ)
    elim-tms-π₁β : elim-tm (π₁ δ) ≡ π₁ᴱ (elim-tms δ)

    elim-tm-·β : elim-tm (M · N) ≡ elim-tm M ·ᴱ elim-tm N
    elim-tm-ƛβ : elim-tm (ƛ M) ≡ ƛᴱ elim-tm M

  {-# REWRITE elim-tms-idβ elim-tms-∘β elim-tms-[]β elim-tms-εβ elim-tms-,β 
              elim-tms-π₀β elim-tms-π₁β elim-tm-·β elim-tm-ƛβ #-}
```