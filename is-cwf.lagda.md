
```
{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality hiding ([_])

open import cwf-simple renaming (CwF-simple to CwF)
open import paper

module is-cwf where

module FirstAttempt where
  -- Here, we get stuck! 

  record _⊢_ (Γ : Con)(A : Ty) : Set where
    constructor tm
    field
      {qq} : Sort
      xx : Γ ⊢[ qq ] A

  record _⊨_ (Γ Δ : Con) : Set where
    constructor tms
    field
      {qq} : Sort
      xss : Γ ⊨[ qq ] Δ

  variable
    xx yy zz : Γ ⊢ A 
    xss yss zss : Γ ⊨ Δ 

  stlc : CwF
  stlc .CwF.Con = Con
  stlc .CwF.Ty = Ty
  stlc .CwF._⊢_ = _⊢_
  stlc .CwF._⊨_ = _⊨_
  stlc .CwF.id = tms id
  stlc .CwF._∘_ (tms xs) (tms ys) = tms (xs ∘ ys)
  stlc .CwF.id∘ = cong tms id∘
  stlc .CwF.∘id = cong tms ∘id
  stlc .CwF.∘∘ = cong tms (sym ∘∘)
  stlc .CwF._[_] (tm x) (tms xs) = tm (x [ xs ])
  stlc .CwF.[id] = cong tm [id]
  stlc .CwF.[∘] {t = tm x} = cong tm (sym ([∘] {x = x}))
  stlc .CwF.• = •
  stlc .CwF.ε = tms {qq = V} ε
  -- We are stuck!
  stlc .CwF.•-η {δ = tms ε} = {!!}
  stlc .CwF._▷_ = _▷_
  stlc .CwF._,_ (tms xs) (tm x) = tms (xs , {!x!})
  stlc .CwF.π₀ = {!   !}
  stlc .CwF.π₁ = {!   !}
  stlc .CwF.▷-β₀ = {!   !}
  stlc .CwF.▷-β₁ = {!   !}
  stlc .CwF.▷-η = {!   !}
  stlc .CwF.π₀∘ = {!   !}
  stlc .CwF.π₁∘ = {!   !}
  stlc .CwF.o = {!   !}
  stlc .CwF._⇒_ = {!   !}
  stlc .CwF._·_ = {!   !}
  CwF.ƛ stlc = {!   !}
  stlc .CwF.·[] = {!   !}
  stlc .CwF.ƛ[] = {!   !}

module SecondAttempt where

  _⊢_ = _⊢[ T ]_
  _⊨_ = _⊨[ T ]_

```
  