
```
{-# OPTIONS --rewriting #-}

open import Relation.Binary.PropositionalEquality hiding ([_])

open import cwf-simple
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
  xx yy zz : Γ ⊢ A 
  xss yss zss : Γ ⊨ Δ 

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

∘xidx : xss ∘x idx ≡ xss
∘xidx {xss = record { qq = qq ; xss = xss }} =
  cong (λ xss → record { qq = qq ; xss = xss }) (∘id {xs = xss})

∘x∘x :  xss ∘x (yss ∘x zss) ≡ (xss ∘x yss) ∘x zss
∘x∘x {xss = record { qq = q ; xss = xs }} 
     {yss = record { qq = r ; xss = ys }} 
     {zss = record { qq = s ; xss = zs }} = {!!}

stlc : CwF-simple
stlc = record
         { Con = Con
         ; Ty = Ty
         ; _⊢_ = _⊢_
         ; _⊨_ = _⊨_
         ; id = idx
         ; _∘_ = _∘x_
         ; id∘ = idx∘x
         ; ∘id = ∘xidx
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
