
```
{-# OPTIONS --rewriting #-}

open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
  renaming (trans to _∙_)

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
  -- Here, we need to coerce 'xs' and 'x' to 'Sort' 'q ⊔ r'. 
  -- Do-able, but a bit painful...
  stlc .CwF._,_ (tms {qq = q} xs) (tm {qq = r} x) 
    = tms {qq = q ⊔ r} ({!xs!} , tm⊑ (⊑⊔r {q = q}) x)
  stlc .CwF.π₀ (tms (xs , x)) = tms xs
  stlc .CwF.π₁ (tms (xs , x)) = tm x
  stlc .CwF.▷-β₀ = {!!}
  stlc .CwF.▷-β₁ = {!!}
  stlc .CwF.▷-η = {!!}
  stlc .CwF.π₀∘ {θ = tms (xs , x)} = refl
  stlc .CwF.π₁∘ {θ = tms (xs , x)} = refl
  stlc .CwF.o = o
  stlc .CwF._⇒_ = _⇒_
  stlc .CwF._·_ (tm x) (tm y) = tm {qq = T} (tm⊑ ⊑t x · tm⊑  ⊑t y)
  stlc .CwF.ƛ_ (tm x) = tm {qq = T} (ƛ tm⊑ ⊑t x)
  stlc .CwF.·[] = {!!}
  stlc .CwF.ƛ[] = {!!}

module SecondAttempt where

  tm*⊑ : q ⊑ s → Γ ⊨[ q ] Δ → Γ ⊨[ s ] Δ
  tm*⊑ q⊑s ε = ε
  tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x

  _⊢_ = _⊢[ T ]_
  _⊨_ = _⊨[ T ]_

  ⊑∘ : xs ∘ ys ≡ tm*⊑ v⊑t xs ∘ ys
  ⊑∘ {xs = ε} = refl
  ⊑∘ {xs = xs , x} = cong₂ _,_ ⊑∘ refl

  ⊑⁺ : tm*⊑ v⊑t xs ⁺ A ≡ tm*⊑ v⊑t (xs ⁺ A)
  ⊑⁺ {xs = ε} = refl
  ⊑⁺ {xs = xs , x} {A = A} = cong₂ _,_ ⊑⁺ 
    (` x [ id ⁺ A ] 
    ≡⟨ cong `_ (⁺-nat[]v {i = x}) ⟩ 
    ` suc (x [ id ]) A
    ≡⟨ cong (λ y → ` suc y A) [id] ⟩
    ` suc x A ∎)

  ⊑^ : tm*⊑ v⊑t xs ^ A ≡ tm*⊑ v⊑t (xs ^ A)
  ⊑^ = cong (_, ` zero) ⊑⁺

  `[⊑] : ∀ {x : Γ ⊢[ V ] A} {ys : Δ ⊨[ V ] Γ} → ` x [ ys ] ≡ x [ tm*⊑ v⊑t ys ]
  `[⊑] {x = zero} {ys = ys , y} = refl
  `[⊑] {x = suc x _} {ys = ys , y} = `[⊑] {x = x}

  [⊑] : ∀ {x : Γ ⊢[ T ] A} {ys : Δ ⊨[ V ] Γ} → x [ ys ] ≡ x [ tm*⊑ v⊑t ys ]
  [⊑] {x = ` x} = `[⊑] {x = x}
  [⊑] {x = x · y} = cong₂ _·_ ([⊑] {x = x}) ([⊑] {x = y})
  [⊑] {x = ƛ x} {ys = ys} = 
    ƛ x [ ys ^ _ ]
    ≡⟨ cong ƛ_ ([⊑] {x = x}) ⟩ 
    ƛ x [ tm*⊑ v⊑t (ys ^ _) ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ ]) (sym ⊑^) ⟩
    ƛ x [ tm*⊑ v⊑t ys ^ _ ] ∎

  ∘⊑ : ∀ {xs : Δ ⊨[ T ] Γ} {ys : Θ ⊨[ V ] Δ} → xs ∘ ys ≡ xs ∘ tm*⊑ v⊑t ys
  ∘⊑ {xs = ε} {ys = ys} = refl
  ∘⊑ {xs = xs , x} = cong₂ _,_ ∘⊑ ([⊑] {x = x})

  ∘id⁺ : {xs : Δ ⊨[ q ] Γ} → xs ⁺ A ≡ xs ∘ id ⁺ A 
  ∘id⁺ {A = A} {xs = xs} =
    xs ⁺ A
    ≡⟨ cong (_⁺ A) (sym ∘id) ⟩
    (xs ∘ id) ⁺ A
    ≡⟨ sym (⁺-nat∘ {xs = xs} {ys = id}) ⟩
    xs ∘ id ⁺ A ∎

  stlc : CwF
  stlc .CwF.Con = Con
  stlc .CwF.Ty = Ty
  stlc .CwF._⊢_ = _⊢_
  stlc .CwF._⊨_ = _⊨_
  stlc .CwF.id = tm*⊑ v⊑t id
  stlc .CwF._∘_ = _∘_
  stlc .CwF.id∘ = sym ⊑∘ ∙ id∘
  stlc .CwF.∘id = sym ∘⊑ ∙ ∘id
  stlc .CwF.∘∘ = sym ∘∘
  stlc .CwF._[_] = _[_]
  stlc .CwF.[id] {t = x} = sym ([⊑] {x = x}) ∙ [id]
  stlc .CwF.[∘] {t = x} = sym ([∘] {x = x})
  stlc .CwF.• = •
  stlc .CwF.ε = ε
  stlc .CwF.•-η {δ = ε} = refl
  stlc .CwF._▷_ = _▷_
  stlc .CwF._,_ = _,_
  stlc .CwF.π₀ (xs , x) = xs
  stlc .CwF.π₁ (xs , x) = x
  stlc .CwF.▷-β₀ = refl
  stlc .CwF.▷-β₁ = refl
  stlc .CwF.▷-η {δ = xs , x} = refl
  stlc .CwF.π₀∘ {θ = xs , x} = refl
  stlc .CwF.π₁∘ {θ = xs , x} = refl
  stlc .CwF.o = o
  stlc .CwF._⇒_ = _⇒_
  stlc .CwF._·_ = _·_
  stlc .CwF.ƛ_ = ƛ_
  stlc .CwF.·[] = refl
  stlc .CwF.ƛ[] {A = A} {t = x} {δ = ys} = 
    ƛ x [ ys ^ A ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (∘id⁺ {A = A} {xs = ys}) ⟩ 
    ƛ x [ ys ∘ id ⁺ A , ` zero ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (∘⊑ {xs = ys} {ys = id ⁺ A}) ⟩
    ƛ x [ ys ∘ tm*⊑ v⊑t (id-poly ⁺ A) , ` zero ] ∎
  
  open import initial-cwf as ICwF 
    using (rec-con; rec-ty; rec-tm; rec-tms
          ; elim-con; elim-ty; elim-tm; elim-tms)
  open ICwF.Motive
  open ICwF.Cases

  Con≡ : rec-con stlc Γ ≡ Γ
  Ty≡  : rec-ty stlc A ≡ A

  Con≡ {Γ = •} = refl
  Con≡ {Γ = Γ ▷ A} = cong₂ _▷_ Con≡ Ty≡

  Ty≡ {A = o} = refl
  Ty≡ {A = A ⇒ B} = cong₂ _⇒_ Ty≡ Ty≡

  {-# REWRITE Con≡ Ty≡ #-}

  to-stlc-tm : Γ ICwF.⊢ A → Γ ⊢ A
  to-stlc-tm = rec-tm stlc

  to-stlc-tms : Δ ICwF.⊨ Γ → Δ ⊨ Γ
  to-stlc-tms = rec-tms stlc

  to-cwf-tm : Γ ⊢[ q ] A → Γ ICwF.⊢ A
  to-cwf-tm zero = ICwF.vz
  to-cwf-tm (suc x _) = ICwF.vs (to-cwf-tm x)
  to-cwf-tm (` x) = to-cwf-tm x
  to-cwf-tm (M · N) = to-cwf-tm M ICwF.· to-cwf-tm N
  to-cwf-tm (ƛ M) = ICwF.ƛ (to-cwf-tm M)

  to-cwf-tms : Δ ⊨ Γ → ICwF._⊨_ Δ Γ
  to-cwf-tms ε = ICwF.ε
  to-cwf-tms (δ , M) = to-cwf-tms δ ICwF., to-cwf-tm M

  to-stlc-inv-tm : ∀ {M : Γ ⊢[ q ] A} → to-stlc-tm (to-cwf-tm M) ≡ tm⊑ ⊑t M
  to-stlc-inv-tm {M = zero} = refl
  to-stlc-inv-tm {M = suc x B} = {!   !}
  to-stlc-inv-tm {M = ` x} = to-stlc-inv-tm {M = x}
  to-stlc-inv-tm {M = M · N} 
    = cong₂ _·_ (to-stlc-inv-tm {M = M}) (to-stlc-inv-tm {M = N})
  to-stlc-inv-tm {M = ƛ M} = cong ƛ_ (to-stlc-inv-tm {M = M})

  to-cwf-inv-𝕄 : ICwF.Motive
  to-cwf-inv-𝕄 .Conᴱ _ = ⊤
  to-cwf-inv-𝕄 .Tyᴱ  _ = ⊤
  to-cwf-inv-𝕄 .Tmᴱ Γ A M = to-cwf-tm (to-stlc-tm M) ≡ M
  to-cwf-inv-𝕄 .Tmsᴱ Δ Γ δ = to-cwf-tms (to-stlc-tms δ) ≡ δ

  to-cwf-inv-ℂ : ICwF.Cases to-cwf-inv-𝕄
  to-cwf-inv-ℂ .idᴱ {•} = sym (ICwF.•-η {δ = ICwF.id})
  to-cwf-inv-ℂ .idᴱ {Γ ▷ A} = {!!}
  to-cwf-inv-ℂ ._∘ᴱ_ = {!   !}
  to-cwf-inv-ℂ .id∘ᴱ = {!   !}
  to-cwf-inv-ℂ .∘idᴱ = {!   !}
  to-cwf-inv-ℂ .∘∘ᴱ = {!   !}
  to-cwf-inv-ℂ ._[_]ᴱ Mᴱ δᴱ = {!   !}
  to-cwf-inv-ℂ .[id]ᴱ = {!   !}
  to-cwf-inv-ℂ .[∘]ᴱ = {!   !}
  to-cwf-inv-ℂ .•ᴱ = {!   !}
  to-cwf-inv-ℂ .εᴱ = {!   !}
  to-cwf-inv-ℂ .•-ηᴱ = {!   !}
  to-cwf-inv-ℂ ._▷ᴱ_ = {!   !}
  to-cwf-inv-ℂ ._,ᴱ_ = {!   !}
  to-cwf-inv-ℂ .π₀ᴱ = {!   !}
  to-cwf-inv-ℂ .π₁ᴱ = {!   !}
  to-cwf-inv-ℂ .▷-β₀ᴱ = {!   !}
  to-cwf-inv-ℂ .▷-β₁ᴱ = {!   !}
  to-cwf-inv-ℂ .▷-ηᴱ = {!   !}
  to-cwf-inv-ℂ .π₀∘ᴱ = {!   !}
  to-cwf-inv-ℂ .π₁∘ᴱ = {!   !}
  to-cwf-inv-ℂ .oᴱ = {!   !}
  to-cwf-inv-ℂ ._⇒ᴱ_ = {!   !}
  to-cwf-inv-ℂ ._·ᴱ_ = {!   !}
  to-cwf-inv-ℂ .ƛᴱ_ = {!   !}
  to-cwf-inv-ℂ .·[]ᴱ = {!   !}
  to-cwf-inv-ℂ .ƛ[]ᴱ = {!   !}


  -- to-cwf-inv-tm : ∀ {M : Γ ICwF.⊢ A} → to-cwf-tm (to-stlc-tm M) ≡ M
  -- to-cwf-inv-tm {M = M} 
  --   = elim-tm {𝕄 = record 
  --   { Conᴱ = λ _ → ⊤
  --   ; Tyᴱ  = λ _ → ⊤
  --   ; Tmᴱ  = λ Γ A M → to-cwf-tm (to-stlc-tm M) ≡ M
  --   ; Tmsᴱ = λ Δ Γ δ → ⊤ }} record 
  --   { idᴱ = tt
  --   ; _∘ᴱ_ = λ where _ _ → tt
  --   ; id∘ᴱ = refl
  --   ; ∘idᴱ = refl
  --   ; ∘∘ᴱ  = refl
  --   ; _[_]ᴱ = λ where {M = M} Mᴱ tt → {!!}
  --   } M
```
    