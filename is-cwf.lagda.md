
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

  idT : Γ ⊨ Γ
  idT = tm*⊑ v⊑t id

  -- Turning these into rewrites might be a good idea...
  ⊑∘ : tm*⊑ v⊑t xs ∘ ys ≡ xs ∘ ys
  ⊑∘ {xs = ε} = refl
  ⊑∘ {xs = xs , x} = cong₂ _,_ ⊑∘ refl

  ⊑suc : tm⊑ ⊑t (suc[ q ] x A) ≡ tm⊑ ⊑t x [ id ⁺ A ]
  ⊑suc {q = V} {x = x} {A = A} =
    ` suc x A 
    ≡⟨ cong (λ y → ` suc y A) (sym [id]) ⟩
    ` suc (x [ id ]) A
    ≡⟨ cong `_ (sym (⁺-nat[]v {i = x})) ⟩ 
    ` x [ id ⁺ A ] ∎
  ⊑suc {q = T} = refl

  ⊑⁺ : tm*⊑ (⊑t {s = q}) (xs ⁺ A) ≡ tm*⊑ ⊑t xs ⁺ A
  ⊑⁺ {xs = ε} = refl
  ⊑⁺ {q = q} {xs = xs , x} {A = A} = cong₂ _,_ ⊑⁺ (⊑suc {x = x})

  ⊑zero : tm⊑ ⊑t zero[ q ] ≡ ` zero {Γ = Γ} {A = A}
  ⊑zero {q = V} = refl
  ⊑zero {q = T} = refl

  ⊑^ : tm*⊑ (⊑t {s = q}) (xs ^ A) ≡ tm*⊑ ⊑t xs ^ A
  ⊑^ {q = q} = cong₂ _,_ ⊑⁺ (⊑zero {q = q})

  `[⊑] : ∀ {x : Γ ⊢[ V ] A} {ys : Δ ⊨[ q ] Γ} 
       → x [ tm*⊑ ⊑t ys ] ≡ tm⊑ ⊑t x [ ys ]
  `[⊑] {x = zero} {ys = ys , y} = refl
  `[⊑] {x = suc x _} {ys = ys , y} = `[⊑] {x = x}

  [⊑] : ∀ {x : Γ ⊢[ T ] A} {ys : Δ ⊨[ q ] Γ} → x [ tm*⊑ ⊑t ys ] ≡ x [ ys ]
  [⊑] {x = ` x} = `[⊑] {x = x}
  [⊑] {x = x · y} = cong₂ _·_ ([⊑] {x = x}) ([⊑] {x = y})
  [⊑] {x = ƛ x} {ys = ys} = 
    ƛ x [ tm*⊑ ⊑t ys ^ _ ]
    ≡⟨ cong (λ ρ → ƛ x [ ρ ]) (sym ⊑^) ⟩
    ƛ x [ tm*⊑ ⊑t (ys ^ _) ]
    ≡⟨ cong ƛ_ ([⊑] {x = x}) ⟩ 
    ƛ x [ ys ^ _ ] ∎

  ∘⊑ : ∀ {xs : Δ ⊨[ T ] Γ} {ys : Θ ⊨[ q ] Δ} → xs ∘ tm*⊑ ⊑t ys ≡ xs ∘ ys
  ∘⊑ {xs = ε} {ys = ys} = refl
  ∘⊑ {xs = xs , x} = cong₂ _,_ ∘⊑ ([⊑] {x = x})
  
  ∘id⁺ : {xs : Δ ⊨[ q ] Γ} → xs ⁺ A ≡ xs ∘ id ⁺ A 
  ∘id⁺ {A = A} {xs = xs} =
    xs ⁺ A
    ≡⟨ cong (_⁺ A) (sym ∘id) ⟩
    (xs ∘ id) ⁺ A
    ≡⟨ sym (⁺-nat∘ {xs = xs} {ys = id}) ⟩
    xs ∘ id ⁺ A ∎

  π₀ : Δ ⊨ (Γ ▷ A) → Δ ⊨ Γ
  π₀ (δ , M) = δ

  π₁ : Δ ⊨ (Γ ▷ A) → Δ ⊢ A
  π₁ (δ , M) = M

  stlc : CwF
  stlc .CwF.Con = Con
  stlc .CwF.Ty = Ty
  stlc .CwF._⊢_ = _⊢_
  stlc .CwF._⊨_ = _⊨_
  stlc .CwF.id = idT
  stlc .CwF._∘_ = _∘_
  stlc .CwF.id∘ = ⊑∘ ∙ id∘
  stlc .CwF.∘id = ∘⊑ ∙ ∘id
  stlc .CwF.∘∘ = sym ∘∘
  stlc .CwF._[_] = _[_]
  stlc .CwF.[id] {t = x} = ([⊑] {x = x}) ∙ [id]
  stlc .CwF.[∘] {t = x} = sym ([∘] {x = x})
  stlc .CwF.• = •
  stlc .CwF.ε = ε
  stlc .CwF.•-η {δ = ε} = refl
  stlc .CwF._▷_ = _▷_
  stlc .CwF._,_ = _,_
  stlc .CwF.π₀ = π₀
  stlc .CwF.π₁ = π₁
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
    ≡⟨ cong (λ ρ → ƛ x [ ρ , ` zero ]) (sym (∘⊑ {xs = ys} {ys = id ⁺ A})) ⟩
    ƛ x [ ys ∘ tm*⊑ v⊑t (id-poly ⁺ A) , ` zero ] ∎
  
  -- Conversion to and from the initial CwF
  
  open import initial-cwf as ICwF 
    using (_≡[_]≡_; rec-con; rec-ty; rec-tm; rec-tms
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

  to-cwf-π₀ : ∀ {δ : Δ ⊨ (Γ ▷ A)} 
            → to-cwf-tms (π₀ δ) ≡ ICwF.π₀ (to-cwf-tms δ)
  to-cwf-π₀ {δ = δ , M} = sym ICwF.▷-β₀

  to-cwf-π₁ : ∀ {δ : Δ ⊨ (Γ ▷ A)} 
            → to-cwf-tm (π₁ δ) ≡ ICwF.π₁ (to-cwf-tms δ)
  to-cwf-π₁ {δ = δ , M} = sym ICwF.▷-β₁

  to-cwf-[] : ∀ {M : Γ ⊢ A} {δ : Δ ⊨ Γ} 
            → to-cwf-tm (M [ δ ]) ≡ to-cwf-tm M ICwF.[ to-cwf-tms δ ]

  to-cwf-⁺ : ∀ {δ : Δ ⊨ Γ} 
          --  → to-cwf-tms (idT ⁺ A) ≡ to-cwf-tms (idT {Γ = Δ}) ICwF.∘ ICwF.π₀ ICwF.id
           → to-cwf-tms (δ ⁺ A) ≡ to-cwf-tms δ ICwF.∘ ICwF.π₀ ICwF.id
  
  to-cwf-⁺-poly : ∀ {δ : Δ ⊨[ q ] Γ} 
                → to-cwf-tms (tm*⊑ ⊑t (δ ⁺ A)) 
                ≡ to-cwf-tms (tm*⊑ ⊑t δ) ICwF.∘ ICwF.π₀ ICwF.id
  to-cwf-⁺-poly {δ = ε} = sym ICwF.•-η
  to-cwf-⁺-poly {q = q} {A = A} {δ = δ , M} = 
    to-cwf-tms (tm*⊑ ⊑t (δ ⁺ A)) ICwF., to-cwf-tm (tm⊑ ⊑t (suc[ q ] M A))
    ≡⟨ {!!} ⟩
    to-cwf-tms (tm*⊑ ⊑t δ ⁺ A) 
      ICwF., (to-cwf-tm (tm⊑ ⊑t M) ICwF.[ ICwF.π₀ ICwF.id ])
    ≡⟨ cong (ICwF._, (to-cwf-tm (tm⊑ ⊑t M) ICwF.[ ICwF.π₀ ICwF.id ])) to-cwf-⁺ ⟩
    (to-cwf-tms (tm*⊑ ⊑t δ) ICwF.∘ ICwF.π₀ ICwF.id) 
      ICwF., (to-cwf-tm (tm⊑ ⊑t M) ICwF.[ ICwF.π₀ ICwF.id ])
    ≡⟨ sym ICwF.∘[] ⟩
    (to-cwf-tms (tm*⊑ ⊑t δ) ICwF., to-cwf-tm (tm⊑ ⊑t M)) 
      ICwF.∘ ICwF.π₀ ICwF.id ∎

  -- Defining this lemma in a terminating way is tricky... We might need to 
  -- introduce sorts again...
  -- to-cwf-⁺ {δ = ε} = sym ICwF.•-η
  -- to-cwf-⁺ {Δ = Δ} {A = A} {δ = δ , M} = 
  --   to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm (M [ id ⁺ A ])
  --   ≡⟨ cong (λ M[] → to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm M[]) (sym ([⊑] {x = M})) ⟩
  --   to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm (M [ tm*⊑ v⊑t (id ⁺ A) ])
  --   ≡⟨ cong (λ ρ → to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm (M [ ρ ])) ⊑⁺ ⟩
  --   to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm (M [ idT ⁺ A ])
  --   ≡⟨ cong (to-cwf-tms (δ ⁺ A) ICwF.,_) (to-cwf-[] {M = M}) ⟩
  --   to-cwf-tms (δ ⁺ A) ICwF., (to-cwf-tm M ICwF.[ to-cwf-tms (idT ⁺ A) ])
  --   ≡⟨ cong (λ ρ → to-cwf-tms (δ ⁺ A) ICwF., (to-cwf-tm M ICwF.[ ρ ])) {!!} ⟩
  --   _ ICwF., (to-cwf-tm M ICwF.[ to-cwf-tms idT ICwF.∘ ICwF.π₀ ICwF.id ])
  --   ≡⟨ {!!} ⟩
  --   _ ICwF., (to-cwf-tm M ICwF.[ ICwF.id ICwF.∘ ICwF.π₀ ICwF.id ])
  --   ≡⟨ cong (λ ρ → to-cwf-tms (δ ⁺ A) ICwF., (to-cwf-tm M ICwF.[ ρ ])) ICwF.id∘ ⟩
  --   to-cwf-tms (δ ⁺ A) ICwF., (to-cwf-tm M ICwF.[ ICwF.π₀ ICwF.id ])
  --   ≡⟨ cong (ICwF._, (to-cwf-tm M ICwF.[ ICwF.π₀ ICwF.id ])) to-cwf-⁺ ⟩
  --   (to-cwf-tms δ ICwF.∘ ICwF.π₀ ICwF.id) ICwF., _
  --   ≡⟨ sym ICwF.∘[] ⟩
  --   (to-cwf-tms δ ICwF., to-cwf-tm M) ICwF.∘ ICwF.π₀ ICwF.id ∎

  to-cwf-id : to-cwf-tms idT ≡ ICwF.id {Γ = Γ}
  to-cwf-id {Γ = •} = sym ICwF.•-η
  to-cwf-id {Γ = Γ ▷ A} = 
    to-cwf-tms (tm*⊑ v⊑t (id ⁺ A)) ICwF., ICwF.π₁ ICwF.id
    ≡⟨ cong (λ ρ → to-cwf-tms ρ ICwF., ICwF.π₁ ICwF.id) ⊑⁺ ⟩
    to-cwf-tms (idT ⁺ A) ICwF., ICwF.π₁ ICwF.id
    ≡⟨ cong (λ ρ → ρ ICwF., ICwF.π₁ ICwF.id) to-cwf-⁺ ⟩
    to-cwf-tms idT ICwF.^ A
    ≡⟨ cong (ICwF._^ A) to-cwf-id ⟩
    ICwF.id ICwF.^ A
    ≡⟨ ICwF.id^ ⟩
    ICwF.id ∎

  to-cwf-inv-𝕄 : ICwF.Motive
  to-cwf-inv-𝕄 .Conᴱ _ = ⊤
  to-cwf-inv-𝕄 .Tyᴱ  _ = ⊤
  to-cwf-inv-𝕄 .Tmᴱ Γ A M = to-cwf-tm (to-stlc-tm M) ≡ M
  to-cwf-inv-𝕄 .Tmsᴱ Δ Γ δ = to-cwf-tms (to-stlc-tms δ) ≡ δ

  -- Paths don't compute outside of Cubical Agda so I think we need UIP
  uip : ∀ {ℓ} {A : Set ℓ} {x y : A} {p q : x ≡ y} → p ≡ q
  uip {p = refl} {q = refl} = refl

  drefl : ∀ {ℓ} {A : Set ℓ} {x} {p : A ≡ A} → x ≡[ p ]≡ x
  drefl {p = refl} = refl

  -- I've left the cases for higher-dimensional paths commented out because they
  -- make typechecking way slower and I plan on just filling them all with UIP 
  -- anyway
  to-cwf-inv-ℂ : ICwF.Cases to-cwf-inv-𝕄
  to-cwf-inv-ℂ .idᴱ = to-cwf-id
  to-cwf-inv-ℂ ._∘ᴱ_ {σ = σ} σᴱ δᴱ = {!  !}
  -- to-cwf-inv-ℂ .id∘ᴱ = {!   !}
  -- to-cwf-inv-ℂ .∘idᴱ = {!   !}
  -- to-cwf-inv-ℂ .∘∘ᴱ = {!   !}
  -- to-cwf-inv-ℂ ._[_]ᴱ Mᴱ δᴱ = {!   !}
  -- to-cwf-inv-ℂ .[id]ᴱ = {!   !}
  -- to-cwf-inv-ℂ .[∘]ᴱ = {!   !}
  to-cwf-inv-ℂ .•ᴱ = tt
  to-cwf-inv-ℂ .εᴱ = refl
  -- to-cwf-inv-ℂ .•-ηᴱ = {!   !}
  to-cwf-inv-ℂ ._▷ᴱ_ tt tt = tt
  to-cwf-inv-ℂ ._,ᴱ_ δᴱ Mᴱ = cong₂ ICwF._,_ δᴱ Mᴱ
  to-cwf-inv-ℂ .π₀ᴱ {δ = δ} δᴱ = 
    to-cwf-tms (to-stlc-tms (ICwF.π₀ δ))
    ≡⟨ to-cwf-π₀ ⟩
    ICwF.π₀ (to-cwf-tms (to-stlc-tms δ))
    ≡⟨ cong ICwF.π₀ δᴱ ⟩
    ICwF.π₀ δ ∎
  to-cwf-inv-ℂ .π₁ᴱ {δ = δ} δᴱ = 
    to-cwf-tm (to-stlc-tm (ICwF.π₁ δ))
    ≡⟨ to-cwf-π₁ ⟩
    ICwF.π₁ (to-cwf-tms (to-stlc-tms δ))
    ≡⟨ cong ICwF.π₁ δᴱ ⟩
    ICwF.π₁ δ ∎
  -- to-cwf-inv-ℂ .▷-β₀ᴱ = {!   !}
  -- to-cwf-inv-ℂ .▷-β₁ᴱ = {!   !}
  -- to-cwf-inv-ℂ .▷-ηᴱ = {!   !}
  -- to-cwf-inv-ℂ .π₀∘ᴱ = {!   !}
  -- to-cwf-inv-ℂ .π₁∘ᴱ = {!   !}
  to-cwf-inv-ℂ .oᴱ = tt
  to-cwf-inv-ℂ ._⇒ᴱ_ tt tt = tt
  to-cwf-inv-ℂ ._·ᴱ_ Mᴱ Nᴱ = cong₂ ICwF._·_ Mᴱ Nᴱ
  to-cwf-inv-ℂ .ƛᴱ_ Mᴱ = cong (ICwF.ƛ_) Mᴱ
  -- to-cwf-inv-ℂ .·[]ᴱ = {!   !}
  -- to-cwf-inv-ℂ .ƛ[]ᴱ = {!!}


  to-cwf-inv-tm : ∀ {M : Γ ICwF.⊢ A} → to-cwf-tm (to-stlc-tm M) ≡ M
  to-cwf-inv-tm {M = M} = elim-tm to-cwf-inv-ℂ M
  ```
