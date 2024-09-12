
```
-- I am relying on type-constructor injectivity for proving dependent UIP
-- I don't know whether injectivity of '_≡_' is provable without this
{-# OPTIONS --rewriting --injective-type-constructors #-}

open import Data.Unit
open import Relation.Binary.PropositionalEquality hiding ([_])
  renaming (trans to _∙_)

open import cwf-simple renaming (CwF-simple to CwF)
open import subst
open import laws

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

  suc[id⁺] : x [ id ⁺ A ] ≡ suc x A
  suc[id⁺] {x = x} {A = A} =
    x [ id ⁺ A ]
    ≡⟨ ⁺-nat[]v {i = x} ⟩ 
    suc (x [ id ]) A
    ≡⟨ cong (λ y → suc y A) [id] ⟩
    suc x A ∎

  ⊑suc : tm⊑ ⊑t (suc[ q ] x A) ≡ tm⊑ ⊑t x [ id ⁺ A ]
  ⊑suc {q = V} {x = x} {A = A} = cong (`_) (sym suc[id⁺])
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

  π₀ : Δ ⊨[ q ] (Γ ▷ A) → Δ ⊨[ q ] Γ
  π₀ (δ , M) = δ

  π₁ : Δ ⊨[ q ] (Γ ▷ A) → Δ ⊢[ q ] A
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
    ƛ x [ ys ∘ tm*⊑ v⊑t (id ⁺ A) , ` zero ] ∎
  
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

  to-cwf-tms : Δ ⊨[ q ] Γ → ICwF._⊨_ Δ Γ
  to-cwf-tms ε = ICwF.ε
  to-cwf-tms (δ , M) = to-cwf-tms δ ICwF., to-cwf-tm M

  to-stlc-inv-tm : ∀ {M : Γ ⊢[ q ] A} → to-stlc-tm (to-cwf-tm M) ≡ tm⊑ ⊑t M
  to-stlc-inv-tm {M = zero} = refl
  to-stlc-inv-tm {M = suc x B} = 
    to-stlc-tm (to-cwf-tm x) [ tm*⊑ v⊑t (id ⁺ B) ]
    ≡⟨ [⊑] {x = to-stlc-tm (to-cwf-tm x)} ⟩
     (to-stlc-tm (to-cwf-tm x)) [ id ⁺ B ]
    ≡⟨ cong (λ M → suc[ _ ] M B) (to-stlc-inv-tm {M = x}) ⟩
    ` x [ id ⁺ B ]
    ≡⟨ cong `_ suc[id⁺] ⟩
    ` suc x B ∎
  to-stlc-inv-tm {M = ` x} = to-stlc-inv-tm {M = x}
  to-stlc-inv-tm {M = M · N} 
    = cong₂ _·_ (to-stlc-inv-tm {M = M}) (to-stlc-inv-tm {M = N})
  to-stlc-inv-tm {M = ƛ M} = cong ƛ_ (to-stlc-inv-tm {M = M})

  to-cwf-π₀ : ∀ {δ : Δ ⊨ (Γ ▷ A)} 
            → to-cwf-tms (π₀ δ) ≡ ICwF.π₀ (to-cwf-tms δ)
  to-cwf-π₀ {δ = δ , M} = sym ICwF.▷-β₀

  to-cwf-π₁ : ∀ {δ : Δ ⊨[ q ] (Γ ▷ A)} 
            → to-cwf-tm (π₁ δ) ≡ ICwF.π₁ (to-cwf-tms δ)
  to-cwf-π₁ {δ = δ , M} = sym ICwF.▷-β₁

  to-cwf-∘ : ∀ {σ : Θ ⊨ Δ} {δ : Δ ⊨ Γ}
           → to-cwf-tms (δ ∘ σ) ≡ to-cwf-tms δ ICwF.∘ to-cwf-tms σ 
  to-cwf-[] : ∀ {M : Γ ⊢[ q ] A} {δ : Δ ⊨[ s ] Γ} 
          → to-cwf-tm (M [ δ ]) ≡ to-cwf-tm M ICwF.[ to-cwf-tms δ ]
  to-cwf-^ : ∀ {δ : Δ ⊨[ q ] Γ}
           → to-cwf-tms (δ ^ A) ≡ to-cwf-tms δ ICwF.^ A
  to-cwf-⁺ : ∀ {δ : Δ ⊨[ q ] Γ}
                → to-cwf-tms (δ ⁺ A) 
                ≡ to-cwf-tms δ ICwF.∘ ICwF.π₀ ICwF.id

  to-cwf-id′ : Sort → to-cwf-tms id ≡ ICwF.id {Γ = Γ}

  -- Our classic termination trick
  to-cwf-id : to-cwf-tms id ≡ ICwF.id {Γ = Γ}
  to-cwf-id = to-cwf-id′ V
  {-# INLINE to-cwf-id #-}

  to-cwf-vz : to-cwf-tm (zero[_] {Γ = Γ} {A = A} q) ≡ ICwF.π₁ ICwF.id

  to-cwf-vz {q = V} = refl
  to-cwf-vz {q = T} = refl

  to-cwf-vs : ∀ {M : Γ ⊢[ q ] A} {B} 
            → to-cwf-tm (suc[ q ] M B) ≡ to-cwf-tm M ICwF.[ ICwF.wk ]
  to-cwf-vs {q = V} = refl
  to-cwf-vs {q = T} {M = M} {B = B} = 
    to-cwf-tm (M [ id ⁺ B ])
    ≡⟨ to-cwf-[] {M = M} ⟩
    to-cwf-tm M ICwF.[ to-cwf-tms (id ⁺ B) ]
    ≡⟨ cong (to-cwf-tm M ICwF.[_]) to-cwf-⁺ ⟩
    to-cwf-tm M ICwF.[ to-cwf-tms id ICwF.∘ ICwF.wk ]
    ≡⟨ cong (λ ρ → to-cwf-tm M ICwF.[ ρ ICwF.∘ ICwF.wk ]) to-cwf-id ⟩
    to-cwf-tm M ICwF.[ ICwF.id ICwF.∘ ICwF.wk ]
    ≡⟨ cong (to-cwf-tm M ICwF.[_]) ICwF.id∘  ⟩
    to-cwf-tm M ICwF.[ ICwF.wk ] ∎

  to-cwf-^ {q = q} {A = A} {δ = δ} 
    = cong₂ ICwF._,_ to-cwf-⁺ (to-cwf-vz {q = q})

  to-cwf-tm⊑ : ∀ {M : Γ ⊢[ q ] A} → to-cwf-tm (tm⊑ ⊑t M) ≡ to-cwf-tm M
  to-cwf-tm⊑ {q = V} = refl
  to-cwf-tm⊑ {q = T} = refl

  to-cwf-tm*⊑ : ∀ {δ : Δ ⊨[ q ] Γ} → to-cwf-tms (tm*⊑ ⊑t δ) ≡ to-cwf-tms δ
  to-cwf-tm*⊑ {δ = ε} = refl
  to-cwf-tm*⊑ {δ = δ , M} = cong₂ ICwF._,_ to-cwf-tm*⊑ (to-cwf-tm⊑ {M = M})
  
  to-cwf-[] {M = zero} {δ = δ , N} = sym (ICwF.vz[] {δ = to-cwf-tms δ})
  to-cwf-[] {M = suc M B} {δ = δ , N} = 
    to-cwf-tm (M [ δ ])
    ≡⟨ to-cwf-[] {M = M} ⟩
    to-cwf-tm M ICwF.[ to-cwf-tms δ ]
    ≡⟨ sym ICwF.vs[] ⟩
    ICwF.vs (to-cwf-tm M) ICwF.[ to-cwf-tms δ ICwF., to-cwf-tm N ] ∎
  to-cwf-[] {M = ` M} {δ = δ} = 
    to-cwf-tm (tm⊑ ⊑t (M [ δ ]))
    ≡⟨ to-cwf-tm⊑ {M = M [ δ ]} ⟩
    to-cwf-tm (M [ δ ])
    ≡⟨ to-cwf-[] {M = M} ⟩
    to-cwf-tm M ICwF.[ to-cwf-tms δ ] ∎
  to-cwf-[] {M = M · N} {δ = δ} = 
    to-cwf-tm (M [ δ ]) ICwF.· to-cwf-tm (N [ δ ])
    ≡⟨ cong₂ ICwF._·_ (to-cwf-[] {M = M}) (to-cwf-[] {M = N}) ⟩
    to-cwf-tm M ICwF.[ to-cwf-tms δ ] ICwF.· to-cwf-tm N ICwF.[ to-cwf-tms δ ]
    ≡⟨ sym ICwF.·[] ⟩
    (to-cwf-tm M ICwF.· to-cwf-tm N) ICwF.[ to-cwf-tms δ ] ∎
  to-cwf-[] {M = ƛ M} {δ = δ} =
    ICwF.ƛ to-cwf-tm (M [ δ ^ _ ])
    ≡⟨ cong ICwF.ƛ_ (to-cwf-[] {M = M} {δ = δ ^ _}) ⟩
    ICwF.ƛ to-cwf-tm M ICwF.[ to-cwf-tms (δ ^ _) ]
    ≡⟨ cong (λ ρ → ICwF.ƛ (to-cwf-tm M ICwF.[ ρ ])) to-cwf-^ ⟩
    ICwF.ƛ to-cwf-tm M ICwF.[ to-cwf-tms δ ICwF.^ _ ]
    ≡⟨ sym ICwF.ƛ[] ⟩
    (ICwF.ƛ to-cwf-tm M) ICwF.[ to-cwf-tms δ ] ∎
  
  to-cwf-∘ {δ = ε} = sym ICwF.•-η
  to-cwf-∘ {σ = σ} {δ = δ , M} = 
    δ∘σ ICwF., M[σ]
    ≡⟨ cong (δ∘σ ICwF.,_) (to-cwf-[] {M = M}) ⟩
    δ∘σ ICwF., (M′ ICwF.[ σ′ ])
    ≡⟨ cong (ICwF._, (M′ ICwF.[ σ′ ])) to-cwf-∘ ⟩
    (δ′ ICwF.∘ σ′) ICwF., (M′ ICwF.[ σ′ ])
    ≡⟨ sym ICwF.∘[] ⟩
    (δ′ ICwF., M′) ICwF.∘ σ′ ∎
    where
      δ∘σ = to-cwf-tms (δ ∘ σ)
      δ′ = to-cwf-tms δ
      σ′ = to-cwf-tms σ
      M′ = to-cwf-tm M
      M[σ] = to-cwf-tm (M [ σ ])

  to-cwf-⁺ {δ = ε} = sym ICwF.•-η
  to-cwf-⁺ {A = A} {δ = δ , M} = 
    to-cwf-tms (δ ⁺ A) ICwF., to-cwf-tm (suc[ _ ] M A)
    ≡⟨ cong₂ ICwF._,_ to-cwf-⁺ (to-cwf-vs {M = M}) ⟩
    (to-cwf-tms δ ICwF.∘ ICwF.π₀ ICwF.id) ICwF., (to-cwf-tm M ICwF.[ ICwF.wk ])
    ≡⟨ sym ICwF.∘[] ⟩
    (to-cwf-tms δ ICwF., to-cwf-tm M) ICwF.∘ ICwF.π₀ ICwF.id ∎

  to-cwf-id′ {Γ = •} _ = sym ICwF.•-η
  to-cwf-id′ {Γ = Γ ▷ A} _ = 
    to-cwf-tms (id ⁺ A) ICwF., ICwF.π₁ ICwF.id
    ≡⟨ cong (λ ρ → ρ ICwF., ICwF.π₁ ICwF.id) to-cwf-⁺ ⟩
    to-cwf-tms id ICwF.^ A
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

  -- This implementation of dependent UIP relies type constructor injectivity
  -- I don't know whether injectivity of '_≡_' is provable otherwise...

  -- If we are also given a proof of 'AB : A ≡ B' and 'x ≡[ AB ]≡ z' then
  -- I think this should be derivable from standard UIP (but I think obligating
  -- callers to provide those extra proofs would be pretty painful)
  duip : ∀ {ℓ} {A B : Set ℓ} {x y : A} {z w : B} {p q} {r : (x ≡ y) ≡ (z ≡ w)}
       → p ≡[ r ]≡ q
  duip {p = refl} {q = refl} {r = refl} = refl

  to-cwf-inv-ℂ : ICwF.Cases to-cwf-inv-𝕄
  to-cwf-inv-ℂ .idᴱ = to-cwf-tm*⊑ ∙ to-cwf-id
  to-cwf-inv-ℂ ._∘ᴱ_ {σ = σ} {δ = δ} σᴱ δᴱ = 
    to-cwf-tms (to-stlc-tms σ ∘ to-stlc-tms δ)
    ≡⟨ to-cwf-∘ ⟩
    to-cwf-tms (to-stlc-tms σ) ICwF.∘ to-cwf-tms (to-stlc-tms δ)
    ≡⟨ cong₂ ICwF._∘_ σᴱ δᴱ ⟩
    σ ICwF.∘ δ ∎
  to-cwf-inv-ℂ ._[_]ᴱ {M = M} {δ = δ} Mᴱ δᴱ =
    to-cwf-tm (to-stlc-tm M [ to-stlc-tms δ ])
    ≡⟨ to-cwf-[] {M = to-stlc-tm M} ⟩
    to-cwf-tm (to-stlc-tm M) ICwF.[ to-cwf-tms (to-stlc-tms δ) ]
    ≡⟨ cong₂ ICwF._[_] Mᴱ δᴱ ⟩
    M ICwF.[ δ ] ∎
  to-cwf-inv-ℂ .•ᴱ = tt
  to-cwf-inv-ℂ .εᴱ = refl
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
  to-cwf-inv-ℂ .oᴱ = tt
  to-cwf-inv-ℂ ._⇒ᴱ_ tt tt = tt
  to-cwf-inv-ℂ ._·ᴱ_ Mᴱ Nᴱ = cong₂ ICwF._·_ Mᴱ Nᴱ
  to-cwf-inv-ℂ .ƛᴱ_ Mᴱ = cong (ICwF.ƛ_) Mᴱ

  -- Boring UIP proofs
  to-cwf-inv-ℂ .id∘ᴱ  = duip
  to-cwf-inv-ℂ .∘idᴱ  = duip
  to-cwf-inv-ℂ .∘∘ᴱ   = duip
  to-cwf-inv-ℂ .[id]ᴱ = duip
  to-cwf-inv-ℂ .[∘]ᴱ  = duip
  to-cwf-inv-ℂ .•-ηᴱ  = duip
  to-cwf-inv-ℂ .▷-β₀ᴱ = duip
  to-cwf-inv-ℂ .▷-β₁ᴱ = duip
  to-cwf-inv-ℂ .▷-ηᴱ  = duip
  to-cwf-inv-ℂ .π₀∘ᴱ  = duip
  to-cwf-inv-ℂ .π₁∘ᴱ  = duip
  to-cwf-inv-ℂ .·[]ᴱ  = duip
  to-cwf-inv-ℂ .ƛ[]ᴱ  = duip

 
  to-cwf-inv-tm : ∀ {M : Γ ICwF.⊢ A} → to-cwf-tm (to-stlc-tm M) ≡ M
  to-cwf-inv-tm {M = M} = elim-tm to-cwf-inv-ℂ M
  ```
  