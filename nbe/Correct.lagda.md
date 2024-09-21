Normalisation by Evaluation
inspired by Kovacs and Lindley

Philip Wadler, 21 September 2024
```
{-# OPTIONS --rewriting #-}
module Correct where

open import Agda.Builtin.FromNat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to infixl 4 _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Core
open import Nbe
```

# Operators
```
infix 4  _≈_
```


# Category theory

Category
```
record Category : Set₁ where
  field
    Obj   : Set
    morph : Obj → Obj → Set
    ident : ∀ {I} → morph I I
    _∘_   : ∀ {I J K} → morph J K → morph I J → morph I K
    idl   : ∀ {I J}(f : morph I J) → f ∘ ident ≡ f
    idr   : ∀ {I J}(f : morph I J) → ident ∘ f ≡ f
    ass   : ∀ {I J K L}(f : morph K L)(g : morph J K)(h : morph I J) → f ∘ (g ∘ h) ≡ (f ∘ g) ∘ h
open Category
```

Functor
```
record Functor (C D : Category) : Set₁ where
  field
    Obj⇒   : Obj C → Obj D
    morph⇒ : ∀ {I J} → morph C I J → morph D (Obj⇒ I) (Obj⇒ J)
    id⇒    : ∀ {I} → morph⇒ (ident C {I}) ≡ ident D
    ∘⇒     : ∀ {I J K}{f : morph C J K}{g : morph C I J} → morph⇒ (_∘_ C f g) ≡ _∘_ D (morph⇒ f) (morph⇒ g)
open Functor
```

Natural transformation
```
record Nat {C D : Category}(F G : Functor C D) : Set₁ where
  field
    ψ   : ∀ {I} → morph D (Obj⇒ F I) (Obj⇒ G I)
    nat : ∀ {I J}{f : morph C I J} → _∘_ D ψ (morph⇒ F f) ≡ _∘_ D (morph⇒ G f) ψ
```

# Completeness

```
variable
  γ : ⟦ Γ ⟧ᶜ Δ
  v w : ⟦ A ⟧ᵀ Γ
  f : ⟦ A ⇒ B ⟧ᵀ Γ
```

```
complete : (M : Γ ⊢ A) → M ~ ⌜ nf M ⌝nf
complete = {!!}
```

Kripke logical relation for completeness
```
_≈_ : Γ ⊢ A → ⟦ A ⟧ᵀ Γ → Set
_≈_ {Γ = Γ} {A = ι} M v  =  M ~ ⌜ v ⌝nf
_≈_ {Γ = Γ} {A = A ⇒ B} L f  =  ∀ {Δ} (ρ : Δ ⊇ Γ) {M} {v} → (L [ ρ ]ʳ) · M ≈ f ρ v
```

Extension of the above to substitutions
```
data _≈ᶜ_ {Δ} : ∀ {Γ} → Δ ⊨ Γ → ⟦ Γ ⟧ᶜ Δ → Set where
  ∅   : ∀ {σ : Δ ⊨ ∅} → σ ≈ᶜ tt
  _,_ : ∀ {Γ A} {σ : Δ ⊨ Γ} {M : Δ ⊢ A} {γ : ⟦ Γ ⟧ᶜ Δ} {v : ⟦ A ⟧ᵀ Δ}
          → σ ≈ᶜ γ → M ≈ v → (σ ▷ M) ≈ᶜ (γ , v)
```

The logical relation is preserved under substitution
```
preserve-value : (ρ : Δ ⊇ Γ) {M : Γ ⊢ A} {v : ⟦ A ⟧ᵀ Γ} → M ≈ v → M [ ρ ]ʳ ≈ weaken-value ρ v
preserve-value {A = ι} ρ M≈v = {!!}
preserve-value {A = A ⇒ B} ρ L≈f = {!!}

preserve-env : (ρ : Δ ⊇ Γ) {σ : Γ ⊨ Θ} {γ : ⟦ Θ ⟧ᶜ Γ} → σ ≈ᶜ γ → (σ ⨾ʳ ρ) ≈ᶜ weaken-env ρ γ
preserve-env = {!!}
```

