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
