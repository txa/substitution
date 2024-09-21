Normalisation by Evaluation
inspired by Kovacs and Lindley

Philip Wadler, 31 August 2024
```
{-# OPTIONS --rewriting #-}
module Nbe where

open import Agda.Builtin.FromNat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; cong₂; sym)
open Eq.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to infixl 4 _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)
open import Core
```

Operator precedence
```
infix  3 _⊢nf_  _⊢ne_
infix  5 ′_
```

Normal and neutral forms
```
data _⊢nf_ : Con -> Ty -> Set
data _⊢ne_ : Con -> Ty -> Set

data _⊢nf_ where

  ′_ :
      (M : Γ ⊢ne ι)
    → -------------
      Γ ⊢nf ι

  ƛ_ :
      (N : Γ , A ⊢nf B)
    → -------------------
      Γ ⊢nf A ⇒ B

data _⊢ne_ where

  `_ :
      (x : Γ ∋ A)
    → -----------
      Γ ⊢ne A

  _·_ :
      (L : Γ ⊢ne A ⇒ B)
      (M : Γ ⊢nf A)
    → -----------------
      Γ ⊢ne B
```

Converting normal and neutral forms to terms
```
⌜_⌝nf : Γ ⊢nf A -> Γ ⊢ A
⌜_⌝ne : Γ ⊢ne A -> Γ ⊢ A

⌜ ′ M ⌝nf  =  ⌜ M ⌝ne
⌜ ƛ N ⌝nf  =  ƛ ⌜ N ⌝nf

⌜ ` x ⌝ne    =  ` x
⌜ L · M ⌝ne  =  ⌜ L ⌝ne · ⌜ M ⌝nf
```

Renaming normal and neutral forms
```
ren-nf : Δ ⊇ Γ → Γ ⊢nf A → Δ ⊢nf A
ren-ne : Δ ⊇ Γ → Γ ⊢ne A → Δ ⊢ne A

ren-nf ρ (′ M) = ′ (ren-ne ρ M)
ren-nf ρ (ƛ N) = ƛ (ren-nf (ρ ^ʳ _) N)

ren-ne ρ (` x) = ` (ρ x)
ren-ne ρ (L · M) = (ren-ne ρ L) · (ren-nf ρ M)
```

Renaming commutes with erasure
```
comm-nf : ∀ (ρ : Δ ⊇ Γ) (M : Γ ⊢nf A) → ⌜ M ⌝nf [ ρ ]ʳ ≡ ⌜ ren-nf ρ M ⌝nf
comm-ne : ∀ (ρ : Δ ⊇ Γ) (M : Γ ⊢ne A) → ⌜ M ⌝ne [ ρ ]ʳ ≡ ⌜ ren-ne ρ M ⌝ne

comm-nf ρ (′ M) = comm-ne ρ M
comm-nf ρ (ƛ N) = cong ƛ_ (comm-nf (ρ ^ʳ _) N)

comm-ne ρ (` x)   = refl
comm-ne ρ (L · M) = cong₂ _·_ (comm-ne ρ L) (comm-nf ρ M)
```

Interpretation of types and contexts
```
⟦_⟧ᵀ : Ty -> Con -> Set
⟦ ι ⟧ᵀ     Γ = Γ ⊢nf ι
⟦ A ⇒ B ⟧ᵀ Γ = ∀ {Δ} → Δ ⊇ Γ → ⟦ A ⟧ᵀ Δ → ⟦ B ⟧ᵀ Δ

⟦_⟧ᶜ : Con -> Con -> Set
⟦ ∅ ⟧ᶜ     Δ = ⊤
⟦ Γ , A ⟧ᶜ Δ = ⟦ Γ ⟧ᶜ Δ × ⟦ A ⟧ᵀ Δ
```

Weakening values and environments
```
weaken-value : Δ ⊇ Γ → ⟦ A ⟧ᵀ Γ -> ⟦ A ⟧ᵀ Δ
weaken-value {A = ι}     ρ M = ren-nf ρ M
weaken-value {A = A ⇒ B} ρ f = λ ρ′ v → f (ρ ʳ⨾ʳ ρ′) v

weaken-env : Δ ⊇ Γ -> ⟦ Θ ⟧ᶜ Γ -> ⟦ Θ ⟧ᶜ Δ
weaken-env {Θ = ∅}     ρ tt      = tt
weaken-env {Θ = Θ , A} ρ (γ , v) = weaken-env {Θ = Θ} ρ γ , weaken-value {A = A} ρ v
```

Interpretation of variables and terms
```
⟦_⟧ⱽ : Γ ∋ A → ⟦ Γ ⟧ᶜ Δ → ⟦ A ⟧ᵀ Δ
⟦ zero ⟧ⱽ  (_ , v) = v
⟦ suc x ⟧ⱽ (γ , _) = ⟦ x ⟧ⱽ γ

⟦_⟧ : Γ ⊢ A -> ⟦ Γ ⟧ᶜ Δ -> ⟦ A ⟧ᵀ Δ
⟦_⟧ (` x) γ = ⟦ x ⟧ⱽ γ
⟦_⟧ (ƛ N) γ = λ ρ v → ⟦ N ⟧ (weaken-env ρ γ , v)
⟦_⟧ (L · M) γ = ⟦ L ⟧ γ idʳ (⟦ M ⟧ γ)
```

Reify and reflect
```
reify : ⟦ A ⟧ᵀ Γ -> Γ ⊢nf A
reflect : Γ ⊢ne A -> ⟦ A ⟧ᵀ Γ

reify {A = ι}     t = t
reify {A = A ⇒ B} f = ƛ (reify (f suc (reflect (` zero))))

reflect {A = ι}     M = ′ M
reflect {A = A ⇒ B} L = λ ρ v → reflect (ren-ne ρ L · reify v)
```

Reflect environment
```
reflectᶜ : ⟦ Γ ⟧ᶜ Γ
reflectᶜ {∅} = tt
reflectᶜ {Γ , A} = weaken-env suc (reflectᶜ {Γ}) , reflect (` zero)
```

Normalisation-by-evaluation, open terms
```
nf : Γ ⊢ A -> Γ ⊢nf A
nf M = reify (⟦ M ⟧ reflectᶜ)
```


Church numerals
```
Ch : Ty → Ty
Ch A = (A ⇒ A) ⇒ (A ⇒ A)

one : ∅ ⊢ Ch ι
one = ƛ (` 0)

two : ∅ ⊢ Ch A
two = ƛ ƛ (` 1 · (` 1 · ` 0))

plus : ∅ ⊢ Ch A ⇒ Ch A ⇒ Ch A
plus = ƛ ƛ ƛ ƛ (` 3 · ` 1 · (` 2 · ` 1 · ` 0))

four : ∅ ⊢ Ch A
four = plus · two · two
```

Testing NBE
```
one-nf : ∅ ⊢nf Ch ι
one-nf = ƛ (ƛ (′ ` 1 · (′ ` 0)))

four-nf : ∅ ⊢nf Ch ι
four-nf = ƛ ƛ (′ ` 1 · (′ ` 1 · (′ ` 1 · (′ ` 1 · (′ ` 0)))))

_ : nf one ≡ one-nf
_ = refl

_ : nf four ≡ four-nf
_ = refl
```

Now need to add the proof that nbe is sound, complete, and stable.
