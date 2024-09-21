Core STLC
With renaming and substitution defined in the traditional way.
Renamings and substitutions defined as functions.
Four different compositions and related theorems.


Philip Wadler, 8 Sep 2024

## Preliminaries

```
{-# OPTIONS --rewriting #-}
module Core where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Agda.Builtin.FromNat
import Relation.Binary.PropositionalEquality as EQ
open EQ using (_≡_; refl; cong; cong₂; sym; trans)
open EQ.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; step-≡-⟨; _∎)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to infixl 4 _,_)
open import Data.Nat using (ℕ; zero; suc)
open import Function using (_∘_)
```

instantiate natural number literals
```
instance
  NumNat : Number ℕ
  NumNat .Number.Constraint _ = ⊤
  NumNat .Number.fromNat    m = m

_ : ℕ
_ = 42
```

# Operator precedence

Operator precedence
```
infix  3  _∋_ _⊢_ _⊇_ _⊨_
infix  4  _==ʳ_ _==_ _~_
infixl 4  _,_
infixl 5  _^ʳ_ _↑_ _^_ _▷_
infixr 5  _ʳ⨾ʳ_ _ʳ⨾_ _⨾ʳ_ _⨾_
infixr 5  _⇒_
infix  5  ƛ_
infixl 6  _·_
infix  7  `_
```

let X, Y, Z range over Set
```
variable
  X Y Z : Set
```

Types and contexts
```
data Ty : Set where
  ι   : Ty
  _⇒_ : (A B : Ty) → Ty

variable
  A B C : Ty

data Con : Set where
  ∅   : Con
  _,_  : (Γ : Con) (A : Ty) -> Con

variable
  Γ Δ Θ : Con
```

Variables and terms
```
data _∋_ : Con -> Ty -> Set where

  zero :
      ---------
      Γ , A ∋ A

  suc  :
      (x : Γ ∋ B)
    → -----------
      Γ , A ∋ B

data _⊢_ : Con -> Ty -> Set where

  `_ :
      (x : Γ ∋ A)
    → -----------
      Γ ⊢ A

  ƛ_ :
      (N : Γ , A ⊢ B)
    → ---------------
      Γ ⊢ A ⇒ B

  _·_ :
      (L : Γ ⊢ A ⇒ B)
      (M : Γ ⊢ A)
    → ---------------
      Γ ⊢ B

variable
  x y z : Γ ∋ A
  L M N L′ M′ N′ : Γ ⊢ A
```

natural number literals as DeBruijn indices
```
record Convert (n : ℕ) (X : Set) : Set where
  field
    convert : X

open Convert {{...}} public

variable
  n : ℕ

instance
  ConvertZ : Convert zero (Γ , A ∋ A)
  ConvertZ .convert = zero

instance
  ConvertS : {{Convert n (Γ ∋ A)}} → Convert (suc n) (Γ , B ∋ A)
  ConvertS .convert = suc convert

instance
  Num∋ : Number (Γ ∋ A)
  Num∋ .Number.Constraint n = Convert n (_ ∋ _)
  Num∋ .Number.fromNat n = convert

_ : Γ , A , B , C ∋ A
_ = 2
```

## Rename

Renamings
```
_⊇_ : Con → Con → Set
Δ ⊇ Γ  =  ∀ {A : Ty} → Γ ∋ A → Δ ∋ A

variable
  ρ ξ ζ : Δ ⊇ Γ
```

Extensional equality
```
_==ʳ_ : (ρ ξ : Δ ⊇ Γ) → Set
_==ʳ_ {Γ = Γ} ρ ξ = ∀ {A : Ty} (x : Γ ∋ A) → ρ x ≡ ξ x
```

Extension
```
_^ʳ_ : ∀ {Γ Δ : Con} → Δ ⊇ Γ → (A : Ty) → Δ , A ⊇ Γ , A
(ρ ^ʳ A) zero = zero
(ρ ^ʳ A) (suc x) = suc (ρ x)
```

Instantiation
```
_[_]ʳ : Γ ⊢ A → Δ ⊇ Γ → Δ ⊢ A
(` x) [ ρ ]ʳ = ` (ρ x)
(ƛ N) [ ρ ]ʳ = ƛ (N [ ρ ^ʳ _ ]ʳ)
(L · M) [ ρ ]ʳ = (L [ ρ ]ʳ) · (M [ ρ ]ʳ)
```

Weaken
```
_↑_ : Γ ⊢ B → (A : Ty) → Γ , A ⊢ B
M ↑ A = M [ suc ]ʳ
```

## Identity

Identity
```
idʳ : Γ ⊇ Γ
idʳ x  =  x
```

Instantiate identity
```
idʳ^ʳ : ρ ==ʳ idʳ → ρ ^ʳ A ==ʳ idʳ
idʳ^ʳ e zero = refl
idʳ^ʳ e (suc x) = cong suc (e x)

[idʳ]ʳ : ρ ==ʳ idʳ → ∀ (M : Γ ⊢ A) → M [ ρ ]ʳ ≡ M
[idʳ]ʳ e (` x) = cong `_ (e x)
[idʳ]ʳ e (ƛ N) = cong ƛ_ ([idʳ]ʳ (idʳ^ʳ e) N)
[idʳ]ʳ e (L · M) = cong₂ _·_ ([idʳ]ʳ e L) ([idʳ]ʳ e M)

[idʳ]ʳ-corollary : M [ idʳ ]ʳ ≡ M
[idʳ]ʳ-corollary {M = M} = [idʳ]ʳ (λ x → refl) M
```

## Rename twice

Compose
```
_ʳ⨾ʳ_ : Θ ⊇ Γ → Δ ⊇ Θ → Δ ⊇ Γ
(ρ ʳ⨾ʳ ξ) x  =  ξ (ρ x)
```

Instantiate twice
```
^ʳ^ʳ : ρ ʳ⨾ʳ ξ ==ʳ ζ → (ρ ^ʳ A) ʳ⨾ʳ (ξ ^ʳ A) ==ʳ ζ ^ʳ A
^ʳ^ʳ e zero = refl
^ʳ^ʳ e (suc x) = cong suc (e x)

[]ʳ[]ʳ : ρ ʳ⨾ʳ ξ ==ʳ ζ → ∀ (M : Γ ⊢ A) → M [ ρ ]ʳ [ ξ ]ʳ ≡ M [ ζ ]ʳ
[]ʳ[]ʳ e (` x) = cong `_ (e x)
[]ʳ[]ʳ e (ƛ N) = cong ƛ_ ([]ʳ[]ʳ (^ʳ^ʳ e) N)
[]ʳ[]ʳ e (L · M) = cong₂ _·_ ([]ʳ[]ʳ e L) ([]ʳ[]ʳ e M)

[]ʳ[]ʳ-corollary : M [ ρ ]ʳ [ ξ ]ʳ ≡ M [ ρ ʳ⨾ʳ ξ ]ʳ
[]ʳ[]ʳ-corollary {M = M} = []ʳ[]ʳ (λ x → refl) M
```

## Monoid laws

```
ʳ⨾ʳʳ⨾ʳ : (ρ ʳ⨾ʳ ξ) ʳ⨾ʳ ζ ==ʳ ρ ʳ⨾ʳ (ξ ʳ⨾ʳ ζ)
ʳ⨾ʳʳ⨾ʳ x = refl

ʳ⨾ʳidʳ : ρ ʳ⨾ʳ idʳ ==ʳ ρ
ʳ⨾ʳidʳ x = refl

idʳʳ⨾ʳ : idʳ ʳ⨾ʳ ξ ==ʳ ξ
idʳʳ⨾ʳ x = refl
```

## Weaken and rename

```
↑[^ʳ]ʳ : (M ↑ A) [ ρ ^ʳ A ]ʳ ≡ (M [ ρ ]ʳ) ↑ A
↑[^ʳ]ʳ {M = M} {A = A} {ρ = ρ} =
  begin
    (M ↑ A) [ ρ ^ʳ A ]ʳ
  ≡⟨ []ʳ[]ʳ (λ x → refl) M ⟩
    M [ ρ ʳ⨾ʳ suc ]ʳ
  ≡⟨ []ʳ[]ʳ (λ x → refl) M ⟨
    (M [ ρ ]ʳ) ↑ A
  ∎
```

## Substitute

Substitutions
```
_⊨_ : Con → Con → Set
Δ ⊨ Γ  =  ∀ {A} → Γ ∋ A → Δ ⊢ A

variable
  σ τ υ : Δ ⊨ Γ
```

Extensional equality
```
_==_ : (σ τ : Δ ⊨ Γ) → Set
_==_ {Γ = Γ} σ τ = ∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ τ x
```

Extension
```
_^_ : ∀ {Γ Δ : Con} → Δ ⊨ Γ → (A : Ty) → Δ , A ⊨ Γ , A
(σ ^ A) zero = ` zero
(σ ^ A) (suc x) = (σ x) ↑ A
```

Instantiation
```
_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` x) [ σ ] = σ x
(ƛ N) [ σ ] = ƛ (N [ σ ^ _ ])
(L · M) [ σ ] = (L [ σ ]) · (M [ σ ])
```

Cons
```
_▷_ : Δ ⊨ Γ → Δ ⊢ A → Δ ⊨ Γ , A
(σ ▷ M) zero  =  M
(σ ▷ M) (suc x)  =  σ x
```

Identity
```
id : Γ ⊨ Γ
id x  =  ` x
```

Instantiate identity
```
id^ : σ == id → σ ^ A == id
id^ e zero = refl
id^ e (suc x) rewrite e x = refl

[id] : σ == id → ∀ (M : Γ ⊢ A) → M [ σ ] ≡ M
[id] e (` x) = e x
[id] e (ƛ N) = cong ƛ_ ([id] (id^ e) N)
[id] e (L · M) = cong₂ _·_ ([id] e L) ([id] e M)

[id]-corollary : M [ id ] ≡ M
[id]-corollary {M = M} = [id] (λ x → refl) M
```

## Rename and substitute

Composition
```
_ʳ⨾_ : Θ ⊇ Γ → Δ ⊨ Θ → Δ ⊨ Γ
(ρ ʳ⨾ τ) x  =  τ (ρ x)
```

Instantiate twice
```
^ʳ^ : ρ ʳ⨾ τ == υ → (ρ ^ʳ A) ʳ⨾ (τ ^ A) == υ ^ A
^ʳ^ e zero = refl
^ʳ^ e (suc x) rewrite e x = refl

[]ʳ[] : ρ ʳ⨾ τ == υ → ∀ (M : Γ ⊢ A) → M [ ρ ]ʳ [ τ ] ≡ M [ υ ]
[]ʳ[] e (` x) = e x
[]ʳ[] e (ƛ N) = cong ƛ_ ([]ʳ[] (^ʳ^ e) N)
[]ʳ[] e (L · M) = cong₂ _·_ ([]ʳ[] e L) ([]ʳ[] e M)

[]ʳ[]-corollary : M [ ρ ]ʳ [ τ ] ≡ M [ ρ ʳ⨾ τ ]
[]ʳ[]-corollary {M = M} = []ʳ[] (λ x → refl) M
```

## Substitute and rename

Composition
```
_⨾ʳ_ : Θ ⊨ Γ → Δ ⊇ Θ → Δ ⊨ Γ
(σ ⨾ʳ ξ) x  =  (σ x) [ ξ ]ʳ
```

Instantiate twice
```
^^ʳ : σ ⨾ʳ ξ == υ → (σ ^ A) ⨾ʳ (ξ ^ʳ A) == υ ^ A
^^ʳ e zero = refl
^^ʳ{σ = σ} {ξ = ξ} {υ = υ} e (suc x) =
  begin
    ((σ x) ↑ _) [ ξ ^ʳ _ ]ʳ
  ≡⟨ ↑[^ʳ]ʳ ⟩
    ((σ x) [ ξ ]ʳ) ↑ _
  ≡⟨ cong (_↑ _) (e x) ⟩
    (υ x) ↑ _
  ∎

[][]ʳ : σ ⨾ʳ ξ == υ → ∀ (M : Γ ⊢ A) → M [ σ ] [ ξ ]ʳ ≡ M [ υ ]
[][]ʳ e (` x) = e x
[][]ʳ e (ƛ N) = cong ƛ_ ([][]ʳ (^^ʳ e) N)
[][]ʳ e (L · M) = cong₂ _·_ ([][]ʳ e L) ([][]ʳ e M)

[][]ʳ-corollary : M [ σ ] [ ξ ]ʳ ≡ M [ σ ⨾ʳ ξ ]
[][]ʳ-corollary {M = M} = [][]ʳ (λ x → refl) M
```

## Weaken and substitute

```
↑[^] : (M ↑ A) [ σ ^ A ] ≡ (M [ σ ]) ↑ A
↑[^] {M = M} {A = A} {σ = σ} =
  begin
    (M ↑ A) [ σ ^ A ]
  ≡⟨ []ʳ[] (λ x → refl) M ⟩
    M [ σ ⨾ʳ suc ]
  ≡⟨ [][]ʳ (λ x → refl) M ⟨
    (M [ σ ]) ↑ A
  ∎
```

## Substitute twice

Composition
```
_⨾_ : Θ ⊨ Γ → Δ ⊨ Θ → Δ ⊨ Γ
(σ ⨾ τ) x  =  (σ x) [ τ ]
```

Instantiate twice
```
^^ : σ ⨾ τ == υ → (σ ^ A) ⨾ (τ ^ A) == υ ^ A
^^ e zero = refl
^^ {σ = σ} {τ = τ} {υ = υ} e (suc x) =
  begin
    (σ x ↑ _) [ τ ^ _ ]
  ≡⟨ ↑[^] {M = σ x} ⟩
    (σ x) [ τ ] ↑ _
  ≡⟨ cong (_↑ _) (e x) ⟩
    (υ x) ↑ _
  ∎

[][] : σ ⨾ τ == υ → ∀ (M : Γ ⊢ A) → M [ σ ] [ τ ] ≡ M [ υ ]
[][] e (` x) = e x
[][] e (ƛ N) = cong ƛ_ ([][] (^^ e) N)
[][] e (L · M) = cong₂ _·_ ([][] e L) ([][] e M)

[][]-corollary : M [ σ ] [ τ ] ≡ M [ σ ⨾ τ ]
[][]-corollary {M = M} = [][] (λ x → refl) M
```

## Monoid laws

```
⨾⨾ : (σ ⨾ τ) ⨾ υ == σ ⨾ (τ ⨾ υ)
⨾⨾ {σ = σ} {τ = τ} {υ = υ} x = [][]-corollary {M = σ x} {σ = τ} {τ = υ}

⨾id : σ ⨾ id == σ
⨾id {σ = σ} x = [id]-corollary {M = σ x}

id⨾ : id ⨾ τ == τ
id⨾ x = refl
```

# Beta and eta equivalence

```
data _~_ : Γ ⊢ A → Γ ⊢ A → Set where

  η     : L ~ ƛ ((L ↑ _) · ` zero)
  β     : (ƛ N) · M ~ N [ id ▷ M ]

  ƛ_    : N ~ N′ → (ƛ N) ~ (ƛ N′)
  _·_   : L ~ L′ → M ~ M′ → L · M ~ L′ · M′

  ~refl : M ~ M
  ~sym  : M ~ N → N ~ M
  ~tran : L ~ M → M ~ N → L ~ N
```

