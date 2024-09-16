# traditional-fun-full

Traditional approach
Data to represent renaming and substitution
In full, without factoring
Philip Wadler, 8 Sep 2024

## Preliminaries

```
{-# OPTIONS --rewriting --no-forcing #-}
module tradional-data-full where
```
The --no-forcing flag is needed because of a bug

```
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
infix  4  _==ʳ_ _==_
infixl 4  _,_
infixl 5  _^ʳ_ _↑_ _^_
infixr 5  _ʳ⨾ʳ_ _ʳ⨾_ _⨾ʳ_ _⨾_
infixr 5  _⇒_
infix  5  ƛ_
infixl 6  _·_
infix  6  `_
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
  L M N : Γ ⊢ A
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
data _⊇_ : Con → Con → Set where
  ∅   : Δ ⊇ ∅
  _,_ : Δ ⊇ Γ → Δ ∋ A → Δ ⊇ Γ , A

variable
  ρ ξ ζ : Δ ⊇ Γ
```

Weaken
```
_⁺_ : Δ ⊇ Γ → (A : Ty) → Δ , A ⊇ Γ
∅ ⁺ A = ∅
(ρ , x) ⁺ A = (ρ ⁺ A) , suc x
```

Extension
```
_^ʳ_ : ∀ {Γ Δ : Con} → Δ ⊇ Γ → (A : Ty) → Δ , A ⊇ Γ , A
ρ ^ʳ A  =  ρ ⁺ A , zero
```

Lookup
```
lookupʳ : Δ ⊇ Γ → Γ ∋ A → Δ ∋ A
lookupʳ (ρ , y) zero = y
lookupʳ (ρ , y) (suc x) = lookupʳ ρ x
```

Instantiation
```
_[_]ʳ : Γ ⊢ A → Δ ⊇ Γ → Δ ⊢ A
(` x) [ ρ ]ʳ = ` lookupʳ ρ x
(ƛ N) [ ρ ]ʳ = ƛ (N [ ρ ^ʳ _ ]ʳ)
(L · M) [ ρ ]ʳ = (L [ ρ ]ʳ) · (M [ ρ ]ʳ)
```

Identity
```
idʳ : Γ ⊇ Γ
idʳ {∅} = ∅
idʳ {Γ , A} = idʳ {Γ} ^ʳ A
```

Composition
```
_ʳ⨾ʳ_ : Θ ⊇ Γ → Δ ⊇ Θ → Δ ⊇ Γ
∅ ʳ⨾ʳ ξ = ∅
(ρ , x) ʳ⨾ʳ ξ = (ρ ʳ⨾ʳ ξ) , lookupʳ ξ x
```

Weaken
```
⤊ : Γ , A ⊇ Γ
⤊ = idʳ ⁺ _

_↑_ : Γ ⊢ B → (A : Ty) → Γ , A ⊢ B
M ↑ A = M [ ⤊ ]ʳ
```

Lemma.
```
lookupʳ⁺ : lookupʳ (ρ ⁺ A) x ≡ suc (lookupʳ ρ x)
lookupʳ⁺ {ρ = ρ , y} {x = zero} = refl
lookupʳ⁺ {ρ = ρ , y} {x = suc x} = lookupʳ⁺ {ρ = ρ} {x = x}
```

Instantiate identity
```
lookupʳidʳ : lookupʳ idʳ x ≡ x
lookupʳidʳ {x = zero} = refl
lookupʳidʳ {x = suc x} =
  begin
    lookupʳ idʳ (suc x)
  ≡⟨⟩
    lookupʳ (idʳ ⁺ _ , zero) (suc x)
  ≡⟨⟩
    lookupʳ (idʳ ⁺ _) x
  ≡⟨ lookupʳ⁺ {ρ = idʳ} {x = x} ⟩
    suc (lookupʳ idʳ x)
  ≡⟨ cong suc (lookupʳidʳ {x = x}) ⟩
    suc x
  ∎

[idʳ]ʳ : M [ idʳ ]ʳ ≡ M
[idʳ]ʳ {M = ` x} = cong `_ lookupʳidʳ
[idʳ]ʳ {M = ƛ N} = cong ƛ_ [idʳ]ʳ
[idʳ]ʳ {M = L · M} = cong₂ _·_ [idʳ]ʳ [idʳ]ʳ
```

Right identity
```
ʳ⨾ʳidʳ : ρ ʳ⨾ʳ idʳ ≡ ρ
ʳ⨾ʳidʳ {ρ = ∅} = refl
ʳ⨾ʳidʳ {ρ = ρ , x} = cong₂ _,_ ʳ⨾ʳidʳ lookupʳidʳ
```

```
⁺ʳ⨾ʳ : (ρ ⁺ A) ʳ⨾ʳ (ξ , y) ≡ ρ ʳ⨾ʳ ξ
⁺ʳ⨾ʳ {ρ = ∅} = refl
⁺ʳ⨾ʳ {ρ = ρ , x} = cong₂ _,_ ⁺ʳ⨾ʳ refl
```

Left identity
```
idʳʳ⨾ʳ : idʳ ʳ⨾ʳ ρ ≡ ρ
idʳʳ⨾ʳ {ρ = ∅} = refl
idʳʳ⨾ʳ {ρ = ρ , x} = cong₂ _,_
  (begin
    (idʳ ⁺ _) ʳ⨾ʳ (ρ , x)
  ≡⟨ ⁺ʳ⨾ʳ {ρ = idʳ} {ξ = ρ} ⟩
    idʳ ʳ⨾ʳ ρ
  ≡⟨ idʳʳ⨾ʳ {ρ = ρ} ⟩
    ρ
  ∎)
  refl
```

Functor laws
```
lookupʳʳ⨾ʳ : lookupʳ (ρ ʳ⨾ʳ ξ) x ≡ lookupʳ ξ (lookupʳ ρ x)
lookupʳʳ⨾ʳ {ρ = ρ , y} {ξ = ξ} {x = zero} = refl
lookupʳʳ⨾ʳ {ρ = ρ , y} {ξ = ξ} {x = suc x} = lookupʳʳ⨾ʳ {ρ = ρ} {ξ = ξ} {x = x}

^ʳʳ⨾ʳ̂ʳ : (ρ ʳ⨾ʳ ξ) ^ʳ A ≡ (ρ ^ʳ A) ʳ⨾ʳ (ξ ^ʳ A)

[ʳ⨾ʳ]ʳ : M [ ρ ʳ⨾ʳ ξ ]ʳ ≡ M [ ρ ]ʳ [ ξ ]ʳ
[ʳ⨾ʳ]ʳ {M = ` x} {ρ = ρ} {ξ = ξ} = cong `_ (lookupʳʳ⨾ʳ {ρ = ρ} {ξ = ξ} {x = x})
[ʳ⨾ʳ]ʳ {M = ƛ N} {ρ = ρ} {ξ = ξ} =
  cong ƛ_
    (begin
      N [ (ρ ʳ⨾ʳ ξ) ^ʳ _ ]ʳ
    ≡⟨ cong (λ □ → N [ □ ]ʳ) ^ʳʳ⨾ʳ̂ʳ ⟩
      N [ (ρ ʳ⨾ʳ ξ) ^ʳ _ ]ʳ
    ≡⟨ [ʳ⨾ʳ]ʳ {M = N} ⟩
      N [ ρ ^ʳ _ ]ʳ [ ξ ^ʳ _ ]ʳ
    ∎)
[ʳ⨾ʳ]ʳ {M = L · M} = cong₂ _·_ [ʳ⨾ʳ]ʳ [ʳ⨾ʳ]ʳ


```







-- ## Rename twice

-- Compose
-- ```
-- _ʳ⨾ʳ_ : Θ ⊇ Γ → Δ ⊇ Θ → Δ ⊇ Γ
-- (ρ ʳ⨾ʳ ξ) x  =  ξ (ρ x)
-- ```

-- Instantiate twice
-- ```
-- ^ʳ^ʳ : ρ ʳ⨾ʳ ξ ==ʳ ζ → (ρ ^ʳ A) ʳ⨾ʳ (ξ ^ʳ A) ==ʳ ζ ^ʳ A
-- ^ʳ^ʳ e zero = refl
-- ^ʳ^ʳ e (suc x) = cong suc (e x)

-- []ʳ[]ʳ : ρ ʳ⨾ʳ ξ ==ʳ ζ → ∀ (M : Γ ⊢ A) → M [ ρ ]ʳ [ ξ ]ʳ ≡ M [ ζ ]ʳ
-- []ʳ[]ʳ e (` x) = cong `_ (e x)
-- []ʳ[]ʳ e (ƛ N) = cong ƛ_ ([]ʳ[]ʳ (^ʳ^ʳ e) N)
-- []ʳ[]ʳ e (L · M) = cong₂ _·_ ([]ʳ[]ʳ e L) ([]ʳ[]ʳ e M)

-- []ʳ[]ʳ-corollary : M [ ρ ]ʳ [ ξ ]ʳ ≡ M [ ρ ʳ⨾ʳ ξ ]ʳ
-- []ʳ[]ʳ-corollary {M = M} = []ʳ[]ʳ (λ x → refl) M
-- ```

-- ## Monoid laws

-- ```
-- ʳ⨾ʳʳ⨾ʳ : (ρ ʳ⨾ʳ ξ) ʳ⨾ʳ ζ ==ʳ ρ ʳ⨾ʳ (ξ ʳ⨾ʳ ζ)
-- ʳ⨾ʳʳ⨾ʳ x = refl

-- ʳ⨾ʳidʳ : ρ ʳ⨾ʳ idʳ ==ʳ ρ
-- ʳ⨾ʳidʳ x = refl

-- idʳʳ⨾ʳ : idʳ ʳ⨾ʳ ξ ==ʳ ξ
-- idʳʳ⨾ʳ x = refl
-- ```

-- ## Weaken and rename

-- ```
-- ↑[^ʳ]ʳ : (M ↑ A) [ ρ ^ʳ A ]ʳ ≡ (M [ ρ ]ʳ) ↑ A
-- ↑[^ʳ]ʳ {M = M} {A = A} {ρ = ρ} =
--   begin
--     (M ↑ A) [ ρ ^ʳ A ]ʳ
--   ≡⟨ []ʳ[]ʳ (λ x → refl) M ⟩
--     M [ ρ ʳ⨾ʳ suc ]ʳ
--   ≡⟨ []ʳ[]ʳ (λ x → refl) M ⟨
--     (M [ ρ ]ʳ) ↑ A
--   ∎
-- ```

-- ## Substitute

-- Substitutions
-- ```
-- _⊨_ : Con → Con → Set
-- Δ ⊨ Γ  =  ∀ {A} → Γ ∋ A → Δ ⊢ A

-- variable
--   σ τ υ : Δ ⊨ Γ
-- ```

-- Extensional equality
-- ```
-- _==_ : (σ τ : Δ ⊨ Γ) → Set
-- _==_ {Γ = Γ} σ τ = ∀ {A : Ty} (x : Γ ∋ A) → σ x ≡ τ x
-- ```

-- Extension
-- ```
-- _^_ : ∀ {Γ Δ : Con} → Δ ⊨ Γ → (A : Ty) → Δ , A ⊨ Γ , A
-- (σ ^ A) zero = ` zero
-- (σ ^ A) (suc x) = (σ x) ↑ A
-- ```

-- Instantiation
-- ```
-- _[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
-- (` x) [ σ ] = σ x
-- (ƛ N) [ σ ] = ƛ (N [ σ ^ _ ])
-- (L · M) [ σ ] = (L [ σ ]) · (M [ σ ])
-- ```

-- Identity
-- ```
-- id : Γ ⊨ Γ
-- id x  =  ` x
-- ```

-- Instantiate identity
-- ```
-- id^ : σ == id → σ ^ A == id
-- id^ e zero = refl
-- id^ e (suc x) rewrite e x = refl

-- [id] : σ == id → ∀ (M : Γ ⊢ A) → M [ σ ] ≡ M
-- [id] e (` x) = e x
-- [id] e (ƛ N) = cong ƛ_ ([id] (id^ e) N)
-- [id] e (L · M) = cong₂ _·_ ([id] e L) ([id] e M)

-- [id]-corollary : M [ id ] ≡ M
-- [id]-corollary {M = M} = [id] (λ x → refl) M
-- ```

-- ## Rename and substitute

-- Composition
-- ```
-- _ʳ⨾_ : Θ ⊇ Γ → Δ ⊨ Θ → Δ ⊨ Γ
-- (ρ ʳ⨾ τ) x  =  τ (ρ x)
-- ```

-- Instantiate twice
-- ```
-- ^ʳ^ : ρ ʳ⨾ τ == υ → (ρ ^ʳ A) ʳ⨾ (τ ^ A) == υ ^ A
-- ^ʳ^ e zero = refl
-- ^ʳ^ e (suc x) rewrite e x = refl

-- []ʳ[] : ρ ʳ⨾ τ == υ → ∀ (M : Γ ⊢ A) → M [ ρ ]ʳ [ τ ] ≡ M [ υ ]
-- []ʳ[] e (` x) = e x
-- []ʳ[] e (ƛ N) = cong ƛ_ ([]ʳ[] (^ʳ^ e) N)
-- []ʳ[] e (L · M) = cong₂ _·_ ([]ʳ[] e L) ([]ʳ[] e M)

-- []ʳ[]-corollary : M [ ρ ]ʳ [ τ ] ≡ M [ ρ ʳ⨾ τ ]
-- []ʳ[]-corollary {M = M} = []ʳ[] (λ x → refl) M
-- ```

-- ## Substitute and rename

-- Composition
-- ```
-- _⨾ʳ_ : Θ ⊨ Γ → Δ ⊇ Θ → Δ ⊨ Γ
-- (σ ⨾ʳ ξ) x  =  (σ x) [ ξ ]ʳ
-- ```

-- Instantiate twice
-- ```
-- ^^ʳ : σ ⨾ʳ ξ == υ → (σ ^ A) ⨾ʳ (ξ ^ʳ A) == υ ^ A
-- ^^ʳ e zero = refl
-- ^^ʳ{σ = σ} {ξ = ξ} {υ = υ} e (suc x) =
--   begin
--     ((σ x) ↑ _) [ ξ ^ʳ _ ]ʳ
--   ≡⟨ ↑[^ʳ]ʳ ⟩
--     ((σ x) [ ξ ]ʳ) ↑ _
--   ≡⟨ cong (_↑ _) (e x) ⟩
--     (υ x) ↑ _
--   ∎

-- [][]ʳ : σ ⨾ʳ ξ == υ → ∀ (M : Γ ⊢ A) → M [ σ ] [ ξ ]ʳ ≡ M [ υ ]
-- [][]ʳ e (` x) = e x
-- [][]ʳ e (ƛ N) = cong ƛ_ ([][]ʳ (^^ʳ e) N)
-- [][]ʳ e (L · M) = cong₂ _·_ ([][]ʳ e L) ([][]ʳ e M)

-- [][]ʳ-corollary : M [ σ ] [ ξ ]ʳ ≡ M [ σ ⨾ʳ ξ ]
-- [][]ʳ-corollary {M = M} = [][]ʳ (λ x → refl) M
-- ```

-- ## Weaken and substitute

-- ```
-- ↑[^] : (M ↑ A) [ σ ^ A ] ≡ (M [ σ ]) ↑ A
-- ↑[^] {M = M} {A = A} {σ = σ} =
--   begin
--     (M ↑ A) [ σ ^ A ]
--   ≡⟨ []ʳ[] (λ x → refl) M ⟩
--     M [ σ ⨾ʳ suc ]
--   ≡⟨ [][]ʳ (λ x → refl) M ⟨
--     (M [ σ ]) ↑ A
--   ∎
-- ```

-- ## Substitute twice

-- Composition
-- ```
-- _⨾_ : Θ ⊨ Γ → Δ ⊨ Θ → Δ ⊨ Γ
-- (σ ⨾ τ) x  =  (σ x) [ τ ]
-- ```

-- Instantiate twice
-- ```
-- ^^ : σ ⨾ τ == υ → (σ ^ A) ⨾ (τ ^ A) == υ ^ A
-- ^^ e zero = refl
-- ^^ {σ = σ} {τ = τ} {υ = υ} e (suc x) =
--   begin
--     (σ x ↑ _) [ τ ^ _ ]
--   ≡⟨ ↑[^] {M = σ x} ⟩
--     (σ x) [ τ ] ↑ _
--   ≡⟨ cong (_↑ _) (e x) ⟩
--     (υ x) ↑ _
--   ∎

-- [][] : σ ⨾ τ == υ → ∀ (M : Γ ⊢ A) → M [ σ ] [ τ ] ≡ M [ υ ]
-- [][] e (` x) = e x
-- [][] e (ƛ N) = cong ƛ_ ([][] (^^ e) N)
-- [][] e (L · M) = cong₂ _·_ ([][] e L) ([][] e M)

-- [][]-corollary : M [ σ ] [ τ ] ≡ M [ σ ⨾ τ ]
-- [][]-corollary {M = M} = [][] (λ x → refl) M
-- ```

-- ## Monoid laws

-- ```
-- ⨾⨾ : (σ ⨾ τ) ⨾ υ == σ ⨾ (τ ⨾ υ)
-- ⨾⨾ {σ = σ} {τ = τ} {υ = υ} x = [][]-corollary {M = σ x} {σ = τ} {τ = υ}

-- ⨾id : σ ⨾ id == σ
-- ⨾id {σ = σ} x = [id]-corollary {M = σ x}

-- id⨾ : id ⨾ τ == τ
-- id⨾ x = refl
-- ```
