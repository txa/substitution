Parameterised development
Following Substitution with Copy and Paste

New version with id polymorphic in q
Based on new treatment of ⊑ in terms of ⊔.

Previous version required id to be a renaming,
but we also need id as a substitution to define
beta reduction:

   (ƛ N) V --> N [ id , V ]

Alas, this means some equations become more clumsy.

    id⨾ : (φ : Δ ⊨[ r ] Γ) → id {q = q} ⨾ φ ≡ lift* (⊑⊔₁ {q = q} {r = r}) φ

Here

    lift* : (q ⊑ r) → Δ ⊨[ q ] Γ → Δ ⊨[ r ] Γ

An alternative may be to eliminate `lift*` by restricting our
equation to the cases where q ⊑ r:

    id⨾′ : {q ⊑ r} → (φ : Δ ⊨[ r ] Γ) → id {q = q} ⨾ φ ≡ φ

but I'm not sure how to get the equation to typecheck under that resriction,
even thouqh `q ⊑ r` holds exactly when `q ⊔ r ≡ r` which is exactly what we
need for `id⨾′` to be well typed.



Philip Wadler, 26 Sep 2024
```
{-# OPTIONS --rewriting #-}
module parameterised where

open import Agda.Builtin.FromNat
import Relation.Binary.PropositionalEquality as EQ
open EQ using (_≡_; refl; cong; cong₂; sym; trans; subst)
open EQ.≡-Reasoning using (begin_; step-≡-∣; step-≡-⟩; _∎)
{-# BUILTIN REWRITE _≡_ #-}

open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_) renaming (_,_ to infixl 4 _,_)
open import Data.Nat using (ℕ; zero; suc)
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

Operator precedence
```
infix  3 _∋_ _⊢_ _⊢[_]_ _⊇_ _⊨_ _⊨[_]_
infixl 4 _,_
infixl 5 _⁺_ _^_
infixr 5 _⨾_
infixr 6 _⇒_
infix  7 ƛ_
infixl 8 _·_
infix  9 `_
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
  Γ Δ Θ Φ : Con
```

Sort
```
data Sort : Set where
  V : Sort
  T>V : (v : Sort) → v ≡ V → Sort

pattern T = T>V V refl

variable
  q r s : Sort

_⊔_ : Sort → Sort → Sort
V ⊔ q  =  q
T ⊔ q  =  T

data _⊑_ : Sort → Sort → Set where
  rfl : q ⊑ q
  V⊑T : V ⊑ T

⊑T : q ⊑ T
⊑T {q = V} = V⊑T
⊑T {q = T} = rfl

V⊑ : V ⊑ q
V⊑ {q = V} = rfl
V⊑ {q = T} = V⊑T

⊑⊔₀ : q ⊑ (q ⊔ r)
⊑⊔₀ {q = V} = V⊑
⊑⊔₀ {q = T} = rfl

⊑⊔₁ : r ⊑ (q ⊔ r)
⊑⊔₁ {q = V} = rfl
⊑⊔₁ {q = T} = ⊑T

⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔⊔ {q = V} = refl
⊔⊔ {q = T} = refl

⊔V : q ⊔ V ≡ q
⊔V {q = V} = refl
⊔V {q = T} = refl

⊔-idem : q ⊔ q ≡ q
⊔-idem {q = V} = refl
⊔-idem {q = T} = refl

{-# REWRITE ⊔⊔ ⊔V ⊔-idem #-}

⊑⊔-idem : ⊑⊔₁ {r = q} {q = q} ≡ rfl {q = q}
⊑⊔-idem {q = V} = refl
⊑⊔-idem {q = T} = refl

{-# REWRITE ⊑⊔-idem #-}

⊑→⊔≡ : q ⊑ r → q ⊔ r ≡ r
⊑→⊔≡ rfl = refl
⊑→⊔≡ V⊑T = refl
```

Transitivity
```
tr : q ⊑ r → r ⊑ s → q ⊑ s
tr rfl r⊑s = r⊑s
tr V⊑T rfl = V⊑T

vt : {v⊑t : V ⊑ T} → v⊑t ≡ V⊑T
vt {V⊑T} = refl
```

Variables and terms
```
data _⊢[_]_ : Con -> Sort → Ty -> Set

_∋_ _⊢_ : Con → Ty → Set
_∋_ = _⊢[ V ]_
_⊢_ = _⊢[ T ]_

data _⊢[_]_ where

  zero :
      ---------
      Γ , A ⊢[ V ] A

  suc  :
      (x : Γ ⊢[ V ] B)
    → -----------
      Γ , A ⊢[ V ] B

  `_ :
      (x : Γ ⊢[ V ] A)
    → -----------
      Γ ⊢[ T ] A

  ƛ_ :
      (N : Γ , A ⊢[ T ] B)
    → ---------------
      Γ ⊢[ T ] A ⇒ B

  _·_ :
      (L : Γ ⊢[ T ] A ⇒ B)
      (M : Γ ⊢[ T ] A)
    → ---------------
      Γ ⊢[ T ] B

variable
  x y z : Γ ∋ A
  L M N : Γ ⊢ A
  P Q   : Γ ⊢[ q ] A
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

List of variables or terms
```
data _⊨[_]_ (Δ : Con) (q : Sort) : Con → Set where
  ∅ : Δ ⊨[ q ] ∅
  _,_ : Δ ⊨[ q ] Γ → Δ ⊢[ q ] A → Δ ⊨[ q ] (Γ , A)

_⊇_ _⊨_ : Con → Con → Set
_⊇_ = _⊨[ V ]_
_⊨_ = _⊨[ T ]_

variable
  ρ ξ ζ : Δ ⊇ Γ
  σ τ υ : Δ ⊨ Γ
  φ ψ θ : Δ ⊨[ q ] Γ
```

Promotion
```
lift : q ⊑ r → Γ ⊢[ q ] A → Γ ⊢[ r ] A
lift rfl P = P
lift V⊑T x = ` x
```

Extension (signature)
```
_^_ : Δ ⊨[ q ] Γ → (A : Ty) → Δ , A ⊨[ q ] Γ , A
```

Instantiate
```
_[_] : Γ ⊢[ q ] A → Δ ⊨[ r ] Γ → Δ ⊢[ q ⊔ r ] A
zero    [ φ , P ]  =  P
(suc x) [ φ , P ]  =  x [ φ ]
(` x)   [ φ ]      =  lift ⊑T (x [ φ ])
(ƛ N)   [ φ ]      =  ƛ (N [ φ ^ _ ])
(L · M) [ φ ]      =  L [ φ ] · M [ φ ]
```

Identity
```
id : Γ ⊨[ q ] Γ
id {Γ = ∅} = ∅
id {Γ = Γ , A} = id ^ _
```

Composition
```
_⨾_ : Θ ⊨[ q ] Γ → Δ ⊨[ r ] Θ → Δ ⊨[ q ⊔ r ] Γ
∅ ⨾ ψ = ∅
(φ , P) ⨾ ψ = (φ ⨾ ψ) , (P [ ψ ])
```

Zero and Shift
```
Zero : Γ , A ⊢[ q ] A
Zero {q = V}  =  zero
Zero {q = T}  =  ` zero

Suc : Δ ⊢[ q ] B → Δ , A ⊢[ q ] B

_⁺_ : Δ ⊨[ q ] Γ → (A : Ty) → Δ , A ⊨[ q ] Γ
∅       ⁺ A  =  ∅
(φ , P) ⁺ A  =  φ ⁺ A , Suc P

Suc {q = V} x  =  suc x
Suc {q = T} M  =  M [ id {q = V} ⁺ _ ]

⤊ : Γ , A ⊨[ q ] Γ
⤊ = id ⁺ _
```

Extension (definition)
```
-- φ ^ A = φ ⨾ ⤊ {q = V} , Zero
-- {-# INLINE _^_ #-}

φ ^ A = φ ⁺ A , Zero
```

# Laws

Left identity

Naturality of shift
```
[⁺]∋ : (x : Γ ∋ B) (φ : Δ ⊨[ r ] Γ) → x [ φ ⁺ A ] ≡ Suc (x [ φ ])
[⁺]∋ zero    (φ , P)  =  refl
[⁺]∋ (suc x) (φ , P)  =  [⁺]∋ x φ
```

Naturality of lift
```
lift-lift : (q⊑r : q ⊑ r) (r⊑s : r ⊑ s) (P : Γ ⊢[ q ] A) → lift r⊑s (lift q⊑r P) ≡ lift (tr q⊑r r⊑s) P
lift-lift rfl r⊑s P = refl
lift-lift V⊑T rfl P = refl

lift-Zero : (q⊑r : q ⊑ r) → lift q⊑r (Zero {Γ = Γ} {A = A}) ≡ Zero
lift-Zero rfl = refl
lift-Zero V⊑T = refl

```

Identity instantiation (signature)
```
[id] : (P : Γ ⊢[ q ] A) → P [ id {q = r} ] ≡ lift (⊑⊔₀ {r = r}) P

lift-Suc : (q⊑r : q ⊑ r) (P : Γ ⊢[ q ] B) → lift q⊑r (Suc {A = A} P) ≡ Suc (lift q⊑r P)
lift-Suc rfl P = refl
lift-Suc {A = A} V⊑T x =
  begin
    ` suc x
  ≡⟨ sym (cong (λ □ → ` suc □) ([id] {r = V} x)) ⟩
    ` suc (x [ id {q = V} ])
  ≡⟨ sym (cong `_ ([⁺]∋ x (id {q = V}))) ⟩
    ` (x [ id {q = V} ⁺ A ])
  ∎

[id] zero = sym (lift-Zero V⊑)
[id] (suc {A = A} x) =
  begin
    x [ id ⁺ A ]
  ≡⟨ [⁺]∋ x id ⟩
    Suc (x [ id ])
  ≡⟨ cong Suc ([id] x) ⟩
    Suc (lift V⊑ x)
  ≡⟨ sym (lift-Suc V⊑ x) ⟩
    lift V⊑ (suc x)
  ∎
[id] {r = r} (` x) =
  begin
    lift ⊑T (x [ id ])
  ≡⟨ cong (lift ⊑T) ([id] x) ⟩
    lift {q = r} ⊑T (lift V⊑ x)
  ≡⟨ lift-lift {r = r} V⊑ ⊑T x ⟩
    lift (tr {r = r} V⊑ ⊑T) x
  ≡⟨ cong (λ □ → lift □ x) vt ⟩
    ` x
  ∎
[id] (ƛ N) = cong ƛ_ ([id] N)
[id] (L · M) = cong₂ _·_ ([id] L) ([id] M)
```

-- [id] : (q⊑q⊔r : q ⊑ (q ⊔ r)) (P : Γ ⊢[ q ] A) →
--           P [ id {q = r} ] ≡ lift q⊑q⊔r P
-- [id] V⊑T zero = refl
-- [id] V⊑T (suc x) =
--   begin
--     (suc x) [ id ]
--   ≡⟨⟩
--     x [ id ⁺ _ ]
--   ≡⟨ [⁺]∋ x id ⟩
--     Suc (x [ id ])
--   ≡⟨ cong Suc ([id] V⊑T x) ⟩
--     Suc (` x)
--   ≡⟨⟩
--     ` (x [ id {q = V} ⁺ _ ])
--   ≡⟨ cong `_ ([⁺]∋ x id) ⟩
--     ` (suc (x [ id ]))
--   ≡⟨ cong `_ (cong suc ([id] rfl x)) ⟩
--     ` suc x
--   ∎
-- [id] rfl zero    =  refl
-- [id] rfl (suc x) =
--   begin
--     (suc x) [ id ]
--   ≡⟨⟩
--     x [ id ⁺ _ ]
--   ≡⟨ [⁺]∋ x id ⟩
--     suc (x [ id ])
--   ≡⟨ cong suc ([id] rfl x) ⟩
--     suc x
--   ∎
-- [id] rfl (` x)    =  {![id] V⊑T x!}
-- [id] rfl (ƛ N)    =  cong ƛ_ ([id] rfl N)
-- [id] rfl (L · M)  =  cong₂ _·_ ([id] rfl L) ([id] rfl M)
-- -- {-# REWRITE [id] #-}
-- ```

-- -- Right identity
-- -- ```
-- -- ⨾id : (φ : Δ ⊨[ q ] Γ) → φ ⨾ id {q = q} ≡ φ
-- -- ⨾id ∅        =  refl
-- -- ⨾id (φ , P)  =  cong₂ _,_ (⨾id φ) [id] ⊑⊔ P
-- -- ```

-- -- Functor law (signature)
-- -- ```
-- -- [][] : (M : Γ ⊢[ q ] A) (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ)
-- --         → M [ φ  ] [ ψ ] ≡ M [ φ ⨾ ψ ]
-- -- ```

-- -- Beta for Zero, Suc, ⁺ (signatures)
-- -- ```
-- -- Zero[]′ : (φ : Δ ⊨[ q ] Γ) (Q : Δ ⊢[ q ] B)
-- --             → Zero {q = q} [ φ , Q ] ≡ Q

-- -- Zero[] : (φ : Δ ⊨[ r ] Γ) (Q : Δ ⊢[ r ] B)
-- --            → Zero {q = q} [ (φ , Q) ] ≡ lift (⊑⊔₁ {r = r} {q = q})  Q

-- -- Suc[] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ) (Q : Δ ⊢[ r ] B)
-- --            → (Suc {q = q} P) [ (φ , Q) ] ≡ P [ φ ]

-- -- ⁺⨾ : (φ : Θ ⊨[ q ] Γ) (ψ : Δ ⊨[ r ] Θ) (Q : Δ ⊢[ r ] A)
-- --           → (φ ⁺ A) ⨾ (ψ , Q) ≡ φ ⨾ ψ
-- -- ```


-- -- Left identity
-- -- ```
-- -- id⨾ : (φ : Δ ⊨[ q ] Γ) → id {q = q} ⨾ φ ≡ φ
-- -- id⨾ ∅ = refl
-- -- id⨾ (φ , P) = cong₂ _,_
-- --   (begin
-- --     (id ⁺ _) ⨾ (φ , P)
-- --   ≡⟨ ⁺⨾ id φ P ⟩
-- --     id ⨾ φ
-- --   ≡⟨ id⨾ φ ⟩
-- --     φ
-- --   ∎)
-- --   ((Zero[]′ φ P))
-- -- ```

-- -- -- Beta for Zero, Suc, ⁺ (proved)
-- -- -- ```
-- -- -- Zero[]′ {q = V} φ Q = refl
-- -- -- Zero[]′ {q = T} φ Q = refl

-- -- -- Zero[] {q = V} φ Q = refl
-- -- -- Zero[] {q = T} φ Q = refl

-- -- -- Suc[] {q = V} P φ Q = refl
-- -- -- Suc[] {q = T} P φ Q =
-- -- --   begin
-- -- --     P [ id {q = V} ⁺ _ ] [ φ , Q ]
-- -- --   ≡⟨ [][] P (id {q = V} ⁺ _) (φ , Q) ⟩
-- -- --     P [ (id {q = V} ⁺ _) ⨾ (φ , Q) ]
-- -- --   ≡⟨ cong (λ □ → P [ □ ]) (⁺⨾ id φ Q)  ⟩
-- -- --     P [ id {q = V} ⨾ φ ]
-- -- --   ≡⟨ cong (λ □ → P [ □ ]) {!!} ⟩  -- (id⨾ φ)
-- -- --     P [ φ ]
-- -- --   ∎

-- -- -- ⁺⨾ ∅ ψ Q = refl
-- -- -- ⁺⨾ (φ , P) ψ Q = cong₂ _,_ (⁺⨾ φ ψ Q) (Suc[] P ψ Q)
-- -- -- ```

-- -- -- Naturality for lift
-- -- -- ```
-- -- -- lift[] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ)
-- -- --   → (lift ⊑T P) [ φ ] ≡ lift ⊑T (P [ φ ])
-- -- -- lift[] {q = V} P φ = refl
-- -- -- lift[] {q = T} P φ = refl
-- -- -- ```

-- -- -- Context extension for functor law (signature)
-- -- -- ```
-- -- -- ⨾^ : (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ) (A : Ty)
-- -- --       → (φ ^ A) ⨾ (ψ ^ A) ≡ (φ ⨾ ψ) ^ A
-- -- -- ```

-- -- -- Functor law (proof)
-- -- -- ```
-- -- -- [][] zero (φ , P) ψ = refl
-- -- -- [][] (suc x) (φ , P) ψ = [][] x φ ψ
-- -- -- [][] (` x) φ ψ =
-- -- --   begin
-- -- --     (lift ⊑T (x [ φ ])) [ ψ ]
-- -- --   ≡⟨ lift[] (x [ φ ]) ψ ⟩
-- -- --     lift ⊑T (x [ φ ] [ ψ ])
-- -- --   ≡⟨ cong (λ □ → lift ⊑T □) ([][] x φ ψ) ⟩
-- -- --     lift ⊑T (x [ φ ⨾ ψ ])
-- -- --   ∎
-- -- -- [][] (ƛ_ {A = A} N) φ ψ = cong ƛ_ (
-- -- --   begin
-- -- --     N [ φ ^ A ] [ ψ ^ A ]
-- -- --   ≡⟨ [][] N (φ ^ A) (ψ ^ A) ⟩
-- -- --     N [ (φ ^ A) ⨾ (ψ ^ A) ]
-- -- --   ≡⟨ cong (λ □ → N [ □ ]) (⨾^ φ ψ A) ⟩
-- -- --     N [ (φ ⨾ ψ) ^ A ]
-- -- --   ∎)
-- -- -- [][] (L · M) φ ψ = cong₂ _·_ ([][] L φ ψ) ([][] M φ ψ)
-- -- -- ```

-- -- -- Naturality for weakening and instantiation
-- -- -- ```
-- -- -- ⨾⁺ : (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ) (A : Ty)
-- -- --         → φ ⨾ (ψ ⁺ A) ≡ (φ ⨾ ψ) ⁺ A

-- -- -- [⁺] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ) (A : Ty)
-- -- --         → P [ φ ⁺ A ] ≡ Suc (P [ φ ])
-- -- -- [⁺] {q = V} x φ A = [⁺]∋ x φ
-- -- -- [⁺] {q = T} M φ A =
-- -- --   begin
-- -- --     M [ φ ⁺ A ]
-- -- --   ≡⟨ cong (λ □ → M [ □ ⁺ A ]) (sym (⨾id φ)) ⟩
-- -- --     M [ (φ ⨾ id) ⁺ A ]
-- -- --   ≡⟨ cong (λ □ → M [ □ ]) (sym (⨾⁺ φ id A)) ⟩
-- -- --     M [ φ ⨾ (id ⁺ A) ]
-- -- --   ≡⟨ sym ([][] M φ (id ⁺ A)) ⟩
-- -- --     M [ φ ] [ id ⁺ A ]
-- -- --   ∎

-- -- -- ⨾⁺ ∅ ψ A = refl
-- -- -- ⨾⁺ (φ , P) ψ A = cong₂ _,_ (⨾⁺ φ ψ A) ([⁺] P ψ A)
-- -- -- ```

-- -- -- Lift Zero
-- -- -- ```
-- -- -- liftZero : (q⊑r : q ⊑ r) → lift q⊑r (Zero {Γ = Γ} {A = A} {q = q}) ≡ Zero {q = r}
-- -- -- liftZero rfl = refl
-- -- -- liftZero V⊑T = refl
-- -- -- ```

-- -- -- Context extension for functor law (proof)
-- -- -- ```
-- -- -- ⨾^ {r = r} {s = s} φ ψ A =
-- -- --   begin
-- -- --     (φ ^ A) ⨾ (ψ ^ A)
-- -- --   ≡⟨⟩
-- -- --     ((φ ⁺ A) ⨾ (ψ ^ A)) , Zero {q = r} [ ψ ^ A ]
-- -- --   ≡⟨ cong₂ _,_ (⁺⨾ φ (ψ ⁺ A) Zero) (Zero[] {q = r} (ψ ⁺ A) (Zero {q = s})) ⟩
-- -- --     (φ ⨾ (ψ ⁺ A)) , lift (⊑⊔₁ {q = r}) (Zero {q = s})
-- -- --   ≡⟨ cong₂ _,_ (⨾⁺ φ ψ A) (liftZero {q = s} (⊑⊔₁ {q = r})) ⟩
-- -- --     ((φ ⨾ ψ) ⁺ A) , Zero {q = r ⊔ s}
-- -- --   ≡⟨⟩
-- -- --     (φ ⨾ ψ) ^ A
-- -- --   ∎
-- -- -- ```

-- -- -- Associativity
-- -- -- ```
-- -- -- ⨾⨾ : ∀ (φ : Θ ⊨[ q ] Γ) (ψ : Φ ⊨[ r ] Θ) (θ : Δ ⊨ Φ) →
-- -- --           (φ ⨾ ψ) ⨾ θ ≡ φ ⨾ (ψ ⨾ θ)
-- -- -- ⨾⨾ ∅ ψ θ = refl
-- -- -- ⨾⨾ (φ , P) ψ θ =
-- -- --   begin
-- -- --     (((φ ⨾ ψ) ⨾ θ) , ((P [ ψ ]) [ θ ]))
-- -- --   ≡⟨ cong₂ _,_ (⨾⨾ φ ψ θ) ([][] P ψ θ) ⟩
-- -- --     ((φ ⨾ (ψ ⨾ θ)) , (P [ ψ ⨾ θ ]))
-- -- --   ∎
-- -- -- ```

-- -- -- # Relating to the laws in Autosubst paper

-- -- -- Alternative way to compute _⁺_
-- -- -- ```
-- -- -- ⨾⤊ : (φ : Δ ⊨[ q ] Γ) (A : Ty) → φ ⨾ ⤊ ≡ φ ⁺ A
-- -- -- ⨾⤊ φ A =
-- -- --   begin
-- -- --     φ ⨾ ⤊
-- -- --   ≡⟨⟩
-- -- --     φ ⨾ (id ⁺ A)
-- -- --   ≡⟨ ⨾⁺ φ id A ⟩
-- -- --     (φ ⨾ id) ⁺ A
-- -- --   ≡⟨ cong (λ □ → □ ⁺ A) (⨾id φ) ⟩
-- -- --     φ ⁺ A
-- -- --   ∎

-- -- -- ⁺-def : (φ : Δ ⊨[ q ] Γ) (A : Ty) → φ ⁺ A ≡ φ ⨾ ⤊
-- -- -- ⁺-def φ A = sym (⨾⤊ φ A)
-- -- -- ```

-- -- -- Alternative way to compute _^_
-- -- -- ```
-- -- -- ⨾⤊, : (φ : Δ ⊨[ q ] Γ) (A : Ty) → (φ ⨾ ⤊ , Zero) ≡ φ ^ A
-- -- -- ⨾⤊, φ A =
-- -- --   begin
-- -- --     (φ ⨾ ⤊ , Zero)
-- -- --   ≡⟨ cong (λ □ → □ , Zero) (⨾⤊ φ A) ⟩
-- -- --     φ ⁺ A , Zero
-- -- --   ≡⟨⟩
-- -- --     φ ^ A
-- -- --   ∎
-- -- -- ```

-- -- -- π₁ law
-- -- -- ```
-- -- -- ⤊⨾, : (φ : Δ ⊨[ q ] Γ) (P : Δ ⊢[ q ] A) → (⤊ ⨾ (φ , P)) ≡ φ
-- -- -- ⤊⨾, φ P =
-- -- --   begin
-- -- --     (⤊ ⨾ (φ , P))
-- -- --   ≡⟨⟩
-- -- --     (id ⁺ _) ⨾ (φ , P)
-- -- --   ≡⟨ ⁺⨾ id φ P ⟩
-- -- --      id ⨾ φ
-- -- --   ≡⟨ id⨾ φ ⟩
-- -- --     φ
-- -- --   ∎
-- -- -- ```

-- -- -- eta law
-- -- -- ```
-- -- -- η : (φ : Δ ⊨[ q ] Γ , A) → ((⤊ ⨾ φ) , Zero {q = q} [ φ ]) ≡ φ
-- -- -- η {q = q} (φ , P) =
-- -- --   begin
-- -- --     ((⤊ ⨾ (φ , P)) , (Zero {q = q} [ φ , P ]))
-- -- --   ≡⟨ cong₂ _,_ (⤊⨾, φ P) (Zero[] {q = q} φ P) ⟩
-- -- --     φ , P
-- -- --   ∎
-- -- -- ```

-- -- -- Autosubst rewrites
-- -- -- ```
-- -- -- {-# REWRITE id⨾ ⨾id ⨾⨾ [id] [][] ⤊⨾, Zero[] Suc[] ⁺-def #-}
-- -- -- ```

-- -- -- ## Special cases of substitution

-- -- -- Neither of the following can be defined, because
-- -- -- we need id on terms, not variables.

-- -- -- Substitute for the last variable in the environment
-- -- -- (de Bruijn index zero).

-- -- -- _[_]₀ :
-- -- --     (N : Γ , A ⊢ B)
-- -- --     (M : Γ ⊢ A)
-- -- --   → ----------------
-- -- --      Γ ⊢ B
-- -- -- N [ M ]₀ = N [ id , M ]

-- -- -- This is exactly what we need for beta reduction.

-- -- -- Substitute for the last but one variable in the environment
-- -- -- (de Bruijn index one).

-- -- -- _[_]₁ :
-- -- --     (N : Γ , A , B ⊢ C)
-- -- --     (M : Γ ⊢ A)
-- -- --   → -------------------
-- -- --      Γ , B ⊢ C
-- -- -- N [ M ]₁ = N [ (id , M) ⨾ ⤊ , Zero ]


