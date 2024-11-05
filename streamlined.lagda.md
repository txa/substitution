Parameterised development
based on
Substitution without Copy and Paste

Philip Wadler, 26 Sep--3 Nov 2024


The previous version required id to be a renaming, but we also need id
as a substitution to define beta reduction:

   (ƛ N) V --> N [ id , V ]

Alas, this means some equations become more clumsy:

    id⨾ : (φ : Δ ⊇ r ⊨ Γ) → id {q = q} ⨾ φ ≡ lift* (⊑⊔₁ {q = q}) φ

Here we define

    lift* : (q ⊑ r) → Δ ⊇ q ⊨ Γ → Δ ⊆ r ⊨ Γ

The following paper

  Schäfer, Steven, Tobias Tebbi, and Gert Smolka. ‘Autosubst: Reasoning
  with de Bruijn Terms and Parallel Substitutions’. In Interactive
  Theorem Proving, edited by Christian Urban and Xingyuan Zhang,
  359–74. Lecture Notes in Computer Science. Cham: Springer
  International Publishing, 2015.
  https://doi.org/10.1007/978-3-319-22102-1_24.

defines twelve rules which are confluent over open terms and complete
for the given model of λ-calculus.

  (st)[σ] ≡ (s[σ])(t[σ])
  (λ.s)[σ] ≡λ.(s[0·σ◦↑])
  0[s · σ] ≡ s
  ↑ ◦ (s · σ) ≡ σ
  s[id] ≡ s
  0[σ]·(↑∘σ) ≡ σ
  id◦σ ≡ σ
  σ◦id ≡σ
  (σ ◦ τ) ◦ θ ≡ σ ◦ (τ ◦ θ)
  (s · σ) ◦ τ ≡ s[τ] · σ ◦ τ
  s[σ][τ] ≡ s[σ ◦ τ]
  0 · ↑ ≡ id

(Their s·σ is our σ,N and their σ∘τ is our σ⨾τ.)

I'd like to have the same twelve rules as either equationally true or
as rewrites. I define rewrites in this direction toward the end but
they fail to work, as indicated by the final example.



```
{-# OPTIONS --rewriting #-}
module streamlined where

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
infixl 5 _↑_ _⇑_ _^_
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

⊔V : q ⊔ V ≡ q
⊔V {q = V} = refl
⊔V {q = T} = refl

⊔T : q ⊔ T ≡ T
⊔T {q = V} = refl
⊔T {q = T} = refl

{-# REWRITE ⊔V ⊔T #-}

⊑⊔₀ : q ⊑ (q ⊔ r)
⊑⊔₀ {q = V} = V⊑
⊑⊔₀ {q = T} = rfl

⊑⊔₁ : r ⊑ (q ⊔ r)
⊑⊔₁ {q = V} = rfl
⊑⊔₁ {q = T} = ⊑T

⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔⊔ {q = V} = refl
⊔⊔ {q = T} = refl

⊔-idem : q ⊔ q ≡ q
⊔-idem {q = V} = refl
⊔-idem {q = T} = refl

{-# REWRITE ⊔⊔ ⊔-idem #-}

⊑⊔₀-idem : ⊑⊔₀ {q = q} {r = q}  ≡ rfl {q = q}
⊑⊔₀-idem {q = V} = refl
⊑⊔₀-idem {q = T} = refl

⊑⊔₁-idem : ⊑⊔₁ {r = q} {q = q}  ≡ rfl {q = q}
⊑⊔₁-idem {q = V} = refl
⊑⊔₁-idem {q = T} = refl

⊑⊔₀-V : ⊑⊔₀ {q = q} {r = V} ≡ rfl
⊑⊔₀-V {q = V} = refl
⊑⊔₀-V {q = T} = refl

{-# REWRITE ⊑⊔₀-idem ⊑⊔₁-idem ⊑⊔₀-V #-}

⊑→⊔≡ : q ⊑ r → q ⊔ r ≡ r
⊑→⊔≡ rfl = refl
⊑→⊔≡ V⊑T = refl
```

Transitivity
```
tr : q ⊑ r → r ⊑ s → q ⊑ s
tr rfl r⊑s = r⊑s
tr V⊑T rfl = V⊑T

uniq : (q⊑r q⊑r′ : q ⊑ r) → q⊑r ≡ q⊑r′
uniq rfl rfl = refl
uniq V⊑T V⊑T = refl
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
      Γ , A ∋ A

  suc  :
      (x : Γ ∋ B)
    → -----------
      Γ , A ∋ B

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
  ∅ :
      ---------
      Δ ⊨[ q ] ∅
  _,_ :
      (φ : Δ ⊨[ q ] Γ)
      (P : Δ ⊢[ q ] A)
    → ---------------
      Δ ⊨[ q ] Γ , A

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

lift* : q ⊑ r → Γ ⊨[ q ] Δ → Γ ⊨[ r ] Δ
lift* q⊑r ∅ = ∅
lift* q⊑r (φ , P) = (lift* q⊑r φ) , (lift q⊑r P)

lift*rfl : (φ : Γ ⊨[ q ] Δ) → lift* rfl φ ≡ φ
lift*rfl ∅ = refl
lift*rfl (φ , P) = cong₂ _,_ (lift*rfl φ) refl

{-# REWRITE lift*rfl #-}
```

Extension (signature)
```
_^_ :
    (φ : Δ ⊨[ q ] Γ)
    (A : Ty)
  → ------------------
    Δ , A ⊨[ q ] Γ , A
```

Instantiate
```
_[_] :
    (P : Γ ⊢[ q ] A)
    (φ : Δ ⊨[ r ] Γ)
  → ----------------
    Δ ⊢[ q ⊔ r ] A
zero    [ φ , P ]  =  P
(suc x) [ φ , P ]  =  x [ φ ]
(` x)   [ φ ]      =  lift ⊑T (x [ φ ])
(ƛ N)   [ φ ]      =  ƛ (N [ φ ^ _ ])
(L · M) [ φ ]      =  L [ φ ] · M [ φ ]
```

Identity
```
id :
    (q : Sort)
  → ----------
    Γ ⊨[ q ] Γ
id {Γ = ∅} q = ∅
id {Γ = Γ , A} q = id q ^ _
```

Composition
```
_⨾_ :
    (φ : Θ ⊨[ q ] Γ)
    (ψ : Δ ⊨[ r ] Θ)
  → ----------------
    Δ ⊨[ q ⊔ r ] Γ
∅ ⨾ ψ = ∅
(φ , P) ⨾ ψ = (φ ⨾ ψ) , (P [ ψ ])
```

Zero and Shift
```
● :
    --------------
    Γ , A ⊢[ q ] A
● {q = V}  =  zero
● {q = T}  =  ` zero

_↑_ :
    (P : Δ ⊢[ q ] B)
    (A : Ty)
  → ----------------
    Δ , A ⊢[ q ] B

_⇑_ :
    (φ : Δ ⊨[ q ] Γ)
    (A : Ty)
  → -----------------
    Δ , A ⊨[ q ] Γ
∅       ⇑ A  =  ∅
(φ , P) ⇑ A  =  φ ⇑ A , P ↑ A

_↑_ {q = V} x A  =  suc x
_↑_ {q = T} M A  =  M [ id V ⇑ A ]
```

Extension (definition)
```
φ ^ A = φ ⇑ A , ●
-- {-# INLINE _^_ #-}
```

# Laws

Left identity

Naturality of shift
```
[⇑]∋ :
    (x : Γ ∋ B)
    (φ : Δ ⊨[ r ] Γ)
  → -------------------------
    x [ φ ⇑ A ] ≡ x [ φ ] ↑ A
[⇑]∋ zero    (φ , P)  =  refl
[⇑]∋ (suc x) (φ , P)  =  [⇑]∋ x φ
```

Naturality of lift
```
lift-lift :
    (q⊑r : q ⊑ r)
    (r⊑s : r ⊑ s)
    (P : Γ ⊢[ q ] A)
  → --------------------------------------------
    lift r⊑s (lift q⊑r P) ≡ lift (tr q⊑r r⊑s) P
lift-lift rfl r⊑s P = refl
lift-lift V⊑T rfl P = refl

lift-● :
    (q⊑r : q ⊑ r)
  → ---------------------------------
    lift q⊑r (● {Γ = Γ} {A = A}) ≡ ●
lift-● rfl = refl
lift-● V⊑T = refl
```

Identity instantiation (signature)
```
[id] :
    (r : Sort)
    (P : Γ ⊢[ q ] A)
  → ---------------------------------
    P [ id r ] ≡ lift (⊑⊔₀ {r = r}) P

lift-↑ :
    (q⊑r : q ⊑ r)
    (P : Γ ⊢[ q ] B)
  → ----------------------------------
    lift q⊑r (P ↑ A) ≡ lift q⊑r P ↑ A
lift-↑ rfl P = refl
lift-↑ {A = A} V⊑T x =
  begin
    ` suc x
  ≡⟨ sym (cong (λ □ → ` suc □) ([id] V x)) ⟩
    ` suc (x [ id V ])
  ≡⟨ sym (cong `_ ([⇑]∋ x (id V))) ⟩
    ` (x [ id V ⇑ A ])
  ∎

[id] r zero = sym (lift-● {q = V} ⊑⊔₀)
[id] r (suc {A = A} x) =
  begin
    x [ id r ⇑ A ]
  ≡⟨ [⇑]∋ x (id r) ⟩
    (x [ id r ]) ↑ A
  ≡⟨ cong (_↑ A) ([id] r x) ⟩
    lift ⊑⊔₀ x ↑ A
  ≡⟨ sym (lift-↑ ⊑⊔₀ x) ⟩
    lift ⊑⊔₀ (suc x)
  ∎
[id] r (` x) =
  begin
    lift ⊑T (x [ id r ])
  ≡⟨ cong (lift ⊑T) ([id] r x) ⟩
    lift {q = r} ⊑T (lift V⊑ x)
  ≡⟨ lift-lift {r = r} V⊑ ⊑T x ⟩
    lift (tr {r = r} V⊑ ⊑T) x
  ≡⟨ cong (λ □ → lift □ x) (uniq (tr {r = r} V⊑ ⊑T) V⊑T) ⟩
    ` x
  ∎
[id] r (ƛ N) = cong ƛ_ ([id] r N)
[id] r (L · M) = cong₂ _·_ ([id] r L) ([id] r M)
```

-- Right identity
-- ```
-- ⨾id : (φ : Δ ⊨[ q ] Γ) → φ ⨾ id {q = r} ≡ lift* (⊑⊔₀ {r = r}) φ
-- ⨾id ∅                =  refl
-- ⨾id {q = q} (φ , P)  =  cong₂ _,_ (⨾id φ) ([id] P)
-- ```

-- Functor law (signature)
-- ```
-- [][] : (P : Γ ⊢[ q ] A) (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ)
--         → P [ φ  ] [ ψ ] ≡ P [ φ ⨾ ψ ]
-- ```

-- Beta for Zero, Suc, ⇑ (signatures)
-- ```
-- ●[] : (φ : Δ ⊨[ r ] Γ) (Q : Δ ⊢[ r ] B)
--            → ● {q = q} [ (φ , Q) ] ≡ lift (⊑⊔₁ {q = q})  Q

-- Suc[] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ) (Q : Δ ⊢[ r ] B)
--            → (Suc {q = q} P) [ (φ , Q) ] ≡ P [ φ ]

-- ⇑⨾ : (φ : Θ ⊨[ q ] Γ) (ψ : Δ ⊨[ r ] Θ) (Q : Δ ⊢[ r ] A)
--           → (φ ⇑ A) ⨾ (ψ , Q) ≡ φ ⨾ ψ
-- ```

-- Left identity
-- ```
-- id⨾ : (φ : Δ ⊨[ r ] Γ) → id {q = q} ⨾ φ ≡ lift* (⊑⊔₁ {q = q}) φ
-- id⨾ ∅ = refl
-- id⨾ {q = q} (φ , P) = cong₂ _,_
--   (begin
--     (id ⇑ _) ⨾ (φ , P)
--   ≡⟨ ⇑⨾ id φ P ⟩
--     id ⨾ φ
--   ≡⟨ id⨾ φ ⟩
--     lift* (⊑⊔₁ {q = q}) φ
--   ∎)
--   (●[] {q = q} φ P)
-- ```

-- Beta for ●, Suc, ⇑ (proved)
-- ```
-- ●[] {q = V} φ Q = refl
-- ●[] {q = T} φ Q = refl

-- Suc[] {q = V} P φ Q = refl
-- Suc[] {q = T} P φ Q =
--   begin
--     P [ id {q = V} ⇑ _ ] [ φ , Q ]
--   ≡⟨ [][] P (id {q = V} ⇑ _) (φ , Q) ⟩
--     P [ (id {q = V} ⇑ _) ⨾ (φ , Q) ]
--   ≡⟨ cong (λ □ → P [ □ ]) (⇑⨾ id φ Q)  ⟩
--     P [ id {q = V} ⨾ φ ]
--   ≡⟨ cong (λ □ → P [ □ ]) (id⨾ {q = V} φ) ⟩
--     P [ lift* (⊑⊔₁ {q = V}) φ ]
--   ≡⟨ cong (λ □ → P [ □ ]) (lift*rfl φ) ⟩
--     P [ φ ]
--   ∎

-- ⇑⨾ ∅ ψ Q = refl
-- ⇑⨾ (φ , P) ψ Q = cong₂ _,_ (⇑⨾ φ ψ Q) (Suc[] P ψ Q)

-- ⤊⨾ : (ψ : Δ ⊨[ r ] Θ) (Q : Δ ⊢[ r ] A)
--           → ⤊ ⨾ (ψ , Q) ≡ ψ
-- ⤊⨾ ψ Q =
--   begin
--     ⤊ ⨾ (ψ , Q)
--   ≡⟨⟩
--     (id ⇑ _) ⨾  (ψ , Q)
--   ≡⟨ ⇑⨾ id ψ Q ⟩
--     id ⨾ ψ
--   ≡⟨ id⨾ ψ ⟩
--     ψ
--   ∎
-- ```

-- Naturality for lift
-- ```
-- lift[] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ)
--   → (lift ⊑T P) [ φ ] ≡ lift ⊑T (P [ φ ])
-- lift[] {q = V} P φ = refl
-- lift[] {q = T} P φ = refl
-- ```

-- Context extension for functor law (signature)
-- ```
-- ⨾^ : (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ) (A : Ty)
--       → (φ ^ A) ⨾ (ψ ^ A) ≡ (φ ⨾ ψ) ^ A
-- ```

-- Functor law (proof)
-- ```
-- [][] zero (φ , P) ψ = refl
-- [][] (suc x) (φ , P) ψ = [][] x φ ψ
-- [][] (` x) φ ψ =
--   begin
--     (lift ⊑T (x [ φ ])) [ ψ ]
--   ≡⟨ lift[] (x [ φ ]) ψ ⟩
--     lift ⊑T (x [ φ ] [ ψ ])
--   ≡⟨ cong (λ □ → lift ⊑T □) ([][] x φ ψ) ⟩
--     lift ⊑T (x [ φ ⨾ ψ ])
--   ∎
-- [][] (ƛ_ {A = A} N) φ ψ = cong ƛ_ (
--   begin
--     N [ φ ^ A ] [ ψ ^ A ]
--   ≡⟨ [][] N (φ ^ A) (ψ ^ A) ⟩
--     N [ (φ ^ A) ⨾ (ψ ^ A) ]
--   ≡⟨ cong (λ □ → N [ □ ]) (⨾^ φ ψ A) ⟩
--     N [ (φ ⨾ ψ) ^ A ]
--   ∎)
-- [][] (L · M) φ ψ = cong₂ _·_ ([][] L φ ψ) ([][] M φ ψ)
-- ```

-- Naturality for weakening and instantiation
-- ```
-- ⨾⇑ : (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ) (A : Ty)
--         → φ ⨾ (ψ ⇑ A) ≡ (φ ⨾ ψ) ⇑ A

-- [⇑] : (P : Γ ⊢[ q ] A) (φ : Δ ⊨[ r ] Γ) (A : Ty)
--         → P [ φ ⇑ A ] ≡ Suc (P [ φ ])
-- [⇑] {q = V} x φ A = [⇑]∋ x φ
-- [⇑] {q = T} M φ A =
--   begin
--     M [ φ ⇑ A ]
--   ≡⟨ cong (λ □ → M [ □ ⇑ A ]) (sym (lift*rfl φ)) ⟩
--     M [ lift* rfl φ ⇑ A ]
--   ≡⟨ cong (λ □ → M [ □ ⇑ A ]) (sym (⨾id φ)) ⟩
--     M [ (φ ⨾ id {q = V}) ⇑ A ]
--   ≡⟨ cong (λ □ → M [ □ ]) (sym (⨾⇑ φ id A)) ⟩
--     M [ φ ⨾ (id {q = V} ⇑ A) ]
--   ≡⟨ sym ([][] M φ (id ⇑ A)) ⟩
--     M [ φ ] [ id {q = V} ⇑ A ]
--   ∎

-- ⨾⇑ ∅ ψ A = refl
-- ⨾⇑ (φ , P) ψ A = cong₂ _,_ (⨾⇑ φ ψ A) ([⇑] P ψ A)
-- ```

-- Context extension for functor law (proof)
-- ```
-- ⨾^ {r = r} {s = s} φ ψ A =
--   begin
--     (φ ^ A) ⨾ (ψ ^ A)
--   ≡⟨⟩
--     ((φ ⇑ A) ⨾ (ψ ^ A)) , ● {q = r} [ ψ ^ A ]
--   ≡⟨ cong₂ _,_ (⇑⨾ φ (ψ ⇑ A) ●) (●[] {q = r} (ψ ⇑ A) (● {q = s})) ⟩
--     (φ ⨾ (ψ ⇑ A)) , lift (⊑⊔₁ {q = r}) (● {q = s})
--   ≡⟨ cong₂ _,_ (⨾⇑ φ ψ A) (lift-● {q = s} (⊑⊔₁ {q = r})) ⟩
--     ((φ ⨾ ψ) ⇑ A) , ● {q = r ⊔ s}
--   ≡⟨⟩
--     (φ ⨾ ψ) ^ A
--   ∎
-- ```

-- Associativity
-- ```
-- ⨾⨾ : ∀ (φ : Θ ⊨[ q ] Γ) (ψ : Φ ⊨[ r ] Θ) (θ : Δ ⊨ Φ) →
--           (φ ⨾ ψ) ⨾ θ ≡ φ ⨾ (ψ ⨾ θ)
-- ⨾⨾ ∅ ψ θ = refl
-- ⨾⨾ (φ , P) ψ θ =
--   begin
--     (((φ ⨾ ψ) ⨾ θ) , ((P [ ψ ]) [ θ ]))
--   ≡⟨ cong₂ _,_ (⨾⨾ φ ψ θ) ([][] P ψ θ) ⟩
--     ((φ ⨾ (ψ ⨾ θ)) , (P [ ψ ⨾ θ ]))
--   ∎
-- ```

-- # Relating to the laws in Autosubst paper

-- Alternative way to compute _⇑_
-- ```
-- ⨾⤊ : (φ : Δ ⊨[ q ] Γ) (A : Ty) → φ ⨾ ⤊ ≡ φ ⇑ A
-- ⨾⤊ φ A =
--   begin
--     φ ⨾ ⤊
--   ≡⟨⟩
--     φ ⨾ (id ⇑ A)
--   ≡⟨ ⨾⇑ φ id A ⟩
--     (φ ⨾ id) ⇑ A
--   ≡⟨ cong (λ □ → □ ⇑ A) (⨾id φ) ⟩
--     φ ⇑ A
--   ∎

-- ⇑-def : (φ : Δ ⊨[ q ] Γ) (A : Ty) → φ ⇑ A ≡ φ ⨾ ⤊
-- ⇑-def φ A = sym (⨾⤊ φ A)
-- ```

-- Alternative way to compute _^_
-- ```
-- ⨾⤊, : (φ : Δ ⊨[ q ] Γ) (A : Ty) → (φ ⨾ ⤊ , ●) ≡ φ ^ A
-- ⨾⤊, φ A =
--   begin
--     (φ ⨾ ⤊ , ●)
--   ≡⟨ cong (λ □ → □ , ●) (⨾⤊ φ A) ⟩
--     φ ⇑ A , ●
--   ≡⟨⟩
--     φ ^ A
--   ∎
-- ```

-- π₁ law
-- ```
-- ⤊⨾, : (φ : Δ ⊨[ q ] Γ) (P : Δ ⊢[ q ] A) → (⤊ ⨾ (φ , P)) ≡ φ
-- ⤊⨾, φ P =
--   begin
--     (⤊ ⨾ (φ , P))
--   ≡⟨⟩
--     (id ⇑ _) ⨾ (φ , P)
--   ≡⟨ ⇑⨾ id φ P ⟩
--      id ⨾ φ
--   ≡⟨ id⨾ φ ⟩
--     φ
--   ∎
-- ```

-- eta law
-- ```
-- η : (φ : Δ ⊨[ q ] Γ , A) → ((⤊ ⨾ φ) , ● {q = q} [ φ ]) ≡ φ
-- η {q = q} (φ , P) =
--   begin
--     ((⤊ ⨾ (φ , P)) , (● {q = q} [ φ , P ]))
--   ≡⟨ cong₂ _,_ (⤊⨾, φ P) (●[] {q = q} φ P) ⟩
--     φ , P
--   ∎
-- ```

-- Autosubst rewrites

-- Nathaniel notes that `[][]` needs to be specialised to type
-- without the `⊔⊔` rewrite before it will itself work as a
-- rewrite.
-- ```
-- idᵀ : Γ ⊨[ T ] Γ
-- idᵀ = id {q = T}

-- [][]ᵀ : (M : Γ ⊢ A) (φ : Θ ⊨[ r ] Γ) (ψ : Δ ⊨[ s ] Θ)
--         → M [ φ  ] [ ψ ] ≡ M [ φ ⨾ ψ ]
-- [][]ᵀ = [][]

-- [id]ᵀ : (M : Γ ⊢ A) → M [ idᵀ ] ≡ M
-- [id]ᵀ = [id]

-- {-# REWRITE [][]ᵀ [id]ᵀ id⨾ ⨾id ⨾⨾ ⤊⨾, #-}
-- ```
-- I've commented out the rewrites below because with them Agda
-- tends to go into an infinite loop.
-- ```
-- -- {-# REWRITE ●[] Suc[] ⇑-def #-}
-- ```

-- ## Special cases of substitution

-- Substitute for the last variable in the environment
-- (de Bruijn index zero).
-- ```
-- _[_]₀ :
--     (N : Γ , A ⊢ B)
--     (M : Γ ⊢ A)
--   → ----------------
--      Γ ⊢ B
-- N [ M ]₀ = N [ id , M ]
-- ```
-- This is exactly what we need for beta reduction.

-- Substitute for the last but one variable in the environment
-- (de Bruijn index one).
-- ```
-- _[_]₁ :
--     (N : Γ , A , B ⊢ C)
--     (M : Γ ⊢ A)
--   → -------------------
--      Γ , B ⊢ C
-- N [ M ]₁ = N [ (id , M) ⨾ ⤊ , ● ]
-- ```

-- Warm up
-- ```
-- warmup : ∀ (N : Γ ⊢ B) (M : Γ ⊢ A) → N [ ⤊ ] [ M ]₀ ≡ N
-- warmup N M =
--   begin
--     N [ ⤊ ] [ M ]₀
--   ≡⟨⟩
--     N [ ⤊ ] [ id , M ]
--   ≡⟨ [][] N ⤊ (id , M) ⟩
--     N [ ⤊ ⨾ (id , M) ]
--   ≡⟨ cong (λ □ → N [ □ ]) (⤊⨾, id M) ⟩
--     N [ id {q = T} ]
--   ≡⟨ [id] {r = T} N ⟩
--     N
--   ∎
-- ```
-- Here is the automatic version.
-- ```
-- warmup′ : ∀ (N : Γ ⊢ B) (M : Γ ⊢ A) → N [ ⤊ ] [ M ]₀ ≡ N
-- warmup′ N M =  refl
-- ```

-- First challenge
-- ```
-- double-subst : ∀ (N : Γ , A , B ⊢ C) (M : Γ ⊢ A) (L : Γ ⊢ B) →
--   N [ M ]₁ [ L ]₀ ≡ N [ L [ ⤊ ] ]₀ [ M ]₀
-- double-subst N M L =
--   begin
--     N [ M ]₁ [ L ]₀
--   ≡⟨⟩
--     N [ (id , M) ⨾ ⤊ , ● ] [ id , L ]
--   ≡⟨ [][] N ((id , M) ⨾ ⤊ , ●) (id , L) ⟩
--     N [ ((id , M) ⨾ ⤊ , ●) ⨾ (id , L) ]    
--   ≡⟨⟩
--     N [ (((id , M) ⨾ ⤊) ⨾ (id , L)) , ● {q = T} [ id , L ] ]
--   ≡⟨ cong₂ (λ □₀ □₁ → N [ □₀ , □₁ ]) (⨾⨾ (id , M) ⤊ (id , L)) (●[] {q = T} id L) ⟩
--     N [ ((id , M) ⨾ (⤊ ⨾ (id , L))) , L ]
--   ≡⟨ cong (λ □ → N [ ((id , M) ⨾ □) , L ]) (⤊⨾, id L) ⟩
--     N [ ((id , M) ⨾ id {q = T}) , L ]
--   ≡⟨ cong (λ □ → N [ □ , L ]) (⨾id {r = T} (id , M)) ⟩
--     N [ id , M , L ]
--   ≡⟨ cong (λ □ → N [ id , M , □ ]) (sym ([id] {r = T} L)) ⟩
--     N [ id , M , L [ id {q = T} ] ]
--   ≡⟨ cong (λ □ → N [ id , M , L [ □ ] ]) (⤊⨾ id M) ⟩
--     N [ id , M , L [ ⤊ ⨾ (id , M) ] ]
--   ≡⟨ cong₂ (λ □₀ □₁ → N [ □₀ , □₁ ]) (sym (id⨾ {q = T} (id , M))) ([][] L (⤊) (id , M)) ⟩
--     N [ (id {q = T} ⨾ (id , M)) , (L [ ⤊ ] [ id , M ]) ]
--   ≡⟨⟩
--     N [ (id , (L [ ⤊ ])) ⨾ (id , M) ]
--   ≡⟨ sym ([][] N (id , (L [ ⤊ ])) (id , M)) ⟩
--     N [ id , (L [ ⤊ ]) ] [ id , M ]
--   ≡⟨⟩
--     N [ L [ ⤊ ] ]₀ [ M ]₀
--   ∎

-- double-subst′ : ∀ (N : Γ , A , B ⊢ C) (M : Γ ⊢ A) (L : Γ ⊢ B) →
--   N [ M ]₁ [ L ]₀ ≡ N [ L [ ⤊ ] ]₀ [ M ]₀
-- double-subst′ N M L = {!refl!}
-- ```

-- Second challenge
-- ```
-- commute-subst : N [ M ]₀ [ L ]₀ ≡ N [ L ]₁ [ M [ L ]₀ ]₀
-- commute-subst = {! !}
-- ```
