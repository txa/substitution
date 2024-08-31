Normalisation by Evaluation
inspired by Kovacs and Lindley

Philip Wadler, 31 August 2024
```
module nbe where

open import Agda.Builtin.FromNat
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
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

let X, Y, Z range over Set
```
variable
  X Y Z : Set
```

Operator precedence
```
infix  3 _⊢_
infix  3 _⊢nf_
infix  3 _⊢ne_
infix  3 _∋_
infixl 4 _,_
infixr 5 _⇒_
infix  5 ƛ_
infix  5 ′_
infixl 6 _·_
infix  7 `_
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
      (x : Γ ∋ A)
    → -----------
      Γ , B ∋ A

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

Renaming
```
_⇒ʳ_ : Con → Con → Set
Γ ⇒ʳ Δ  =  ∀ {A} → Γ ∋ A → Δ ∋ A

variable
  ρ ρ′ ρ″ : Γ ⇒ʳ Δ
```

Extension for renamings
```
ext : Γ ⇒ʳ Δ → (Γ , A) ⇒ʳ (Δ , A)
ext ρ zero = zero
ext ρ (suc i) = suc (ρ i)
```

Renaming terms
```
ren : Γ ⇒ʳ Δ → Γ ⊢ A → Δ ⊢ A
ren ρ (` x) = ` (ρ x)
ren ρ (L · M) = (ren ρ L) · (ren ρ M)
ren ρ (ƛ N) = ƛ (ren (ext ρ) N)
```

Renaming normal and neutral forms
```
ren-nf : Γ ⇒ʳ Δ → Γ ⊢nf A → Δ ⊢nf A
ren-ne : Γ ⇒ʳ Δ → Γ ⊢ne A → Δ ⊢ne A

ren-nf ρ (′ M) = ′ (ren-ne ρ M)
ren-nf ρ (ƛ N) = ƛ (ren-nf (ext ρ) N)

ren-ne ρ (` x) = ` (ρ x)
ren-ne ρ (L · M) = (ren-ne ρ L) · (ren-nf ρ M)
```

Identity renaming
```
id : Γ ⇒ʳ Γ
id x  =  x
```

Substitution
```
_⇒ˢ_ : Con → Con → Set
Γ ⇒ˢ Δ  =  ∀ {A} → Γ ∋ A → Δ ⊢ A

variable
  σ σ′ σ″ : Γ ⇒ˢ Δ
```

Extension for substitution
```
exts : Γ ⇒ˢ Δ → (Γ , A) ⇒ˢ (Δ , A)
exts σ zero = ` zero
exts σ (suc x) = ren suc (σ x)
```

Substitution for terms
```
sub : Γ ⇒ˢ Δ → Γ ⊢ A → Δ ⊢ A
sub σ (` x) = σ x
sub σ (L · M) = (sub σ L) · (sub σ M)
sub σ (ƛ N) = ƛ (sub (exts σ) N)
```

Four kinds of composition
```
_ʳ∘ʳ_ : Θ ⇒ʳ Δ → Γ ⇒ʳ Θ → Γ ⇒ʳ Δ
ρ′ ʳ∘ʳ ρ = ρ′ ∘ ρ

_ˢ∘ʳ_ : Θ ⇒ˢ Δ → Γ ⇒ʳ Θ → Γ ⇒ˢ Δ
σ′ ˢ∘ʳ ρ = σ′ ∘ ρ

_ʳ∘ˢ_ : Θ ⇒ʳ Δ → Γ ⇒ˢ Θ → Γ ⇒ˢ Δ
ρ′ ʳ∘ˢ σ = ren ρ′ ∘ σ

_ˢ∘ˢ_ : Θ ⇒ˢ Δ → Γ ⇒ˢ Θ → Γ ⇒ˢ Δ
σ′ ˢ∘ˢ σ = sub σ′ ∘ σ
```

Interpretation of types and contexts
```
⟦_⟧ᵀ : Ty -> Con -> Set
⟦ ι ⟧ᵀ     Γ = Γ ⊢nf ι
⟦ A ⇒ B ⟧ᵀ Γ = ∀ {Δ} → Γ ⇒ʳ Δ → ⟦ A ⟧ᵀ Δ → ⟦ B ⟧ᵀ Δ

⟦_⟧ᶜ : Con -> Con -> Set
⟦ ∅ ⟧ᶜ     Δ = ⊤
⟦ Γ , A ⟧ᶜ Δ = ⟦ Γ ⟧ᶜ Δ × ⟦ A ⟧ᵀ Δ
```

Weakening values and environments
```
weaken-value : Γ ⇒ʳ Δ → ⟦ A ⟧ᵀ Γ -> ⟦ A ⟧ᵀ Δ
weaken-value {A = ι}     ρ M = ren-nf ρ M
weaken-value {A = A ⇒ B} ρ f = λ ρ′ v → f (ρ′ ʳ∘ʳ ρ) v

weaken-env : Γ ⇒ʳ Δ -> ⟦ Θ ⟧ᶜ Γ -> ⟦ Θ ⟧ᶜ Δ
weaken-env {Θ = ∅}     ρ tt      = tt
weaken-env {Θ = Θ , A} ρ (η , v) = weaken-env {Θ = Θ} ρ η , weaken-value {A = A} ρ v
```

Interpretation of variables and terms
```
⟦_⟧ⱽ : Γ ∋ A → ⟦ Γ ⟧ᶜ Δ → ⟦ A ⟧ᵀ Δ
⟦ zero ⟧ⱽ  (_ , v) = v
⟦ suc x ⟧ⱽ (η , _) = ⟦ x ⟧ⱽ η

⟦_⟧ : Γ ⊢ A -> ⟦ Γ ⟧ᶜ Δ -> ⟦ A ⟧ᵀ Δ
⟦_⟧ (` x) η = ⟦ x ⟧ⱽ η
⟦_⟧ (ƛ N) η = λ ρ v → ⟦ N ⟧ (weaken-env ρ η , v)
⟦_⟧ (L · M) η = ⟦ L ⟧ η id (⟦ M ⟧ η)
```

Evaluator for closed terms
```
eval : ∅ ⊢ A -> ⟦ A ⟧ᵀ ∅
eval M = ⟦ M ⟧ tt
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

Normalisation by evaluation
```
norm : ∅ ⊢ A -> ∅ ⊢nf A
norm t = reify (eval t)
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

_ : norm one ≡ one-nf
_ = refl

_ : norm four ≡ four-nf
_ = refl
```

Now need to add the proof that nbe is sound, complete, and stable.
