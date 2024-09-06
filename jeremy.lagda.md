Traditional rewriting and substitution
Based on Jeremy Siek's development
  github.com/jsiek/abstract-binding-trees/src/rewriting/AbstractBindingTrees.agda

```
{-# OPTIONS --rewriting #-}
open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Nat using (ℕ; zero; suc; _+_; _⊔_; _∸_; _≟_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; suc-injective)
open import Data.Product using (_×_; proj₁; proj₂; ∃-syntax; Σ-syntax)
  renaming (_,_ to infixl 5 _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit.Polymorphic using (⊤; tt)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; cong-app; subst)
open Eq.≡-Reasoning
open import Relation.Nullary using (¬_; Dec; yes; no)

module jeremy where

variable
  X Y : Set
  f g : X → Y

postulate
  extensionality : (∀ (x : X) → f x ≡ g x) → f ≡ g
```

Operator precedence
```
infix  3 _⊢_
infix  3 _∋_
infix  3 _⊨ʳ_  _⊨_
infixl 5 _•ʳ_  _•_
infixl 5 _⨾ʳ_  _⨾_
infixl 5 _,_
infix  6 _⤊ʳ  _⤊
infix  6 _^ʳ  _^
infixr 6 _⇒_
infix  6 ƛ_
infixl 7 _·_
infix  8 `_
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

Renaming
```
data _⊨ʳ_ : Con → Con → Set where
  ∅ : Δ ⊨ʳ ∅
  _,_ : Δ ⊨ʳ Γ → Δ ∋ A → Δ ⊨ʳ Γ , A

variable
  ρ ξ : Δ ⊨ʳ Γ
```

Shift and extend for renaming
```
_⤊ʳ : Δ ⊨ʳ Γ → Δ , A ⊨ʳ Γ
∅ ⤊ʳ = ∅
(ρ , x) ⤊ʳ = ρ ⤊ʳ , suc x

_^ʳ : Δ ⊨ʳ Γ → Δ , A ⊨ʳ Γ , A
_^ʳ ρ = ρ ⤊ʳ , zero
```

Instantiate a renaming
```
lookupʳ : Γ ∋ A → Δ ⊨ʳ Γ → Δ ∋ A
lookupʳ zero (ρ , y)  =  y
lookupʳ (suc x) (ρ , y)  =  lookupʳ x ρ

_[_]ʳ : Γ ⊢ A → Δ ⊨ʳ Γ → Δ ⊢ A
(` x) [ ρ ]ʳ = ` lookupʳ x ρ
(ƛ N) [ ρ ]ʳ = ƛ (N [ ρ ^ʳ ]ʳ)
(L · M) [ ρ ]ʳ = (L [ ρ ]ʳ) · (M [ ρ ]ʳ)
```

Identity and composition for renaming
```
idʳ : Γ ⊨ʳ Γ
idʳ {∅}  =  ∅
idʳ {Γ , A}  =  idʳ {Γ} ^ʳ

_⨾ʳ_ : Θ ⊨ʳ Γ → Δ ⊨ʳ Θ → Δ ⊨ʳ Γ
∅ ⨾ʳ ξ = ∅
(ρ , x) ⨾ʳ ξ = (ρ ⨾ʳ ξ) , lookupʳ x ξ
```

Substitution
```
data _⊨_ : Con → Con → Set where
  ∅ : Δ ⊨ ∅
  _,_ : Δ ⊨ Γ → Δ ⊢ A → Δ ⊨ Γ , A

variable
  σ τ : Γ ⊨ Δ
```

Shift and extend for substitution
```
_⤊ : Δ ⊨ Γ → Δ , A ⊨ Γ
∅ ⤊ = ∅
(σ , M) ⤊ = σ ⤊ , M [ idʳ ⤊ʳ ]ʳ

_^ : Δ ⊨ Γ → Δ , A ⊨ Γ , A
_^ σ = σ ⤊ , ` zero
```

Instantiate a substitution
```
lookup : Γ ∋ A → Δ ⊨ Γ → Δ ⊢ A
lookup zero (σ , P)  =  P
lookup (suc x) (σ , P) = lookup x σ

_[_] : Γ ⊢ A → Δ ⊨ Γ → Δ ⊢ A
(` x) [ σ ] = lookup x σ
(ƛ N) [ σ ] = ƛ (N [ σ ^ ])
(L · M) [ σ ] = (L [ σ ]) · (M [ σ ])
```

Identity and composition for renaming
```
id : Γ ⊨ Γ
id {∅}  =  ∅
id {Γ , A}  =  id {Γ} ^

_⨾_ : Θ ⊨ Γ → Δ ⊨ Θ → Δ ⊨ Γ
∅ ⨾ τ = ∅
(σ , M) ⨾ τ = (σ ⨾ τ) , (M [ τ ])
```

Convert a renaming to a substitution
```
lift : Δ ⊨ʳ Γ → Δ ⊨ Γ
lift ∅ = ∅
lift (ρ , x) = lift ρ , ` x
```


  ext-ren : ∀{ρ} → (` 0) • ⟰ (ren ρ) ≡ ren (extr ρ)
  ext-ren {ρ} = extensionality aux
      where
      aux : ∀{ρ} → ∀ x → exts (ren ρ) x ≡ ren (extr ρ) x
      aux {ρ} zero = refl
      aux {ρ} (suc x) = refl
  {-# REWRITE ext-ren #-}

  rename-ren : ∀{ρ M} → rename ρ M ≡ sub (ren ρ) M
  rename-ren-arg : ∀{ρ b}{arg : Arg b} → rename-arg ρ arg ≡ sub-arg (ren ρ) arg
  rename-ren-args : ∀{ρ bs}{args : Args bs}
     → rename-args ρ args ≡ sub-args (ren ρ) args
  rename-ren {ρ} {` x} = refl
  rename-ren {ρ} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) rename-ren-args
  rename-ren-arg {ρ} {.■} {ast M} = cong ast rename-ren
  rename-ren-arg {ρ} {.(ν _)} {bind arg} =
      cong bind rename-ren-arg
  rename-ren-args {ρ} {.[]} {nil} = refl
  rename-ren-args {ρ} {.(_ ∷ _)} {cons arg args} =
      cong₂ cons rename-ren-arg rename-ren-args
  {-# REWRITE rename-ren #-}

  ext-ren-sub : ∀ {ρ}{τ} → exts (ren ρ) ⨟ exts τ ≡ exts (ren ρ ⨟ τ)
  ext-ren-sub {ρ}{τ} = extensionality (aux{ρ}{τ})
      where
      aux : ∀{ρ}{τ} → ∀ x → (exts (ren ρ) ⨟ exts τ) x ≡ exts (ren ρ ⨟ τ) x
      aux {ρ} {τ} zero = refl
      aux {ρ} {τ} (suc x) = refl
  {-# REWRITE ext-ren-sub #-}

  ren-sub : ∀ {τ ρ M} → sub τ (sub (ren ρ) M) ≡ sub (ren ρ ⨟ τ) M
  ren-sub-arg : ∀ {τ ρ b}{arg : Arg b}
     → sub-arg τ (sub-arg (ren ρ) arg) ≡ sub-arg (ren ρ ⨟ τ) arg
  ren-sub-args : ∀ {τ ρ bs}{args : Args bs}
     → sub-args τ (sub-args (ren ρ) args) ≡ sub-args (ren ρ ⨟ τ) args
  ren-sub {τ} {ρ} {` x} = refl
  ren-sub {τ} {ρ} {op ⦅ args ⦆} = cong ((λ X → op ⦅ X ⦆)) ren-sub-args
  ren-sub-arg {τ} {ρ} {.■} {ast M} = cong ast (ren-sub{τ}{ρ}{M})
  ren-sub-arg {τ} {ρ} {.(ν _)} {bind arg} = cong bind (ren-sub-arg{exts τ}{extr ρ})
  ren-sub-args {τ} {ρ} {.[]} {nil} = refl
  ren-sub-args {τ} {ρ} {.(_ ∷ _)} {cons arg args} =
     cong₂ cons ren-sub-arg ren-sub-args
  {-# REWRITE ren-sub #-}

  sub-ren : ∀{ρ σ M} → sub (ren ρ) (sub σ M) ≡ sub (σ ⨟ ren ρ) M
  sub-ren-arg : ∀{ρ σ b}{arg : Arg b} → sub-arg (ren ρ) (sub-arg σ arg) ≡ sub-arg (σ ⨟ ren ρ) arg
  sub-ren-args : ∀{ρ σ bs}{args : Args bs} → sub-args (ren ρ) (sub-args σ args) ≡ sub-args (σ ⨟ ren ρ) args
  sub-ren {ρ} {σ} {` x} = refl
  sub-ren {ρ} {σ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-ren-args
  sub-ren-arg {ρ} {σ} {.■} {ast M} = cong ast (sub-ren{ρ}{σ}{M})
  sub-ren-arg {ρ} {σ} {.(ν _)} {bind arg} = cong bind sub-ren-arg
  sub-ren-args {ρ} {σ} {.[]} {nil} = refl
  sub-ren-args {ρ} {σ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-ren-arg sub-ren-args
  {-# REWRITE sub-ren #-}

  sub-sub : ∀{σ τ M} → sub τ (sub σ M) ≡ sub (σ ⨟ τ) M
  sub-sub-arg : ∀{σ τ b}{arg : Arg b} → sub-arg τ (sub-arg σ arg) ≡ sub-arg (σ ⨟ τ) arg
  sub-sub-args : ∀{σ τ bs}{args : Args bs} → sub-args τ (sub-args σ args) ≡ sub-args (σ ⨟ τ) args
  sub-sub {σ} {τ} {` x} = refl
  sub-sub {σ} {τ} {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-sub-args
  sub-sub-arg {σ} {τ} {.■} {ast M} = cong ast (sub-sub{σ}{τ}{M})
  sub-sub-arg {σ} {τ} {.(ν _)} {bind arg} = cong bind sub-sub-arg
  sub-sub-args {σ} {τ} {.[]} {nil} = refl
  sub-sub-args {σ} {τ} {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-sub-arg sub-sub-args
  {-# REWRITE sub-sub #-}

  shift-seq : ∀{σ} → ⟰ σ ≡ σ ⨟ ren suc
  shift-seq {σ} = refl

  idʳ : Rename
  idʳ x = x

  extr-id : (0 •ʳ ⟰ʳ idʳ) ≡ idʳ {- extr idʳ ≡ idʳ -}
  extr-id = extensionality aux
    where
    aux : ∀ x → extr idʳ x ≡ idʳ x
    aux zero = refl
    aux (suc x) = refl
  {-# REWRITE extr-id #-}

  id : Subst
  id x = ` x

  ext-id : exts id ≡ id
  ext-id = refl

  sub-id : ∀ {M} → sub id M ≡ M
  sub-arg-id : ∀ {b}{arg : Arg b} → sub-arg id arg ≡ arg
  sub-args-id : ∀ {bs}{args : Args bs} → sub-args id args ≡ args
  sub-id {` x} = refl
  sub-id {op ⦅ args ⦆} = cong (λ X → op ⦅ X ⦆) sub-args-id
  sub-arg-id {.■} {ast M} = cong ast sub-id
  sub-arg-id {.(ν _)} {bind arg} = cong bind sub-arg-id
  sub-args-id {.[]} {nil} = refl
  sub-args-id {.(_ ∷ _)} {cons arg args} = cong₂ cons sub-arg-id sub-args-id
  {-# REWRITE sub-id #-}

{----------------------------------------------------------------------------
 Public
----------------------------------------------------------------------------}

abstract {- experimenting with making ren abstract -Jeremy -}
  ren : Rename → Subst
  ren = Private.ren

  ren-def : ∀ ρ x → ren ρ x ≡ ` ρ x
  ren-def ρ x = refl

↑ : Subst
↑ = ren suc

up-def : ↑ ≡ ren suc
up-def = refl

abstract
  infixr 5 _⨟_
  _⨟_ : Subst → Subst → Subst
  σ ⨟ τ = Private._⨟_ σ τ

  id : Subst
  id = Private.id
    
ext : Subst → Subst
ext σ = ` 0 • (σ ⨟ ↑)

abstract
  -- Phil: you're using semicolon, so this should be postfix
  ⟪_⟫ : Subst → ABT → ABT
  ⟪ σ ⟫ M = Private.sub σ M

  -- Phil: try switching + to *
  ⟪_⟫₊ : Subst → {bs : List Sig} → Args bs → Args bs
  ⟪ σ ⟫₊ args = Private.sub-args σ args

  ⟪_⟫ₐ : Subst → {b : Sig} → Arg b → Arg b
  ⟪ σ ⟫ₐ arg = Private.sub-arg σ arg

  id-var : ∀{x} → id x ≡ ` x
  id-var {x} = refl
  {-# REWRITE id-var #-}
  
  sub-var : ∀ σ x → ⟪ σ ⟫ (` x) ≡ σ x
  sub-var σ x = refl
  {- REWRITE sub-var -}
  
  sub-op : ∀{σ : Subst}{op : Op}{args : Args (sig op)}
     → ⟪ σ ⟫ (op ⦅ args ⦆) ≡ op ⦅ ⟪ σ ⟫₊ args ⦆
  sub-op {σ}{op}{args} = refl
  {-# REWRITE sub-op #-}

  sub-arg-ast : ∀{σ M} → ⟪ σ ⟫ₐ (ast M) ≡ ast (⟪ σ ⟫ M)
  sub-arg-ast {σ}{M} = refl
  {-# REWRITE sub-arg-ast #-}
  
  sub-arg-bind : ∀{σ b}{arg : Arg b}
     → ⟪ σ ⟫ₐ (bind arg) ≡ bind (⟪ ext σ ⟫ₐ arg)
  sub-arg-bind {σ}{b}{arg} = refl
  {-# REWRITE sub-arg-bind #-}

  sub-args-nil : ∀{σ} → ⟪ σ ⟫₊ nil ≡ nil
  sub-args-nil {σ} = refl
  {-# REWRITE sub-args-nil #-}

  sub-args-cons : ∀{σ}{b}{bs}{arg : Arg b}{args : Args bs}
     → ⟪ σ ⟫₊ (cons arg args) ≡ cons (⟪ σ ⟫ₐ arg) (⟪ σ ⟫₊ args)
  sub-args-cons {σ}{arg}{args} = refl
  {-# REWRITE sub-args-cons #-}

  sub-head : ∀ σ M → ⟪ M • σ ⟫ (` 0) ≡ M
  sub-head σ M = refl
  {-# REWRITE sub-head #-}

  sub-tail : ∀ σ M → ↑ ⨟ M • σ ≡ σ
  sub-tail σ M = extensionality (aux{σ}{M})
      where
      aux : ∀{σ M} → ∀ x → (↑ ⨟ M • σ) x ≡ σ x
      aux {σ} {M} zero = refl
      aux {σ} {M} (suc x) = refl
  {-# REWRITE sub-tail #-}

  sub-id : ∀ M → ⟪ id ⟫ M ≡ M
  sub-id M = Private.sub-id
  {-# REWRITE sub-id #-}  

  sub-eta : ∀ σ → (⟪ σ ⟫ (` 0)) • (↑ ⨟ σ) ≡ σ
  sub-eta σ = extensionality aux
    where
    aux : ∀ {σ} x → ((⟪ σ ⟫ (` 0)) • (↑ ⨟ σ)) x ≡ σ x
    aux {σ} zero = refl
    aux {σ} (suc x) = refl
  {-# REWRITE sub-eta #-}  

  sub-id-right : ∀ (σ : Subst) → σ ⨟ id ≡ σ 
  sub-id-right σ = refl
  {-# REWRITE sub-id-right #-}  

  sub-id-left : (σ : Subst) → id ⨟ σ ≡ σ
  sub-id-left σ = refl
  {-# REWRITE sub-id-left #-}

  sub-assoc : ∀ σ τ θ → (σ ⨟ τ) ⨟ θ ≡ σ ⨟ τ ⨟ θ
  sub-assoc σ τ θ = refl
  {-# REWRITE sub-assoc #-}
  
  cons-seq : ∀ σ τ M → (M • σ) ⨟ τ ≡ ⟪ τ ⟫ M • (σ ⨟ τ)
  cons-seq σ τ M = refl
  {-# REWRITE cons-seq #-}  

  compose-sub : ∀ σ τ M → ⟪ τ ⟫ (⟪ σ ⟫ M) ≡ ⟪ σ ⨟ τ ⟫ M
  compose-sub σ τ M = refl
  {-# REWRITE compose-sub #-}  

  cons-zero-up : ` 0 • ↑ ≡ id
  cons-zero-up = refl
  {-# REWRITE cons-zero-up #-}  

  seq-def : ∀ σ τ x → (σ ⨟ τ) x ≡ ⟪ τ ⟫ (σ x)
  seq-def σ τ x = refl

  up-var : ∀ x → ↑ x ≡ ` suc x
  up-var x = refl

  ext-ren-extr : ∀ ρ → (` 0) • (ren ρ ⨟ ↑) ≡ ren (extr ρ)
  ext-ren-extr ρ = refl
  -- {-# REWRITE ext-ren-extr #-}
  
  ren-extr-def : ∀ ρ → ren (extr ρ) ≡ ` 0 • (ren ρ ⨟ ↑)
  ren-extr-def ρ = refl
  {-# REWRITE ren-extr-def #-}

  ren-extr-zero : ∀ ρ → ren (extr ρ) 0 ≡ ` 0
  ren-extr-zero ρ = refl
  {- REWRITE ren-extr-zero -}

  ren-extr-suc : ∀ ρ x → ren (extr ρ) (suc x) ≡ ` suc (ρ x)
  ren-extr-suc ρ x = refl
  {- REWRITE ren-extr-suc -}

  seq-up-ren-suc : ∀ σ x → (σ ⨟ ↑) x ≡ Private.sub (Private.ren suc) (σ x)  
  seq-up-ren-suc σ x = refl

  ren-seq-up : ∀ ρ x → (ren ρ ⨟ ↑) x ≡ ` suc (ρ x)
  ren-seq-up ρ x = refl
  {- REWRITE ren-seq-up -}

_[_] : ABT → ABT → ABT
N [ M ] =  ⟪ M • id ⟫ N

_〔_〕 : ABT → ABT → ABT
_〔_〕 N M = ⟪ ext (M • id) ⟫ N

substitution : ∀{M N L} → M [ N ] [ L ] ≡ M 〔 L 〕 [ N [ L ] ]
substitution {M}{N}{L} = refl

exts-sub-cons : ∀ {σ N V} → (⟪ ext σ ⟫ N) [ V ] ≡ ⟪ V • σ ⟫ N
exts-sub-cons {σ}{N}{V} = refl

{----------------------------------------------------------------------------
 Free variables
----------------------------------------------------------------------------}

FV? : ABT → Var → Bool
FV-arg? : ∀{b} → Arg b → Var → Bool
FV-args? : ∀{bs} → Args bs → Var → Bool
FV? (` x) y
    with x ≟ y
... | yes xy = true
... | no xy = false
FV? (op ⦅ args ⦆) y = FV-args? args y
FV-arg? (ast M) y = FV? M y
FV-arg? (bind arg) y = FV-arg? arg (suc y)
FV-args? nil y = false
FV-args? (cons arg args) y = FV-arg? arg y ∨ FV-args? args y

{- Predicate Version -}

FV : ABT → Var → Set
FV-arg : ∀{b} → Arg b → Var → Set
FV-args : ∀{bs} → Args bs → Var → Set
FV (` x) y = x ≡ y
FV (op ⦅ args ⦆) y = FV-args args y
FV-arg (ast M) y = FV M y
FV-arg (bind arg) y = FV-arg arg (suc y)
FV-args nil y = ⊥
FV-args (cons arg args) y = FV-arg arg y ⊎ FV-args args y

FV-rename-fwd : ∀ (ρ : Rename) M y → FV M y
   → FV (rename ρ M) (ρ y)
FV-rename-fwd ρ (` x) y refl = refl
FV-rename-fwd ρ (op ⦅ args ⦆) y fvMy = fvr-args ρ (sig op) args y fvMy
  where
  fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
      → FV-arg arg y → FV-arg (rename-arg ρ arg) (ρ y)
  fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
      → FV-args args y → FV-args (rename-args ρ args) (ρ y)
  fvr-arg ρ ■ (ast M) y fvarg = FV-rename-fwd ρ M y fvarg
  fvr-arg ρ (ν b) (bind arg) y fvarg =
      fvr-arg (extr ρ) b arg (suc y) fvarg
  fvr-args ρ [] nil y ()
  fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fvargy) =
      inj₁ (fvr-arg ρ b arg y fvargy)
  fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fvargsy) =
      inj₂ (fvr-args ρ bs args y fvargsy)

FV-rename : ∀ (ρ : Rename) M y → FV (rename ρ M) y
   → Σ[ x ∈ Var ] ρ x ≡ y × FV M x
FV-rename ρ (` x) y refl = ⟨ x , ⟨ refl , refl ⟩ ⟩
FV-rename ρ (op ⦅ args ⦆) y fv = fvr-args ρ (sig op) args y fv
  where
  fvr-arg : ∀ (ρ : Rename) b (arg : Arg b) y
     → FV-arg (rename-arg ρ arg) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-arg arg x
  fvr-args : ∀ (ρ : Rename) bs (args : Args bs) y
     → FV-args (rename-args ρ args) y → Σ[ x ∈ Var ] (ρ) x ≡ y × FV-args args x
  fvr-arg ρ b (ast M) y fv = FV-rename ρ M y fv 
  fvr-arg ρ (ν b) (bind arg) y fv 
      with fvr-arg (extr ρ) b arg (suc y) fv
  ... | ⟨ 0 , eq ⟩  
      with eq
  ... | ()
  fvr-arg ρ (ν b) (bind arg) y fv 
      | ⟨ suc x , ⟨ eq , sx∈arg ⟩ ⟩ =
        ⟨ x , ⟨ suc-injective eq , sx∈arg ⟩ ⟩
  fvr-args ρ [] nil y ()
  fvr-args ρ (b ∷ bs) (cons arg args) y (inj₁ fv)
      with fvr-arg ρ b arg y fv
  ... | ⟨ x , ⟨ ρx , x∈arg ⟩ ⟩ = 
        ⟨ x , ⟨ ρx , (inj₁ x∈arg) ⟩ ⟩
  fvr-args ρ (b ∷ bs) (cons arg args) y (inj₂ fv)
      with fvr-args ρ bs args y fv
  ... | ⟨ x , ⟨ ρx , x∈args ⟩ ⟩ = 
        ⟨ x , ⟨ ρx , (inj₂ x∈args) ⟩ ⟩

rename-FV-⊥ : ∀ y (ρ : Rename) M → (∀ x → (ρ) x ≢ y) → FV (rename ρ M) y → ⊥
rename-FV-⊥ y ρ M ρx≢y fvρM 
    with FV-rename ρ M y fvρM
... | ⟨ x , ⟨ ρxy , x∈M ⟩ ⟩ = ⊥-elim (ρx≢y x ρxy)

FV-↑1-0 : ∀ M → FV (rename suc M) 0 → ⊥
FV-↑1-0 M = rename-FV-⊥ 0 suc M (λ { x () })

abstract
  FV-ren : ∀ (ρ : Rename) M y → FV (⟪ ren ρ ⟫ M) y
     → ∃[ x ] ρ x ≡ y × FV M x
  FV-ren ρ M y y∈FVρM = FV-rename ρ M y y∈FVρM

  FV-ren-fwd : ∀ (ρ : Rename) M y → FV M y
     → FV (⟪ ren ρ ⟫ M) (ρ y)
  FV-ren-fwd ρ M y y∈M = FV-rename-fwd ρ M y y∈M

  FV-suc-0 : ∀ M → FV (⟪ ren suc ⟫ M) 0 → ⊥
  FV-suc-0 M = rename-FV-⊥ 0 suc M (λ { x () })



