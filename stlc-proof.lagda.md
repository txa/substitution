```
{-# OPTIONS --prop --rewriting #-}
module stlc-proof where

open import Relation.Binary.PropositionalEquality hiding ([_])
open  ≡-Reasoning public
{-# BUILTIN REWRITE _≡_ #-}

infix   3  _∋_
infix   3  _⊢_
infix   3  _⊢[_]_
infix   3  _⊨[_]_
infixl  4  _,_
infix   5  _∘_
infix   5  ƛ_
infixr  6  _⇒_
infixl  6  _·_
infix   7  `_
infix   8  _^_
infix   8  _↑_
infix   8  _[_]

data Ty : Set where
  o : Ty
  _⇒_ : Ty → Ty → Ty

variable
  A B C : Ty

data Con : Set where
  ∅ : Con
  _,_ : Con → Ty → Con

variable
  Γ Δ Θ : Con

data Sort : Set 
data IsV : Sort → Set
data Sort where
  V : Sort
  T>V : (s : Sort) → IsV s → Sort
data IsV where
  isV : IsV V

pattern T = T>V V isV

variable
  q r s    : Sort

data _⊢[_]_ : Con → Sort → Ty → Set

_∋_ : Con → Ty → Set
Γ ∋ A  =  Γ ⊢[ V ] A

_⊢_ : Con → Ty → Set
Γ ⊢ A  =  Γ ⊢[ T ] A

data _⊢[_]_ where 
  zero : Γ , A ∋ A
  suc  : Γ ∋ A → Γ , B ∋ A
  `_   : Γ ∋ A → Γ ⊢ A
  _·_  : Γ ⊢ A ⇒ B → Γ ⊢ A → Γ ⊢ B
  ƛ_   : Γ , A ⊢ B → Γ ⊢ A ⇒ B

variable
  i j k    : Γ ∋ A
  t u v    : Γ ⊢ A
  x y z : Γ ⊢[ q ] A




data _⊨[_]_ : Con → Sort → Con → Set where
  ∅   : Γ ⊨[ q ] ∅
  _,_ : Γ ⊨[ q ] Δ → Γ ⊢[ q ] A → Γ ⊨[ q ] Δ , A

_⊨_ : Con → Con → Set
Γ ⊨ Δ  =  Γ ⊨[ T ] Δ

variable
  xs ys zs : Γ ⊨[ q ] Δ
  is js ks : Γ ⊨[ V ] Δ
```

Order and lub

```
data _⊑_ : Sort → Sort → Set where
  rfl : s ⊑ s
  v⊑t : V ⊑ T

_⊔_ : Sort → Sort → Sort
V ⊔ r  =  r
T ⊔ r  =  T

⊑t : s ⊑ T
⊑t {V} = v⊑t
⊑t {T} = rfl

v⊑ : V ⊑ s
v⊑ {V} = rfl
v⊑ {T} = v⊑t

⊑q⊔ : q ⊑ (q ⊔ r)
⊑q⊔ {V} = v⊑
⊑q⊔ {T} = rfl

⊑⊔r : r ⊑ (q ⊔ r)
⊑⊔r {q = V} = rfl
⊑⊔r {q = T} = ⊑t


tm⊑ : q ⊑ s → Γ ⊢[ q ] A → Γ ⊢[ s ]  A
tm⊑ rfl x = x
tm⊑ v⊑t i = ` i

tm*⊑ : q ⊑ s → Γ ⊨[ q ] Δ → Γ ⊨[ s ] Δ
tm*⊑ q⊑s ∅ = ∅
tm*⊑ q⊑s (σ , x) = tm*⊑ q⊑s σ , tm⊑ q⊑s x

tm : Γ ⊢[ q ] A → Γ ⊢ A
tm = tm⊑ ⊑t

tm⊔ : Γ ⊢[ r ] A → Γ ⊢[ s ⊔ r ] A
tm⊔ = tm⊑ ⊑⊔r

tm*⊔ : Γ ⊨[ r ] Δ → Γ ⊨[ s ⊔ r ] Δ
tm*⊔ = tm*⊑ ⊑⊔r
```

Derivations

```
_↑_ : Γ ⊨[ q ] Δ → (A : Ty) → Γ , A ⊨[ q ] Δ -- depracated

suc* :  Γ ⊨[ q ] Δ → (A : Ty) → Γ , A ⊨[ q ] Δ

_^_ : Γ ⊨[ q ] Δ → (A : Ty) → Γ , A ⊨[ q ] Δ , A

_[_] : Γ ⊢[ q ] A → Δ ⊨[ r ] Γ → Δ ⊢[ q ⊔ r ] A
zero    [ xs , x ]  =  x
(suc i) [ xs , x ]  =  i [ xs ]
(` i)   [ xs ]       =  tm (i [ xs ])
(ƛ t)   [ xs ]       =  ƛ (t [ xs ^ _ ])
(t · u) [ xs ]       =  (t [ xs ]) · (u [ xs ])

id : Γ ⊨[ q ] Γ
id {Γ = ∅}          =  ∅
id {Γ = Γ , A}      =  id ^ A

--id : Γ ⊨[ V ] Γ
-- destroys termination



_∘_ : Γ ⊨[ q ] Θ → Δ ⊨[ r ] Γ → Δ ⊨[ q ⊔ r ] Θ
∅ ∘ τ = ∅
(σ , x) ∘ τ = (σ ∘ τ) , x [ τ ]

⊔⊔ : q ⊔ (r ⊔ s) ≡ (q ⊔ r) ⊔ s
⊔⊔ {V} = refl
⊔⊔ {T} = refl

⊔v : q ⊔ V ≡ q
⊔v {V} = refl
⊔v {T} = refl

-- q⊔q : q ⊔ q ≡ q
-- q⊔q {V} = refl
-- q⊔q {T} = refl

{-# REWRITE ⊔⊔ ⊔v  #-}

zeroq : Γ , A ⊢[ q ] A
zeroq {q = V}       =  zero
zeroq {q = T}       =  ` zero

tm⊑zeroq : {q⊑r : q ⊑ r} → zeroq {Γ = Γ}{A = A}  ≡ tm⊑ q⊑r zeroq
tm⊑zeroq {q⊑r = rfl} = refl
tm⊑zeroq {q⊑r = v⊑t} = refl

sucq : Γ ⊢[ q ] B  → Γ , A ⊢[ q ] B -- should also get A
sucq {q = V} i      =  suc i
sucq {q = T} t      =  t [ id {q = V} ↑ _ ]

suc* ∅ A = ∅
suc* (xs , x) A = suc* xs A , sucq x 

∅ ↑ A              =  ∅
(xs , x) ↑ A       =  xs ↑ A , sucq x

xs ^ A                 =  xs ↑ A , zeroq

tm* : Γ ⊨[ q ] Δ → Γ ⊨ Δ
tm* ∅ = ∅
tm* (xs , x) = (tm* xs) , (tm x)

```

The right identity law:
```
↑-nat[]v : {i : Γ  ⊢[ V ] B}{xs : Δ ⊨[ r ] Γ}
  → i [ xs ↑ A ] ≡ sucq (i [ xs ])
↑-nat[]v {i = zero} {xs , x} = refl
↑-nat[]v {i = suc j} {xs , _} = ↑-nat[]v {i = j}


[id] : x [ id {q = V} ] ≡ x
[id] {x = zero} = refl
[id] {x = suc i} = 
   i [ id ↑ _ ] 
   ≡⟨ ↑-nat[]v {i = i} ⟩
   suc (i [ id ])
   ≡⟨ cong suc ([id] {x = i}) ⟩      
   suc i ∎
[id] {x = ` i} = cong `_ ([id] {x = i})
[id] {x = t · u} = cong₂ _·_ ([id] {x = t}) ([id] {x = u})
[id] {x = ƛ t} = cong ƛ_ ([id] {x = t})

∘id : xs ∘ (id {q = V}) ≡ xs
∘id {xs = ∅} = refl
∘id {xs = xs , x} = cong₂ _,_ (∘id {xs = xs}) ([id] {x = x})

```

We use functoriality but prove it later.
```
[∘] : {x : Θ ⊢[ q ] A}{xs : Γ ⊨[ r ] Θ}{ys : Δ ⊨[ s ] Γ}
      → x [ xs ∘ ys ] ≡ x [ xs ] [ ys ]
```

The left identity law:
```
↑∘ : xs ↑ A  ∘ (ys , x) ≡ xs ∘ ys
id∘ : ∀ {r} {xs : Γ ⊨[ q ] Δ} → (id {q = r}) ∘ xs ≡ tm*⊔ {s = r} xs

zeroq[] : tm⊔ {s = q} x ≡ zeroq {q = q} [ xs , x ]
zeroq[] {q = V} = refl
zeroq[] {q = T} = refl

tm*rfl : {q⊑q : q ⊑ q} → tm*⊑ q⊑q xs ≡ xs
tm*rfl {xs = ∅} {q⊑q = rfl} = refl
tm*rfl {xs = xs , x} {q⊑q = rfl} = cong₂ _,_ (tm*rfl {xs = xs}) refl

sucq[] : {ys : Γ ⊨[ r ] Δ} → sucq {q = q} x [ ys , y ] ≡ x [ ys ]
sucq[] {q = V} = refl
sucq[] {q = T} {x = x} {y = y} {ys = ys} =
  sucq x [ ys , y ]
  ≡⟨⟩
  x [ id {q = V} ↑ _ ] [ ys , y ]
  ≡⟨ sym ([∘] {x = x}) ⟩
  x [ (id {q = V} ↑ _) ∘  (ys , y) ]
  ≡⟨ cong (λ ρ → x [ ρ ]) ↑∘  ⟩
  x [ (id {q = V}) ∘  ys  ]
  ≡⟨ cong (λ ρ → x [ ρ ]) id∘ ⟩
  x [ tm*⊔ {s = V} ys ]
  ≡⟨ cong (λ ρ → x [ ρ ]) tm*rfl ⟩
  x [ ys ]  ∎

↑∘ {xs = ∅} = refl
↑∘ {xs = xs , x} = cong₂ _,_ (↑∘ {xs = xs}) (sucq[] {x = x})

id∘ {xs = ∅} = refl
id∘ {r = r} {xs = xs , x} = cong₂ _,_ (
   id ↑ _ ∘ (xs , x)
     ≡⟨ ↑∘ {xs = id} ⟩
   id ∘ xs
     ≡⟨ id∘ {xs = xs} ⟩
   tm*⊔ {s = r} xs ∎) (sym (zeroq[] {q = r}))

```

Associativity
```


↑-nat∘ : xs ∘ (ys ↑ A) ≡ (xs ∘ ys) ↑ A
{-
   Δ ⊨[ r ] Γ --↑--> Δ,A ⊨[ r ] Γ 
        |                 |
       xs ∘ _             xs ∘ _
        |                 |
        V                 V
   Δ ⊨[ r ] Θ --↑->  Θ,A ⊨[ r ] Θ  
-}

↑-nat[] : {x : Γ  ⊢[ q ] B}{xs : Δ ⊨[ r ] Γ}
  → x [ xs ↑ A ] ≡ sucq (x [ xs ])
↑-nat[] {q = V}{x = i} = ↑-nat[]v {i = i}
↑-nat[] {q = T} {A = A} {x = x} {xs} = 
   x [ xs ↑ A ]
   ≡⟨ cong (λ ρ → x [ ρ ↑ A ]) (sym ∘id) ⟩
   x [ (xs ∘ id {q = V}) ↑ A ]     
   ≡⟨ cong (λ ρ → x [ ρ ]) (sym (↑-nat∘ {xs = xs})) ⟩
   x [ xs ∘ (id {q = V} ↑ A) ]   
   ≡⟨ [∘] {x = x} ⟩
   x [ xs ] [ id {q = V} ↑ A ] ∎


↑-nat∘ {xs = ∅} = refl
↑-nat∘ {xs = xs , x} = cong₂ _,_ (↑-nat∘ {xs = xs}) (↑-nat[] {x = x})

^∘ :  {xs : Γ ⊨[ r ] Θ}{τ : Δ ⊨[ s ] Γ}{A : Ty}
      → (xs ∘ τ) ^ A ≡ (xs ^ A) ∘ (τ ^ A)
^∘ {r = r}{s = s}{xs = xs}{τ = τ} {A = A} = 
    (xs ∘ τ) ^ A
    ≡⟨⟩
    (xs ∘ τ) ↑ A , zeroq {q = r ⊔ s}    
    ≡⟨ cong₂ _,_ (sym (↑-nat∘ {xs = xs})) refl ⟩
    xs ∘ (τ ↑ A) , zeroq {q = r ⊔ s}
    ≡⟨ cong₂ _,_ refl (tm⊑zeroq {q⊑r = ⊑⊔r {r = s}{q = r}}) ⟩        
    xs ∘ (τ ↑ A) , tm⊔ {s = r} (zeroq {q = s})
    ≡⟨ cong₂ _,_ (sym (↑∘ {xs = xs})) (zeroq[] {q = r} {x = zeroq {q = s}})  ⟩    
    xs ↑ A ∘ τ ^ A , zeroq {q = r} [ τ ^ A ]
    ≡⟨⟩           
    xs ^ A ∘ τ ^ A ∎

tm[] : {x : Θ ⊢[ q ] A}{xs : Γ ⊨[ r ] Θ}
  → tm (x [ xs ]) ≡ (tm x) [ xs ]
tm[] {q = V} = refl
tm[] {q = T} = refl

[∘] {x = zero} {ys , y} = refl
[∘] {x = suc i} {ys , y} = [∘] {x = i}
[∘] {x = ` x}{xs = xs}{ys = ys} = 
   tm (x [ xs ∘ ys ])
    ≡⟨ cong tm ([∘] {x = x}) ⟩
   tm (x [ xs ] [ ys ])
    ≡⟨ tm[] {x = x [ xs ]} ⟩        
   tm (x [ xs ]) [ ys ] ∎
[∘] {x = t · u} = cong₂ _·_ ([∘] {x = t}) ([∘] {x = u})
[∘] {x = ƛ t}{xs = xs}{ys = ys} = cong ƛ_ (
   t [ (xs ∘ ys) ^ _ ]
   ≡⟨ cong (λ zs → t [ zs ]) ^∘  ⟩
   t [ (xs ^ _) ∘ (ys ^ _)  ]
   ≡⟨ [∘] {x = t} ⟩           
   (t [ xs ^ _ ]) [ ys ^ _ ] ∎)

∘∘ : xs ∘ (ys ∘ zs) ≡ (xs ∘ ys) ∘ zs
∘∘ {xs = ∅} = refl
∘∘ {xs = xs , x} = cong₂ _,_ (∘∘ {xs = xs}) ([∘] {x = x})

```


