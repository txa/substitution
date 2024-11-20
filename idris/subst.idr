%default total

ack : Nat -> Nat -> Nat
ack Z     n     = S n
ack (S m) Z     = ack m 1
ack (S m) (S n) = ack m (ack (S m) n)

infix 5 -.
infix 5 ==>
infix 5 ~.
infix 5 ^

data Sort : Type
data IsV  : Sort -> Type

data Sort where
  V : Sort
  T : forall q. IsV q -> Sort

data IsV where
  VV : IsV V

lub : Sort -> Sort -> Sort
lub V q      = q
lub (T VV) q = T VV 

data Leq : Sort -> Sort -> Type where
  VT  : Leq V (T VV)
  Rfl : Leq q q

qT : {q : Sort} -> Leq q (T VV)
qT {q = V}    = VT
qT {q = T VV} = Rfl

data Ctx : Type
data Ty  : Type

data Ctx where
  Nil  : Ctx
  (-.) : Ctx -> Ty -> Ctx

data Ty where
  O     : Ty
  (==>) : Ty -> Ty -> Ty

data Tm : Sort -> Ctx -> Ty -> Type where
  VZ  : Tm V (g -. a) a
  VS  : Tm V g b -> Tm V (g -. a) b
  Var : Tm V g a -> Tm (T VV) g a
  Lam : {a : Ty} -> Tm (T VV) (g -. a) b -> Tm (T VV) g (a ==> b)
  App : Tm (T VV) g (a ==> b) -> Tm (T VV) g a -> Tm (T VV) g b

data Tms : Sort -> Ctx -> Ctx -> Type where
  Eps  : Tms q d Nil
  (~.) : Tms q d g -> Tm q d a -> Tms q d (g -. a)

-- There is a bit of fiddly stuff with quantities to make the 'Sort' recoverable
-- from a 'Tm'. Alternatively, I think we could just match on the term in 'suc'
-- but I wanted to stay as close to the Agda definitions as possible.
sort : Tm q g a -> Sort
sort VZ        = V
sort (VS _)    = V
sort (Var _)   = T VV
sort (Lam _)   = T VV
sort (App _ _) = T VV

sortEq : {x : Tm q g a} -> q = sort x
sortEq {x = VZ}      = Refl
sortEq {x = VS _}    = Refl
sortEq {x = Var _}   = Refl
sortEq {x = Lam _}   = Refl
sortEq {x = App _ _} = Refl

lift : Leq q r -> Tm q g a -> Tm r g a
lift VT  t = Var t
lift Rfl x = x

zero : {q : Sort} -> Tm q (g -. a) a
zero {q = V}    = VZ
zero {q = T VV} = Var VZ

subst : {r : Sort} -> {d : Ctx} -> Tm q g a -> Tms r d g -> Tm (lub q r) d a
(^)   : {q : Sort} -> {d : Ctx} -> Tms q d g -> (a : Ty) 
     -> Tms q (d -. a) (g -. a)
sucs  : {d : Ctx} -> Tms q d g -> (a : Ty) 
     -> Tms q (d -. a) g
-- Instead of matching
suc'  : {r : Sort} -> {g : Ctx} -> q = r -> Tm q g b -> (a : Ty) 
     -> Tm q (g -. a) b
suc   : {g : Ctx} -> Tm q g b -> (a : Ty) 
     -> Tm q (g -. a) b
id    : {q : Sort} -> {g : Ctx} -> Tms q g g

id {g = Nil}    = Eps
id {g = g -. a} = id ^ a

xs ^ a = sucs xs a ~. zero

sucs Eps       a = Eps
sucs (xs ~. x) a = sucs xs a ~. suc x a

suc' {r = V}    Refl i a = VS i
suc' {r = T VV} Refl t a = subst t (sucs (id {q = V}) a)

suc x a = suc' {r = sort x} sortEq x a

subst VZ        (ys ~. y) = y
subst (VS i)    (ys ~. y) = subst i ys
subst (Var i)   ys        = lift qT (subst i ys)
subst (Lam t)   ys        = Lam (subst t (ys ^ _))
subst (App t u) ys        = App (subst t ys) (subst u ys)


