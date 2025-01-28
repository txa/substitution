-- Given the termination proof has to be manual anyway, we might as well just
-- use a boolean for the sort (plus a function that calculates the size for
-- termination) but I wanted to try a 'Nat'-based 'sort' to give Lean a chance
-- at infering lexicographic termination order.
--
-- It might also worth be trying just leaving 'sort' as 'Nat' and use the fact
-- that there exists no 'Tm (.succ (.succ n)) Γ A' as proof it is < 2
structure sort where
  n   : Nat
  prf : n < 2

@[reducible]
def V : sort := sort.mk 0 (Nat.zero_lt_succ _)
@[reducible]
def T : sort := sort.mk 1 (Nat.lt_succ_self _)

inductive SortRel : sort → sort → Type where
| vt  : SortRel V T
| rfl : SortRel q q

infix:50 " ⊑ " => SortRel

def qT : q ⊑ T := match q with
  | .mk 0 _ => .vt
  | .mk 1 _ => .rfl

inductive Ty where
  | o
  | fn : Ty → Ty → Ty

infix:50 " ⇒ " => Ty.fn

inductive Ctx where
  | ε
  | cons : Ctx → Ty → Ctx

infix:50 " ▷ " => Ctx.cons

inductive Tm : sort → Ctx → Ty → Type where
  | vz  : Tm V (Γ ▷ A) A
  | vs  : Tm V Γ B → Tm V (Γ ▷ A) B
  | var : Tm V Γ A → Tm T Γ A
  | app : Tm T Γ (A ⇒ B) → Tm T Γ A → Tm T Γ B
  | lam : Tm T (Γ ▷ A) B → Tm T Γ (A ⇒ B)

inductive Tms (q : sort) (Δ : Ctx) : Ctx → Type where
  | ε    : Tms q Δ Ctx.ε
  | cons : Tms q Δ Γ → Tm q Δ A → Tms q Δ (Γ ▷ A)

infix:50 " -, " => Tms.cons

def lub : sort → sort → sort
  | .mk 0 _, q => q
  | .mk 1 _, _ => T

infix:50 " ⊔ " => lub

def lift : q ⊑ r → Tm q Γ A → Tm r Γ A
  | .vt  => .var
  | .rfl => id

def zero : Tm q (Γ ▷ A) A := match q with
  | .mk 0 _ => .vz
  | .mk 1 _ => .var .vz

mutual
  def suc : ∀ q, Tm q Γ B → Tm q (Γ ▷ A) B
    | .mk 0 _, i => .vs i
    | .mk 1 _, t => subst _ _ t (sucs V (identity V Γ) _)
  termination_by q _ => (q.n, 0, 0)

  def sucs : ∀q, Tms q Δ Γ → ∀ A, Tms q (Δ ▷ A) Γ
    | q, .ε    , A => .ε
    | q, δ -, x, A => sucs q δ A -, suc q x
  termination_by q δ => (q.n, 0, sizeOf δ)

  def identity : ∀ q Γ, Tms q Γ Γ
    | q, .ε    => .ε
    | q, Γ ▷ A => sucs q (identity q Γ) _ -, zero
  termination_by q Γ => (q.n, sizeOf Γ, 0)

  def subst : ∀ q r, Tm q Γ A → Tms r Δ Γ
            → Tm (q ⊔ r) Δ A
    | .mk 0 _, _, .vz     , δ -, u => u
    | .mk 0 _, _, .vs  i  , δ -, u => subst _ _ i δ
    | .mk 1 _, _, .var i  , δ      => lift qT (subst _ _ i δ)
    | .mk 1 _, _, .lam t  , δ      => .lam (subst _ _ t (sucs _ δ _ -, zero))
    | .mk 1 _, _, .app t u, δ      => .app (subst _ _ t δ) (subst _ _ u δ)
  termination_by q r x _  => (r.n, sizeOf x, 0)
end
