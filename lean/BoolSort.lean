-- Like 'AutoDecreasing.lean' but just using a boolean for the 'Sort'
-- instead of anything fancier.
inductive sort where
  | V
  | T

inductive SortRel : sort → sort → Type where
| vt  : SortRel .V .T
| rfl : SortRel q q

infix:50 " ⊑ " => SortRel

def qT : q ⊑ .T := match q with
  | .V => .vt
  | .T => .rfl

inductive Ty where
  | o
  | fn : Ty → Ty → Ty

infix:50 " ⇒ " => Ty.fn

inductive Ctx where
  | ε
  | cons : Ctx → Ty → Ctx

infix:50 " ▷ " => Ctx.cons

inductive Tm : sort → Ctx → Ty → Type where
  | vz  : Tm .V (Γ ▷ A) A
  | vs  : Tm .V Γ B → Tm .V (Γ ▷ A) B
  | var : Tm .V Γ A → Tm .T Γ A
  | app : Tm .T Γ (A ⇒ B) → Tm .T Γ A → Tm .T Γ B
  | lam : Tm .T (Γ ▷ A) B → Tm .T Γ (A ⇒ B)

inductive Tms (q : sort) (Δ : Ctx) : Ctx → Type where
  | ε    : Tms q Δ Ctx.ε
  | cons : Tms q Δ Γ → Tm q Δ A → Tms q Δ (Γ ▷ A)

infix:50 " -, " => Tms.cons

def lub : sort → sort → sort
  | .V, q => q
  | .T, _ => .T

infix:50 " ⊔ " => lub

def lift : q ⊑ r → Tm q Γ A → Tm r Γ A
  | .vt  => .var
  | .rfl => id

def zero : Tm q (Γ ▷ A) A := match q with
  | .V => .vz
  | .T => .var .vz

@[reducible]
def sortSize : sort → Nat
  | .V => 0
  | .T => 1

mutual
  def suc : ∀ q, Tm q Γ B → Tm q (Γ ▷ A) B
    | .V, i => .vs i
    | .T, t => subst _ t (sucs .V (identity .V Γ) _)
  termination_by q _ => (sortSize q, 0, 0)

  def sucs : ∀q, Tms q Δ Γ → ∀ A, Tms q (Δ ▷ A) Γ
    | q, .ε    , A => .ε
    | q, δ -, x, A => sucs q δ A -, suc q x
  termination_by q δ => (sortSize q, 0, sizeOf δ)

  -- 'identity : ∀ Γ, Tms V Γ Γ' with 'termination_by Γ => (0, sizeOf Γ, 0)'
  -- also works, but then we would need to also define lifting for lists of
  -- terms to build single-substitutions.
  def identity : ∀ q Γ, Tms q Γ Γ
    | q, .ε    => .ε
    | q, Γ ▷ A => sucs q (identity q Γ) A -, zero
  termination_by q Γ => (sortSize q, sizeOf Γ, 0)

  def subst : ∀ r, Tm q Γ A → Tms r Δ Γ
            → Tm (q ⊔ r) Δ A
    | _, .vz     , δ -, u => u
    | _, .vs  i  , δ -, u => subst _ i δ
    | _, .var i  , δ      => lift qT (subst _ i δ)
    | _, .lam t  , δ      => .lam (subst _ t (sucs _ δ _ -, zero))
    | _, .app t u, δ      => .app (subst _ t δ) (subst _ u δ)
  termination_by r x _ => (sortSize r, sizeOf x, 0)
end
