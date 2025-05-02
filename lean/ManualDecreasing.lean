-- Lean supports inferring lexicographic termination for individual definition,
-- but unfortunately this does not seem to work for 'mutual' blocks (which
-- appear to at minimum require manually specifying 'termination_by' metrics)
def ack : Nat → Nat → Nat
  | .zero  , n       => .succ n
  | .succ m, .zero   => ack m 1
  | .succ m, .succ n => ack m (ack (.succ m) n)

-- Given we are doing the termination proof manually here anyway, we might as
-- well just use a boolean for the sort (plus a function that calculates the
-- size for termination).
--
-- It might also worth be trying just leaving 'sort' as 'Nat' and use the fact
-- that there exists no 'Tm (.succ (.succ n)) Γ A' as proof it is < 2
structure sort where
  n   : Nat
  prf : n < 2

def V : sort := .mk 0 (Nat.zero_lt_succ _)
def T : sort := .mk 1 (Nat.lt_succ_self _)

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

-- I think Lean can derive these size functions with 'sizeOf' but defining them
-- manually seems to make the goal types a bit simpler
def ctxlen : Ctx → Nat
  | .ε    => 0
  | Γ ▷ _ => .succ (ctxlen Γ)

def tmlen : Tm q Γ A → Nat
  | .vz      => 0
  | .vs i    => .succ (tmlen i)
  | .var i   => .succ (tmlen i)
  | .app t u => .succ (tmlen t + tmlen u)
  | .lam t   => .succ (tmlen t)

def tmslen : Tms q Δ Γ → Nat
  | .ε     => 0
  | δ -, x => .succ (tmslen δ + tmlen x)

-- See AutoDecreasing.lean' for a version where Lean can infer all the
-- 'decreasing_by' proofs (it turns out we only need to annotate 'V' and 'T' as
-- @[reducible]!)
mutual
  def suc : ∀ q, Tm q Γ B → Tm q (Γ ▷ A) B
    | .mk 0 _, i => .vs i
    | .mk 1 _, t => subst _ t (sucs V (identity V Γ) _)
  termination_by q _ => (q.n, 0, 0)
  decreasing_by
  . exact (.left _ _ Nat.zero_lt_one)
  . exact (.left _ _ Nat.zero_lt_one)
  . exact (.left _ _ Nat.zero_lt_one)

  def sucs : ∀ q, Tms q Δ Γ → ∀ A, Tms q (Δ ▷ A) Γ
    | q, .ε    , A => .ε
    | q, δ -, x, A => sucs q δ A -, suc q x
  termination_by q δ => (q.n, 0, tmslen δ)
  decreasing_by
  . exact (.right _ (.right _
          ((Nat.lt_succ_of_le (Nat.le_add_right _ (tmlen x))))))
  . exact (.right _ (.right _
          ((Nat.lt_succ_of_le (Nat.le_add_left _ _)))))

  def identity : ∀ q Γ, Tms q Γ Γ
    | q, .ε    => .ε
    | q, Γ ▷ A => sucs q (identity q Γ) _ -, zero
  termination_by q Γ => (q.n, ctxlen Γ, 0)
  decreasing_by
  . exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . exact (.right _ (.left _ _ (Nat.zero_lt_succ _)))

  def subst : ∀ r, Tm q Γ A → Tms r Δ Γ
            → Tm (q ⊔ r) Δ A
    | _, .vz     , δ -, u => u
    | _, .vs  i  , δ -, u => subst _ i δ
    | _, .var i  , δ      => lift qT (subst _ i δ)
    | _, .lam t  , δ      => .lam (subst _ t (sucs _ δ _ -, zero))
    | _, .app t u, δ      => .app (subst _ t δ) (subst _ u δ)
  termination_by r x _  => (r.n, tmlen x, 0)
  decreasing_by
  . exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . exact (.right _ (.left _ _ (Nat.zero_lt_succ _)))
  . exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . exact (.right _ (.left _ _ (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
  . exact (.right _ (.left _ _ (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
end
