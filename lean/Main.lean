import «Lean»

-- Ackermann
def ack : Nat → Nat → Nat
  | .zero  , n       => .succ n
  | .succ m, .zero   => ack m 1
  | .succ m, .succ n => ack m (ack (.succ m) n)

-- It might also worth be trying just leaving 'sort' as 'Nat' and use the fact
-- that there exists no 'Tm (.succ (.succ n)) Γ A' as proof it is < 2
structure sort where
  n   : Nat
  prf : n < 2

def V : sort := sort.mk 0 (Nat.zero_lt_succ _)
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

-- I think Lean can derive these size functions with 'sizeOf' but defining these
-- functions manually seems to make the goal types a bit simpler
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

-- Work-in-progress (I think the 'termination_by' criteria I have given is not
-- quite right yet)
-- I think there is a possibility that once we get the 'termination_by' criteria
-- right, Lean will be able to infer the 'decreasing_by' proof, which would
-- make this actually quite nice.

-- I also think we could probably get away with taking a sort and projecting out
-- the 'Nat' instead of taking the 'Nat' and proof separately.
mutual
  def suc : ∀ n p, Tm (sort.mk n p) Γ B → Tm (sort.mk n p) (Γ ▷ A) B
    | 0, p, i => .vs i
    | 1, p, t => subst _ _ _ _ t (sucs 0 (Nat.zero_lt_succ _) (identity 0 (Nat.zero_lt_succ _) Γ) _)
  termination_by n p x => (n, 0, tmlen x)
  decreasing_by
  . exact (.left _ _ Nat.zero_lt_one)
  . exact (.left _ _ Nat.zero_lt_one)
  . exact (.left _ _ Nat.zero_lt_one)

  def sucs : ∀ n p, Tms (sort.mk n p) Δ Γ → ∀ A, Tms (sort.mk n p) (Δ ▷ A) Γ
    | n, p, .ε    , A => .ε
    | n, p, δ -, x, A => sucs n _ δ A -, suc n _ x
  termination_by n p δ => (n, 0, tmslen δ)
  decreasing_by
  . simp!
    exact (.right _ (.right _
          ((Nat.lt_succ_of_le (Nat.le_add_right _ (tmlen x))))))
  . simp!
    exact (.right _ (.right _
          ((Nat.lt_succ_of_le (Nat.le_add_left _ _)))))

  def identity : ∀ n p Γ, Tms (sort.mk n p) Γ Γ
    | n, p, .ε    => .ε
    | n, p, Γ ▷ A => sucs n _ (identity n _ Γ) _ -, zero
  termination_by n _ Γ => (n, ctxlen Γ, 0)
  decreasing_by
  . simp!
    exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . exact (.right _ (.left _ _ sorry)) -- TODO

  def subst : ∀ n p m q, Tm (sort.mk n p) Γ A → Tms (sort.mk m q) Δ Γ
            → Tm ((sort.mk n p) ⊔ (sort.mk m q)) Δ A
    | 0, p, m, q, .vz     , δ -, u => u
    | 0, p, m, q, .vs i   , δ -, u => subst _ _ _ _ i δ
    | 1, p, m, q, .var i  , δ      => lift qT (subst _ _ _ _ i δ)
    | 1, p, m, q, .lam t  , δ      => .lam (subst _ _ _ _ t (sucs _ _ δ _ -, zero))
    | 1, p, m, q, .app t u, δ      => .app (subst _ _ _ _ t δ) (subst _ _ _ _ u δ)
  termination_by n p m q x δ  => (m, tmlen x, tmslen δ)
  decreasing_by
  . simp!
    exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . simp!
    exact (.right _ (.left _ _ (Nat.lt_succ_self _)))
  . simp!
    exact (.right _ (.left _ _ (Nat.zero_lt_succ _)))
  . exact (.right _ sorry) -- TODO
  . simp!
    exact (.right _ (.left _ _ (Nat.lt_succ_of_le (Nat.le_add_right _ _))))
  . exact (.right _ (.left _ _ (Nat.lt_succ_of_le (Nat.le_add_left _ _))))
end

def main : IO Unit :=
  IO.println s!"Hello!"
