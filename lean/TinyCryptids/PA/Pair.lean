/-!
# Cantor pairing

`pair a b = T(a + b) + a` with `T n = n(n+1)/2`.  `unpair` walks the pairs in Cantor order —
`(a, 0)` is followed by `(0, a + 1)`, `(a, b + 1)` by `(a + 1, b)` — which is what the
machine's `unpair` loop does one unit at a time.
-/

namespace TM.PA

/-- `T n = 0 + 1 + … + n` -/
def tri : Nat → Nat
  | 0 => 0
  | n + 1 => tri n + (n + 1)

def pair (a b : Nat) : Nat := tri (a + b) + a

/-- the next pair in Cantor order -/
def nextP : Nat × Nat → Nat × Nat
  | (a, 0) => (0, a + 1)
  | (a, b + 1) => (a + 1, b)

def unpair : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 => nextP (unpair n)

theorem pair_nextP (p : Nat × Nat) : pair (nextP p).1 (nextP p).2 = pair p.1 p.2 + 1 := by
  obtain ⟨a, b⟩ := p
  cases b with
  | zero => simp [nextP, pair, tri]; omega
  | succ b => simp [nextP, pair]; rw [show a + 1 + b = a + (b + 1) by omega]; omega

theorem pair_unpair (n : Nat) : pair (unpair n).1 (unpair n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [unpair, pair_nextP, ih]

theorem tri_mono {m n : Nat} (h : m < n) : tri m + m < tri n := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp h with h | rfl
    · have := ih h; simp [tri]; omega
    · simp [tri]

theorem pair_inj {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  unfold pair at h
  rcases Nat.lt_trichotomy (a + b) (c + d) with hl | he | hl
  · have := tri_mono hl; omega
  · rw [he] at h; omega
  · have := tri_mono hl; omega

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  have h := pair_unpair (pair a b)
  obtain ⟨h1, h2⟩ := pair_inj h
  exact Prod.ext h1 h2

@[simp] theorem unpair_pair_fst (a b : Nat) : (unpair (pair a b)).1 = a := by rw [unpair_pair]
@[simp] theorem unpair_pair_snd (a b : Nat) : (unpair (pair a b)).2 = b := by rw [unpair_pair]

/-- `n` steps of `nextP` -/
def nextN : Nat → Nat × Nat → Nat × Nat
  | 0, p => p
  | n + 1, p => nextN n (nextP p)

theorem nextN_eq (n : Nat) (p : Nat × Nat) : nextN n p = unpair (pair p.1 p.2 + n) := by
  induction n generalizing p with
  | zero => simp [nextN]; exact (Prod.ext (by rw [unpair_pair]) (by rw [unpair_pair]))
  | succ n ih => rw [nextN, ih, pair_nextP]; congr 1; omega

theorem pair_le_left (a b : Nat) : a ≤ pair a b := by unfold pair; omega

theorem tri_le (n : Nat) : n ≤ tri n := by
  induction n with
  | zero => exact Nat.le_refl 0
  | succ n ih => simp only [tri]; omega

theorem pair_le_right (a b : Nat) : b ≤ pair a b := by
  unfold pair; have := tri_le (a + b); omega

/-- the first component of a nonzero code is smaller -/
theorem pair_fst_lt {a b : Nat} (h : 0 < a + b) : a < pair a b := by
  unfold pair; have := tri_le (a + b); omega

end TM.PA
