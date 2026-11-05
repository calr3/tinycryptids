import TinyCryptids.Defs

/-!
# The arithmetic side

The second Hardy–Littlewood conjecture: `π(x + y) ≤ π(x) + π(y)` for all `x, y ≥ 2`.

The machine works with `Q`: 1 and the odd primes. For `x ≥ 2` they are counted by
`primeCount x` (1 stands in for 2). It keeps the half gaps `g = [h₁, h₂, …]` of the
`Q`-elements `1 = q₀ < q₁ = 3 < q₂ < …`, so `q_i = 2·(h₁ + … + h_i) + 1`.

At a new prime `m` with gap list `g` (`G` gaps, `m = q_G`) it looks for an `i` with
`1 ≤ i ≤ G - 1` and `h₁ + … + h_G < (h₁ + … + h_i) + (h₁ + … + h_{G-i})` (`bad g`):
then `y = q_{G-i} - 1` and `x = m - y` have `π(x) + π(y) ≤ G < π(m)` (`sound`); and every
counterexample `(x, y)` gives such an `i` at the largest `m ≤ x + y` in `Q` (`complete`).
-/

namespace TM.HardyLittlewood2

open TinyCryptids

/-- 1 and the odd primes -/
def Q (n : Nat) : Prop := n = 1 ∨ (n % 2 = 1 ∧ Prime n)

instance : DecidablePred Q := fun n => by unfold Q; exact inferInstance

/-- the number of `Q`-elements `≤ x` -/
def pq (x : Nat) : Nat := ((List.range (x + 1)).filter (fun k => decide (Q k))).length

theorem pq_zero : pq 0 = 0 := by decide

theorem pq_succ (x : Nat) : pq (x + 1) = pq x + (if Q (x + 1) then 1 else 0) := by
  unfold pq
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : Q (x + 1) <;> simp [h]

theorem pq_mono {a b : Nat} (h : a ≤ b) : pq a ≤ pq b := by
  induction b with
  | zero => rw [show a = 0 by omega]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_ge a (b + 1) with h' | h'
    · have := ih (by omega); rw [pq_succ]; omega
    · rw [show a = b + 1 by omega]; exact Nat.le_refl _

theorem pq_one : pq 1 = 1 := by decide

theorem pq_pos {x : Nat} (h : 1 ≤ x) : 1 ≤ pq x := by
  have := pq_mono h; rw [pq_one] at this; exact this

theorem primeCount_succ (x : Nat) :
    primeCount (x + 1) = primeCount x + (if Prime (x + 1) then 1 else 0) := by
  unfold primeCount
  rw [List.range_succ, List.filter_append, List.length_append]
  by_cases h : Prime (x + 1) <;> simp [h]

/-- an odd number `≥ 3` is in `Q` iff it is prime; even numbers `≥ 3` are in neither -/
theorem q_iff_prime {p : Nat} (hp : 3 ≤ p) : Q p ↔ Prime p := by
  constructor
  · rintro (h | ⟨_, h⟩)
    · omega
    · exact h
  · intro h
    refine Or.inr ⟨?_, h⟩
    have := h.2 2 (by omega) (Nat.le_refl _)
    omega

theorem primeCount_eq : ∀ x, 2 ≤ x → primeCount x = pq x
  | 0, h => absurd h (by decide)
  | 1, h => absurd h (by decide)
  | 2, _ => by decide
  | x + 3, _ => by
    rw [primeCount_succ, pq_succ, primeCount_eq (x + 2) (by omega)]
    by_cases h : Prime (x + 3)
    · rw [if_pos h, if_pos ((q_iff_prime (by omega)).2 h)]
    · rw [if_neg h, if_neg (fun h' => h ((q_iff_prime (by omega)).1 h'))]

/-! ## sums of gaps -/

def ssum : List Nat → Nat
  | [] => 0
  | a :: l => a + ssum l

theorem ssum_append (l m : List Nat) : ssum (l ++ m) = ssum l + ssum m := by
  induction l with
  | nil => simp [ssum]
  | cons a l ih => simp [ssum, ih]; omega

theorem ssum_reverse (l : List Nat) : ssum l.reverse = ssum l := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.reverse_cons, ssum_append, ih]; simp [ssum]; omega

/-- `h₁ + … + h_i` -/
def B (g : List Nat) (i : Nat) : Nat := ssum (g.take i)

theorem B_take_drop (g : List Nat) (i : Nat) : B g i + ssum (g.drop i) = ssum g := by
  unfold B; rw [← ssum_append, List.take_append_drop]

theorem B_len (g : List Nat) : B g g.length = ssum g := by
  unfold B; rw [List.take_length]

theorem B_append (g : List Nat) (c : Nat) {i : Nat} (h : i ≤ g.length) :
    B (g ++ [c]) i = B g i := by
  unfold B; rw [List.take_append_of_le_length h]

theorem B_append_len (g : List Nat) (c : Nat) : B (g ++ [c]) (g.length + 1) = ssum g + c := by
  unfold B
  rw [show g.length + 1 = (g ++ [c]).length by simp, List.take_length, ssum_append]
  simp [ssum]

/-- `1 + 2·B g i` is the `(i+1)`-th element of `Q`, for each `i ≤ |g|` -/
def Fit (g : List Nat) : Prop := ∀ i, i ≤ g.length → pq (2 * B g i) = i ∧ pq (2 * B g i + 1) = i + 1

/-- the test at a prime: some `i` in `[1, G-1]` with `Σg < B_i + B_{G-i}` -/
def bad (g : List Nat) : Prop :=
  ∃ i, 1 ≤ i ∧ i + 1 ≤ g.length ∧ ssum g < B g i + B g (g.length - i)

/-- `B` increases with `i` (strictly, by the elements of `Q` it counts) -/
theorem fit_lt {g : List Nat} (hf : Fit g) {i j : Nat} (hij : i < j) (hj : j ≤ g.length) :
    B g i < B g j := by
  have h1 := (hf i (by omega)).2
  have h2 := (hf j hj).2
  rcases Nat.lt_or_ge (B g i) (B g j) with h | h
  · exact h
  · have := pq_mono (show 2 * B g j + 1 ≤ 2 * B g i + 1 by omega); omega

theorem sound {g : List Nat} (hf : Fit g) (hb : bad g) :
    ∃ x y, 2 ≤ x ∧ 2 ≤ y ∧ primeCount x + primeCount y < primeCount (x + y) := by
  obtain ⟨i, h1, h2, hs⟩ := hb
  have hG := B_len g
  have hfi := hf i (by omega)
  have hfa := hf (g.length - i) (by omega)
  have hfG := hf g.length (Nat.le_refl _)
  have hlt := fit_lt hf (show g.length - i < g.length by omega) (Nat.le_refl _)
  have hpos : 1 ≤ B g (g.length - i) := by
    rcases Nat.eq_zero_or_pos (B g (g.length - i)) with h | h
    · rw [h, show 2 * 0 = 0 by rfl, pq_zero] at hfa; omega
    · exact h
  refine ⟨2 * (ssum g - B g (g.length - i)) + 1, 2 * B g (g.length - i), by omega, by omega, ?_⟩
  rw [primeCount_eq _ (by omega), primeCount_eq _ (by omega), primeCount_eq _ (by omega),
    show 2 * (ssum g - B g (g.length - i)) + 1 + 2 * B g (g.length - i) = 2 * B g g.length + 1 by omega,
    hfG.2, hfa.1]
  have := pq_mono (show 2 * (ssum g - B g (g.length - i)) + 1 ≤ 2 * B g i by omega)
  omega

theorem complete {g : List Nat} (hf : Fit g) {x y : Nat} (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hc : pq x + pq y < pq (x + y)) (hn : pq (x + y) = g.length + 1)
    (hm : 2 * ssum g + 1 ≤ x + y) : bad g := by
  have ha := pq_pos (show 1 ≤ y by omega)
  have hb := pq_pos (show 1 ≤ x by omega)
  refine ⟨g.length - pq y, by omega, by omega, ?_⟩
  rw [show g.length - (g.length - pq y) = pq y by omega]
  have hfi := (hf (g.length - pq y) (by omega)).2
  have hfa := (hf (pq y) (by omega)).2
  have e1 : x < 2 * B g (g.length - pq y) + 1 := by
    rcases Nat.lt_or_ge x (2 * B g (g.length - pq y) + 1) with h | h
    · exact h
    · have := pq_mono h; omega
  have e2 : y < 2 * B g (pq y) + 1 := by
    rcases Nat.lt_or_ge y (2 * B g (pq y) + 1) with h | h
    · exact h
    · have := pq_mono h; omega
  omega

/-- the largest element of `Q` up to `n` (for `n ≥ 1`) -/
theorem last_q : ∀ n, 1 ≤ n → ∃ m, m ≤ n ∧ Q m ∧ pq m = pq n
  | 0, h => absurd h (by decide)
  | n + 1, _ => by
    by_cases hq : Q (n + 1)
    · exact ⟨n + 1, Nat.le_refl _, hq, rfl⟩
    · rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact absurd (Or.inl rfl) hq
      obtain ⟨m, h1, h2, h3⟩ := last_q n hn
      exact ⟨m, by omega, h2, by rw [pq_succ, if_neg hq]; exact h3⟩

/-! ## the counter `E` of the test

At a prime the machine runs `E := 0`; for each pair `(t, b)`: `E += t`, then `E -= b`,
halting if `E` would drop below 0. The tops are `c, h_{G-1}, …, h₂` and the bottoms
`h₁, …, h_{G-1}`. -/

def ok : Nat → List Nat → List Nat → Prop
  | e, t :: ts, b :: bs => b ≤ e + t ∧ ok (e + t - b) ts bs
  | _, _, _ => True

theorem ok_iff : ∀ (bs ts : List Nat) (e : Nat), ts.length = bs.length →
    (ok e ts bs ↔ ∀ k, k ≤ bs.length → ssum (bs.take k) ≤ e + ssum (ts.take k))
  | [], [], e, _ => by
    simp only [ok, List.length_nil, List.take_nil, ssum, true_iff]; intro k _; omega
  | [], _ :: _, _, h => by simp at h
  | _ :: _, [], _, h => by simp at h
  | b :: bs, t :: ts, e, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [ok, List.length_cons]
    rw [ok_iff bs ts (e + t - b) h]
    constructor
    · rintro ⟨h1, h2⟩ k hk
      rcases k with _ | k
      · simp [ssum]
      · simp only [List.take_succ_cons, ssum]
        have := h2 k (by omega); omega
    · intro h2
      have h1 := h2 1 (by omega)
      simp only [List.take_succ_cons, List.take_zero, ssum] at h1
      refine ⟨by omega, fun k hk => ?_⟩
      have := h2 (k + 1) (by omega)
      simp only [List.take_succ_cons, ssum] at this
      omega

theorem ssum_take_rev (l : List Nat) (k : Nat) :
    ssum (l.reverse.take k) = ssum (l.drop (l.length - k)) := by
  rw [List.take_reverse, ssum_reverse]

/-- the test passes iff the gaps after the prime are not `bad` -/
theorem ok_iff_bad (g₀ : List Nat) (c : Nat) :
    ok 0 (c :: g₀.reverse) (1 :: g₀) ↔ ¬ bad (1 :: g₀ ++ [c]) := by
  have hts : c :: g₀.reverse = (g₀ ++ [c]).reverse := by simp
  rw [ok_iff _ _ _ (by simp), hts]
  have hlen : (1 :: g₀ ++ [c]).length = g₀.length + 2 := by simp
  have key : ∀ k, k ≤ g₀.length + 1 →
      ssum ((g₀ ++ [c]).reverse.take k) = ssum (1 :: g₀ ++ [c]) - B (1 :: g₀ ++ [c]) (g₀.length + 2 - k) := by
    intro k hk
    rw [ssum_take_rev]
    have := B_take_drop (1 :: g₀ ++ [c]) (g₀.length + 2 - k)
    rw [show g₀.length + 2 - k = (g₀.length + 1 - k) + 1 by omega] at this ⊢
    simp only [List.cons_append, List.drop_succ_cons, List.length_append, List.length_singleton] at this ⊢
    omega
  have hb : ∀ k, k ≤ (1 :: g₀).length → ssum ((1 :: g₀).take k) = B (1 :: g₀ ++ [c]) k := by
    intro k hk; rw [List.cons_append, ← List.cons_append, B_append _ _ hk]; rfl
  constructor
  · rintro h ⟨i, h1, h2, h3⟩
    rw [hlen] at h2 h3
    have := h i (by simp; omega)
    rw [hb i (by simp; omega), key i (by omega)] at this
    have := B_take_drop (1 :: g₀ ++ [c]) (g₀.length + 2 - i)
    omega
  · intro h k hk
    simp only [List.length_cons] at hk
    rw [hb k (by simp; omega), key k hk]
    have := B_take_drop (1 :: g₀ ++ [c]) (g₀.length + 2 - k)
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [B, ssum]
    · have : ¬ (ssum (1 :: g₀ ++ [c]) < B (1 :: g₀ ++ [c]) k + B (1 :: g₀ ++ [c]) (g₀.length + 2 - k)) :=
        fun h' => h ⟨k, hk0, by rw [hlen]; omega, by rw [hlen]; exact h'⟩
      omega

/-! ## the machine's bookkeeping: the gaps so far and the next gap `c` -/

/-- at the candidate `m`: `g` lists the half gaps of the `Q`-elements below `m`, the last
of which is `m - 2c` -/
structure Inv (m : Nat) (g : List Nat) (c : Nat) : Prop where
  hd : ∃ g₀, g = 1 :: g₀
  pos : ∀ h, h ∈ g → 1 ≤ h
  c1 : 1 ≤ c
  hm : m = 2 * ssum g + 1 + 2 * c
  fit : Fit g
  top : pq (m - 1) = g.length + 1

theorem Inv.odd {m : Nat} {g : List Nat} {c : Nat} (h : Inv m g c) : m % 2 = 1 := by
  have := h.hm; omega

theorem Inv.ge {m : Nat} {g : List Nat} {c : Nat} (h : Inv m g c) : 5 ≤ m := by
  obtain ⟨g₀, rfl⟩ := h.hd
  have := h.hm; have := h.c1; simp only [ssum] at *; omega

/-- a composite candidate: one more step of the next gap -/
theorem Inv.comp {m : Nat} {g : List Nat} {c : Nat} (h : Inv m g c) (hq : ¬ Q m) :
    Inv (m + 2) g (c + 1) := by
  refine ⟨h.hd, h.pos, by omega, by have := h.hm; omega, h.fit, ?_⟩
  have := h.top; have hm5 := h.ge; have ho := h.odd
  rw [show m + 2 - 1 = (m - 1) + 1 + 1 by omega, pq_succ, pq_succ,
    show m - 1 + 1 = m by omega, if_neg hq,
    if_neg (show ¬ Q (m + 1) by intro h'; rcases h' with h' | ⟨h', _⟩ <;> omega)]
  omega

/-- a prime candidate: `c` becomes the last gap -/
theorem Inv.prime {m : Nat} {g : List Nat} {c : Nat} (h : Inv m g c) (hq : Q m) :
    Inv (m + 2) (g ++ [c]) 1 := by
  obtain ⟨g₀, hg⟩ := h.hd
  have hm := h.hm; have ht := h.top; have hm5 := h.ge; have ho := h.odd
  have hpm : pq m = g.length + 2 := by
    rw [show m = (m - 1) + 1 by omega, pq_succ, show m - 1 + 1 = m by omega, if_pos hq]; omega
  refine ⟨⟨g₀ ++ [c], by rw [hg]; rfl⟩, fun x hx => ?_, Nat.le_refl _, ?_, ?_, ?_⟩
  · rcases List.mem_append.1 hx with hx | hx
    · exact h.pos x hx
    · simp at hx; have := h.c1; omega
  · rw [ssum_append]; simp [ssum]; omega
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    rcases Nat.lt_or_ge i (g.length + 1) with hi' | hi'
    · rw [B_append g c (by omega)]; exact h.fit i (by omega)
    · rw [show i = g.length + 1 by omega, B_append_len,
        show 2 * (ssum g + c) = m - 1 by omega, show m - 1 + 1 = m by omega, hpm]
      exact ⟨by omega, by omega⟩
  · simp only [List.length_append, List.length_singleton]
    rw [show m + 2 - 1 = m + 1 by omega, pq_succ,
      if_neg (show ¬ Q (m + 1) by intro h'; rcases h' with h' | ⟨h', _⟩ <;> omega)]
    omega

/-- the first candidate the machine tests after the seed: `m = 5`, `g = [1]` (3 - 1 = 2·1),
`c = 1` -/
theorem inv_five : Inv 5 [1] 1 := by
  refine ⟨⟨[], rfl⟩, fun h hh => by simp at hh; omega, Nat.le_refl _, rfl, ?_, by decide⟩
  intro i hi
  simp only [List.length_singleton] at hi
  rcases Nat.lt_or_ge i 1 with h | h
  · rw [show i = 0 by omega]; decide
  · rw [show i = 1 by omega]; decide

end TM.HardyLittlewood2
