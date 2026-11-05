import TinyCryptids.PerfectCuboid.Tuple

/-!
# Main theorem: the design halts iff a perfect cuboid exists

One tuple (`tuple`): from `TS t s` the twelve checks run as in the windows
`[A B C] [Z A B] [C Z A] [B C Z]`; the four that can fail test `a² + b²`, `a² + b² + c²`,
`c² + a²`, `b² + c²`. All pass: halt. One fails: the next tuple, `TS (nxt t) s'`.
-/

namespace TM.PerfectCuboid

open St

/-- the counter after `n` units from `(0, 0)` -/
def σ (n : Nat) : Nat × Nat := advN n (0, 0)

theorem σ_valid (n : Nat) : Valid (σ n) := advN_valid n _ (by show 0 ≤ 2 * 0; omega)

theorem σ_val (n : Nat) : val (σ n) = n := by
  unfold σ; rw [val_advN n _ (by show 0 ≤ 2 * 0; omega)]; simp [val]

theorem σ_sq (n : Nat) : (σ n).2 = 0 ↔ IsSq n := by
  rw [← sq_iff _ (σ_valid n), σ_val]

theorem rs0 (s : Nat × Nat) : rs 0 s = s := rfl
theorem rs1 (s : Nat × Nat) : rs 1 s = s := rfl
theorem rs2 (s : Nat × Nat) : rs 2 s = σ 0 := rfl

theorem σ_add (n m : Nat) : advN m (σ n) = σ (n + m) := by unfold σ; rw [advN_add]

theorem σ_zero : σ 0 = (0, 0) := rfl
theorem tk0 : tk 0 = 1 := rfl
theorem tk1 : tk 1 = 2 := rfl
theorem tk2 : tk 2 = 0 := rfl

theorem sq_self (a : Nat) : IsSq (a * a) := ⟨a, rfl⟩

theorem reach1_of_q {a b : Cfg St} (h : Rch a b) (hq : a.q ≠ b.q) : Rch1 a b := by
  obtain ⟨n, hn⟩ := h
  cases n with
  | zero => simp [run, Sys.run] at hn; subst hn; exact absurd rfl hq
  | succ n => exact ⟨n, hn⟩

/-- after an abort: the next tuple -/
theorem next_of_abort (t : Tup) (ht : Valid3 t) (k : Nat) (c : Cfg St) (hc : c.q ≠ ea0)
    (h : Rch c ⟨ea0, blank, app (qL t ++ gapL 2) (Sb (k, 0))⟩) :
    ∃ s', Valid s' ∧ s'.2 = 0 ∧ Rch1 c (TS (nxt t) s') := by
  refine ⟨(k, 0), by show 0 ≤ 2 * k; omega, rfl, ?_⟩
  refine Reach1.trans_reach delta (reach1_of_q h hc) ?_
  have := nexcom t ht (app (gapL 2) (Sb (k, 0)))
  simp only [← app_append] at this
  exact this

theorem tuple (x y z : Nat) (ht : Valid3 (x, y, z)) (s : Nat × Nat) (hs : Valid s) (h0 : s.2 = 0) :
    (Good (x, y, z) → HaltAt (TS (x, y, z) s)) ∧
    (¬ Good (x, y, z) → ∃ s', Valid s' ∧ s'.2 = 0 ∧ Rch1 (TS (x, y, z) s) (TS (nxt (x, y, z)) s')) := by
  obtain ⟨hx, hy, hz⟩ := ht
  have vt : Valid3 (x, y, z) := ⟨hx, hy, hz⟩
  -- the values and their squares
  generalize hA : v x * v x = A
  generalize hB : v y * v y = B
  generalize hC : v z * v z = C
  have sA : IsSq A := hA ▸ sq_self _
  have sB : IsSq B := hB ▸ sq_self _
  have sC : IsSq C := hC ▸ sq_self _
  have good : Good (x, y, z) ↔ IsSq (A + B) ∧ IsSq (A + B + C) ∧ IsSq (C + A) ∧ IsSq (B + C) := by
    simp only [Good, hA, hB, hC]
  -- the steps, with W and S normalized
  have hs0 : Valid (σ 0) := σ_valid 0
  have r1 : Rch (TS (x, y, z) s) (PC x y z 1 (σ (A + B))) := by
    have e1 := stepA x y z hx 2 (by omega) s hs h0
    have e2 := stepB x y z hy 0 (by omega) (σ A) (σ_valid _) ((σ_sq _).2 sA)
    simp only [tk0, tk1, tk2, rs0, rs1, rs2, σ_add, Nat.zero_add, hA, hB] at e1 e2
    exact Rch.tr e1 e2
  have r2 : IsSq (A + B) → Rch (PC x y z 1 (σ (A + B))) (PZ x y z 2 (σ (A + B + C))) := by
    intro h
    have e := stepC x y z hz 1 (by omega) _ (σ_valid _) ((σ_sq _).2 h)
    simp only [tk0, tk1, tk2, rs0, rs1, rs2, σ_add, Nat.zero_add, hC] at e
    exact e
  have r3 : IsSq (A + B) → IsSq (A + B + C) →
      Rch (PZ x y z 2 (σ (A + B + C))) (PZ x y z 0 (σ C)) := by
    intro h1 h2
    have e1 := stepZ x y z 2 (by omega) _ ((σ_sq _).2 h2)
    have e2 := endA x y z vt 0 (by omega) (σ 0)
    have e3 := stepA x y z hx 0 (by omega) (σ 0) hs0 rfl
    have e4 := stepB x y z hy 1 (by omega) (σ A) (σ_valid _) ((σ_sq _).2 sA)
    have e5 := stepC x y z hz 2 (by omega) (σ (A + B)) (σ_valid _) ((σ_sq _).2 h1)
    simp only [tk0, tk1, tk2, rs0, rs1, rs2, σ_add, Nat.zero_add, hA, hB, hC] at e1 e2 e3 e4 e5
    exact Rch.tr e1 (Rch.tr e2 (Rch.tr e3 (Rch.tr e4 e5)))
  have r4 : Rch (PZ x y z 0 (σ C)) (PB x y z 2 (σ (C + A))) := by
    have e1 := stepZ x y z 0 (by omega) _ ((σ_sq _).2 sC)
    have e2 := endA x y z vt 1 (by omega) (σ C)
    have e3 := stepA x y z hx 1 (by omega) (σ C) (σ_valid _) ((σ_sq _).2 sC)
    simp only [tk0, tk1, tk2, rs0, rs1, rs2, σ_add, Nat.zero_add, hA] at e1 e2 e3
    exact Rch.tr e1 (Rch.tr e2 e3)
  have r5 : IsSq (C + A) → Rch (PB x y z 2 (σ (C + A))) (PZ x y z 1 (σ (B + C))) := by
    intro h
    have e1 := stepB x y z hy 2 (by omega) _ (σ_valid _) ((σ_sq _).2 h)
    have e2 := stepC x y z hz 0 (by omega) (σ B) (σ_valid _) ((σ_sq _).2 sB)
    simp only [tk0, tk1, tk2, rs0, rs1, rs2, σ_add, Nat.zero_add, hB, hC] at e1 e2
    exact Rch.tr e1 e2
  have r6 : IsSq (B + C) → HaltAt (PZ x y z 1 (σ (B + C))) := by
    intro h
    have e := stepZ x y z 1 (by omega) _ ((σ_sq _).2 h)
    simp only [tk1, rs1] at e
    exact HaltAt.back e (endH x y z _)
  -- the aborts
  have nq : ∀ W s, (PC x y z W s).q ≠ ea0 ∧ (PZ x y z W s).q ≠ ea0 ∧ (PB x y z W s).q ≠ ea0 :=
    fun _ _ => ⟨by simp [PC], by simp [PZ], by simp [PB]⟩
  have ab : ∀ c : Cfg St, Rch (TS (x, y, z) s) c → c.q ≠ ea0 → (∃ k, Rch c
      ⟨ea0, blank, app (qL (x, y, z) ++ gapL 2) (Sb (k, 0))⟩) →
      ∃ s', Valid s' ∧ s'.2 = 0 ∧ Rch1 (TS (x, y, z) s) (TS (nxt (x, y, z)) s') := by
    rintro c hc hq ⟨k, hk⟩
    obtain ⟨s', h1, h2, h3⟩ := next_of_abort (x, y, z) vt k c hq hk
    exact ⟨s', h1, h2, Reach.trans_reach1 delta hc h3⟩
  constructor
  · intro hg
    obtain ⟨g1, g2, g3, g4⟩ := good.1 hg
    exact HaltAt.back (Rch.tr r1 (Rch.tr (r2 g1) (Rch.tr (r3 g1 g2) (Rch.tr r4 (r5 g3))))) (r6 g4)
  · intro hg
    by_cases g1 : IsSq (A + B)
    · by_cases g2 : IsSq (A + B + C)
      · by_cases g3 : IsSq (C + A)
        · by_cases g4 : IsSq (B + C)
          · exact absurd (good.2 ⟨g1, g2, g3, g4⟩) hg
          · exact ab _ (Rch.tr r1 (Rch.tr (r2 g1) (Rch.tr (r3 g1 g2) (Rch.tr r4 (r5 g3)))))
              (nq _ _).2.1 ⟨_, abZ x y z vt 1 _ (σ_valid _) (fun h => g4 ((σ_sq _).1 h))⟩
        · exact ab _ (Rch.tr r1 (Rch.tr (r2 g1) (Rch.tr (r3 g1 g2) r4)))
            (nq _ _).2.2 ⟨_, abB x y z vt 2 _ (σ_valid _) (fun h => g3 ((σ_sq _).1 h))⟩
      · exact ab _ (Rch.tr r1 (r2 g1)) (nq _ _).2.1
          ⟨_, abZ x y z vt 2 _ (σ_valid _) (fun h => g2 ((σ_sq _).1 h))⟩
    · exact ab _ r1 (nq _ _).1 ⟨_, abC x y z vt 1 _ (σ_valid _) (fun h => g1 ((σ_sq _).1 h))⟩

theorem tuple' (t : Tup) (ht : Valid3 t) (s : Nat × Nat) (hs : Valid s) (h0 : s.2 = 0) :
    (Good t → HaltAt (TS t s)) ∧
    (¬ Good t → ∃ s', Valid s' ∧ s'.2 = 0 ∧ Rch1 (TS t s) (TS (nxt t) s')) := by
  obtain ⟨x, y, z⟩ := t
  exact tuple x y z ht s hs h0

/-- the search order: before the `k`-th tuple, unless the machine has halted already -/
theorem search : ∀ k, HaltAt start ∨
    ∃ s, Valid s ∧ s.2 = 0 ∧ Rch start (TS (itr k seedT) s)
  | 0 => Or.inr ⟨(0, 0), by show 0 ≤ 2 * 0; omega, rfl, boot⟩
  | k + 1 => by
    rcases search k with h | ⟨s, hs, h0, hr⟩
    · exact Or.inl h
    · by_cases hg : Good (itr k seedT)
      · exact Or.inl (HaltAt.back hr ((tuple' _ (itr_valid k) s hs h0).1 hg))
      · obtain ⟨s', h1, h2, h3⟩ := (tuple' _ (itr_valid k) s hs h0).2 hg
        exact Or.inr ⟨s', h1, h2, Rch.tr hr h3.reach⟩

/-- If a perfect cuboid exists, the machine reaches its halting state. -/
theorem haltAt_of (h : ∃ a b c d e f g : Nat, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a * a + b * b = d * d ∧
    a * a + c * c = e * e ∧ b * b + c * c = f * f ∧ a * a + b * b + c * c = g * g) :
    HaltAt start := by
  obtain ⟨a, b, c, d, e, f, g, ha, hb, hc, hd, he, hf, hg⟩ := h
  have hv : Valid3 (2 * a + 2, 2 * b + 2, 2 * c + 2) := by simp only [Valid3]; omega
  obtain ⟨k, hk⟩ := reached (2 * a + 2) (2 * b + 2) (2 * c + 2) hv
  rcases search k with h | ⟨s, hs, h0, hr⟩
  · exact h
  · rw [hk] at hr
    exact HaltAt.back hr ((tuple' _ hv s hs h0).1
      (good_of_cuboid a b c d e f g hd he hf hg))

theorem halts_det {a b : Cfg St} (ha : Halts delta a) (hab : Reach delta a b) : Halts delta b :=
  Sys.Halts.of_reach hab ha

/-- **Main theorem.** Started on a blank tape, the design halts if and only if a perfect
cuboid exists: positive integers `a, b, c` whose face diagonals `√(a² + b²)`, `√(a² + c²)`,
`√(b² + c²)` and space diagonal `√(a² + b² + c²)` are all integers. -/
theorem halts_iff :
    Halts delta start ↔ ∃ a b c d e f g : Nat, 1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ c ∧ a * a + b * b = d * d ∧
      a * a + c * c = e * e ∧ b * b + c * c = f * f ∧ a * a + b * b + c * c = g * g := by
  constructor
  · intro hH
    apply Classical.byContradiction
    intro hno
    have bad : ∀ t, Valid3 t → ¬ Good t := fun t ht hg => hno (cuboid_of_good t ht hg)
    have prog := not_halts_of_progress delta
      (fun c => ∃ t s, Valid3 t ∧ Valid s ∧ s.2 = 0 ∧ c = TS t s) (by
        rintro c ⟨t, s, ht, hs, h0, rfl⟩
        obtain ⟨s', h1, h2, h3⟩ := (tuple' t ht s hs h0).2 (bad t ht)
        exact ⟨_, ⟨nxt t, s', nxt_valid t ht, h1, h2, rfl⟩, h3⟩)
    exact prog _ ⟨seedT, (0, 0), ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩,
      by show 0 ≤ 2 * 0; omega, rfl, rfl⟩ (halts_det hH boot)
  · intro h; exact (haltAt_of h).halts

end TM.PerfectCuboid
