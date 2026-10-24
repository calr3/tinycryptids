import TinyCryptids.Riesel.Round

/-!
# One candidate: trial division, the rebuild, the loop
-/

namespace TM.Riesel
open St TinyCryptids

local notation "F" => false

theorem mod_succ' (x d : Nat) (hd : 2 ≤ d) : (x % d + 1) % d = (x + 1) % d := by
  rw [Nat.add_mod x 1 d, Nat.mod_eq_of_lt (show 1 < d by omega)]

/-! ## trial division -/

/-- trial division of `P = d + r + 1` by `d, d + 1, …`, from the walk with the D hole home
and the R hole at cell 0; no divisor in `[2, d)`.  A prime ends in the wipe (`WP`), a
composite on a divisor `d'` (its D hole home) -/
theorem test (Y : Strm) : ∀ r d, 3 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r + 1) % e ≠ 0) →
    (Prime (d + r + 1) → Rch (MW Y d r d 0) (WP Y (d + r))) ∧
    (¬ Prime (d + r + 1) → ∃ d' r', d' + r' = d + r ∧ 3 ≤ d' ∧ Rch (MW Y d r d 0) (E3 Y d' r' d')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    have walk := mw_last Y d 0 d (by omega) (by omega) (Nat.le_refl _)
    rw [Nat.mod_self] at walk
    have st := Rch.tr walk (prime_end Y d (0 + 1) (by omega))
    have hp : Prime (d + 0 + 1) := ⟨by omega, fun e h1 h2 => by
      rcases Nat.lt_or_ge e d with h | h
      · exact hno e h2 h
      · rw [show e = d by omega, show d + 0 + 1 = d + 1 by omega, add_mod_self_left',
          Nat.mod_eq_of_lt (by omega)]
        omega⟩
    exact ⟨fun _ => st, fun hnp => absurd hp hnp⟩
  | succ r ih =>
    intro d hd hno
    have walk := Rch.tr (mw_upto Y d (r + 1) (by omega) (r + 1) (Nat.le_refl _))
      (mw_last Y d (r + 1) _ (by omega) (by omega) (Nat.mod_lt _ (by omega)))
    rw [mod_succ' _ d (by omega), show d + (r + 1) - 1 + 1 = d + (r + 1) by omega,
      add_mod_self_left'] at walk
    have hlt := Nat.mod_lt (r + 1) (show d > 0 by omega)
    by_cases hw : (r + 1) % d + 1 < d
    · have hnd : (d + (r + 1) + 1) % d ≠ 0 := by
        rw [Nat.add_assoc, add_mod_self_left', ← mod_succ' _ d (by omega), Nat.mod_eq_of_lt hw]; omega
      have step := Rch.tr walk (shift Y d r _ hw)
      have := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega]
        rcases Nat.lt_or_ge e d with h | h
        · exact hno e h1 h
        · rw [show e = d by omega]; exact hnd)
      rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega, show d + 1 + r = d + (r + 1) by omega] at this
      exact ⟨fun hp => Rch.tr step (this.1 hp), fun hp => by
        obtain ⟨d', r', h1, h2, h3⟩ := this.2 hp
        exact ⟨d', r', h1, h2, Rch.tr step h3⟩⟩
    · have h2 : (r + 1) % d + 1 = d := by omega
      have hdv : (d + (r + 1) + 1) % d = 0 := by
        rw [Nat.add_assoc, add_mod_self_left', ← mod_succ' _ d (by omega), h2, Nat.mod_self]
      rw [h2] at walk
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) (by omega)), fun _ => ⟨d, r + 1, rfl, hd, walk⟩⟩

/-! ## the rebuild -/

/-- left of R's cell 0 after a rebuild: the separator, D = 3 (hole home at cell 3), then `Y` -/
def YR (Y : Strm) : Strm := F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y

/-- from D's cell 1 with `n + 6` ones to the end: D := 3 (its hole at cell 3), separator, R
hole at R's cell 0; then the loop on R -/
theorem rtail (Y : Strm) (n : Nat) :
    Rch ⟨g1, true ::: F ::: Y, ones (n + 6) blank⟩ (cfgL s1 (ones n (F ::: YR Y)) blank) := by
  gR; gR; gR; gR; gR; gR
  sRn n; refine blankR ?_; gL
  rw [cons_blank]; fin

/-- the mod walk found a divisor `d` of `P = d + r + 1`: rebuild D := 3 and R := P - 2 cells,
R hole at cell 0, and go to the loop -/
theorem comp_end (Y : Strm) (d r : Nat) (hd : 3 ≤ d) :
    Rch (E3 Y d r d) (cfgL s1 (ones (d + r - 2) (F ::: YR Y)) blank) := by
  refine Rch.tr (comp_start Y d r) ?_
  rw [show d + r + 4 = d + r - 2 + 6 by omega]
  exact rtail Y _

/-! ## the loop -/

/-- one cell of X (left of the head) moves to X' (the separator moves left) and one more cell
is appended to T -/
theorem loop_tail (W : Strm) (m b c : Nat) :
    Rch ⟨s4, F ::: ones m (F ::: W), F ::: ones b (F ::: ones c blank)⟩
      (cfgL s1 (ones m (F ::: W)) (F ::: ones (b + 1) (F ::: ones (c + 1) blank))) := by
  gR; sRn b; gR; sRn c; refine blankR ?_; gL
  sLn c; gL
  show Rch (cfgL s7c (ones b (true ::: F ::: ones m (F ::: W))) (F ::: ones c (true ::: blank))) _
  rw [show ones b (true ::: F ::: ones m (F ::: W)) = ones (b + 1) (F ::: ones m (F ::: W)) from
    (ones_succ' b _).symm]
  sLn (b + 1); gL
  rw [ones_cons_blank]; fin

theorem loop_step (W : Strm) (m b c : Nat) :
    Rch (cfgL s1 (ones (m + 1) (F ::: W)) (F ::: ones b (F ::: ones c blank)))
      (cfgL s1 (ones m (F ::: W)) (F ::: ones (b + 1) (F ::: ones (c + 1) blank))) := by
  gR; exact loop_tail W m b c

/-- the loop: X (`m` cells left of the head, then a 0) moves to X' and is copied to T -/
theorem loop (W : Strm) : ∀ m b c,
    Rch (cfgL s1 (ones m (F ::: W)) (F ::: ones b (F ::: ones c blank)))
      (cfgL t1 W (F ::: F ::: ones (b + m) (F ::: ones (c + m) blank)))
  | 0, b, c => by gL; fin
  | m + 1, b, c => by
      refine Rch.tr (loop_step W m b c) ?_
      rw [show b + (m + 1) = b + 1 + m by omega, show c + (m + 1) = c + 1 + m by omega]
      exact loop W m (b + 1) (c + 1)

/-- the loop from a block followed by blank -/
theorem loop0 (W : Strm) (m : Nat) :
    Rch (cfgL s1 (ones m (F ::: W)) blank) (cfgL t1 W (F ::: F ::: ones m (F ::: ones m blank))) := by
  have := loop W m 0 0
  simp only [Nat.zero_add, ones_zero, cons_blank] at this
  exact this

/-- X was R (stopped at its hole): fill the gap and the X'/T separator; append two cells to
R (none when R was its hole only, the pseudo-round), then to the D hole -/
theorem dfin (Y : Strm) (m : Nat) (hm : 1 ≤ m) :
    Rch (cfgL t1 (YR Y) (F ::: F ::: ones m (F ::: ones m blank))) (MW Y 3 (2 * m + 3) 3 0) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  unfold YR MW
  gR; gR; gR; sRn (n + 1); gR; gR; sRn n
  refine blankR ?_; gR
  refine blankR ?_; gL
  show Rch (cfgL a6 (true ::: ones n (true ::: true ::: ones (n + 1)
      (true ::: F ::: F ::: tl (F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y))))
      (true ::: blank)) _
  have hL : (true ::: ones n (true ::: true ::: ones (n + 1)
      (true ::: F ::: F ::: tl (F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y))))
      = ones (2 * n + 5) (F ::: F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y) := by
    rw [show tl (F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y)
      = F ::: F ::: true ::: true ::: true ::: F ::: Y from rfl,
      ← ones_succ,
      show (true ::: true ::: ones (n + 1)
          (true ::: F ::: F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y))
        = ones 2 (ones (n + 1)
          (true ::: F ::: F ::: F ::: F ::: true ::: true ::: true ::: F ::: Y)) from rfl,
      ← ones_succ', ones_add, ones_add]
    rw [show (n + 1) + 2 + (n + 2) = 2 * n + 5 by omega]
  rw [hL, show (true ::: blank) = ones 1 blank from rfl]
  sLn (2 * n + 5); gL
  refine Rch.tr (PPM.find3 0 _ _) ?_
  gR
  rw [show ones (2 * (n + 1) + 3 + 1 - 0) blank = ones (2 * n + 5) (ones 1 blank) by
    rw [ones_add, show 2 * n + 5 + 1 = 2 * (n + 1) + 3 + 1 - 0 by omega]]
  fin

/-- the pseudo-round: `R` is its hole only, nothing is appended; the candidate is `3 + 1 + 1` -/
theorem dfin0 (Y : Strm) :
    Rch (cfgL t1 (YR Y) (F ::: F ::: blank)) (MW Y 3 1 3 0) := by
  unfold YR MW
  gR; gR; gR; gRb
  refine blankR ?_; gL
  gL; gL; gL; gL; gL; gL; gR
  rw [cons_blank]
  fin

/-- P is prime: wipe D and R, append a cell to K, back onto it -/
theorem wipe (Y : Strm) (d : Nat) : Rch (WP Y d) (cfgL s1 (true ::: Y) blank) := by
  unfold WP
  zLn 4; gL; eLn d; gR
  simp only [cons_blank, zeros_blank]; refine blankR ?_; gL
  rw [cons_blank]; fin

end TM.Riesel
