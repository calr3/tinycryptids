import TinyCryptids.Riesel.Round

/-!
# One candidate: trial division, the rebuild, the loop
-/

namespace TM.Riesel
open St TinyCryptids

local notation "F" => false

/-! ## trial division -/

/-- trial division of `P = d + r + 1` by `d, d+1, …`, from the walk with `r + 1` steps;
no divisor below `d` -/
theorem test (X : Strm) : ∀ r d, 3 ≤ d →
    (∀ e, 2 ≤ e → e < d → (d + r + 1) % e ≠ 0) →
    (Prime (d + r + 1) → Rch (MW X d (r + 1) 0 1) (P6 X (d + r + 1))) ∧
    (¬ Prime (d + r + 1) → ∃ d' r', d' + r' = d + r + 1 ∧ 3 ≤ d' ∧ 1 ≤ r' ∧
      Rch (MW X d (r + 1) 0 1) (MW X d' r' (d' - 1) r')) := by
  intro r
  induction r with
  | zero =>
    intro d hd hno
    have st := Rch.tr (mw_last_nodiv X d 1 0 (Nat.le_refl _) (by omega))
      (Rch.tr (shift X d 1 (Nat.le_refl _)) (tail_zero X (d + 1)))
    have hp : Prime (d + 0 + 1) := ⟨by omega, fun e h1 h2 => by
      rcases Nat.lt_or_ge e d with h | h
      · exact hno e h2 h
      · rw [show e = d by omega, show d + 0 + 1 = d + 1 by omega, add_mod_self_left',
          Nat.mod_eq_of_lt (by omega)]
        omega⟩
    exact ⟨fun _ => st, fun hnp => absurd hp hnp⟩
  | succ r ih =>
    intro d hd hno
    have walk := mw_upto X d (r + 2) (by omega) (r + 2) (by omega) (Nat.le_refl _)
    rw [show r + 2 - 1 = r + 1 by omega] at walk
    have ms := mod_succ (r + 1) d
    have hlt := Nat.mod_lt (r + 1) (show d > 0 by omega)
    by_cases hw : (r + 1) % d + 1 < d
    · have hnd : (d + (r + 1) + 1) % d ≠ 0 := by
        rw [Nat.add_assoc, add_mod_self_left', ms.1 hw]; omega
      have step := Rch.tr walk (Rch.tr (mw_last_nodiv _ d (r + 2) _ (by omega) hw)
        (Rch.tr (shift _ d (r + 2) (by omega)) (tail_more _ (d + 1) (r + 2 - 1) (by omega) (by omega))))
      rw [show r + 2 - 1 = r + 1 by omega] at step
      have := ih (d + 1) (by omega) (fun e h1 h2 => by
        rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega]
        rcases Nat.lt_or_ge e d with h | h
        · exact hno e h1 h
        · rw [show e = d by omega]; exact hnd)
      rw [show d + 1 + r + 1 = d + (r + 1) + 1 by omega] at this
      exact ⟨fun hp => Rch.tr step (this.1 hp), fun hp => by
        obtain ⟨d', r', h1, h2, h3, h4⟩ := this.2 hp
        exact ⟨d', r', h1, h2, h3, Rch.tr step h4⟩⟩
    · have h2 : (r + 1) % d + 1 = d := by omega
      have hdv : (d + (r + 1) + 1) % d = 0 := by rw [Nat.add_assoc, add_mod_self_left', ms.2 h2]
      rw [show (r + 1) % d = d - 1 by omega] at walk
      refine ⟨fun hp => absurd hdv (hp.2 d (by omega) (by omega)),
        fun _ => ⟨d, r + 2, by omega, hd, by omega, walk⟩⟩

/-! ## the rebuild -/

/-- left of the R hole after a rebuild: R's cell 0, the separator, D = 3 with its hole, X -/
def YR (X : Strm) : Strm := true ::: F ::: F ::: ones 3 (F ::: true ::: F ::: F ::: X)

/-- the end of the rebuild (also used for a new k): from D's cell 2 (D hole at cell 1) with
`n + 7` ones to the end: D := 3, separator, R with its hole at cell 1; then to the loop -/
theorem rtail (X : Strm) (n : Nat) :
    Rch ⟨c5, F ::: true ::: F ::: F ::: X, ones (n + 7) blank⟩ (cfgL s1 (ones n (F ::: YR X)) blank) := by
  gR; gR; gR; gR; gR; gR; gR
  sRn n; refine blankR ?_; gL
  rw [cons_blank]; fin

/-- the mod walk found a divisor `d` of `P = d + r`: rebuild D := 3 and R := P - 1 cells,
R hole at cell 1, and go to the loop -/
theorem comp_end (X : Strm) (d r : Nat) (hd : 3 ≤ d) (hr : 1 ≤ r) :
    Rch (MW X d r (d - 1) r) (cfgL s1 (ones (d + r - 3) (F ::: YR X)) blank) := by
  obtain ⟨b, rfl⟩ : ∃ b, r = b + 1 := ⟨r - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold MW
  rw [show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show b + 1 + 1 - (b + 1) = 1 by omega]
  refine Rch.tr (Dma.toDW.wrap (c + 1) (F ::: X) _) ?_
  refine Rch.tr (PPR.find2 (c + 1) b _ blank) ?_
  gL; gR; gR; refine blankR ?_; gL
  refine Rch.tr (PPK.find2 (b + 3) c _ _) ?_
  gL; gR; gR; gR
  sRn (c + 1); gR; gR; sRn (b + 3); gL
  show Rch (cfgL c4 (ones (b + 3) (ones 2 (ones (c + 1) (F ::: true ::: F ::: F ::: X))))
    (F ::: blank)) _
  rw [ones_add, ones_add]
  sLn (b + 3 + 2 + (c + 1)); gR
  rw [cons_blank, show c + 1 + (b + 1) - 3 = b + c - 1 by omega,
    show b + 3 + 2 + (c + 1) = b + c - 1 + 7 by omega]
  exact rtail X (b + c - 1)

/-! ## the loop -/

/-- one cell of X (left of the head) moves to X' (the separator moves left) and one more cell
is appended to T -/
theorem loop_tail (Y : Strm) (m b c : Nat) :
    Rch ⟨s4, F ::: ones m (F ::: Y), F ::: F ::: ones b (F ::: F ::: ones c blank)⟩
      (cfgL s1 (ones m (F ::: Y)) (F ::: F ::: ones (b + 1) (F ::: F ::: ones (c + 1) blank))) := by
  gR; gR; sRn b; gR; gR; sRn c; refine blankR ?_; gL
  rw [show ones b (true ::: F ::: F ::: ones m (F ::: Y)) =
    ones (b + 1) (F ::: F ::: ones m (F ::: Y)) from (ones_succ' b _).symm]
  sLn c; gL; gL; sLn (b + 1); gL; gL
  rw [ones_cons_blank]; fin

theorem loop_step (Y : Strm) (m b c : Nat) :
    Rch (cfgL s1 (ones (m + 1) (F ::: Y)) (F ::: F ::: ones b (F ::: F ::: ones c blank)))
      (cfgL s1 (ones m (F ::: Y)) (F ::: F ::: ones (b + 1) (F ::: F ::: ones (c + 1) blank))) := by
  gR; exact loop_tail Y m b c

/-- the loop: X (`m` cells left of the head, then a 0) moves to X' and is copied to T -/
theorem loop (Y : Strm) : ∀ m b c,
    Rch (cfgL s1 (ones m (F ::: Y)) (F ::: F ::: ones b (F ::: F ::: ones c blank)))
      (cfgL t1 Y (F ::: F ::: F ::: ones (b + m) (F ::: F ::: ones (c + m) blank)))
  | 0, b, c => by gL; fin
  | m + 1, b, c => by
      refine Rch.tr (loop_step Y m b c) ?_
      rw [show b + (m + 1) = b + 1 + m by omega, show c + (m + 1) = c + 1 + m by omega]
      exact loop Y m (b + 1) (c + 1)

/-- the loop from a block followed by blank -/
theorem loop0 (Y : Strm) (m : Nat) :
    Rch (cfgL s1 (ones m (F ::: Y)) blank)
      (cfgL t1 Y (F ::: F ::: F ::: ones m (F ::: F ::: ones m blank))) := by
  have := loop Y m 0 0
  simp only [Nat.zero_add, ones_zero, cons_blank] at this
  exact this

/-- X was R (stopped at its hole): fill the gap and the X'/T separator, then to the D hole -/
theorem dfin (X : Strm) (m : Nat) :
    Rch (cfgL t1 (YR X) (F ::: F ::: F ::: ones m (F ::: F ::: ones m blank))) (MW X 3 (2 * m + 4) 0 1) := by
  unfold YR MW
  gR; gR; gR; gR; sRn m; gR; gL
  show Rch (cfgL a6 (true ::: ones m (ones 2 (F ::: true ::: F ::: F ::: ones 3 (F ::: true ::: F ::: F ::: X))))
    (true ::: ones m blank)) _
  rw [ones_add, ← ones_succ, show m + 2 + 1 = m + 3 by omega]
  sLn (m + 3); gL
  refine Rch.tr (PPM.find2 1 2 _ _) ?_
  gR
  rw [show ones (2 * m + 4 + 1 - 1) blank = ones (m + 3) (ones (m + 1) blank) by
    rw [ones_add, show m + 3 + (m + 1) = 2 * m + 4 + 1 - 1 by omega]]
  fin

/-- P is prime: wipe D and R, back to K's last cell -/
theorem wipe (X : Strm) (d : Nat) : Rch (P6 X d) (cfgL s1 X blank) := by
  unfold P6
  refine blankR ?_; gL
  eLn 2; gL; gL; eLn d; gL; gL; gL; gL
  simp only [cons_blank, zeros_blank]; fin

end TM.Riesel
