import TinyCryptids.PerfectCuboid.Check

/-!
# One block of the queue: set up, check the sum so far, process

`n5` reads the first cell of the next block. A real block Y (`L ≥ 4` cells) gets `h` and `m`
and the head goes to S: the sum of the blocks before Y is checked (`cktick` / `ckabort`),
then Y is processed (`block`). Z (three cells) gets only `h`, so it adds nothing.
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

/-- W after the tick; S after the tick (reset when W wraps) -/
def rs (W : Nat) (s : Nat × Nat) : Nat × Nat := if W = 2 then (0, 0) else s

theorem rs_valid (W : Nat) (s : Nat × Nat) (hs : Valid s) : Valid (rs W s) := by
  unfold rs; split
  · show 0 ≤ 2 * 0; omega
  · exact hs

/-- set up a real block: `h` on its last cell, `m` on cell `L - 3`, then to S -/
theorem init_real (L : Nat) (hL : 4 ≤ L) (LL Rr : Strm) :
    Rch ⟨n5, LL, ones L (F ::: Rr)⟩ ⟨PK1, F ::: T ::: F ::: ones (L - 3) LL, F ::: Rr⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 4 := ⟨L - 4, by omega⟩
  rw [show n + 4 = 4 + n by omega, ← ones_add]
  show Rch ⟨n5, LL, T ::: T ::: T ::: T ::: ones n (F ::: Rr)⟩ _
  gR; gR; gR; gR
  sr n
  rw [show T ::: T ::: T ::: T ::: LL = ones 4 LL from rfl, ones_add]
  rw [show n + 4 = n + 3 + 1 by omega, ones_succ]
  gl
  rw [ones_succ]
  gl
  rw [ones_succ]
  gl; gR; gR; gR
  apply rch_eq _ rfl
  streq

theorem init_Z (LL Rr : Strm) :
    Rch ⟨n5, LL, T ::: T ::: T ::: F ::: Rr⟩ ⟨PK1, F ::: T ::: T ::: LL, F ::: Rr⟩ := by
  gR; gR; gR; gl; gR; fin

/-- a real block whose check passes: set up, tick, process -/
theorem step_real (L : Nat) (hL : 4 ≤ L) (Lx : Strm) (u : List Bool) (hu : Ev u) (W : Nat)
    (hW : W ≤ 2) (s : Nat × Nat) (hs : Valid s) (h0 : s.2 = 0) :
    Rch ⟨n5, F ::: F ::: Lx, ones L (app ([F, F] ++ u ++ gapL W) (Sb s))⟩
      ⟨n5, F ::: F ::: ones L (F ::: F ::: Lx),
        app (u ++ gapL (tk W)) (Sb (advN (v L * v L) (rs W s)))⟩ := by
  have e : app ([F, F] ++ u ++ gapL W) (Sb s) = F ::: app (F :: (u ++ gapL W)) (Sb s) := by
    simp [app_append]
  rw [e]
  refine Rch.tr (init_real L hL _ _) ?_
  have t := cktick (F :: F :: u) (Ev.zz hu) (F ::: ones (L - 3) (F ::: F ::: Lx)) W hW s h0
  simp only [app_cons, List.cons_append] at t
  refine Rch.tr t ?_
  have b := block L hL Lx (u ++ [F, F] ++ gm (tk W)) (Ev.append (Ev.append hu (Ev.zz Ev.nil))
    (gm_ev _)) (rs W s) (rs_valid W s hs)
  unfold Xw RX at b
  simp only [Nat.mul_zero, Nat.sub_self, ones_zero, List.append_assoc, List.cons_append,
    List.nil_append] at b
  unfold rs at b
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr b ?_)
  · simp [gapL, app_append]
  · apply rch_eq rfl
    simp [gapL, app_append, rs]

/-- Z, whose check passes: set up, tick, nothing to add, to G's cell 3 -/
theorem step_Z (Lx : Strm) (W : Nat) (hW : W ≤ 2) (s : Nat × Nat) (h0 : s.2 = 0) :
    Rch ⟨n5, F ::: F ::: Lx, T ::: T ::: T ::: app (gapL W) (Sb s)⟩
      ⟨n5, F ::: F ::: ones 3 (F ::: F ::: Lx), app (gm (tk W) ++ [F, F]) (Sb (rs W s))⟩ := by
  have e : app (gapL W) (Sb s) = F ::: app (F :: (gm W ++ [F, F])) (Sb s) := by
    simp [gapL, app_append]
  rw [e]
  refine Rch.tr (init_Z _ _) ?_
  have t := cktick [] Ev.nil (T ::: F ::: F ::: Lx) W hW s h0
  simp only [List.nil_append, gapL] at t
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr t ?_)
  · simp [app_append]
  · have d := xe_done 3 (by omega) Lx (gm (tk W)) (rs W s)
    unfold XE RX at d
    unfold rs at d
    refine Rch.tr (rch_eq rfl ?_) (Rch.tr d ?_)
    · simp [app_append]
    · apply rch_eq rfl
      simp [app_append, rs]

end TM.PerfectCuboid
