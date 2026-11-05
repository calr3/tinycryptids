import TinyCryptids.LehmerTau.RStep

/-!
# The start of the L phase

At `i = n − 1` Re has two cells: E becomes the dummy E' (4 cells), Re' (1 cell), S0 moves one
cell right, Rd gains a cell (`i = n`); at the far left M is created (one cell, `M = 0`), K252
is switched off, and the head finds D's hole.

The constants are `kA = 65`, `kB = 252`, `kC = 691`, kept as variables.
-/

namespace TM.LehmerTau
open St

local notation "F" => false

/-- the left part in the R phase: K691 and K252 active, K65 at rest -/
def KR (kA kB kC : Nat) : List KB := [.dg kC 1, .dg kB 1, .pl (kA + 2)]

/-- the left part in the L phase: L1 (K691 active) -/
def KL1 (kA kB kC p : Nat) : List KB := [.dg kC 1, .pl (kB + 2), .pl (kA + 2), .pl (p + 1)]

/-- right of Rd in the L phase: E' (4 cells), Re' (1 cell), S0 -/
def BL : Strm := ones 4 (F ::: F ::: ones 1 (F ::: F ::: ones 2 blank))

theorem FMK : FarL delta MK1 MK2 MK3 := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem c12_LS (a : Nat) (K : List KB) (hk : ∀ b ∈ K, b.ok) : Clean12 (lpR K ++ rep (a + 1)) := by
  have h := c12_LK a K hk
  unfold LK at h
  exact Clean12.suffix (l := [F, F]) (by simpa using h)

/-- far left over `LS a K`: on the third blank -/
theorem farL_LS {p1 p2 p3 : St} (P : FarL delta p1 p2 p3) (a : Nat) (K : List KB) (hk : ∀ b ∈ K, b.ok) (R : Strm) :
    Rch (cfgL p1 (LS a K) R) (cfgL p3 blank (F ::: F ::: app (rep (a + 1) ++ (lpR K).reverse) R)) := by
  have := P.go (c12_LS a K hk) R
  simpa [List.reverse_append, rep_rev] using this

theorem PH2a : ParserR delta H2a1 H2a2 := ⟨rfl, rfl, rfl⟩
theorem PH2b : ParserR delta H2b1 H2b2 := ⟨rfl, rfl, rfl⟩

/-- **The start of the L phase** (`j = 1`) -/
theorem ri_last (kA kB kC : Nat) (hB : 1 ≤ kB) (hC : 1 ≤ kC) (p i : Nat) :
    Rch ⟨UK1, F ::: F ::: LS p (.pl (i + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 :: KR kA kB kC), BD 1⟩
      (DV (LS 0 (.pl 1 :: .pl 13 :: KL1 kA kB kC p)) BL 1 i) := by
  obtain ⟨c, rfl⟩ : ∃ c, kC = c + 1 := ⟨kC - 1, by omega⟩
  unfold BD
  gR; gR; gR; gR; gR; gR; gR; gR; gR; gR; gR
  gL0; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL; gL
  have hk : ∀ b ∈ (.pl (i + 1) :: .dg 1 1 :: .pl 1 :: .pl 13 :: KR kA kB (c + 1) : List KB), b.ok := by
    intro b hb; simp [KR] at hb; rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [KB.ok] <;> omega
  refine Rch.tr (farL_LS FMK p _ hk _) ?_
  simp only [KR, lpR, KB.w, List.reverse_append, List.reverse_cons, List.reverse_nil, rep_rev, List.nil_append,
    List.append_assoc, List.singleton_append, List.cons_append, app_append, app_rep, app_cons, rep, app_replicate, List.reverse_replicate,
    List.reverse_reverse, Nat.add_sub_cancel]
  gR0; gR; gR; sRn (p + 1); gR; gR; sRn (kA + 2); gR; gR; gR; gR
  refine Rch.tr (PH2a.find2 kB 0 _ _) ?_
  gR; sRn c; gR; gR; sRn 13; gR; gR; gR; gR; gR; gR; gR; gL; gL; gL
  unfold DV BL RB KL1
  simp only [LS_pl, LS_dg1, LS, lpR, KB.w, List.nil_append, app_append, app_rep, rep, app_replicate, List.reverse_replicate,
    List.reverse_cons, List.reverse_nil, List.singleton_append, List.cons_append, app_cons, app_nil, List.reverse_append,
    ones_cons_true, Nat.add_sub_cancel]
  fin

end TM.LehmerTau
