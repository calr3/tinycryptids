import TinyCryptids.ErdosStraus.Walk

/-!
# The n step and the seed

After a hit (`D`'s hole home): erase `M`, `K`, `D`, `P`; `N` one cell longer; `R` absorbs `A`
and the separator (`R += a + 2`, `2n + 5` cells), `A := 1` two cells further left; `R`'s hole on
its last-but-one cell; `M = 1`, `K = 1111`; back to `N`'s cell 0: the x step for `n + 1`, `x = 1`.
-/

namespace TM.ErdosStraus

open St

local notation "F" => false
local notation "T" => true

theorem Fz (k : Nat) (X : Strm) : F ::: zeros k X = zeros (k + 1) X := rfl
theorem zF (k : Nat) (X : Strm) : zeros k (F ::: X) = zeros (k + 1) X := (zeros_succ' k X).symm

macro "eRn" n:term : tactic => `(tactic| refine Rch.tr (eraseR (δ := delta) (by rfl) $n _ _) ?_)

/-- from `N`'s last cell (the right of `N` blank): `N += 1`, `R` absorbs `A`, ... -/
theorem nstep_tail (n a : Nat) (ha : 1 ≤ a) (h2 : a ≤ 2 * n) :
    Rch (cfgL er5 (LN n a) blank) (G (Ld (n + 1) 0) (n + 1) 0) := by
  unfold LN Lb
  gR; refine blankR ?_; gL; sLn (n + 1); gL; gL; sLn (2 * n + 3 - a); gL; gL; sLn (a + 1)
  refine blankL ?_; gL
  show Rch ⟨nr5, blank, F ::: F ::: ones (a + 1) (T ::: T ::: ones (2 * n + 3 - a) (F ::: F :::
    ones (n + 1) (T ::: blank)))⟩ _
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨R', hR⟩ : ∃ R', 2 * n + 3 - (a' + 1) = R' + 2 := ⟨2 * n - a', by omega⟩
  rw [hR]
  gR; gR; gR
  rw [← ones_succ' (a' + 1), ← ones_succ' (a' + 1 + 1), ones_add]
  sRn (a' + 1 + 1 + 1 + (R' + 2)); gL; gL; gR; gR; gR; gR; gR; sRn n; gR
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
  refine blankR ?_; gR; refine blankR ?_; gL
  gL; gL; gL; gL; gL; gL; gL; gL; gL; sLn n; gL; gR
  have e : (a' + 1 + 1 + 1).add (R' + 1) = (2 * (n + 1) + 1) + 1 := by
    show a' + 1 + 1 + 1 + (R' + 1) = _; omega
  rw [e, ← ones_succ' n]
  unfold G Ld
  fin

/-- a hit: on to the x step of `n + 1` -/
theorem nstep (n a m e d r : Nat) (ha : 1 ≤ a) (h2 : a ≤ 2 * n) (hm : 1 ≤ m) (hd : 1 ≤ d) (he : 1 ≤ e) :
    Rch (E3 (KY n a m e) d r d) (G (Ld (n + 1) 0) (n + 1) 0) := by
  unfold E3 KY
  rw [Nat.sub_self]
  gL; sLn d; gL; gL; sLn e; gL; gL; gL; gL; sLn (m + 1); gR
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  eRn (m + 1); gR; gR; gR; gR; gR; eRn e'; gR; gR; gR; eRn d'; gR; gR; gR; gR; eRn (r + 1)
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL er5 (F ::: F ::: F ::: zeros (r + 1) (F ::: F ::: F ::: F ::: zeros d' (F ::: F ::: F :::
    zeros e' (F ::: F ::: F ::: F ::: F ::: zeros (m + 1) (F ::: tl (F ::: F ::: LN n a)))))) _) _
  simp only [tl_cons, Fz, zF, zeros_add]
  zLn _
  simp only [cons_blank, zeros_blank]
  exact nstep_tail n a ha h2

/-- the seed writes the end of a solved round `n = 1` (`a = 1`): `A 00 R 00 N` -/
theorem seed_reach : Rch start (cfgL er5 (LN 1 1) blank) := by
  unfold start LN Lb
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; refine blankR ?_; gL
  rw [cons_blank]
  fin

end TM.ErdosStraus
