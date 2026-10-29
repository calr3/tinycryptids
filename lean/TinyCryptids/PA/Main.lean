import TinyCryptids.PA.Boot2

/-!
# The PA machine halts iff T proves `v0 ∈ v0`

T is Tarski's system S2 with Friedman's set existence scheme (`TinyCryptids.Wff.Provable`);
it is equiconsistent with Peano arithmetic and proves `¬ v0 ∈ v0`, so the machine halts iff PA
is inconsistent.

The machine is the one TMBuilder compiles from the program's decision DAG (`delta dag 0`,
310 states; `M309.lean` merges two equal states).  The boot builds the register file
(`boot`); from there each pass through main is one iteration of the proof search
(`from_main`), which keeps `v0 ∈ v0` at some point iff T proves it (`search_iff`).
-/

namespace TM.PA

open TinyCryptids

theorem replicate_add (a b : Nat) : List.replicate (a + b) (0 : Nat) = List.replicate a 0 ++ List.replicate b 0 := by
  induction a with
  | zero => simp
  | succ a ih => rw [Nat.succ_add, List.replicate_succ, ih]; rfl

theorem start_main : mainCfg σ0 0 0 0 1899 = atNode G 0 [] false (List.replicate 1909 0) := by
  unfold mainCfg rsOf
  rw [show List.replicate 1909 0 = List.replicate 10 0 ++ List.replicate 1899 0 from replicate_add 10 1899]
  rfl

theorem halts_iff : Halts (delta dag 0) start ↔ Wff.Provable (Wff.el 0 0) := by
  have hb : Rch dag start (mainCfg σ0 0 0 0 1899) := by rw [start_main]; exact boot
  exact (Sys.Reach.halts_iff hb).trans (from_main 1899).1

/-- when T proves `v0 ∈ v0`, the machine reaches the state `halt` -/
theorem haltAt_of (h : Wff.Provable (Wff.el 0 0)) : ∃ L R, Reach (delta dag 0) start ⟨.halt, L, R⟩ := by
  have hb : Rch dag start (mainCfg σ0 0 0 0 1899) := by rw [start_main]; exact boot
  obtain ⟨L, R, hr⟩ := (from_main 1899).2 h
  exact ⟨L, R, Rch.tr hb hr⟩

end TM.PA
