import TinyCryptids.PA.DagCheck
import TinyCryptids.PA.Search

/-!
# From the start of main: the machine halts iff T proves `v0 ∈ v0`

At the start of each pass through main the tape holds the registers of the iteration
(`aOf`: `prooflist`, `nextproof`, `topwff`, `wffstack` of `S`, `param2` zero, the scratch
registers zero, and leftovers in `axiomcode`, `param1`, `param3`).  `main_emb` and `iter_eq`
make one pass one `S.step`; the pass halts iff the kept theorem is 1 (`v0 ∈ v0`).
-/

namespace TM.PA

open N TinyCryptids

/-- the registers at the start of an iteration with carried-over registers `σ` -/
def aOf (σ : S) (ac p1 p3 : Nat) : A := ⟨σ.pl, σ.np, σ.top, ac, p1, 0, p3, σ.ws, []⟩

/-- main starts with registers `σ` -/
def mainCfg (σ : S) (ac p1 p3 e : Nat) : Cfg St := atNode G 0 [] false (rsOf (aOf σ ac p1 p3).emb e)

theorem G5 : 5 ≤ G := by decide

/-- one pass through main: on to the next iteration, or halt -/
theorem pass (σ : S) (ac p1 p3 e : Nat) :
    (σ.step.top ≠ 1 → ∃ ac' p1' p3' e', Reach1 (delta dag 0) (mainCfg σ ac p1 p3 e) (mainCfg σ.step ac' p1' p3' e')) ∧
    (σ.step.top = 1 → ∃ L R, Rch dag (mainCfg σ ac p1 p3 e) ⟨.halt, L, R⟩) := by
  unfold mainCfg
  obtain ⟨hf, hh⟩ := main_emb (aOf σ ac p1 p3)
  obtain ⟨i1, i2, i3, i4, i5⟩ := iter_eq (aOf σ ac p1 p3) rfl rfl
  have j1 : (A.iter (aOf σ ac p1 p3)).pl = σ.step.pl := i1
  have j2 : (A.iter (aOf σ ac p1 p3)).np = σ.step.np := i2
  have j3 : (A.iter (aOf σ ac p1 p3)).top = σ.step.top := i3
  have j4 : enc (A.iter (aOf σ ac p1 p3)).base (A.iter (aOf σ ac p1 p3)).stk = σ.step.ws := i4
  have hex := e0 (aOf σ ac p1 p3).emb
  rw [hf, hh] at hex
  constructor
  · intro hne
    have ht : (A.iter (aOf σ ac p1 p3)).top ≠ 1 := by rw [j3]; exact hne
    simp only [ht, decide_false, hres] at hex
    obtain ⟨e', he⟩ := main_step1 dagOK G5 (by simpa [Bool.false_eq_true] using hex) e
    refine ⟨(A.iter (aOf σ ac p1 p3)).ac, (A.iter (aOf σ ac p1 p3)).p1, (A.iter (aOf σ ac p1 p3)).p3, e', ?_⟩
    have : (A.haltT (A.iter (aOf σ ac p1 p3))).emb =
        (aOf σ.step (A.iter (aOf σ ac p1 p3)).ac (A.iter (aOf σ ac p1 p3)).p1 (A.iter (aOf σ ac p1 p3)).p3).emb := by
      unfold A.haltT; rw [if_neg ht]
      generalize A.iter (aOf σ ac p1 p3) = b at j1 j2 j3 j4 i5 ⊢
      simp only [A.emb, aOf, enc]
      rw [j1, j2, j3, j4, i5]
    rw [this] at he
    exact he
  · intro heq
    have ht : (A.iter (aOf σ ac p1 p3)).top = 1 := by rw [j3]; exact heq
    simp only [ht, decide_true, hres] at hex
    exact main_halt dagOK (by simpa using hex) e

/-- the iterations from `σ0` -/
theorem reach_iter (k : Nat) (hk : ∀ j < k, (iterS (j + 1) σ0).top ≠ 1) (e0 : Nat) :
    ∃ ac p1 p3 e, Rch dag (mainCfg σ0 0 0 0 e0) (mainCfg (iterS k σ0) ac p1 p3 e) := by
  induction k with
  | zero => exact ⟨0, 0, 0, e0, Reach.refl _ _⟩
  | succ k ih =>
    obtain ⟨ac, p1, p3, e, h⟩ := ih (fun j hj => hk j (by omega))
    have hne : (iterS k σ0).step.top ≠ 1 := by
      have := hk k (by omega)
      rwa [show k + 1 = k + 1 from rfl, iterS_add k 1, iterS, iterS] at this
    obtain ⟨ac', p1', p3', e', h'⟩ := (pass (iterS k σ0) ac p1 p3 e).1 hne
    refine ⟨ac', p1', p3', e', Rch.tr h (Reach1.reach _ ?_)⟩
    rw [iterS_add k 1]
    exact h'

theorem iterS_succ (k : Nat) (σ : S) : iterS (k + 1) σ = (iterS k σ).step := by
  rw [iterS_add k 1]; rfl

/-- from the start of main, the machine halts iff T proves `v0 ∈ v0`; when it does, it reaches
the state `halt` -/
theorem from_main (e0 : Nat) :
    (Halts (delta dag 0) (mainCfg σ0 0 0 0 e0) ↔ Wff.Provable (Wff.el 0 0)) ∧
    (Wff.Provable (Wff.el 0 0) → ∃ L R, Rch dag (mainCfg σ0 0 0 0 e0) ⟨.halt, L, R⟩) := by
  have halt_of : (∃ k, (iterS (k + 1) σ0).top = 1) → ∃ L R, Rch dag (mainCfg σ0 0 0 0 e0) ⟨.halt, L, R⟩ := by
    intro ⟨k, hk⟩
    -- the first iteration that keeps 1
    induction k using Nat.strongRecOn with
    | _ k ih =>
      by_cases hmin : ∃ j < k, (iterS (j + 1) σ0).top = 1
      · obtain ⟨j, hj, hj1⟩ := hmin; exact ih j hj hj1
      · have hall : ∀ j < k, (iterS (j + 1) σ0).top ≠ 1 := fun j hj h => hmin ⟨j, hj, h⟩
        obtain ⟨ac, p1, p3, e, h⟩ := reach_iter k hall e0
        rw [iterS_succ] at hk
        obtain ⟨L, R, h'⟩ := (pass (iterS k σ0) ac p1 p3 e).2 hk
        exact ⟨L, R, Rch.tr h h'⟩
  refine ⟨⟨fun hh => ?_, fun hp => ?_⟩, fun hp => halt_of (search_iff.2 hp)⟩
  · apply search_iff.1
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, (iterS (k + 1) σ0).top ≠ 1 := fun k h => hno ⟨k, h⟩
    refine not_halts_of_progress (δ := delta dag 0)
      (fun c => ∃ k ac p1 p3 e, c = mainCfg (iterS k σ0) ac p1 p3 e) ?_ _ ⟨0, 0, 0, 0, e0, rfl⟩ hh
    rintro c ⟨k, ac, p1, p3, e, rfl⟩
    have hne : (iterS k σ0).step.top ≠ 1 := by rw [← iterS_succ]; exact hall k
    obtain ⟨ac', p1', p3', e', h'⟩ := (pass (iterS k σ0) ac p1 p3 e).1 hne
    exact ⟨_, ⟨k + 1, ac', p1', p3', e', by rw [iterS_succ]⟩, h'⟩
  · obtain ⟨L, R, h⟩ := halt_of (search_iff.2 hp)
    exact Reach.halts _ h (halt_none (by rfl))

end TM.PA
