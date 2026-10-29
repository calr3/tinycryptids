import TinyCryptids.PAK.Frame
import TinyCryptids.PAK.Step
import TinyCryptids.PAK.Boot

/-!
# From the blank tape: the machine halts iff T proves `v0 ∈ v0`

At the start of each pass through main (`mainCfg`) the tape holds the registers of the
iteration (`aOf`: `prooflist`, `nextproof`, `topwff`, `wffstack` of `S`, `param2` zero, the
scratch registers zero, leftovers in `axiomcode`, `param1`, `param3`), with nine or ten
registers present (`LV`).  `pass`: main computes `iterK` (`k0_emb`, `k0_eq`), which is one
`stepK` (`iterK_eq`), and halts iff the kept theorem is 1.  The first pass starts from the
blank tape: the boot and its first operations by computation (`boot_reach`), then the rest of
main's second chunk and main from its third (`first_pass`).
-/

namespace TMK.PA

open TinyCryptids
open TM (Dir)
open TM.PA (R A S enc)

set_option maxRecDepth 10000
set_option linter.constructorNameAsVariable false

/-- the registers at the start of an iteration with carried-over registers `σ` -/
def aOf (σ : S) (ac p1 p3 : Nat) : A := ⟨σ.pl, σ.np, σ.top, ac, p1, 0, p3, σ.ws, []⟩

/-- main starts with registers `σ` -/
def mainCfg (z : Strm) (σ : S) (ac p1 p3 n : Nat) : Cfg St := atNode z [] 0 0 (aOf σ ac p1 p3).emb n

theorem LV_aOf (σ : S) (ac p1 p3 n : Nat) (h : n = 9 ∨ n = 10) : LV (aOf σ ac p1 p3).emb n := by
  rcases h with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr rfl

/-- a run of slots from `j` that ends with `exit` is the node's run from `j` -/
theorem run_from {i j : Nat} (hi : i < NN) {l : List SS} (hm : SMatch i j l) {s t : R} {o : Res}
    (h : runS l s = (.exit o, t)) : Run i j s o t := by
  have := runS_sound hi l j hm s
  rw [h] at this
  exact this

/-- main's run on the registers of an iteration -/
theorem e0' (a : A) : Ex 0 a.emb (if (k0 a).top = 1 then .halt else .brk 0) (A.haltT (k0 a)).emb := by
  have h := e0 a.emb
  rw [k0_emb a] at h
  dsimp only at h
  exact h

/-- after main, `adv` on the blank left of cell 0 enters main again -/
theorem restart (z : Strm) (t : R) (n : Nat) :
    Reach1 delta (endCfg (E 0) z [] t n) (atNode z [] 0 0 t n) := by
  show Reach1 delta ⟨.adv, z, 0 ∷ 1 ∷ rgt 0 t n⟩ ⟨.node 0, 0 ∷ z, tl (0 ∷ 1 ∷ rgt 0 t n)⟩
  exact stepR1 rfl

/-- the end of an iteration: registers of the next one, or halt -/
theorem next_of (σ : S) (ac p1 p3 : Nat) (z : Strm) {c0 : Cfg St}
    (hE : Ends z [] c0 (if (k0 (aOf σ ac p1 p3)).top = 1 then .halt else .brk 0)
      (A.haltT (k0 (aOf σ ac p1 p3))).emb) :
    ((stepK σ).top ≠ 1 → ∃ ac' p1' p3' n', (n' = 9 ∨ n' = 10) ∧
        Reach1 delta c0 (mainCfg z (stepK σ) ac' p1' p3' n')) ∧
      ((stepK σ).top = 1 → ∃ c : Cfg St, Reach delta c0 c ∧ c.q = .halt) := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := iterK_eq (aOf σ ac p1 p3) rfl rfl
  rw [k0_eq] at hE
  have j1 : (iterK (aOf σ ac p1 p3)).pl = (stepK σ).pl := i1
  have j2 : (iterK (aOf σ ac p1 p3)).np = (stepK σ).np := i2
  have j3 : (iterK (aOf σ ac p1 p3)).top = (stepK σ).top := i3
  have j4 : enc (iterK (aOf σ ac p1 p3)).base (iterK (aOf σ ac p1 p3)).stk = (stepK σ).ws := i4
  constructor
  · intro hne
    have ht : (iterK (aOf σ ac p1 p3)).top ≠ 1 := by rw [j3]; exact hne
    rw [if_neg ht] at hE
    obtain ⟨n', hn', hr⟩ := hE
    have e : (A.haltT (iterK (aOf σ ac p1 p3))).emb =
        (aOf (stepK σ) (iterK (aOf σ ac p1 p3)).ac (iterK (aOf σ ac p1 p3)).p1 (iterK (aOf σ ac p1 p3)).p3).emb := by
      unfold A.haltT; rw [if_neg ht]
      generalize iterK (aOf σ ac p1 p3) = b at j1 j2 j3 j4 i5 ⊢
      simp only [A.emb, aOf, enc]
      rw [j1, j2, j3, j4, i5]
    rw [e] at hr hn'
    refine ⟨_, _, _, n', ?_, Sys.Reach.trans_reach1 hr (restart z _ n')⟩
    rcases hn' with ⟨h, _⟩ | h
    · exact Or.inl h
    · exact Or.inr h
  · intro heq
    have ht : (iterK (aOf σ ac p1 p3)).top = 1 := by rw [j3]; exact heq
    rw [if_pos ht] at hE
    exact hE

/-- one pass through main: on to the next iteration, or halt -/
theorem pass (z : Strm) (σ : S) (ac p1 p3 n : Nat) (hn : n = 9 ∨ n = 10) :
    ((stepK σ).top ≠ 1 → ∃ ac' p1' p3' n', (n' = 9 ∨ n' = 10) ∧
        Reach1 delta (mainCfg z σ ac p1 p3 n) (mainCfg z (stepK σ) ac' p1' p3' n')) ∧
      ((stepK σ).top = 1 → ∃ c : Cfg St, Reach delta (mainCfg z σ ac p1 p3 n) c ∧ c.q = .halt) := by
  have hs := sim (e0' (aOf σ ac p1 p3)) z [] 0 n (by decide) rfl (by decide) (by decide)
    (LV_aOf σ ac p1 p3 n hn)
  exact next_of σ ac p1 p3 z hs

/-! ## the first pass -/

/-- the registers where the computation of `Boot.lean` ends, from main's first registers `a` -/
def bmOf (a : A) : A := A.push (A.decP3 (A.decP2 (k1 a)))

/-- from main's second chunk at slot 5 (where the computation ends) to the end of the pass -/
theorem first_pass_gen (a : A) (hp2 : (bmOf a).p2 = 0) {c0 : Cfg St}
    (hb : Reach delta c0 (atNode blank [(0, 1)] 17 5 (bmOf a).emb 9)) :
    Ends blank [] c0 (if (k0 a).top = 1 then .halt else .brk 0) (A.haltT (k0 a)).emb := by
  -- the rest of main's second chunk
  have h17 : Run 17 5 (bmOf a).emb (.brk 0) (k17 (k1 a)).emb := by
    refine run_from (i := 17) (j := 5) (l := [.ch 26 d26, .ch 28 d28, .ch 26 d26]) (by decide)
      ⟨rfl, e26, rfl, e28, rfl, e26, rfl⟩ ?_
    rw [run_ch (par1_emb (bmOf a)), run_ch (k28_emb _), run_ch (par1_emb _)]
    rfl
  have hw : WalkOK [(0, 1)] 17 := ⟨by decide, by decide, rfl⟩
  obtain ⟨n1, hn1, hr1⟩ := sim h17 blank [(0, 1)] 5 9 (by decide) hw (by decide) (by decide) (Or.inl ⟨rfl, hp2⟩)
  -- main advances to its third chunk
  have hadv : Reach delta (endCfg (E 0) blank [(0, 1)] (k17 (k1 a)).emb n1)
      (atNode blank [] 0 2 (k17 (k1 a)).emb n1) := by
    have h1 := stepUp (z := blank) (P := []) (Y := 1 ∷ rgt 1 (k17 (k1 a)).emb n1)
      (adv_tr 1 (by decide) (by decide))
    have h2 := dispatch (z := blank) (P := []) (i := 0) rfl (sy 2 ∷ 1 ∷ rgt 1 (k17 (k1 a)).emb n1)
    have e : atNode blank [] 0 2 (k17 (k1 a)).emb n1 =
        ⟨.node 0, pcL [] blank, sy 2 ∷ 1 ∷ rgt 1 (k17 (k1 a)).emb n1⟩ := by
      simp only [atNode, List.length_nil]
      rw [rgt_succ 0 _ _ (by decide)]
    rw [e]
    exact Reach.trans _ h1 h2
  -- main from its third chunk
  have h0 : Run 0 2 (k17 (k1 a)).emb (if (k0 a).top = 1 then .halt else .brk 0) (A.haltT (k0 a)).emb := by
    refine run_from (i := 0) (j := 2)
      (l := [.ch 37 d37, .ch 51 d51, .ch 59 d59, .ch 60 d60, .ch 62 d62, .ch 63 d63]) (by decide)
      ⟨rfl, e37, rfl, e51, rfl, e59, rfl, e60, rfl, e62, rfl, e63, rfl⟩ ?_
    rw [run_ch (k37_emb _), run_ch (k51_emb _), run_ch (k59_emb _), run_ch (k60_emb _), run_ch (k62_emb _),
      run_last_h (k63_emb _)]
    rfl
  have hs := sim h0 blank [] 2 n1 (by decide) rfl (by decide) (by decide) hn1
  exact Ends.pre (Reach.trans _ hb (Reach.trans _ hr1 hadv)) hs

def a0 : A := aOf σ0 0 0 0

theorem bm_list : (mlist (bmOf a0).emb).take 9 = [0, 1, 0, 0, 0, 0, 0, 0, 0] := by decide

theorem boot_eq : bootEnd.toCfg = atNode blank [(0, 1)] 17 5 (bmOf a0).emb 9 := by
  have e1 : [6, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 9, 9, 1, 9, 9, 9, 9, 9, 9, 9, 0] =
      [6] ++ (List.replicate (G - 1 - 1) 1 ++ regs ((mlist (bmOf a0).emb).take 9)) ++ [0] := by
    rw [bm_list]; rfl
  simp only [LCfg.toCfg, bootEnd, atNode, pcL, rgt, rfile, List.length_singleton]
  rw [e1, lst_append, lst_append]
  simp only [lst_cons, lst_nil, cons_blank, List.map_cons, List.map_nil, sy]

/-- the first pass, from the blank tape -/
theorem first_pass :
    ((stepK σ0).top ≠ 1 → ∃ ac' p1' p3' n', (n' = 9 ∨ n' = 10) ∧
        Reach delta start (mainCfg blank (stepK σ0) ac' p1' p3' n')) ∧
      ((stepK σ0).top = 1 → ∃ c : Cfg St, Reach delta start c ∧ c.q = .halt) := by
  have hb : Reach delta start (atNode blank [(0, 1)] 17 5 (bmOf a0).emb 9) := by
    rw [← boot_eq]; exact boot_reach
  have hn := next_of σ0 0 0 0 blank (first_pass_gen a0 (by decide) hb)
  exact ⟨fun h => let ⟨a, b, c, d, e, f⟩ := hn.1 h; ⟨a, b, c, d, e, f.reach⟩, hn.2⟩

theorem iterS_one : iterS 1 σ0 = stepK σ0 := by
  rw [iterS_succ 0 σ0]; rfl

/-! ## the main theorem for the compiled machine -/

/-- the iterations after the first, while none keeps 1 -/
theorem reach_iter (k : Nat) (hk : ∀ j ≤ k, (iterS (j + 1) σ0).top ≠ 1) :
    ∃ ac p1 p3 n, (n = 9 ∨ n = 10) ∧ Reach delta start (mainCfg blank (iterS (k + 1) σ0) ac p1 p3 n) := by
  induction k with
  | zero =>
    have h := hk 0 (Nat.le_refl 0)
    rw [iterS_one] at h ⊢
    exact first_pass.1 h
  | succ k ih =>
    obtain ⟨ac, p1, p3, n, hn, h⟩ := ih (fun j hj => hk j (by omega))
    have hne : (stepK (iterS (k + 1) σ0)).top ≠ 1 := by
      have := hk (k + 1) (Nat.le_refl _); rwa [iterS_succ] at this
    obtain ⟨ac', p1', p3', n', hn', h'⟩ := (pass blank (iterS (k + 1) σ0) ac p1 p3 n hn).1 hne
    refine ⟨ac', p1', p3', n', hn', Reach.trans _ h ?_⟩
    rw [iterS_succ (k + 1) σ0]
    exact h'.reach

/-- when T proves `v0 ∈ v0`, the machine reaches the state `halt` -/
theorem haltAt_of (h : Wff.Provable (Wff.el 0 0)) : ∃ c : Cfg St, Reach delta start c ∧ c.q = .halt := by
  obtain ⟨k, hk⟩ := search_iff.2 h
  induction k using Nat.strongRecOn with
  | _ k ih =>
    by_cases hmin : ∃ j < k, (iterS (j + 1) σ0).top = 1
    · obtain ⟨j, hj, hj1⟩ := hmin; exact ih j hj hj1
    · have hall : ∀ j < k, (iterS (j + 1) σ0).top ≠ 1 := fun j hj h => hmin ⟨j, hj, h⟩
      cases k with
      | zero =>
        rw [iterS_one] at hk
        exact first_pass.2 hk
      | succ k =>
        obtain ⟨ac, p1, p3, n, hn, hr⟩ := reach_iter k (fun j hj => hall j (by omega))
        rw [iterS_succ (k + 1) σ0] at hk
        obtain ⟨c, hc, hq⟩ := (pass blank (iterS (k + 1) σ0) ac p1 p3 n hn).2 hk
        exact ⟨c, Reach.trans _ hr hc, hq⟩

theorem halts_iff : Halts delta start ↔ Wff.Provable (Wff.el 0 0) := by
  constructor
  · intro hh
    apply Classical.byContradiction
    intro hno
    have hall : ∀ k, (iterS (k + 1) σ0).top ≠ 1 := fun k h => hno (search_iff.1 ⟨k, h⟩)
    obtain ⟨ac, p1, p3, n, hn, hr⟩ := reach_iter 0 (fun j _ => hall j)
    have hP : ∀ c, (∃ k ac p1 p3 n, (n = 9 ∨ n = 10) ∧ c = mainCfg blank (iterS (k + 1) σ0) ac p1 p3 n) →
        ∃ c', (∃ k ac p1 p3 n, (n = 9 ∨ n = 10) ∧ c' = mainCfg blank (iterS (k + 1) σ0) ac p1 p3 n) ∧
          Reach1 delta c c' := by
      rintro c ⟨k, ac, p1, p3, n, hn, rfl⟩
      have hne : (stepK (iterS (k + 1) σ0)).top ≠ 1 := by rw [← iterS_succ]; exact hall (k + 1)
      obtain ⟨ac', p1', p3', n', hn', h'⟩ := (pass blank (iterS (k + 1) σ0) ac p1 p3 n hn).1 hne
      exact ⟨_, ⟨k + 1, ac', p1', p3', n', hn', by rw [iterS_succ (k + 1) σ0]⟩, h'⟩
    have := Sys.not_halts_of_progress _ hP _ ⟨0, ac, p1, p3, n, hn, rfl⟩
    exact this ((Sys.Reach.halts_iff hr).1 hh)
  · intro hp
    obtain ⟨c, hc, hq⟩ := haltAt_of hp
    refine Sys.Reach.halts hc (halts_of_step delta ?_)
    obtain ⟨q, L, R⟩ := c
    simp only at hq
    subst hq
    simp [step, delta, delta0]

end TMK.PA
