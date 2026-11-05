import TinyCryptids.FeitThompson.Horner

/-!
# The trial pass

The tape for the candidate `m`, its list of blocks `bs = 1 :: pl m` (`P0 = 111`, then the
primes below `m`):  `L 00 P0 00 P1 … 00 Pk 00 M` with `L = M = skp m` (hole at cell 1).
`TC m pre p post`: the trial step for the block `p` (`bs = pre ++ p :: post`), state `kn6` on
cell 1 of that block.
-/

namespace TM.FeitThompson
open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-- `00 B1 00 B2 …` for the blocks of the values `ps` -/
def seps : List Nat → List Bool
  | [] => []
  | p :: ps => F :: F :: (List.replicate (p + 2) T ++ seps ps)

theorem blk_seps (q : Nat) : ∀ qs, Blk (List.replicate (q + 2) T ++ seps qs)
  | [] => by simpa [seps] using Blk.one (q + 1)
  | q' :: qs => by
    show Blk (List.replicate (q + 1 + 1) T ++ F :: F :: (List.replicate (q' + 2) T ++ seps qs))
    exact Blk.cons (q + 1) (blk_seps q' qs)

theorem gap_seps : ∀ qs, Gap (seps qs ++ [F, F])
  | [] => Gap.sep
  | q :: qs => Or.inr ⟨_, blk_seps q qs, by simp [seps]⟩

theorem seps_append (a b : List Nat) : seps (a ++ b) = seps a ++ seps b := by
  induction a with
  | nil => rfl
  | cons p a ih => simp [seps, ih]

/-- the trial step for block `p` -/
def TC (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Cfg St :=
  ⟨kn6, T ::: app (skp m ++ seps pre ++ [F, F]).reverse blank,
    app (List.replicate (p + 1) T ++ seps post ++ [F, F] ++ skp m) blank⟩

/-- the stream left of the counter block in the trial cycle -/
theorem tc_left (m : Nat) (pre : List Nat) :
    app (skp m ++ seps pre ++ [F, F]).reverse blank =
      cyL (F ::: blank) m 1 (seps pre ++ [F, F]) := by
  simp only [cyL, skp, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, Nat.add_sub_cancel, ones_succ, ones_zero, cons_blank]

theorem trial_cyc (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch (TC m pre p post)
      ⟨if p ∣ m then kd3 else kn3, ones (p + 2) (cyL (F ::: blank) m 1 (seps pre ++ [F, F])),
        app (seps post ++ [F, F] ++ skp m) blank⟩ := by
  unfold TC
  gR
  show Rch ⟨ca2, T ::: T ::: app (skp m ++ seps pre ++ [F, F]).reverse blank,
    app (List.replicate p T ++ seps post ++ [F, F] ++ skp m) blank⟩ _
  rw [tc_left]
  obtain ⟨Rc, hRc⟩ : ∃ Rc, app (seps post ++ [F, F] ++ skp m) blank = F ::: Rc := by
    cases post <;> exact ⟨_, rfl⟩
  have h := cyc_run (gap_seps pre) blank Rc m p hm hp
  rw [← hRc] at h
  refine Rch.tr ?_ h
  unfold cyc2
  simp only [List.append_assoc, app_append, app_replicate, ones_succ]
  rw [show p + 1 - 1 = p by omega]
  fin

theorem PPX : ParserL delta PX1 PX2 := ⟨rfl, rfl, rfl⟩
theorem PPY : ParserL delta PY1 PY2 := ⟨rfl, rfl, rfl⟩

/-- the next candidate: `M` (head on its cell 3) grows by one cell, then `L` (on its left);
the trial pass starts at `P1` -/
theorem next_cand (m p1 : Nat) (rest : List Nat) (hm : 2 ≤ m) :
    Rch ⟨ms, app (skp m ++ seps (1 :: p1 :: rest) ++ [F, F] ++ [T, F, T]).reverse blank, ones (m - 1) blank⟩
      (TC (m + 1) [1] p1 rest) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  rw [show m' + 2 - 1 = m' + 1 by omega]
  sRn (m' + 1)
  refine blankR ?_
  gL
  show Rch (cfgL PX1 (ones (m' + 1) (app (skp (m' + 2) ++ seps (1 :: p1 :: rest) ++ [F, F] ++ [T, F, T]).reverse blank))
    (T ::: blank)) _
  have e1 : ones (m' + 1) (app (skp (m' + 2) ++ seps (1 :: p1 :: rest) ++ [F, F] ++ [T, F, T]).reverse blank) =
      app (List.replicate (m' + 2) T) (F ::: T ::: app (F :: F :: (seps (1 :: p1 :: rest)).reverse ++
        List.replicate (m' + 2) T) (F ::: T ::: blank)) := by
    simp only [skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
      List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
      app_replicate, app_cons, app_nil, cons_blank]
    rw [← ones_succ']
  rw [e1]
  refine Rch.tr (PPX.find (Clean.replicate _) _ _) ?_
  gL
  have hg := (gap_seps (1 :: p1 :: rest)).reverse
  have hw : Clean (F :: F :: (seps (1 :: p1 :: rest)).reverse ++ List.replicate (m' + 2) T) := by
    have := hg.clean (Clean.replicate (m' + 1))
    simpa [List.reverse_append, List.replicate_succ] using this
  refine Rch.tr (PPY.find hw _ _) ?_
  gR; gL; gL; gR; gR
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append, List.singleton_append,
    app_append, app_replicate, app_cons, app_nil, seps]
  sRn (m' + 3)
  gR; gR
  sRn 3
  gR; gR; gR
  unfold TC
  simp only [skp, seps, List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append, List.singleton_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  rw [ones_cons_true]; fin

theorem PPM : ParserR delta PM1 PM2 := ⟨rfl, rfl, rfl⟩

/-- after the cycle: the counter divides `m`; to `M`'s hole (then `next_cand`) -/
theorem trial_div (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) :
    Rch ⟨kd3, ones (p + 2) (cyL (F ::: blank) m 1 (seps pre ++ [F, F])), app (seps post ++ [F, F] ++ skp m) blank⟩
      ⟨ms, app (skp m ++ seps (pre ++ p :: post) ++ [F, F] ++ [T, F, T]).reverse blank, ones (m - 1) blank⟩ := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  cases post with
  | nil =>
    simp only [seps, skp, List.nil_append, List.cons_append, app_cons, app_nil, app_append, app_replicate]
    gR; gR; gR; gR; gR
    simp only [ones_succ, Nat.add_sub_cancel]
    rw [← tc_left]
    simp only [skp, seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
      app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]
    fin
  | cons q post' =>
    simp only [seps, List.cons_append, app_cons, app_append, app_replicate]
    gR; gR
    rw [ones_succ]
    gR
    have hw : Clean (List.replicate (q + 1) T ++ (seps post' ++ [F, F] ++ [T])) :=
      Clean.rep_append _ (by simpa using (gap_seps post').clean Clean.nil)
    have e : ones (q + 1) (app (seps post') (F ::: F ::: app [] (app (skp (m' + 1)) blank))) =
        app (List.replicate (q + 1) T ++ (seps post' ++ [F, F] ++ [T])) (F ::: T ::: ones m' blank) := by
      simp only [skp, app_append, app_replicate, app_cons, app_nil, List.append_assoc, ones_succ,
        cons_blank]
    rw [e]
    refine Rch.tr (PPM.find hw _ _) ?_
    gR
    rw [Nat.add_sub_cancel, ← tc_left]
    simp only [skp, seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
      List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
      app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]
    rw [ones_cons_true]; fin

/-- after the cycle: the counter does not divide `m`; the next block is a list block -/
theorem trial_next (m : Nat) (pre : List Nat) (p q : Nat) (post : List Nat) :
    Rch ⟨kn3, ones (p + 2) (cyL (F ::: blank) m 1 (seps pre ++ [F, F])), app (seps (q :: post) ++ [F, F] ++ skp m) blank⟩
      (TC m (pre ++ [p]) q post) := by
  simp only [seps, List.cons_append, app_cons, app_append, app_replicate]
  gR; gR
  rw [ones_succ]
  gR
  unfold TC
  rw [← tc_left]
  simp only [skp, seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero]
  fin

/-- the pair step for block `p` (the marker at its cell 1), head on its cell 2 -/
def PC (m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Cfg St :=
  ⟨pw1, F ::: T ::: app (skp m ++ seps pre ++ [F, F]).reverse blank,
    app (List.replicate p T ++ seps post ++ [F, F] ++ skp m) blank⟩

/-- RETREAT: from a block (head on one of its cells left of any hole) to the previous block,
whose cell 1 becomes the marker -/
theorem retreat (a q : Nat) (X R : Strm) :
    Rch (cfgL rt1 (ones a (F ::: F ::: ones (q + 2) (F ::: X))) R)
      ⟨pw1, F ::: T ::: F ::: X, ones q (F ::: F ::: ones a R)⟩ := by
  sLn a
  gL; gL
  sLn (q + 2)
  gR; gR; gR
  fin

/-- after the cycle: the counter does not divide `m` and it is the last list block: `m` is
prime; the pair pass starts with that block -/
theorem trial_prime (m : Nat) (pre : List Nat) (p : Nat) (hm : 1 ≤ m) :
    Rch ⟨kn3, ones (p + 2) (cyL (F ::: blank) m 1 (seps pre ++ [F, F])), app (seps [] ++ [F, F] ++ skp m) blank⟩
      (PC m pre p []) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [seps, skp, List.nil_append, List.cons_append, app_cons, app_nil, app_append, app_replicate]
  gR; gR; gR; gL
  obtain ⟨g', hg'⟩ := (gap_seps pre).rev_head
  have hc : cyL (F ::: blank) (m' + 1) 1 (seps pre ++ [F, F]) =
      F ::: app g' (ones (m' + 1) (F ::: T ::: F ::: blank)) := by
    simp only [cyL, hg', app_cons, Nat.add_sub_cancel, ones_succ, ones_zero]
  rw [hc]
  refine Rch.tr (retreat 1 p _ _) ?_
  unfold PC
  rw [tc_left, hc]
  simp only [seps, skp, List.nil_append, List.cons_append, List.append_assoc, app_cons, app_nil,
    app_append, app_replicate, ones_succ, ones_zero]
  fin

end TM.FeitThompson
