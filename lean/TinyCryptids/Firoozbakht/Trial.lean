import TinyCryptids.Firoozbakht.Cyc
import TinyCryptids.Firoozbakht.Arith

/-!
# The trial pass

The tape for the candidate `m` with the list `ps = pl m` and `N` holding `e`:
`N 00 P1 … 00 Pk 00 M` with `N = skp e`, `M = skp m` (hole at cell 1).
`TC e m pre p post`: the trial step for the block `p` (`ps = pre ++ p :: post`), state `kn6`
on cell 1 of that block.
-/

namespace TM.Firoozbakht
open St TinyCryptids

local notation "F" => false
local notation "T" => true

/-- a block with its hole at cell 1 -/
def skp (s : Nat) : List Bool := true :: false :: List.replicate s true

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

/-- the tape left of the list block after `pre` (its cell 0 excluded) -/
def lft (e : Nat) (pre : List Nat) : Strm := app (skp e ++ seps pre ++ [F, F]).reverse blank

theorem lft_head (e : Nat) (pre : List Nat) : ∃ X, lft e pre = F ::: X :=
  ⟨app (skp e ++ seps pre ++ [F]).reverse blank, by simp [lft, app_append]⟩

/-- the trial step for block `p` -/
def TC (e m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) : Cfg St :=
  ⟨kn6, T ::: lft e pre, app (List.replicate (p + 1) T ++ seps post ++ [F, F] ++ skp m) blank⟩

theorem tc_right (m : Nat) (post : List Nat) :
    app (seps post ++ [F, F] ++ skp m) blank = cyR (F ::: blank) m 1 (seps post ++ [F, F]) := by
  simp only [cyR, skp, app_append, app_cons, app_replicate, ones_succ, ones_zero,
    Nat.add_sub_cancel, cons_blank]

theorem trial_cyc (e m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 1 ≤ m) (hp : 1 ≤ p) :
    Rch (TC e m pre p post)
      ⟨if p ∣ m then PM1 else kn3, ones (p + 2) (lft e pre),
        cyR (F ::: blank) m 1 (seps post ++ [F, F])⟩ := by
  obtain ⟨X, hX⟩ := lft_head e pre
  have : app (List.replicate (p + 1) T ++ seps post ++ [F, F] ++ skp m) blank =
      T ::: ones p (app (seps post ++ [F, F] ++ skp m) blank) := by
    rw [List.append_assoc, List.append_assoc, app_append, app_replicate, List.append_assoc, ones_succ]
  unfold TC
  rw [this]
  gR
  rw [hX]
  have h := cyc_run (gap_seps post) X blank m p hm hp
  refine Rch.tr ?_ h
  unfold cyc2
  rw [← tc_right, show p + 1 - 1 = p by omega]
  fin

/-- at `M`'s cell 3, about to make `M` one longer -/
def MS (e m : Nat) (ps : List Nat) : Cfg St :=
  ⟨ms, app (skp e ++ seps ps ++ [F, F] ++ [T, F, T]).reverse blank, ones (m - 1) blank⟩

theorem PPX : ParserL delta PX1 PX2 := ⟨rfl, rfl, rfl⟩
theorem PPY : ParserL delta PY1 PY2 := ⟨rfl, rfl, rfl⟩
theorem PPM : ParserR delta PM1 PM2 := ⟨rfl, rfl, rfl⟩

/-- at the cell after `M`, about to make `M` one longer -/
def MSE (e m : Nat) (ps : List Nat) : Cfg St := ⟨ms, ones m (F ::: T ::: lft e ps), blank⟩

theorem ms_end (e m : Nat) (ps : List Nat) (hm : 1 ≤ m) : Rch (MS e m ps) (MSE e m ps) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  unfold MS MSE lft
  rw [Nat.add_sub_cancel]
  sRn m'
  simp only [skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
    List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
    app_replicate, app_cons, app_nil, ones_succ]
  rw [← ones_succ', ones_succ]; fin

/-- the next candidate: `M` grows by one cell; back to `N`, the trial pass starts at `P1` -/
theorem next_cand (e m p1 : Nat) (rest : List Nat) (hm : 2 ≤ m) (he : 1 ≤ e) :
    Rch (MSE e m (p1 :: rest)) (TC e (m + 1) [] p1 rest) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  unfold MSE
  refine blankR ?_
  gL
  show Rch (cfgL PX1 (ones (m' + 2) (F ::: T ::: lft e (p1 :: rest))) (T ::: blank)) _
  have e1 : ones (m' + 2) (F ::: T ::: lft e (p1 :: rest)) =
      app (List.replicate (m' + 2) T) (F ::: T ::: app (F :: F :: (seps (p1 :: rest)).reverse ++
        List.replicate e T) (F ::: T ::: blank)) := by
    simp only [lft, skp, List.reverse_append, List.reverse_cons, List.reverse_replicate, List.reverse_nil,
      List.nil_append, List.append_assoc, List.singleton_append, List.cons_append, app_append,
      app_replicate, app_cons, app_nil, cons_blank]
  rw [e1]
  refine Rch.tr (PPX.find (Clean.replicate _) _ _) ?_
  gL
  have hg := (gap_seps (p1 :: rest)).reverse
  have hw : Clean (F :: F :: (seps (p1 :: rest)).reverse ++ List.replicate e T) := by
    obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
    have := hg.clean (Clean.replicate e')
    simpa [List.reverse_append, List.replicate_succ] using this
  refine Rch.tr (PPY.find hw _ _) ?_
  gR; gR
  simp only [List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append, List.singleton_append,
    app_append, app_replicate, app_cons, app_nil, seps]
  sRn e
  gR; gR; gR
  unfold TC lft
  simp only [skp, seps, List.reverse_append, List.reverse_reverse, List.reverse_replicate, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append, List.singleton_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  rw [ones_cons_true]; fin

/-- after the cycle: the counter divides `m`; to `M`'s hole (then `next_cand`) -/
theorem trial_div (e m : Nat) (pre : List Nat) (p : Nat) (post : List Nat) (hm : 2 ≤ m) :
    Rch ⟨PM1, ones (p + 2) (lft e pre), cyR (F ::: blank) m 1 (seps post ++ [F, F])⟩
      (MS e m (pre ++ p :: post)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hw : Clean (seps post ++ [F, F] ++ [T]) := (gap_seps post).clean Clean.nil
  have e1 : cyR (F ::: blank) (m' + 1) 1 (seps post ++ [F, F]) =
      app (seps post ++ [F, F] ++ [T]) (F ::: T ::: ones m' (F ::: blank)) := by
    simp only [cyR, app_append, app_cons, app_nil, ones_succ, ones_zero, Nat.add_sub_cancel]
  rw [e1]
  refine Rch.tr (PPM.find hw _ _) ?_
  gR
  unfold MS lft
  simp only [skp, seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank, Nat.add_sub_cancel]
  fin

/-- after the cycle: the counter does not divide `m`; the next block is a list block -/
theorem trial_next (e m : Nat) (pre : List Nat) (p q : Nat) (post : List Nat) :
    Rch ⟨kn3, ones (p + 2) (lft e pre), cyR (F ::: blank) m 1 (seps (q :: post) ++ [F, F])⟩
      (TC e m (pre ++ [p]) q post) := by
  simp only [cyR, seps, List.cons_append, app_cons, app_append, app_replicate]
  gR; gR
  rw [ones_succ]
  gR
  unfold TC lft
  simp only [skp, seps_append, seps, List.reverse_append, List.reverse_cons, List.reverse_replicate,
    List.reverse_nil, List.nil_append, List.append_assoc, List.singleton_append, List.cons_append,
    app_append, app_replicate, app_cons, app_nil, ones_succ, ones_zero, cons_blank]
  rw [Nat.add_sub_cancel]; fin

end TM.Firoozbakht
