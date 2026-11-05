import TinyCryptids.PerfectCuboid.Enum

/-!
# One tuple: the twelve checks, the halt, the abort to the next tuple

The positions of the queue for `t = (x, y, z)`: `n5` on the first cell of A (`PA`), B (`PB`),
C (`PC`), Z (`PZ`), or on G's cell 3 after Z (`PE`), with W and S.
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

def PA (x y z W : Nat) (s : Nat × Nat) : Cfg St := ⟨n5, blank, app (qL (x, y, z) ++ gapL W) (Sb s)⟩
def PB (x y z W : Nat) (s : Nat × Nat) : Cfg St :=
  ⟨n5, F ::: F ::: ones x blank, app (rep y ++ [F, F] ++ rep z ++ [F, F] ++ [T, T, T] ++ gapL W) (Sb s)⟩
def PC (x y z W : Nat) (s : Nat × Nat) : Cfg St :=
  ⟨n5, F ::: F ::: ones y (F ::: F ::: ones x blank), app (rep z ++ [F, F] ++ [T, T, T] ++ gapL W) (Sb s)⟩
def PZ (x y z W : Nat) (s : Nat × Nat) : Cfg St :=
  ⟨n5, F ::: F ::: ones z (F ::: F ::: ones y (F ::: F ::: ones x blank)), app ([T, T, T] ++ gapL W) (Sb s)⟩
def PE (x y z W : Nat) (s : Nat × Nat) : Cfg St :=
  ⟨n5, F ::: F ::: ones 3 (F ::: F ::: ones z (F ::: F ::: ones y (F ::: F ::: ones x blank))),
    app (gm W ++ [F, F]) (Sb s)⟩

theorem ffb : F ::: F ::: blank = blank := by rw [cons_blank, cons_blank]

theorem stepA (x y z : Nat) (hx : 4 ≤ x) (W : Nat) (hW : W ≤ 2) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 = 0) : Rch (PA x y z W s) (PB x y z (tk W) (advN (v x * v x) (rs W s))) := by
  have := step_real x hx blank (rep y ++ [F, F] ++ rep z ++ [F, F] ++ [T, T, T])
    (Ev.append (Ev.append (Ev.append (Ev.append (Ev.replicate y) (Ev.zz Ev.nil)) (Ev.replicate z))
      (Ev.zz Ev.nil)) (Ev.one (Ev.one (Ev.one Ev.nil)))) W hW s hs h0
  rw [ffb] at this
  unfold PA PB
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr this (rch_eq ?_ ?_))
  · simp [qL, rep, app_append, app_replicate]
  · rfl
  · simp [app_append]

theorem stepB (x y z : Nat) (hy : 4 ≤ y) (W : Nat) (hW : W ≤ 2) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 = 0) : Rch (PB x y z W s) (PC x y z (tk W) (advN (v y * v y) (rs W s))) := by
  have := step_real y hy (ones x blank) (rep z ++ [F, F] ++ [T, T, T])
    (Ev.append (Ev.append (Ev.replicate z) (Ev.zz Ev.nil)) (Ev.one (Ev.one (Ev.one Ev.nil))))
    W hW s hs h0
  unfold PB PC
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr this (rch_eq ?_ ?_))
  · simp [rep, app_append, app_replicate]
  · simp [ffb]
  · simp [app_append]

theorem stepC (x y z : Nat) (hz : 4 ≤ z) (W : Nat) (hW : W ≤ 2) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 = 0) : Rch (PC x y z W s) (PZ x y z (tk W) (advN (v z * v z) (rs W s))) := by
  have := step_real z hz (ones y (F ::: F ::: ones x blank)) [T, T, T]
    (Ev.one (Ev.one (Ev.one Ev.nil))) W hW s hs h0
  unfold PC PZ
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr this (rch_eq rfl ?_))
  · simp [rep, app_append, app_replicate]
  · simp [app_append]

theorem stepZ (x y z : Nat) (W : Nat) (hW : W ≤ 2) (s : Nat × Nat) (h0 : s.2 = 0) :
    Rch (PZ x y z W s) (PE x y z (tk W) (rs W s)) := by
  have := step_Z (ones z (F ::: F ::: ones y (F ::: F ::: ones x blank))) W hW s h0
  unfold PZ PE
  refine Rch.tr (rch_eq rfl ?_) (Rch.tr this (rch_eq rfl rfl))
  · simp [app_append]

theorem endA (x y z : Nat) (ht : Valid3 (x, y, z)) (W : Nat) (hW : W ≤ 1) (s : Nat × Nat) :
    Rch (PE x y z W s) (PA x y z W s) := by
  have := wrap (x, y, z) ht W hW s
  unfold PE PA
  refine Rch.tr (rch_eq ?_ rfl) this
  rw [qrev]
  simp [rep, app_append, app_replicate, ffb]
  rfl

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, hr⟩ := h; ⟨L, R, Rch.tr hab hr⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, hr⟩ := h; Reach.halts delta hr (halt_none (δ := delta) rfl)

theorem endH (x y z : Nat) (s : Nat × Nat) : HaltAt (PE x y z 2 s) := by
  unfold PE
  apply Exists.intro; apply Exists.intro
  simp only [gm, List.cons_append, app_cons]
  gR; gR; gl; fin

/-! ## aborts: Y = B, C or Z has `h` (and `m`) when the check fails -/

theorem Cl.tail (x : Nat) (hx : 1 ≤ x) (l l' : List Bool) (h : Cl l l') :
    Cl ([F, F] ++ rep x ++ l) ([F, F] ++ rep x ++ l') := by
  obtain ⟨x', rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  exact Cl.sep (Cl.reps x' h)

theorem Cl.rep_nil (x : Nat) : Cl (rep x) (rep x) := by simpa using Cl.reps x Cl.nil

/-- the marked block `F T F 1^(L-3)` (h, spacer, m) read leftwards becomes `1^L` -/
theorem Cl.mark (L : Nat) (hL : 4 ≤ L) (l l' : List Bool) (h : Cl l l') :
    Cl ([F, F] ++ [F, T, F] ++ rep (L - 3) ++ l) ([F, F] ++ rep L ++ l') := by
  obtain ⟨w, hw⟩ : ∃ w, L - 3 = w + 1 := ⟨L - 4, by omega⟩
  rw [hw, show L = w + 1 + 3 by omega]
  simp only [rep, List.replicate_succ, List.cons_append, List.nil_append, List.append_assoc]
  exact Cl.seph (Cl.one (Cl.hole (Cl.one (by simpa using Cl.reps w h))))

/-- the abort's end: the scan from the cell left of G to A, then the next tuple's NEXCOM -/
theorem abort_end (v : List Bool) (hv : Ev v) (Q : Strm) (W : Nat) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 ≠ 0) (l l' : List Bool) (hQ : app v.reverse Q = app l blank) (hl : Cl l l')
    (t : Tup) (ht : l'.reverse = qL t) :
    Rch ⟨PK1, Q, app (v ++ gapL W) (Sb s)⟩ ⟨ea0, blank, app (qL t ++ gapL 2) (Sb (s.1, 0))⟩ := by
  refine Rch.tr (ckabort v hv Q W s hs h0) ?_
  rw [hQ]
  refine Rch.tr (clean_home hl _) ?_
  rw [ht]; apply rch_eq rfl; simp [app_append]

theorem abB (x y z : Nat) (ht : Valid3 (x, y, z)) (W : Nat) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 ≠ 0) :
    Rch (PB x y z W s) ⟨ea0, blank, app (qL (x, y, z) ++ gapL 2) (Sb (s.1, 0))⟩ := by
  obtain ⟨hx, hy, hz⟩ := ht
  unfold PB
  have e : app (rep y ++ [F, F] ++ rep z ++ [F, F] ++ [T, T, T] ++ gapL W) (Sb s) =
      ones y (F ::: app (F :: (rep z ++ [F, F] ++ [T, T, T] ++ gapL W)) (Sb s)) := by
    simp [rep, app_append, app_replicate]
  rw [e]
  refine Rch.tr (init_real y hy _ _) ?_
  have := abort_end (F :: F :: (rep z ++ [F, F] ++ [T, T, T])) (Ev.zz (Ev.append (Ev.append
    (Ev.replicate z) (Ev.zz Ev.nil)) (Ev.one (Ev.one (Ev.one Ev.nil)))))
    (F ::: T ::: F ::: ones (y - 3) (F ::: F ::: ones x blank)) W s hs h0
    ([T, T, T] ++ [F, F] ++ rep z ++ ([F, F] ++ [F, T, F] ++ rep (y - 3) ++ ([F, F] ++ rep x)))
    ([T, T, T] ++ [F, F] ++ rep z ++ ([F, F] ++ rep y ++ ([F, F] ++ rep x)))
    (by simp [rep, app_append, app_replicate, List.reverse_append, List.reverse_replicate, ffb])
    (Cl.one (Cl.one (Cl.one (Cl.tail z (by omega) _ _ (Cl.mark y hy _ _ (by
      simpa using Cl.tail x (by omega) [] [] Cl.nil))))))
    (x, y, z) (by simp [qL, rep, List.reverse_append, List.reverse_replicate])
  refine Rch.tr (rch_eq rfl (by simp [app_append])) this

theorem abC (x y z : Nat) (ht : Valid3 (x, y, z)) (W : Nat) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 ≠ 0) :
    Rch (PC x y z W s) ⟨ea0, blank, app (qL (x, y, z) ++ gapL 2) (Sb (s.1, 0))⟩ := by
  obtain ⟨hx, hy, hz⟩ := ht
  unfold PC
  have e : app (rep z ++ [F, F] ++ [T, T, T] ++ gapL W) (Sb s) =
      ones z (F ::: app (F :: ([T, T, T] ++ gapL W)) (Sb s)) := by
    simp [rep, app_append, app_replicate]
  rw [e]
  refine Rch.tr (init_real z hz _ _) ?_
  have := abort_end (F :: F :: [T, T, T]) (Ev.zz (Ev.one (Ev.one (Ev.one Ev.nil))))
    (F ::: T ::: F ::: ones (z - 3) (F ::: F ::: ones y (F ::: F ::: ones x blank))) W s hs h0
    ([T, T, T] ++ ([F, F] ++ [F, T, F] ++ rep (z - 3) ++ ([F, F] ++ rep y ++ ([F, F] ++ rep x))))
    ([T, T, T] ++ ([F, F] ++ rep z ++ ([F, F] ++ rep y ++ ([F, F] ++ rep x))))
    (by simp [rep, app_append, app_replicate, List.reverse_append, List.reverse_replicate])
    (Cl.one (Cl.one (Cl.one (Cl.mark z hz _ _ (Cl.tail y (by omega) _ _ (by
      simpa using Cl.tail x (by omega) [] [] Cl.nil))))))
    (x, y, z) (by simp [qL, rep, List.reverse_append, List.reverse_replicate])
  refine Rch.tr (rch_eq rfl (by simp [app_append])) this

theorem abZ (x y z : Nat) (ht : Valid3 (x, y, z)) (W : Nat) (s : Nat × Nat) (hs : Valid s)
    (h0 : s.2 ≠ 0) :
    Rch (PZ x y z W s) ⟨ea0, blank, app (qL (x, y, z) ++ gapL 2) (Sb (s.1, 0))⟩ := by
  obtain ⟨hx, hy, hz⟩ := ht
  unfold PZ
  have e : app ([T, T, T] ++ gapL W) (Sb s) =
      T ::: T ::: T ::: F ::: app (F :: (gm W ++ [F, F])) (Sb s) := by
    simp [gapL, app_append]
  rw [e]
  refine Rch.tr (init_Z _ _) ?_
  have := abort_end [] Ev.nil
    (F ::: T ::: T ::: F ::: F ::: ones z (F ::: F ::: ones y (F ::: F ::: ones x blank))) W s hs h0
    ([F, T, T] ++ ([F, F] ++ rep z ++ ([F, F] ++ rep y ++ ([F, F] ++ rep x))))
    ([T, T, T] ++ ([F, F] ++ rep z ++ ([F, F] ++ rep y ++ ([F, F] ++ rep x))))
    (by simp [rep, app_append, app_replicate])
    (Cl.hole (Cl.one (Cl.one (Cl.tail z (by omega) _ _ (Cl.tail y (by omega) _ _ (by
      simpa using Cl.tail x (by omega) [] [] Cl.nil))))))
    (x, y, z) (by simp [qL, rep, List.reverse_append, List.reverse_replicate])
  refine Rch.tr (rch_eq rfl (by simp [gapL, app_append])) this

end TM.PerfectCuboid
