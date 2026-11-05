import TinyCryptids.PerfectCuboid.Proc

/-!
# The check after each block, the window counter W, the abort

G, the gap before S, is `gapL W`: eight cells, the marker `11` on cells 5, 6 (`W = 1`) or 3, 4
(`W = 2`). After a block, the next block Y is set up and the head goes to S (`PK`): a square
ticks W (`tk`), and when W wraps S is reset to `(0, 0)` (`cktick`); otherwise the abort moves
S's hole home, sets `W = 2` and goes left in `q1` (`ckabort`).
-/

namespace TM.PerfectCuboid

open St

local notation "F" => false
local notation "T" => true

def gm : Nat → List Bool
  | 0 => [F, F, F, F]
  | 1 => [F, F, T, T]
  | _ => [T, T, F, F]

def gapL (W : Nat) : List Bool := [F, F] ++ gm W ++ [F, F]

def tk : Nat → Nat
  | 0 => 1
  | 1 => 2
  | _ => 0

theorem gm_ev (W : Nat) : Ev (gm W) := by
  rcases W with _ | _ | W
  · exact Ev.zz (Ev.zz Ev.nil)
  · exact Ev.zz (Ev.one (Ev.one Ev.nil))
  · exact Ev.one (Ev.one (Ev.zz Ev.nil))

theorem gapL_ev (W : Nat) : Ev (gapL W) := Ev.zz (Ev.append (gm_ev W) (Ev.zz Ev.nil))

theorem rch_eqL {q : St} {s R R' : Strm} (h : R = R') : Rch (cfgL q s R) (cfgL q s R') := by
  subst h; fin

theorem PK : ParserR delta PK1 PK2 := ⟨rfl, rfl, rfl⟩
theorem PR : ParserR delta PR1 PR2 := ⟨rfl, rfl, rfl⟩

/-- back from the S side to the block's hole -/
theorem pl_ret (u : List Bool) (hu : Ev u) (Xl R : Strm) :
    Rch (cfgL PL1 (app u (F ::: T ::: Xl)) R) ⟨hA, T ::: Xl, F ::: app u.reverse R⟩ := by
  refine Rch.tr (findL PL hu (T ::: Xl) R) ?_
  exact sR (q := PL2) rfl

/-- scan left over `n` zeros (the head on a 0) -/
theorem zcl {q : St} (h : delta q F = some (F, Dir.L, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, zeros n L, F ::: R⟩ ⟨q, L, F ::: zeros n R⟩ := by
  rw [← zeros_cons_false]
  induction n generalizing R with
  | zero => fin
  | succ n ih =>
    refine Rch.tr (sL2 (L := zeros n L) h) ?_
    have := ih (F ::: R); rw [← zeros_succ'] at this; exact this

/-- S reset: from the cell after S's hole (home), S becomes `101`, back on S's lead in `PL1` -/
theorem reset (k : Nat) (G : Strm) :
    Rch ⟨PR2, F ::: T ::: G, ones (2 * k + 1) blank⟩ ⟨PL1, G, Sb (0, 0)⟩ := by
  gR
  refine Rch.tr (eraseR (δ := delta) rfl (2 * k) _ _) ?_
  refine blankR ?_
  have tail : ∀ R : Strm, Rch ⟨r2, F ::: T ::: G, T ::: R⟩ ⟨PL1, G, T ::: F ::: T ::: R⟩ := by
    intro R; gl; gl; fin
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp only [Nat.mul_zero, zeros]
    gl
    refine Rch.tr (tail _) ?_
    apply rch_eq rfl
    simp [Sb, Sr, cons_blank]
  · obtain ⟨n, hn⟩ : ∃ n, 2 * k = n + 1 := ⟨2 * k - 1, by omega⟩
    rw [hn]
    show Rch ⟨r1, F ::: zeros n (T ::: F ::: T ::: G), F ::: blank⟩ _
    gl
    refine Rch.tr (zcl (by rfl) n _ _) ?_
    gl
    refine Rch.tr (tail _) ?_
    apply rch_eq rfl
    simp [Sb, Sr, cons_blank]

theorem PK_find (v : List Bool) (hv : Ev v) (W : Nat) (s : Nat × Nat) (Q : Strm) :
    Rch ⟨PK1, Q, app (v ++ gapL W) (Sb s)⟩
      ⟨PK2, F ::: ones s.2 (T ::: app (gapL W).reverse (app v.reverse Q)),
        ones (2 * s.1 - s.2) (T ::: blank)⟩ := by
  have e : app (v ++ gapL W) (Sb s) =
      app (v ++ gapL W ++ T :: List.replicate s.2 T) (F ::: ones (2 * s.1 - s.2) (T ::: blank)) := by
    simp [Sb, Sr, app_append, app_replicate]
  rw [e]
  refine Rch.tr (findR PK (Ev.append (Ev.append hv (gapL_ev W)) (Ev.one (Ev.replicate _))) Q _) ?_
  simp [List.reverse_append, app_append, app_replicate, List.reverse_replicate]
  fin

theorem gapL_rev (W : Nat) (Q : Strm) : app (gapL W).reverse Q =
    F ::: F ::: app (gm W).reverse (F ::: F ::: Q) := by
  simp [gapL, List.reverse_append, app_append]

/-- a square: W ticks (S reset when it wraps), back to the block's hole -/
theorem cktick (v : List Bool) (hv : Ev v) (Xl : Strm) (W : Nat) (hW : W ≤ 2)
    (s : Nat × Nat) (h0 : s.2 = 0) :
    Rch ⟨PK1, F ::: T ::: Xl, app (v ++ gapL W) (Sb s)⟩
      ⟨hA, T ::: Xl, F ::: app (v ++ gapL (tk W)) (Sb (if W = 2 then (0, 0) else s))⟩ := by
  refine Rch.tr (PK_find v hv W s _) ?_
  obtain ⟨k, j⟩ := s
  simp only at h0 ⊢; subst h0
  rw [Nat.sub_zero, ones_zero, gapL_rev, ones_cons_true]
  gl; gl; gl; gl
  rcases W with _ | _ | W
  · -- W = 0 → 1
    simp only [gm, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, app_cons, app_nil]
    gl; gl; gl; gR; gR; gl
    have := pl_ret ([T, F, F, F, F] ++ v.reverse) (Ev.one (Ev.zz (Ev.zz (Ev.reverse hv)))) Xl
      (T ::: F ::: F ::: Sb (k, 0))
    simp only [List.cons_append, List.nil_append, app_cons, app_append, Sb, Sr, ones_zero,
      Nat.sub_zero] at this
    refine Rch.tr (rch_eq rfl ?_) (Rch.tr this ?_)
    · simp [ones_cons_true]
    · apply rch_eq rfl
      simp [List.reverse_append, app_append, gapL, gm, tk, Sb, Sr]
  · -- W = 1 → 2
    simp only [gm, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, app_cons, app_nil]
    gl; gl; gl; gl; gl
    have := pl_ret ([F, F] ++ v.reverse) (Ev.zz (Ev.reverse hv)) Xl
      (T ::: T ::: F ::: F ::: F ::: F ::: Sb (k, 0))
    simp only [List.cons_append, List.nil_append, app_cons, app_append, Sb, Sr, ones_zero,
      Nat.sub_zero] at this
    refine Rch.tr (rch_eq rfl ?_) (Rch.tr this ?_)
    · simp [ones_cons_true]
    · apply rch_eq rfl
      simp [List.reverse_append, app_append, gapL, gm, tk, Sb, Sr]
  · -- W = 2 → 0, S reset
    obtain rfl : W = 0 := by omega
    simp only [gm, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, app_cons, app_nil]
    gl; gl; gl; gl; gR; gR
    refine Rch.tr (crossR PR (w := [F, F, F, F]) (Ev.zz (Ev.zz Ev.nil)) _ _) ?_
    simp only [app_cons, app_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.singleton_append]
    gR; gR
    refine Rch.tr (reset k _) ?_
    have := pl_ret ([T, F, F, F, F, F, F, F, F] ++ v.reverse)
      (Ev.one (Ev.zz (Ev.zz (Ev.zz (Ev.zz (Ev.reverse hv)))))) Xl (Sr (0, 0))
    simp only [List.cons_append, List.nil_append, app_cons, app_append] at this
    refine Rch.tr this ?_
    apply rch_eq rfl
    simp [List.reverse_append, app_append, gapL, gm, tk, Sb, Sr]

/-- not a square: S's hole moves home, `W := 2`, then left in `q1` from the cell left of G -/
theorem ckabort (v : List Bool) (hv : Ev v) (Q : Strm) (W : Nat) (s : Nat × Nat)
    (hs : Valid s) (h0 : s.2 ≠ 0) :
    Rch ⟨PK1, Q, app (v ++ gapL W) (Sb s)⟩
      (cfgL q1 (app v.reverse Q) (app (gapL 2) (Sb (s.1, 0)))) := by
  refine Rch.tr (PK_find v hv W s _) ?_
  obtain ⟨k, j⟩ := s
  unfold Valid at hs; simp only at h0 hs ⊢
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨m, hm⟩ : ∃ m, 2 * k - (j' + 1) = m := ⟨_, rfl⟩
  rw [hm, ones_cons_true m blank, ones_succ, ones_cons_true j']
  gl; gl; gl; gR; gR; gl
  rw [cons_ones j' (app (gapL W).reverse (app v.reverse Q))]
  sl (j' + 1)
  rw [gapL_rev]
  gl; gR; gR; gl
  gl; gl
  rcases W with _ | _ | W <;>
  · simp only [gm, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, app_cons, app_nil]
    gl; gl; gl; gl; gl; gl
    refine Rch.tr (stepL (δ := delta) (q := ab17) (L := app v.reverse Q)
      (R := F ::: F ::: T ::: T ::: F ::: F ::: F ::: F ::: T ::: F ::: ones j' (T ::: T ::: ones m blank))
      rfl) ?_
    show Rch (cfgL q1 (app v.reverse Q) _) _
    refine rch_eqL ?_
    rw [tl_cons]
    show _ = app [F, F, T, T, F, F, F, F] (T ::: F ::: ones (2 * k - 0) (T ::: blank))
    rw [show 2 * k - 0 = j' + 1 + m by omega]
    simp only [app_cons, app_nil]
    streq

end TM.PerfectCuboid
