import TinyCryptids.Goldbach.Tape
import TinyCryptids.Defs

/-!
# The primality test of one block

A block X lies between a left delimiter `l` (beyond it `Lc`) and a right delimiter `rr`
(beyond it `Rc`); `l` and `rr` are each 0 or `s` = 5.  The divisor `d` is X's first `d` cells
(D), the rest R (`r` cells) starts with the boundary `b` (4; `B` = 3 while marked).  Marks are
`x` = 2.  `x = d + r`, and `d ∣ x` iff `d ∣ r`.

* `T d w`: `mark` on R's first cell, `w` = R's cells (a new round for `d`), or on `rr` if R is
  empty (`d = x`: no divisor below `x`, so X is prime).
* `Zc a j k v`: the zigzag after `k + 1` cells of R and `j + 1` cells of D have been marked
  (`a` cells of D unmarked, `a + j + 1 = d`), `v` the unmarked rest of R; `zr` is on the cell
  right of D's newest mark.
* `Cx d k`: `chk` on `l` after a round that found `d ∣ r` (`r = k + 1`), everything unmarked:
  X = `1^d b 1^k`.
-/

namespace TMK.Goldbach

open TM (Dir)
open TinyCryptids

/-- the cells unmarked in R: 1, or a stale `b` -/
def Good (v : List Nat) : Prop := ∀ a ∈ v, a = 1 ∨ a = 4

/-- the cells from D's newest mark to R's last mark -/
def M (j k : Nat) : List Nat := List.replicate j 2 ++ 3 :: List.replicate k 2

theorem M_mem {j k a : Nat} (h : a ∈ M j k) : a = 2 ∨ a = 3 := by
  simp only [M, List.mem_append, List.mem_cons, List.mem_replicate] at h; omega

section

variable (l rr : Nat) (Lc Rc : Strm)

def T (d : Nat) (w : List Nat) : Cfg St :=
  ⟨.mark, lst (List.replicate d 1) (l ∷ Lc), lst w (rr ∷ Rc)⟩

def Zc (a j k : Nat) (v : List Nat) : Cfg St :=
  ⟨.zr, 2 ∷ lst (List.replicate a 1) (l ∷ Lc), lst (M j k) (lst v (rr ∷ Rc))⟩

def Cx (d k : Nat) : Cfg St :=
  ⟨.chk, Lc, l ∷ lst (List.replicate d 1 ++ 4 :: List.replicate k 1) (rr ∷ Rc)⟩

variable {l rr Lc Rc}
variable (hzl : delta .zl l = some (l, Dir.R, .rst)) (hzr : delta .zr rr = some (rr, Dir.L, .chk))
include hzl

set_option linter.unusedSectionVars false

theorem zr_walk (j k : Nat) (L R : Strm) :
    Rch ⟨.zr, L, lst (M j k) R⟩ ⟨.zr, lst (M j k).reverse L, R⟩ := by
  have := walkR (q := .zr) id (M j k) L R (fun a h => by rcases M_mem h with rfl | rfl <;> rfl)
  simpa using this

theorem zl_walk (j k : Nat) (L R : Strm) :
    Rch (CL .zl (lst (M j k).reverse L) R) (CL .zl L (lst (M j k) R)) := by
  have := walkL (q := .zl) id (M j k).reverse L R (fun a h => by
    rcases M_mem (List.mem_reverse.1 h) with rfl | rfl <;> rfl)
  simpa using this

theorem zr_mark {u : Nat} (hu : u = 1 ∨ u = 4) (j k a : Nat) (v : List Nat) :
    Rch (Zc l rr Lc Rc a j k (u :: v))
      (CL .zl (lst (List.replicate a 1) (l ∷ Lc)) (lst (2 :: M j k) (2 ∷ lst v (rr ∷ Rc)))) := by
  refine Rch.tr (zr_walk hzl j k _ _) ?_
  refine Rch.tr (sL (q' := .zl) (w := 2) (by rcases hu with rfl | rfl <;> rfl)) ?_
  refine Rch.tr (zl_walk hzl j k _ _) ?_
  refine Rch.tr (sL (by rfl)) ?_
  fin

theorem zstep_more {u : Nat} (hu : u = 1 ∨ u = 4) (a j k : Nat) (v : List Nat) :
    Rch (Zc l rr Lc Rc (a + 1) j k (u :: v)) (Zc l rr Lc Rc a (j + 1) (k + 1) v) := by
  refine Rch.tr (zr_mark hzl hu j k (a + 1) v) ?_
  gR
  simp only [Zc, M, List.replicate_succ, List.cons_append, lst_cons, lst_append, lst_rep_comm]
  fin

theorem zstep_wrap {u : Nat} (hu : u = 1 ∨ u = 4) (j k : Nat) (v : List Nat) :
    Rch (Zc l rr Lc Rc 0 j k (u :: v)) (Zc l rr Lc Rc j 0 (k + 1) v) := by
  refine Rch.tr (zr_mark hzl hu j k 0 v) ?_
  refine Rch.tr (sR hzl) ?_
  rw [show (2 :: M j k) = List.replicate (j + 1) 2 ++ 3 :: List.replicate k 2 from rfl, lst_append]
  refine Rch.tr (runR (q := .rst) (a := 2) (w := 1) (by rfl) (j + 1) _ _) ?_
  refine Rch.tr (sL (by rfl)) ?_
  simp only [List.replicate_succ, lst_cons, CL_cons]
  gR
  simp only [Zc, M, List.replicate, List.nil_append, lst_cons, lst_append, lst_rep_comm]
  fin

include hzr

theorem zend_more (a j k : Nat) :
    Rch (Zc l rr Lc Rc (a + 1) j k []) (T l rr Lc Rc (a + j + 3) (List.replicate k 1)) := by
  refine Rch.tr (zr_walk hzl j k _ _) ?_
  refine Rch.tr (sL hzr) ?_
  have := walkL (q := .chk) (fun a => if a = 2 then 1 else 4) (M j k).reverse
    (2 ∷ lst (List.replicate (a + 1) 1) (l ∷ Lc)) (rr ∷ Rc) (fun b h => by
      rcases M_mem (List.mem_reverse.1 h) with rfl | rfl <;> rfl)
  refine Rch.tr this ?_
  refine Rch.tr (sL (by rfl)) ?_
  simp only [List.replicate_succ, lst_cons, CL_cons]
  gR
  simp only [M, List.map_reverse, List.reverse_reverse, List.map_append, List.map_replicate,
    List.map_cons, lst_append, lst_cons]
  simp
  rRn (j + 1)
  gR
  simp only [T]
  rw [show a + j + 3 = 1 + (j + 1) + 1 + a by omega]
  simp only [lst_rep_add]
  fin

theorem zend_div (j k : Nat) : Rch (Zc l rr Lc Rc 0 j k []) (Cx l rr Lc Rc (j + 1) k) := by
  refine Rch.tr (zr_walk hzl j k _ _) ?_
  refine Rch.tr (sL hzr) ?_
  have := walkL (q := .chk) (fun a => if a = 2 then 1 else 4) (M j k).reverse
    (2 ∷ lst (List.replicate 0 1) (l ∷ Lc)) (rr ∷ Rc) (fun b h => by
      rcases M_mem (List.mem_reverse.1 h) with rfl | rfl <;> rfl)
  refine Rch.tr this ?_
  refine Rch.tr (sL (by rfl)) ?_
  simp only [Cx, M, List.map_reverse, List.reverse_reverse, List.map_append, List.map_replicate,
    List.map_cons, lst_append, lst_cons, List.replicate, CL]
  simp
  fin

/-- a whole round: the zigzag to its end, by the number of marks in D modulo `d` -/
theorem zig (d : Nat) : ∀ (v : List Nat), Good v → ∀ a j k, a + j + 1 = d → (j + 1) % d = (k + 1) % d →
    ((k + 1 + v.length) % d = 0 → Rch (Zc l rr Lc Rc a j k v) (Cx l rr Lc Rc d (k + v.length))) ∧
    ((k + 1 + v.length) % d ≠ 0 →
      Rch (Zc l rr Lc Rc a j k v) (T l rr Lc Rc (d + 1) (List.replicate (k + v.length) 1))) := by
  intro v
  induction v with
  | nil =>
    intro _ a j k had hm
    simp only [List.length_nil, Nat.add_zero]
    rcases a with _ | a
    · have hj : j + 1 = d := by omega
      subst hj
      refine ⟨fun _ => zend_div hzl hzr j k, fun h => absurd (hm.symm.trans (Nat.mod_self _)) h⟩
    · refine ⟨fun h => ?_, fun _ => ?_⟩
      · rw [← hm, Nat.mod_eq_of_lt (by omega)] at h; omega
      · have := zend_more (Lc := Lc) (Rc := Rc) hzl hzr a j k
        rwa [show a + j + 3 = d + 1 by omega] at this
  | cons u v ih =>
    intro hg a j k had hm
    have hu := hg u (List.mem_cons_self _ _)
    have hv : Good v := fun b hb => hg b (List.mem_cons_of_mem _ hb)
    simp only [List.length_cons]
    rw [show k + 1 + (v.length + 1) = k + 1 + 1 + v.length by omega,
      show k + (v.length + 1) = k + 1 + v.length by omega]
    rcases a with _ | a
    · have hj : j + 1 = d := by omega
      have hm' : (0 + 1) % d = (k + 1 + 1) % d := by
        rw [Nat.add_mod (k + 1), ← hm, hj, Nat.mod_self, Nat.zero_add, Nat.zero_add, Nat.mod_mod]
      have := ih hv j 0 (k + 1) (by omega) hm'
      exact ⟨fun h => Rch.tr (zstep_wrap hzl hu j k v) (this.1 h),
        fun h => Rch.tr (zstep_wrap hzl hu j k v) (this.2 h)⟩
    · have hm' : (j + 1 + 1) % d = (k + 1 + 1) % d := by
        rw [Nat.add_mod (j + 1), hm, ← Nat.add_mod]
      have := ih hv a (j + 1) (k + 1) (by omega) hm'
      exact ⟨fun h => Rch.tr (zstep_more hzl hu a j k v) (this.1 h),
        fun h => Rch.tr (zstep_more hzl hu a j k v) (this.2 h)⟩

/-- the start of a round: `mark` makes R's first cell the boundary `B` -/
theorem round_start (d : Nat) (v : List Nat) :
    Rch (T l rr Lc Rc (d + 1) (1 :: v)) (Zc l rr Lc Rc d 0 0 v) := by
  refine Rch.tr (sL (by rfl)) ?_
  simp only [List.replicate_succ, lst_cons, CL_cons]
  gR; fin

/-- R's cells at the start of a round: none, or a 1 then 1s and stale `b`s -/
def WOK (w : List Nat) : Prop := w = [] ∨ ∃ v, w = 1 :: v ∧ Good v

omit hzl hzr in
theorem WOK_rep (n : Nat) : WOK (List.replicate n 1) := by
  rcases n with _ | n
  · exact Or.inl rfl
  · exact Or.inr ⟨_, rfl, fun a h => Or.inl (List.eq_of_mem_replicate h)⟩

/-- **The primality test** of a block of `d + n` cells, from the round for `d` (no divisor
in `[2, d)`): prime → `mark` on `rr` with the block all 1s; composite → `Cx m k` for a
divisor `m`. -/
theorem test : ∀ n d (w : List Nat), w.length = n → 2 ≤ d → WOK w →
    (∀ e, 2 ≤ e → e < d → (d + n) % e ≠ 0) →
    (Prime (d + n) → Rch (T l rr Lc Rc d w) (T l rr Lc Rc (d + n) [])) ∧
    (¬ Prime (d + n) → ∃ m k, 2 ≤ m ∧ m + k + 1 = d + n ∧
      Rch (T l rr Lc Rc d w) (Cx l rr Lc Rc m k)) := by
  intro n
  induction n with
  | zero =>
    intro d w hw hd _ he
    have : w = [] := List.eq_nil_of_length_eq_zero hw
    subst this
    refine ⟨fun _ => Reach.refl delta _, fun hp => absurd ⟨by omega, fun e h1 h2 => he e h2 h1⟩ hp⟩
  | succ n ih =>
    intro d w hw hd hwok he
    rcases hwok with rfl | ⟨v, rfl, hg⟩
    · simp at hw
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hw
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    have z := zig (Lc := Lc) (Rc := Rc) hzl hzr (d' + 1) v hg d' 0 0 (by omega) rfl
    rw [Nat.zero_add, Nat.zero_add, hw] at z
    by_cases hdiv : (1 + n) % (d' + 1) = 0
    · have hx : (d' + 1 + (n + 1)) % (d' + 1) = 0 := by
        rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.add_comm n 1, hdiv, Nat.zero_mod]
      have hnp : ¬ Prime (d' + 1 + (n + 1)) := fun hp => hp.2 (d' + 1) (by omega) hd hx
      exact ⟨fun hp => absurd hp hnp,
        fun _ => ⟨d' + 1, n, hd, by omega, Rch.tr (round_start (Lc := Lc) (Rc := Rc) hzl hzr d' v) (z.1 hdiv)⟩⟩
    · have r := Rch.tr (round_start (Lc := Lc) (Rc := Rc) hzl hzr d' v) (z.2 hdiv)
      have := ih (d' + 1 + 1) (List.replicate n 1) (by simp) (by omega) (WOK_rep n) (fun e h1 h2 => by
        rw [show d' + 1 + 1 + n = d' + 1 + (n + 1) by omega]
        rcases Nat.lt_or_ge e (d' + 1) with h | h
        · exact he e h1 h
        · have : e = d' + 1 := by omega
          subst this
          rw [Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.add_comm n 1]; exact hdiv)
      rw [show d' + 1 + 1 + n = d' + 1 + (n + 1) by omega] at this
      exact ⟨fun hp => Rch.tr r (this.1 hp), fun hp =>
        let ⟨m, k, h1, h2, h3⟩ := this.2 hp; ⟨m, k, h1, h2, Rch.tr r h3⟩⟩

end

end TMK.Goldbach
