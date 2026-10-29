import TinyCryptids.PA.Nodes

/-!
# Closed forms of the pairing loops

`unpair`'s loop body moves `(scratch2, scratch1)` one step along Cantor's order, so the loop
leaves `unpair(n)` there; `pair`'s loop adds `T(a + b) + a`.  With these, every subroutine of
the program has a closed form (`Ops.lean`).
-/

namespace TM.PA.N

open TM.PA

theorem f28_eq (s : R) :
    f28 s = { s with s2 := (nextP (s.s2, s.s1)).fst, s1 := (nextP (s.s2, s.s1)).snd } := by
  simp only [f28, f31, f34, p34, f35_eq]
  cases h : s.s1 with
  | zero => simp [h, nextP]
  | succ n => simp [h, nextP]

theorem loop_f28_ws : ∀ (n : Nat) (s : R), n ≤ s.ws →
    loopN 3 f28 n s =
      { s with ws := s.ws - n, s2 := (nextN n (s.s2, s.s1)).fst, s1 := (nextN n (s.s2, s.s1)).snd } := by
  intro n
  induction n with
  | zero => intro s _; simp [loopN, nextN]
  | succ n ih =>
    intro s hn
    rw [loopN, ih _ (by simp [f28_eq]; omega)]
    simp [f28_eq, nextN]; omega

theorem loop_f28_pl : ∀ (n : Nat) (s : R), n ≤ s.pl →
    loopN 0 f28 n s =
      { s with pl := s.pl - n, s2 := (nextN n (s.s2, s.s1)).fst, s1 := (nextN n (s.s2, s.s1)).snd } := by
  intro n
  induction n with
  | zero => intro s _; simp [loopN, nextN]
  | succ n ih =>
    intro s hn
    rw [loopN, ih _ (by simp [f28_eq]; omega)]
    simp [f28_eq, nextN]; omega

/-- `unpair(scratch2, scratch1, wffstack)` -/
theorem f74_eq (s : R) : f74 s =
    { s with ws := 0, s2 := (unpair (pair s.s2 s.s1 + s.ws)).fst, s1 := (unpair (pair s.s2 s.s1 + s.ws)).snd } := by
  simp only [f74]; rw [loop_f28_ws _ s (by simp)]; simp [nextN_eq]

/-- `unpair(scratch2, scratch1, prooflist)` -/
theorem f22_eq (s : R) : f22 s =
    { s with pl := 0, s2 := (unpair (pair s.s2 s.s1 + s.pl)).fst, s1 := (unpair (pair s.s2 s.s1 + s.pl)).snd } := by
  simp only [f22]; rw [loop_f28_pl _ s (by simp)]; simp [nextN_eq]

theorem f72_eq (s : R) (h : s.ws = 0) : f72 s = { s with s1 := s.s1 + 1 + s.top } := by
  simp [f72, f80, f84_eq, f56_eq, h]

theorem tri_succ (n : Nat) : tri (n + 1) = tri n + (n + 1) := rfl

theorem loop_f72 : ∀ (t : Nat) (s : R), s.ws = 0 → s.top = t →
    loopN 2 f72 t s = { s with top := 0, s1 := s.s1 + tri t } := by
  intro t
  induction t with
  | zero => intro s _ ht; obtain ⟨⟩ := s; simp_all [loopN, tri]
  | succ t ih =>
    intro s hw ht
    rw [loopN, f72_eq _ (by simpa using hw), ih _ (by simpa using hw) (by simp; omega)]
    simp [ht, tri_succ]; omega

/-- `pair(scratch1, wffstack, topwff)`: scratch1 += pair(wffstack, topwff) -/
theorem f52_eq (s : R) : f52 s = { s with ws := 0, top := 0, s1 := s.s1 + pair s.ws s.top } := by
  have h := loop_f72 _ (f56 s) (by simp) rfl
  simp only [f52, f57, R.get_2]
  rw [h]
  simp [pair, Nat.add_comm s.top s.ws]; omega

end TM.PA.N

namespace TM.PA.N

open TM.PA

@[simp] theorem pair_zero : pair 0 0 = 0 := rfl

/-- pop the stack into scratch1 (`un(wffstack)` then `while scratch2: wffstack++`) -/
theorem f112_eq (s : R) (h1 : s.s1 = 0) (h2 : s.s2 = 0) :
    f112 s = { s with ws := (unpair s.ws).fst, s1 := (unpair s.ws).snd } := by
  simp [f112, f74_eq, f88_eq, h1, h2]

theorem f109_eq (s : R) (h1 : s.s1 = 0) (h2 : s.s2 = 0) :
    f109 s = { s with ws := (unpair s.ws).fst, ac := s.ac - 1, top := if s.ac = 0 then (unpair s.ws).snd else s.top } := by
  simp only [f109, f113, f112_eq s h1 h2, p116, f116, f117, f119, f120, f123, f87_eq]
  by_cases h : s.ac = 0 <;> simp [h, h1]

theorem f66_eq (s : R) (h1 : s.s1 = 0) (h2 : s.s2 = 0) :
    f66 s = { s with ws := (unpair s.ws).fst, top := pair (unpair s.ws).snd s.top } := by
  simp [f66, f75, f81, f85, f74_eq, f53_eq, f52_eq, f87_eq, f88_eq, h1, h2]

end TM.PA.N

namespace TM.PA

/-- a test between two register files is a register file of tests -/
@[simp] theorem R.ite_mk (c : Prop) [Decidable c] (a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Nat) :
    (if c then R.mk a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 else R.mk b1 b2 b3 b4 b5 b6 b7 b8 b9 b10) =
      R.mk (if c then a1 else b1) (if c then a2 else b2) (if c then a3 else b3) (if c then a4 else b4)
        (if c then a5 else b5) (if c then a6 else b6) (if c then a7 else b7) (if c then a8 else b8)
        (if c then a9 else b9) (if c then a10 else b10) := by
  by_cases h : c <;> simp [h]

end TM.PA
