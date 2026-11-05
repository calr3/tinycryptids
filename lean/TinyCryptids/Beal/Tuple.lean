import TinyCryptids.Beal.Stack
import TinyCryptids.Beal.Walk

/-!
# One tuple

The tape for `(x, y, z, a, b, c)`: exponent blocks of `x + 1`, `y + 1`, `z + 1` cells, base
blocks of `a + 3`, `b + 3`, `c + 3` cells, then `00 M 00 A` with `M = 1`, `A = 11`; x carries the
anchor on cell 1. From `gAC` (the coprimality walk starts) the machine halts if
`gcd(a, b) = 1` and `a^x + b^y = c^z`, and otherwise reaches `en2C` (the next enumeration
step) with the same tuple.
-/

namespace TM.Beal
open St TM.Carmichael

/-- `00 M 00 A` -/
def RT : Strm := F ::: F ::: true ::: F ::: F ::: ones 2 blank

/-- the tape right of x -/
def tupR (y z a b c : Nat) : Strm :=
  F ::: F ::: ones (y + 1) (F ::: F ::: ones (z + 1) (F ::: F ::: ones (a + 3) (F ::: F ::: ones (b + 3)
    (F ::: F ::: ones (c + 3) RT))))

/-- state `gA0` on x's anchor -/
def gAC (x y z a b c : Nat) : Cfg St := ⟨gA0, true ::: blank, F ::: ones (x - 1) (tupR y z a b c)⟩

/-- state `en2` on x's cell 2 -/
def en2C (x y z a b c : Nat) : Cfg St := ⟨en2, F ::: true ::: blank, ones (x - 1) (tupR y z a b c)⟩

/-- left of a's separator: z, y and x with its anchor -/
def La (x y z : Nat) : Strm := ones (z + 1) (F ::: F ::: ones (y + 1) (F ::: F ::: ones (x - 1) (F ::: true ::: blank)))

theorem walk_entry (x y z a b c : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (gAC x y z a b c) (TK 0 (a - 1) 0 (b - 1) (La x y z) (ones (c + 3) RT)) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold gAC tupR TK La
  gR; sRn (x - 1); gR; gR; sRn (y + 1); gR; gR; sRn (z + 1); gR; gR; gR; gR; gR
  sRn (a + 1); gR; gR; gR; gR; gL
  rw [show a + 1 - 1 + 1 = a + 1 by omega, show b + 1 - 1 + 1 = b + 1 by omega]
  fin

theorem PHE : ParserL delta HE1 HE2 := ⟨rfl, rfl, rfl⟩
theorem HH : Home delta H1 H2 H3 H4 H5 := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

macro "c12" : tactic => `(tactic| repeat (first | exact Clean.nil | apply Clean.one | apply Clean.sep))

/-- not coprime: H_a is filled, the machine goes home and on to the next tuple -/
theorem nc_exit (x y z a b c : Nat) (hx : 2 ≤ x) (ha : 1 ≤ a) (hb : 2 ≤ b) :
    Rch (NcC (a - 1) (b - 2) (La x y z) (ones (c + 3) RT)) (en2C x y z a b c) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 2 := ⟨x - 2, by omega⟩
  unfold NcC La
  rw [show a + 1 - 1 + 1 = a + 1 by omega, show b + 2 - 2 + 5 = b + 5 by omega]
  have hw : Clean (rep (b + 5) ++ F :: F :: rep (a + 1)) := Clean.rep_append _ (Clean.sep (Clean.replicate a))
  have e1 : ∀ S : Strm, ones (b + 5) (F ::: F ::: ones (a + 1) (F ::: ones 2 S)) =
      app (rep (b + 5) ++ F :: F :: rep (a + 1)) (F ::: true ::: true ::: S) := by
    intro S; simp [app_append, app_replicate, ones_succ]
  rw [e1]
  refine Rch.tr (PHE.find hw _ _) ?_
  gR; gL
  have hw2 : Clean12 ([true, true, F, F] ++ rep (z + 1) ++ F :: F :: rep (y + 1) ++ F :: F :: rep (x + 1)) := by
    refine Clean12.of_clean ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Clean.one (Clean.one (Clean.sep (Clean.rep_append z (Clean.sep (Clean.rep_append y
      (Clean.sep (Clean.replicate x)))))))
  have e2 : true ::: true ::: F ::: F ::: ones (z + 1) (F ::: F ::: ones (y + 1) (F ::: F :::
      ones (x + 2 - 1) (F ::: true ::: blank))) =
      app ([true, true, F, F] ++ rep (z + 1) ++ F :: F :: rep (y + 1) ++ F :: F :: rep (x + 1))
        (F ::: true ::: blank) := by
    rw [show x + 2 - 1 = x + 1 by omega]; simp [app_append, app_replicate]
  rw [e2]
  refine Rch.tr (HH.goHole hw2 _) ?_
  gR
  unfold en2C tupR
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  fin

/-- the blocks right of a during the first power: b, c, M, A -/
def X1 (b c : Nat) : List Bool := rep (b + 3) ++ F :: F :: (rep (c + 3) ++ F :: F :: (true :: F :: F :: rep 2))

theorem X1_blk (b c : Nat) : Blk (X1 b c) :=
  Blk.cons (b + 2) (Blk.cons (c + 2) (Blk.cons 0 (Blk.one 1)))

/-- coprime: push R = 1 and start the first power at H_a -/
theorem cop_start (x y z a b c : Nat) (hx : 1 ≤ x) (hy : 1 ≤ y) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Rch (CopC (a - 1) (b - 1) (La x y z) (ones (c + 3) RT))
      (bAtC (true ::: leftOf (y - 1) (z + 1) x 1 blank) a 1 (X1 b c) 1 0) := by
  obtain ⟨a, rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  unfold CopC
  rw [show a + 1 - 1 + 1 = a + 1 by omega, show b + 1 - 1 + 1 = b + 1 by omega]
  have hW : Blk (rep (b + 1) ++ F :: F :: (rep (c + 3) ++ F :: F :: (true :: F :: F :: rep 2))) :=
    Blk.cons b (Blk.cons (c + 2) (Blk.cons 0 (Blk.one 1)))
  have e0 : ones (b + 1) (F ::: F ::: ones (c + 3) RT) =
      app (rep (b + 1) ++ F :: F :: (rep (c + 3) ++ F :: F :: (true :: F :: F :: rep 2))) blank := by
    simp [RT, app_append, app_replicate]
  rw [e0]
  refine Rch.tr ((tscan hW _).1) ?_
  refine Rch.tr (push3 _) ?_
  have hw : Clean (true :: F :: F :: ((rep (b + 1) ++ F :: F :: (rep (c + 3) ++ F :: F :: true :: F :: F :: rep 2)).reverse
      ++ rep 3 ++ F :: F :: rep (a + 1))) := by
    refine Clean.one ?_
    rw [List.append_assoc]
    exact hW.reverse.clean_sep_append (Clean.rep_append 3 (Clean.sep (Clean.replicate a)))
  have e : true ::: false ::: false ::: app (rep (b + 1) ++ F :: F :: (rep (c + 3) ++ F :: F :: true :: F :: F :: rep 2)).reverse
      (ones 3 (F ::: F ::: ones (a + 1) (F ::: ones 2 (F ::: F ::: La x y z)))) =
      app (true :: F :: F :: ((rep (b + 1) ++ F :: F :: (rep (c + 3) ++ F :: F :: true :: F :: F :: rep 2)).reverse
        ++ rep 3 ++ F :: F :: rep (a + 1))) (F ::: true ::: true ::: F ::: F ::: La x y z) := by
    simp only [app_cons, app_append, app_replicate]; rfl
  rw [e]
  refine Rch.tr (PNB.find hw _ _) ?_
  gR
  obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  unfold bAtC leftOf preL rgt X1 La
  simp [sep, List.reverse_append, List.reverse_replicate, app_append, app_replicate, cons_blank, ones_succ]
  fin

/-- after an unequal compare: restore A, take the cursor out of a, go home, anchor x -/
theorem clear_home (x y z a b c : Nat) (hx : 1 ≤ x) :
    Rch (crC (F ::: F ::: ones (c + 3) (F ::: F ::: ones (b + 3) (F ::: F ::: ones (a + 1)
        (F ::: true ::: F ::: F ::: ones (z + 1) (F ::: F ::: ones (y + 1) (F ::: F ::: ones (x + 1) blank)))))))
      (en2C x y z a b c) := by
  unfold crC
  gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gL
  have hw : Clean ([true, F, F, true] ++ F :: F :: (rep (c + 3) ++ F :: F :: (rep (b + 3) ++ F :: F :: rep (a + 1)))) := by
    simp only [List.cons_append, List.nil_append]
    exact Clean.one (Clean.sep (Clean.sep (Clean.rep_append (c + 2) (Clean.sep (Clean.rep_append (b + 2)
      (Clean.sep (Clean.replicate a)))))))
  have e1 : ∀ S : Strm, true ::: F ::: F ::: true ::: F ::: F ::: ones (c + 3) (F ::: F ::: ones (b + 3)
      (F ::: F ::: ones (a + 1) (F ::: true ::: S))) =
      app ([true, F, F, true] ++ F :: F :: (rep (c + 3) ++ F :: F :: (rep (b + 3) ++ F :: F :: rep (a + 1))))
        (F ::: true ::: S) := by
    intro S; simp [app_append, app_replicate]
  show Rch (cfgL HE1 (true ::: F ::: F ::: true ::: F ::: F ::: ones (c + 3) (F ::: F ::: ones (b + 3)
      (F ::: F ::: ones (a + 1) (F ::: true ::: F ::: F ::: ones (z + 1) (F ::: F ::: ones (y + 1)
        (F ::: F ::: ones (x + 1) blank)))))) (true ::: blank)) _
  rw [e1]
  refine Rch.tr (PHE.find hw _ _) ?_
  gR; gL
  obtain ⟨x, rfl⟩ : ∃ x', x = x' + 1 := ⟨x - 1, by omega⟩
  have hw2 : Clean12 ([true, F, F] ++ rep (z + 1) ++ F :: F :: rep (y + 1) ++ F :: F :: rep (x + 1)) := by
    refine Clean12.of_clean ?_
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    exact Clean.one (Clean.sep (Clean.rep_append z (Clean.sep (Clean.rep_append y
      (Clean.sep (Clean.replicate x))))))
  have e2 : true ::: F ::: F ::: ones (z + 1) (F ::: F ::: ones (y + 1) (F ::: F ::: ones (x + 1 + 1) blank)) =
      app ([true, F, F] ++ rep (z + 1) ++ F :: F :: rep (y + 1) ++ F :: F :: rep (x + 1)) (true ::: blank) := by
    simp [app_append, app_replicate, ones_succ']
  rw [e2]
  show Rch (cfgL H1 (app ([true, F, F] ++ rep (z + 1) ++ F :: F :: rep (y + 1) ++ F :: F :: rep (x + 1))
    (true ::: blank)) _) _
  refine Rch.tr (HH.go hw2 _) ?_
  simp only [List.reverse_append, List.reverse_replicate, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.append_assoc, List.cons_append, List.singleton_append, app_append, app_replicate, app_cons, app_nil]
  gR
  unfold en2C tupR RT
  simp [List.reverse_append, List.reverse_replicate, app_append, app_replicate, ones_succ]
  fin

theorem pow_pos' {a : Nat} (ha : 1 ≤ a) (E : Nat) : 1 ≤ a ^ E := by
  induction E with
  | zero => simp
  | succ n ih => rw [Nat.pow_succ]; exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ ha)

/-- One tuple: from the coprimality walk the machine halts iff `gcd(a, b) = 1` and
`a^x + b^y = c^z`, and otherwise reaches the next enumeration step with the same tuple. -/
theorem tuple_check (x y z a b c : Nat) (hx : 2 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) :
    (Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z → HaltAt (gAC x y z a b c)) ∧
    (¬ (Nat.gcd a b = 1 ∧ a ^ x + b ^ y = c ^ z) → Rch (gAC x y z a b c) (en2C x y z a b c)) := by
  have walk := Rch.tr (walk_entry x y z a b c ha hb) (test a b ha hb (La x y z) (ones (c + 3) RT))
  unfold Res at walk
  by_cases hg : Nat.gcd a b = 1
  · rw [if_pos hg] at walk
    obtain ⟨y, rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    obtain ⟨z, rfl⟩ : ∃ z', z = z' + 1 := ⟨z - 1, by omega⟩
    have hpa := pow_pos' ha x
    have hpb := pow_pos' hb (y + 1)
    have hpc := pow_pos' hc (z + 1)
    have s1 := cop_start x (y + 1) (z + 1) a b c (by omega) (by omega) ha hb
    rw [show y + 1 - 1 = y by omega] at s1
    have p1 := pow_full (X1_blk b c) y (z + 1 + 1) x a blank (by omega) (by omega) ha
    have hY : Blk (rep (c + 3) ++ [F, F, true]) := Blk.cons (c + 2) (Blk.one 0)
    have hX1 : X1 b c = rep (b + 3) ++ F :: F :: ((rep (c + 3) ++ [F, F, true]) ++ F :: F :: rep 2) := by
      simp [X1]
    rw [hX1] at p1 s1
    have n1 := next_base hY y (z + 1 + 1) x a b 2 (a ^ x) blank (by omega) hb (by omega) hpa
    rw [show z + 1 + 1 - 2 = z by omega] at n1
    have hX2 : Blk ((rep (c + 3) ++ [F, F, true]) ++ F :: F :: rep (2 + a ^ x)) := by
      rw [show 2 + a ^ x = (1 + a ^ x) + 1 by omega]; exact hY.join (Blk.one _)
    have p2 := pow_full hX2 z (a + 3) (y + 1) b (F ::: F ::: ones (x + 1) blank) (by omega) (by omega) hb
    have hX2' : (rep (c + 3) ++ [F, F, true]) ++ F :: F :: rep (2 + a ^ x) =
        rep (c + 3) ++ F :: F :: ([true] ++ F :: F :: rep (2 + a ^ x)) := by simp
    rw [hX2'] at p2 n1
    have n2 := next_base (Blk.one 0) z (a + 3) (y + 1) b c (2 + a ^ x) (b ^ (y + 1))
      (F ::: F ::: ones (x + 1) blank) (by omega) hc (by omega) hpb
    rw [show a + 3 - 2 = a + 1 by omega] at n2
    have hX3 : Blk ([true] ++ F :: F :: rep (2 + a ^ x + b ^ (y + 1))) := by
      rw [show 2 + a ^ x + b ^ (y + 1) = (1 + a ^ x + b ^ (y + 1)) + 1 by omega]; exact (Blk.one 0).join (Blk.one _)
    have p3 := pow_full hX3 (a + 1) (b + 3) (z + 1) c (F ::: F ::: ones (y + 1 + 1) (F ::: F ::: ones (x + 1) blank))
      (by omega) (by omega) hc
    have ce := compare_entry (a + 1) (b + 3) (z + 1) c (2 + a ^ x + b ^ (y + 1)) (c ^ (z + 1))
      (F ::: F ::: ones (y + 1 + 1) (F ::: F ::: ones (x + 1) blank)) (by omega) hpc
    simp only [List.singleton_append] at p3
    have path := Rch.tr walk (Rch.tr s1 (Rch.tr p1 (Rch.tr n1 (Rch.tr p2 (Rch.tr n2 (Rch.tr p3 ce))))))
    have zr := zz_result (F ::: F ::: ones (c + 3) (F ::: F ::: ones (b + 3) (F ::: F ::: ones (a + 1)
      (F ::: true ::: F ::: F ::: ones (z + 1 + 1) (F ::: F ::: ones (y + 1 + 1) (F ::: F ::: ones (x + 1) blank))))))
      (2 + a ^ x + b ^ (y + 1)) (c ^ (z + 1) + 2) 2 0 (by omega) (by omega)
    refine ⟨fun h => HaltAt.back path (zr.1 (by omega)), fun h => ?_⟩
    have hne : a ^ x + b ^ (y + 1) ≠ c ^ (z + 1) := fun he => h ⟨hg, he⟩
    exact Rch.tr path (Rch.tr (zr.2 (by omega)) (clear_home x (y + 1) (z + 1) a b c (by omega)))
  · rw [if_neg hg] at walk
    have hb2 : 2 ≤ b := by
      rcases Nat.lt_or_ge b 2 with h | h
      · obtain rfl : b = 1 := by omega
        exact absurd (Nat.gcd_one_right a) hg
      · exact h
    exact ⟨fun h => absurd h.1 hg, fun _ => Rch.tr walk (nc_exit x y z a b c hx ha hb2)⟩

end TM.Beal
