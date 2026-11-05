import TinyCryptids.Core.Routines
import TinyCryptids.Brocard.Tac

/-!
# Routines of the design

Tape (`F` = blank):

    W 00 N 00 F 00 S        (square test)
    W 00 N 00 F 00 Q        (multiplication)

* `W` : `w` ones, the warm-up countdown;
* `N` : `n + 2` cells, the round `n`; during the multiplication a hole at cell `a + 1`;
* `F` : `v + 4` cells (`v = n!`); a hole at `u + 1` (test) or the copy cursor at `b + 3`;
* `S` : `d + 2` cells, the odd number `d`, with a cyclic hole at `c + 1`;
* `Q` : `q` ones, the copies made so far.
-/

namespace TM.Brocard
open St

local notation "F" => false

theorem PPS : ParserR delta PS1 PS2 := by constructor <;> rfl
theorem PPK : ParserR delta PK1 PK2 := by constructor <;> rfl
theorem PPP : ParserL delta PP1 PP2 := by constructor <;> rfl
theorem PPB : ParserL delta PB1 PB2 := by constructor <;> rfl
theorem PPN : ParserL delta PN1 PN2 := by constructor <;> rfl

/-! ## configurations -/

/-- left of N: the separator, then W -/
def LW (w : Nat) : Strm := F ::: F ::: ones w blank
/-- N seen from its right end, hole at cell `a + 1`, then W -/
def NH (n a w : Nat) : Strm := ones (n - a) (F ::: ones (a + 1) (LW w))
/-- right of F: the separator, then Q -/
def QS (q : Nat) : Strm := F ::: F ::: ones q blank

/-- multiplication: about to scan N right of its hole (at cell `a + 1`) and set the F cursor -/
def G (n w a v q : Nat) : Cfg St :=
  ⟨g1, F ::: ones (a + 1) (LW w), ones (n - a) (F ::: F ::: ones (v + 4) (QS q))⟩

/-- copy loop: the cursor is at cell `b + 3` of F, the head on F's right separator -/
def X (n w a v b q : Nat) : Cfg St :=
  ⟨x1, ones (v - b) (F ::: ones (b + 3) (F ::: F ::: NH n a w)), QS q⟩

/-- merge: all copies made, the head on the separator between N and F -/
def MG (n w v q : Nat) : Cfg St := ⟨m1, F ::: ones (n + 2) (LW w), F ::: ones (v + 4) (QS q)⟩

def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_none rfl)

theorem ones_cons_blank (s : Nat) : ones s (true ::: blank) = ones (s + 1) blank := (ones_succ' s blank).symm

/-- a left step from any configuration whose cells compute (e.g. on the blank part) -/
macro "gL0" : tactic => `(tactic| refine Rch.tr (stepL (δ := delta) (by rfl)) ?_)
macro "gRb" : tactic => `(tactic| first | gR | (refine blankR ?_; gR))

/-! ## multiplication -/

/-- set the F cursor at cell 3 -/
theorem g_to_x (n w a v q : Nat) : Rch (G n w a v q) (X n w a v 0 q) := by
  unfold G X NH
  sRn (n - a); gR; gR; gR; gR; gR; gR
  sRn v; fin

/-- copy one cell (not the last one) -/
theorem copy_one (n w a v b q : Nat) (hb : b + 1 < v) :
    Rch (X n w a v b q) (X n w a v (b + 1) (q + 1)) := by
  obtain ⟨k, hk⟩ : ∃ k, v - b = k + 2 := ⟨v - b - 2, by omega⟩
  unfold X QS
  rw [hk, show v - (b + 1) = k + 1 by omega]
  gR; gR; sRn q; refine blankR ?_; gL
  refine Rch.tr (PPB.find2 q (k + 1) _ _) ?_
  gR; gR; gR; gL; gR; sRn (k + 1)
  rw [ones_cons_blank]; fin

/-- the cursor runs off: back to the N hole and advance it -/
theorem copy_last_pre (n w a v b q : Nat) (hb : b + 1 = v) (ha : a < n) :
    Rch (X n w a v b q)
      ⟨n1, ones (a + 1) (LW w), F ::: ones (n - a) (F ::: F ::: ones (v + 4) (QS (q + 1)))⟩ := by
  obtain ⟨e, he⟩ : ∃ e, n - a = e + 1 := ⟨n - a - 1, by omega⟩
  unfold X QS NH
  obtain rfl : v = b + 1 := hb.symm
  rw [show b + 1 - b = 1 by omega, he]
  gR; gR; sRn q; refine blankR ?_; gL
  refine Rch.tr (PPB.find2 q 0 _ _) ?_
  gR; gR; gR; gL
  show Rch (cfgL PN1 (ones (b + 1 + 4) (F ::: F ::: ones (e + 1) (F ::: ones (a + 1) (LW w))))
    (F ::: F ::: ones q (true ::: blank))) _
  refine Rch.tr (PPN.find2 (b + 1 + 4) e _ _) ?_
  gR; rw [ones_cons_blank]; fin

theorem copy_last_next (n w a v b q : Nat) (hb : b + 1 = v) (ha : a + 1 < n) :
    Rch (X n w a v b q) (G n w (a + 1) v (q + 1)) := by
  refine Rch.tr (copy_last_pre n w a v b q hb (by omega)) ?_
  obtain ⟨e, he⟩ : ∃ e, n - a = e + 2 := ⟨n - a - 2, by omega⟩
  unfold G
  rw [he, show n - (a + 1) = e + 1 by omega]
  gR; gR; gL; gR; fin

theorem copy_last_done (n w a v b q : Nat) (hb : b + 1 = v) (ha : a + 1 = n) :
    Rch (X n w a v b q) (MG n w v (q + 1)) := by
  refine Rch.tr (copy_last_pre n w a v b q hb (by omega)) ?_
  subst ha
  unfold MG
  rw [show a + 1 - a = 1 by omega]
  gR; gR; gR; fin

/-- all the copies: from copy `a`, cell `b` -/
theorem copies (n w v : Nat) (hv : 1 ≤ v) : ∀ k a b q, (n - 1 - a) * v + (v - 1 - b) = k →
    a < n → b < v → Rch (X n w a v b q) (MG n w v (q + k + 1)) := by
  intro k
  induction k with
  | zero =>
    intro a b q h ha hb
    have h1 : v - 1 - b = 0 := by omega
    have h2 : (n - 1 - a) * v = 0 := by omega
    have h3 : n - 1 - a = 0 := by
      rcases Nat.eq_zero_or_pos (n - 1 - a) with h | h
      · exact h
      · have := Nat.mul_le_mul_right v h; omega
    exact copy_last_done n w a v b q (by omega) (by omega)
  | succ k ih =>
    intro a b q h ha hb
    by_cases hb1 : b + 1 < v
    · refine Rch.tr (copy_one n w a v b q hb1) ?_
      rw [show q + (k + 1) + 1 = q + 1 + k + 1 by omega]
      exact ih a (b + 1) (q + 1) (by omega) ha hb1
    · have hb2 : b + 1 = v := by omega
      have ha1 : a + 1 < n := by
        apply Classical.byContradiction; intro hc
        have : n - 1 - a = 0 := by omega
        rw [this] at h; omega
      refine Rch.tr (copy_last_next n w a v b q hb2 ha1) ?_
      refine Rch.tr (g_to_x n w (a + 1) v (q + 1)) ?_
      have e : (n - 1 - a) * v = (n - 1 - (a + 1)) * v + v := by
        rw [show n - 1 - a = n - 1 - (a + 1) + 1 by omega, Nat.add_mul, Nat.one_mul]
      rw [show q + (k + 1) + 1 = q + 1 + k + 1 by omega]
      exact ih (a + 1) 0 (q + 1) (by omega) ha1 (by omega)

/-- the whole multiplication: `n * v` copies -/
theorem multiply (n w v : Nat) (hn : 1 ≤ n) (hv : 1 ≤ v) : Rch (G n w 0 v 0) (MG n w v (n * v)) := by
  refine Rch.tr (g_to_x n w 0 v 0) ?_
  have := copies n w v hv ((n - 1) * v + (v - 1)) 0 0 0 (by simp only [Nat.sub_zero]) (by omega) (by omega)
  have e : n * v = (n - 1) * v + v := by
    rw [show n * v = (n - 1 + 1) * v by rw [Nat.sub_add_cancel hn], Nat.add_mul, Nat.one_mul]
  rw [show 0 + ((n - 1) * v + (v - 1)) + 1 = n * v by rw [e]; omega] at this
  exact this

/-! ## merge Q into F, grow N, the warm-up gate -/

/-- the square test: about to advance the F hole (at cell `u + 1`); S has its hole at `c + 1` -/
def TP (n v u d c : Nat) : Cfg St :=
  ⟨p1, ones (u + 1) (F ::: F ::: ones (n + 2) blank),
    F ::: ones (v + 2 - u) (F ::: F ::: ones (c + 1) (F ::: ones (d - c) blank))⟩

theorem merge_pre (n w v q : Nat) (hq : 1 ≤ q) :
    Rch (MG n w v q) (cfgL v3 (ones w blank) (F ::: ones (n + 3) (F ::: F ::: ones (v + q + 4) blank))) := by
  obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
  unfold MG QS
  gR; sRn (v + 4); gR; gR; sRn (p + 1); refine blankR ?_; gL
  gL; rw [ones_cons_true]; gL
  rw [show ones p (true ::: ones (v + 4) (F ::: F ::: ones (n + 2) (LW w))) =
      ones (p + v + 5) (F ::: F ::: ones (n + 2) (LW w)) by
    rw [← ones_succ, ones_add, show p + (v + 4 + 1) = p + v + 5 by omega]]
  sLn (p + v + 5); gL; gL; sLn (n + 2)
  unfold LW; gL; gL
  rw [cons_blank, cons_blank, cons_blank, show v + (p + 1) + 4 = p + v + 5 by omega]
  fin

/-- W still has a cell: next round is a warm-up round -/
theorem gate_warm (n w v : Nat) :
    Rch (cfgL v3 (ones (w + 2) blank) (F ::: ones (n + 3) (F ::: F ::: ones (v + 4) blank)))
      (G (n + 1) (w + 1) 0 v 0) := by
  unfold G LW QS
  gL; gR; gR; gR; gR; gR
  rw [show n + 1 - 0 = n + 1 by omega]; simp only [ones_zero, cons_blank]; fin

/-- W is used up: write S = 101, put the F hole at cell 1 and start the test -/
theorem gate_test (n w v : Nat) (hw : w ≤ 1) :
    Rch (cfgL v3 (ones w blank) (F ::: ones (n + 3) (F ::: F ::: ones (v + 4) blank)))
      (TP (n + 1) v 0 1 0) := by
  have pre : Rch (cfgL v3 (ones w blank) (F ::: ones (n + 3) (F ::: F ::: ones (v + 4) blank)))
      (cfgL v4 blank (F ::: F ::: ones (n + 3) (F ::: F ::: ones (v + 4) blank))) := by
    rcases w with _ | _ | w
    · gL0; fin
    · gL; fin
    · omega
  refine Rch.tr pre ?_
  unfold TP
  gR; gR; gR; sRn (n + 3); gR; gR; gR; gR; sRn (v + 2)
  refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR; refine blankR ?_; gR
  refine blankR ?_; gL; gL
  refine Rch.tr (PPP.find2 1 (v + 1) _ _) ?_
  gR
  simp only [tl_blank, cons_blank]
  rw [show v + 2 - 0 = v + 2 by omega, show 1 - 0 = 1 by omega]; fin

/-! ## the square test -/

/-- one unit; the S hole moves on without wrapping -/
theorem test_step (n v u d c : Nat) (hu : u ≤ v) (hc : c + 1 < d) :
    Rch (TP n v u d c) (TP n v (u + 1) d (c + 1)) := by
  obtain ⟨e, he⟩ : ∃ e, v + 2 - u = e + 2 := ⟨v - u, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, d - c = k + 2 := ⟨d - c - 2, by omega⟩
  unfold TP
  rw [he, hk, show v + 2 - (u + 1) = e + 1 by omega, show d - (c + 1) = k + 1 by omega]
  gR; gR; gL; gR
  refine Rch.tr (PPS.find2 (e + 1) c _ _) ?_
  gL; gR; gR; gL; gL
  refine Rch.tr (PPP.find2 (c + 2) e _ _) ?_
  gR; fin

/-- one unit; the S hole wraps around and S grows by 2 -/
theorem test_wrap (n v u d : Nat) (hu : u ≤ v) (hd : 1 ≤ d) :
    Rch (TP n v u d (d - 1)) (TP n v (u + 1) (d + 2) 0) := by
  obtain ⟨e, he⟩ : ∃ e, v + 2 - u = e + 2 := ⟨v - u, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold TP
  rw [he, show c + 1 - 1 = c by omega, show c + 1 - c = 1 by omega, show v + 2 - (u + 1) = e + 1 by omega,
    show c + 1 + 2 - 0 = c + 3 by omega]
  gR; gR; gL; gR
  refine Rch.tr (PPS.find2 (e + 1) c _ _) ?_
  gL; gR; gR; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL s6 (ones (c + 4) (F ::: F ::: ones (e + 1) (F ::: true ::: ones (u + 1)
    (F ::: F ::: ones (n + 2) blank)))) (true ::: blank)) _
  sLn (c + 4); gR; gR; gL
  refine Rch.tr (PPP.find2 1 e _ _) ?_
  gR; rw [ones_cons_blank]; fin

theorem PPKc : ParserR delta PK1 PK2 := PPK

/-- no unit left and the S hole at cell 1: n!+1 is a square -/
theorem test_halt (n v d : Nat) (hd : 1 ≤ d) : HaltAt (TP n v (v + 1) d 0) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  unfold TP HaltAt; apply Exists.intro; apply Exists.intro
  rw [show v + 2 - (v + 1) = 1 by omega, show e + 1 - 0 = e + 1 by omega]
  gR; gR; gR; gR
  refine Rch.tr (PPK.find0 1 _ _) ?_
  gL; gL; gL; gL; fin

/-- no unit left, the S hole elsewhere: erase S, put the N hole at cell 1 -/
theorem test_no (n v d c : Nat) (hc0 : 1 ≤ c) (hc : c < d) :
    Rch (TP n v (v + 1) d c) (G n 0 0 v 0) := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, d - (c' + 1) = k + 1 := ⟨d - c' - 2, by omega⟩
  unfold TP G
  rw [show v + 2 - (v + 1) = 1 by omega, hk]
  gR; gR; gR; gR
  refine Rch.tr (PPK.find0 (c' + 2) _ _) ?_
  gL; gL; gL; gL
  sLn c'; gR
  rw [show ones c' (true ::: true ::: F ::: true ::: ones k blank) = ones (c' + 2) (F ::: ones (k + 1) blank)
    from by rw [← ones_succ', ← ones_succ']; rfl]
  eRn (c' + 2); gR; gR; eRn k; refine blankR ?_; gR; refine blankR ?_; gL
  show Rch (cfgL z1 (zeros 1 (zeros k (zeros 2 (zeros (c' + 2) (zeros 2 (true ::: true :::
    ones (v + 1 + 1) (F ::: F ::: ones (n + 2) blank))))))) (F ::: blank)) _
  rw [zeros_add, zeros_add, zeros_add, zeros_add]
  zLn (1 + k + 2 + (c' + 2) + 2); gL; sLn (v + 3); gL; gL; sLn (n + 2); gR; gR; gR
  unfold LW QS; simp only [tl_blank, cons_blank, ones_zero]
  rw [show n - 0 = n by omega, zeros_blank, ones_cons_blank]; fin

/-! ## the seed -/

theorem seed_reach : Rch start (X 1 7 0 1 0 0) := by
  unfold start X NH LW QS
  gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb; gRb
  simp only [ones_zero, cons_blank]; fin

end TM.Brocard
