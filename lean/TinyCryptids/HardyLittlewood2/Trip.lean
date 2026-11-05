import TinyCryptids.HardyLittlewood2.Blocks

/-!
# The test at a prime: one cell of a cursor, a trip to `E` and back

During the test the tape is, left to right,

    E  0000  Ub…  b  00  middle…  t  00  Y

* `E`: `n` ones (`n = e + 1` for the counter value `e`; no cells before the first top cell);
* `Ub`: the bottom blocks still to come (B', nearest the current one first);
* `b`: the bottom block, a hole at cell `jb`; `t`: the top block, a hole at cell `jt`;
* `M`: the blocks between them, listed from `t` leftwards;
* `Y`: everything right of `t` (the processed tops and the trial-division region).

A trip goes home (left to the four 0s), adds a cell to `E` (a top cell) or removes one (a
bottom cell; halt if only one is left), and comes back to the cursor: the second hole (top)
or the first (bottom).
-/

namespace TM.HardyLittlewood2
open St

local notation "F" => false

/-- left of a bottom block: the bottoms to come, the four 0s, `E` -/
def LB (n : Nat) (Ub : List Nat) : Strm := F ::: F ::: bks Ub (F ::: F ::: ones n blank)

/-- left of the top block's cell 0 -/
def LT (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) : Strm :=
  F ::: F ::: bks M (ones (b + 1 - jb) (F ::: ones jb (LB n Ub)))

/-- right of the bottom block's right guard -/
def RB (M : List Nat) (t jt : Nat) (Y : Strm) : Strm :=
  F ::: F ::: bks M.reverse (ones jt (F ::: ones (t + 1 - jt) Y))

/-- right of the four 0s -/
def RT (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) : Strm :=
  bks Ub.reverse (ones jb (F ::: ones (b + 1 - jb) (RB M t jt Y)))

/-- the head on the top hole -/
def TF (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) : Cfg St :=
  ⟨Tf, ones jt (LT n Ub b jb M), F ::: ones (t + 1 - jt) Y⟩

/-- the head on the bottom hole -/
def BF (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) : Cfg St :=
  ⟨Bf, ones jb (LB n Ub), F ::: ones (b + 1 - jb) (RB M t jt Y)⟩

theorem Ha : HomeL H1a H2a H3a H4a H5a := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem Hs : HomeL H1s H2s H3s H4s Xs := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
theorem PAR : ParserR delta AR1 AR2 := ⟨rfl, rfl, rfl⟩
theorem PAQ : ParserR delta AQ1 AQ2 := ⟨rfl, rfl, rfl⟩
theorem PSR : ParserR delta SR1 SR2 := ⟨rfl, rfl, rfl⟩

/-! ## home, from either cursor -/

theorem home_bot {h1 h2 h3 h4 h5 : St} (H : HomeL h1 h2 h3 h4 h5) (n : Nat) (Ub : List Nat)
    (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) :
    Rch (cfgL h1 (ones jb (LB n Ub)) (F ::: ones (b + 1 - jb) (RB M t jt Y)))
      (cfgL h5 (ones n blank) (F ::: F ::: F ::: F ::: RT Ub b jb M t jt Y)) :=
  H.gap n Ub jb _

theorem home_top {h1 h2 h3 h4 h5 : St} (H : HomeL h1 h2 h3 h4 h5) (n : Nat) (Ub : List Nat)
    (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) (h1b : 1 ≤ jb) (hb : jb ≤ b) :
    Rch (cfgL h1 (ones jt (LT n Ub b jb M)) (F ::: ones (t + 1 - jt) Y))
      (cfgL h5 (ones n blank) (F ::: F ::: F ::: F ::: RT Ub b jb M t jt Y)) := by
  obtain ⟨k, hk⟩ : ∃ k, b + 1 - jb = k + 1 := ⟨b - jb, by omega⟩
  obtain ⟨i, rfl⟩ : ∃ i, jb = i + 1 := ⟨jb - 1, by omega⟩
  unfold LT
  rw [hk]
  refine Rch.tr (H.hole k _ M jt _) ?_
  refine Rch.tr (sL (s := ones i (LB n Ub)) H.b1) ?_
  refine Rch.tr (H.gap n Ub i _) ?_
  unfold RT RB
  rw [ones_snoc, hk]
  exact Reach.refl _ _

/-! ## at `E` -/

theorem tl_blank : tl blank = blank := rfl

theorem add_op (n : Nat) (R0 : Strm) :
    Rch (cfgL H5a (ones n blank) R0) ⟨AR1, ones 1 blank, ones (max n 1) R0⟩ := by
  rcases n with _ | n
  · show Rch (cfgL H5a (F ::: blank) R0) _
    gL
    show Rch (cfgL H6a (F ::: blank) _) _
    unfold cfgL; gR
    simp only [cons_blank]; exact Reach.refl _ _
  · gL
    refine Rch.tr (scanL (δ := delta) rfl n _ _) ?_
    show Rch (cfgL Xa (F ::: blank) _) _
    unfold cfgL; gR
    simp only [cons_blank, ← ones_succ']
    rw [show max (n + 1) 1 = n + 1 by omega]; exact Reach.refl _ _

theorem sub_op (n : Nat) (R0 : Strm) :
    Rch (cfgL Xs (ones (n + 2) blank) R0) ⟨SR1, ones 1 blank, ones n R0⟩ := by
  refine Rch.tr (scanL (δ := delta) rfl (n + 2) _ _) ?_
  show Rch (cfgL Xs (F ::: blank) _) _
  unfold cfgL; gR; gR; gR
  simp only [tl_blank, cons_blank]; exact Reach.refl _ _

theorem sub_halt (R1 : Strm) :
    HaltAt (cfgL Xs (ones 1 blank) (F ::: R1)) := by
  refine HaltAt.back (b := ⟨halt, F ::: blank, R1⟩) ?_ ⟨_, _, Reach.refl _ _⟩
  refine Rch.tr (scanL (δ := delta) rfl 1 _ _) ?_
  show Rch (cfgL Xs (F ::: blank) _) _
  unfold cfgL; gR; gR; gR
  simp only [tl_blank, cons_blank]; exact Reach.refl _ _

/-! ## back to a cursor -/

/-- across `E`'s cells right of the head and the four 0s -/
theorem cross_E {p1 p2 : St} (P : ParserR delta p1 p2) (k : Nat) (X : Strm) :
    Rch ⟨p1, ones 1 blank, ones k (F ::: F ::: F ::: F ::: X)⟩
      ⟨p1, F ::: F ::: F ::: F ::: ones (k + 1) blank, X⟩ := by
  refine Rch.tr (scanR P.h1 k _ _) ?_
  refine Rch.tr (sR P.h0) ?_; refine Rch.tr (sR P.h2) ?_
  refine Rch.tr (sR P.h0) ?_; refine Rch.tr (sR P.h2) ?_
  rw [ones_add]; exact Reach.refl _ _

/-- right parser over the bottoms to come and the left part of the bottom block, to its hole -/
theorem to_bot {p1 p2 : St} (P : ParserR delta p1 p2) (k : Nat) (Ub : List Nat) (jb : Nat) (X : Strm) :
    Rch ⟨p1, ones 1 blank, ones k (F ::: F ::: F ::: F ::: bks Ub.reverse (ones jb (F ::: true ::: X)))⟩
      ⟨p2, F ::: ones jb (LB (k + 1) Ub), true ::: X⟩ := by
  refine Rch.tr (cross_E P k _) ?_
  refine Rch.tr (PR_bks P Ub.reverse _ _) ?_
  refine Rch.tr (scanR P.h1 jb _ _) ?_
  refine Rch.tr (sR P.h0) ?_
  rw [List.reverse_reverse]; exact Reach.refl _ _

theorem ret_add (k : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (hb : jb ≤ b) (h1b : 1 ≤ jb) (ht : jt ≤ t) :
    Rch ⟨AR1, ones 1 blank, ones k (F ::: F ::: F ::: F ::: RT Ub b jb M t jt Y)⟩
      (TF (k + 1) Ub b jb M t jt Y) := by
  unfold RT
  rw [show b + 1 - jb = (b - jb) + 1 by omega]
  refine Rch.tr (to_bot PAR k Ub jb _) ?_
  gR
  refine Rch.tr (scanR PAQ.h1 (b - jb) _ _) ?_
  unfold RB
  refine Rch.tr (sR PAQ.h0) ?_; refine Rch.tr (sR PAQ.h2) ?_
  refine Rch.tr (PR_bks PAQ M.reverse _ _) ?_
  refine Rch.tr (scanR PAQ.h1 jt _ _) ?_
  rw [show t + 1 - jt = (t - jt) + 1 by omega]
  refine Rch.tr (sR PAQ.h0) ?_
  gL
  unfold TF LT
  rw [List.reverse_reverse, ones_snoc, show b - jb + 1 = b + 1 - jb by omega,
    show t + 1 - jt = (t - jt) + 1 by omega]
  exact Reach.refl _ _

theorem ret_sub (k : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (hb : jb ≤ b) :
    Rch ⟨SR1, ones 1 blank, ones k (F ::: F ::: F ::: F ::: RT Ub b jb M t jt Y)⟩
      (BF (k + 1) Ub b jb M t jt Y) := by
  unfold RT
  rw [show b + 1 - jb = (b - jb) + 1 by omega]
  refine Rch.tr (to_bot PSR k Ub jb _) ?_
  gL
  unfold BF
  rw [show b + 1 - jb = (b - jb) + 1 by omega]
  exact Reach.refl _ _

/-! ## whole trips -/

theorem add_top (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (h1b : 1 ≤ jb) (hb : jb ≤ b) (ht : jt ≤ t) :
    Rch (cfgL H1a (ones jt (LT n Ub b jb M)) (F ::: ones (t + 1 - jt) Y))
      (TF (max n 1 + 1) Ub b jb M t jt Y) :=
  Rch.tr (home_top Ha n Ub b jb M t jt Y h1b hb)
    (Rch.tr (add_op n _) (ret_add _ Ub b jb M t jt Y hb h1b ht))

theorem add_bot (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (h1b : 1 ≤ jb) (hb : jb ≤ b) (ht : jt ≤ t) :
    Rch (cfgL H1a (ones jb (LB n Ub)) (F ::: ones (b + 1 - jb) (RB M t jt Y)))
      (TF (max n 1 + 1) Ub b jb M t jt Y) :=
  Rch.tr (home_bot Ha n Ub b jb M t jt Y)
    (Rch.tr (add_op n _) (ret_add _ Ub b jb M t jt Y hb h1b ht))

theorem sub_top (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (h1b : 1 ≤ jb) (hb : jb ≤ b) :
    Rch (cfgL H1s (ones jt (LT (n + 2) Ub b jb M)) (F ::: ones (t + 1 - jt) Y))
      (BF (n + 1) Ub b jb M t jt Y) :=
  Rch.tr (home_top Hs _ Ub b jb M t jt Y h1b hb)
    (Rch.tr (sub_op n _) (ret_sub _ Ub b jb M t jt Y hb))

theorem sub_bot (n : Nat) (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (hb : jb ≤ b) :
    Rch (cfgL H1s (ones jb (LB (n + 2) Ub)) (F ::: ones (b + 1 - jb) (RB M t jt Y)))
      (BF (n + 1) Ub b jb M t jt Y) :=
  Rch.tr (home_bot Hs _ Ub b jb M t jt Y)
    (Rch.tr (sub_op n _) (ret_sub _ Ub b jb M t jt Y hb))

theorem sub_top_halt (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm)
    (h1b : 1 ≤ jb) (hb : jb ≤ b) :
    HaltAt (cfgL H1s (ones jt (LT 1 Ub b jb M)) (F ::: ones (t + 1 - jt) Y)) :=
  HaltAt.back (home_top Hs _ Ub b jb M t jt Y h1b hb) (sub_halt _)

theorem sub_bot_halt (Ub : List Nat) (b jb : Nat) (M : List Nat) (t jt : Nat) (Y : Strm) :
    HaltAt (cfgL H1s (ones jb (LB 1 Ub)) (F ::: ones (b + 1 - jb) (RB M t jt Y))) :=
  HaltAt.back (home_bot Hs _ Ub b jb M t jt Y) (sub_halt _)

end TM.HardyLittlewood2
