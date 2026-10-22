import TinyCryptids.Fermat.Tac
namespace TM.Fermat
open St

def sep (s : Strm) : Strm := false ::: false ::: s

/-! The copy loop. R is a block of `r` cells right after a single 0 (its hole); Q follows R after
another single 0. MC punches a copy cursor on R's first cell; each pass appends one cell to Q
and moves the cursor one cell right (it may reach R's last cell); after the last cell, `c6` runs
back over R to its hole and enters the `NB` parser. -/

/-- state `c1` right of the copy cursor (R's cell `c`); `L` is the tape left of R (its hole first) -/
def cpyS (c r q : Nat) (L : Strm) : Cfg St :=
  ⟨c1, F ::: ones c L, ones (r - 1 - c) (F ::: ones q blank)⟩

theorem copy_one (c r q : Nat) (L : Strm) (hc : c + 1 < r) :
    Rch (cpyS c r q L) (cpyS (c+1) r (q+1) L) := by
  obtain ⟨k, hk⟩ : ∃ k, r - 1 - c = k + 1 := ⟨r - 2 - c, by omega⟩
  unfold cpyS
  rw [hk, show r - 1 - (c + 1) = k by omega]
  sRn (k + 1); gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; sLn (k + 1); gR; gR
  rw [ones_succ' q]; fin

/-- after the last cell: `NB1` on the cell left of R's hole -/
def cpyDone (r q : Nat) (L : Strm) : Cfg St :=
  cfgL NB1 L (F ::: ones r (F ::: ones q blank))

theorem copy_last (r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch (cpyS (r - 1) r q (F ::: L)) (cpyDone r (q+1) L) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  unfold cpyS cpyDone
  rw [show r' + 1 - 1 - (r' + 1 - 1) = 0 by omega, ones_zero, show r' + 1 - 1 = r' by omega]
  gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; gR; gL
  show Rch (cfgL c6 (ones (r' + 1) (F ::: L)) _) _
  sLn (r' + 1); gL
  rw [ones_succ' q]; fin

theorem copy_all (r q : Nat) (L : Strm) (hr : 1 ≤ r) : ∀ c, c ≤ r - 1 →
    Rch (cpyS c r q (F ::: L)) (cpyDone r (q + (r - c)) L) := by
  suffices H : ∀ n c q, r - 1 - c = n → c ≤ r - 1 →
      Rch (cpyS c r q (F ::: L)) (cpyDone r (q + (r - c)) L) from
    fun c hc => H _ c q rfl hc
  intro n
  induction n with
  | zero =>
    intro c q h hc
    obtain rfl : c = r - 1 := by omega
    rw [show q + (r - (r - 1)) = q + 1 by omega]
    exact copy_last r q L hr
  | succ n ih =>
    intro c q h hc
    refine Rch.tr (copy_one c r q _ (by omega)) ?_
    have := ih (c+1) (q+1) (by omega) (by omega)
    rw [show q + 1 + (r - (c + 1)) = q + (r - c) by omega] at this
    exact this

/-- a full copy of R onto Q, from the cursor on R's first cell -/
theorem copy_full (r q : Nat) (L : Strm) (hr : 1 ≤ r) :
    Rch (cpyS 0 r q (F ::: L)) (cpyDone r (q + r) L) := by
  have := copy_all r q L hr 0 (Nat.zero_le _)
  rwa [Nat.sub_zero] at this

end TM.Fermat
