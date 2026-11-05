import TinyCryptids.Firoozbakht.Tac
namespace TM.Firoozbakht
open St

def sep (s : Strm) : Strm := false ::: false ::: s

/-- copy loop, state `c1` standing on the separator right of the R block
(R has value `r`, cursor at `c`, Q has `q` cells). -/
def cpyS (c r q : Nat) (Lc : Strm) : Cfg St :=
  ⟨c1, ones (r + 1 - c) (false ::: ones c Lc), sep (ones q blank)⟩

theorem copy_one (c r q : Nat) (Lc : Strm) (hc : c < r) :
    Rch (cpyS c r q Lc) (cpyS (c+1) r (q+1) Lc) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = c + 1 + k := ⟨r - c - 1, by omega⟩
  have e1 : c + 1 + k + 1 - c = k + 2 := by omega
  have e2 : c + 1 + k + 1 - (c + 1) = k + 1 := by omega
  unfold cpyS sep; rw [e1, e2, ones_succ' q]
  gR; gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; gL; sLn (k + 2)
  gR; gR; gL; gR; sRn (k + 1); fin

/-- after the last cell: cursor reset to cell 1, head on cell 0 in state NB1 -/
def cpyDone (r q : Nat) (Lc : Strm) : Cfg St :=
  cfgL NB1 (true ::: false ::: Lc) (false ::: ones r (sep (ones q blank)))

theorem copy_last (r q : Nat) (Lc : Strm) :
    Rch (cpyS r r q (false ::: Lc)) (cpyDone r (q+1) Lc) := by
  unfold cpyS cpyDone sep
  rw [show r + 1 - r = 1 by omega, ones_succ' q]
  gR; gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; gL; gL; gR; gR; gL; sLn (r + 2); gR; gR; gL; fin

theorem copy_all (r q : Nat) (Lc : Strm) : ∀ c, 1 ≤ c → c ≤ r →
    Rch (cpyS c r q (false ::: Lc)) (cpyDone r (q + (r + 1 - c)) Lc) := by
  suffices H : ∀ n c q, r - c = n → 1 ≤ c → c ≤ r →
      Rch (cpyS c r q (false ::: Lc)) (cpyDone r (q + (r + 1 - c)) Lc) from
    fun c h1 h2 => H _ c q rfl h1 h2
  intro n
  induction n with
  | zero =>
    intro c q h _ h2
    have : c = r := by omega
    subst this; rw [show c + 1 - c = 1 by omega]; exact copy_last c q Lc
  | succ n ih =>
    intro c q h h1 h2
    refine Rch.tr (copy_one c r q _ (by omega)) ?_
    have := ih (c+1) (q+1) (by omega) (by omega) (by omega)
    rw [show q + 1 + (r + 1 - (c + 1)) = q + (r + 1 - c) by omega] at this
    exact this

/-- A full copy of R onto Q, entered from the R-parser (head two cells right of
the R cursor, which sits at cell 1). -/
theorem copy_full (r q : Nat) (Lc : Strm) (hr : 1 ≤ r) :
    Rch ⟨c1, true ::: false ::: true ::: false ::: Lc, ones (r - 1) (sep (ones q blank))⟩
      (cpyDone r (q + r) Lc) := by
  sRn (r - 1)
  have := copy_all r q Lc 1 (Nat.le_refl _) hr
  rw [show q + (r + 1 - 1) = q + r by omega] at this
  unfold cpyS at this
  rw [show r + 1 - 1 = (r - 1) + 1 by omega, ones_succ'] at this
  exact this

end TM.Firoozbakht
