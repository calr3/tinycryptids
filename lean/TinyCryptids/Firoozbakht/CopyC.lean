import TinyCryptids.Firoozbakht.Copy
namespace TM.Firoozbakht
open St

/-- the copy loop of `M` onto `M'`, state `Cc1` standing on the separator right of the R block
(R has value `r`, cursor at `c`, Q has `q` cells). -/
def cpySC (c r q : Nat) (Lc : Strm) : Cfg St :=
  ⟨Cc1, ones (r + 1 - c) (false ::: ones c Lc), sep (ones q blank)⟩

theorem copyC_one (c r q : Nat) (Lc : Strm) (hc : c < r) :
    Rch (cpySC c r q Lc) (cpySC (c+1) r (q+1) Lc) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = c + 1 + k := ⟨r - c - 1, by omega⟩
  have e1 : c + 1 + k + 1 - c = k + 2 := by omega
  have e2 : c + 1 + k + 1 - (c + 1) = k + 1 := by omega
  unfold cpySC sep; rw [e1, e2, ones_succ' q]
  gR; gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; gL; sLn (k + 2)
  gR; gR; gL; gR; sRn (k + 1); fin

/-- after the last cell: the block has no hole any more; head on its cell 1, state `cn3` -/
def cpyDoneC (r q : Nat) (Lc : Strm) : Cfg St :=
  ⟨cn3, true ::: false ::: Lc, ones (r + 1) (sep (ones q blank))⟩

theorem copyC_last (r q : Nat) (Lc : Strm) :
    Rch (cpySC r r q (false ::: Lc)) (cpyDoneC r (q+1) Lc) := by
  unfold cpySC cpyDoneC sep
  rw [show r + 1 - r = 1 by omega, ones_succ' q]
  gR; gR; sRn q
  refine blankR ?_
  gL; sLn q; gL; gL; gL; gR; gR; gL; sLn (r + 2); gR; gR; fin

theorem copyC_all (r q : Nat) (Lc : Strm) : ∀ c, 1 ≤ c → c ≤ r →
    Rch (cpySC c r q (false ::: Lc)) (cpyDoneC r (q + (r + 1 - c)) Lc) := by
  suffices H : ∀ n c q, r - c = n → 1 ≤ c → c ≤ r →
      Rch (cpySC c r q (false ::: Lc)) (cpyDoneC r (q + (r + 1 - c)) Lc) from
    fun c h1 h2 => H _ c q rfl h1 h2
  intro n
  induction n with
  | zero =>
    intro c q h _ h2
    have : c = r := by omega
    subst this; rw [show c + 1 - c = 1 by omega]; exact copyC_last c q Lc
  | succ n ih =>
    intro c q h h1 h2
    refine Rch.tr (copyC_one c r q _ (by omega)) ?_
    have := ih (c+1) (q+1) (by omega) (by omega) (by omega)
    rw [show q + 1 + (r + 1 - (c + 1)) = q + (r + 1 - c) by omega] at this
    exact this

/-- A full copy of R onto Q, entered from the R-parser (head two cells right of
the R cursor, which sits at cell 1). -/
theorem copyC_full (r q : Nat) (Lc : Strm) (hr : 1 ≤ r) :
    Rch ⟨Cc1, true ::: false ::: true ::: false ::: Lc, ones (r - 1) (sep (ones q blank))⟩
      (cpyDoneC r (q + r) Lc) := by
  sRn (r - 1)
  have := copyC_all r q Lc 1 (Nat.le_refl _) hr
  rw [show q + (r + 1 - 1) = q + r by omega] at this
  unfold cpySC at this
  rw [show r + 1 - 1 = (r - 1) + 1 by omega, ones_succ'] at this
  exact this

end TM.Firoozbakht
