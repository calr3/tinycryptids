import TinyCryptids.BrocardPrimes.Bound
namespace TM.BrocardPrimes
open St

/-! # From the grown S to the marker -/

theorem ls_zone_b (l : List (Nat × Nat)) : ∀ (L0 R : Strm),
    Rch (cfgL lb (pzR l (F ::: F ::: L0)) R) (cfgL lc L0 (F ::: F ::: pz l R)) := by
  induction l with
  | nil => intro L0 R; simp only [pzR, pz]; gL; gL; fin
  | cons x l ih =>
    intro L0 R
    obtain ⟨a, b⟩ := x
    simp only [pzR]
    refine Rch.tr (ih _ R) ?_
    exact ls_blk a b L0 _

/-- across the counter, the gap and S (hole at its last index) -/
theorem scan_K (c b : Nat) (X : Strm) :
    Rch (cfgL la (ones c (F ::: true ::: F ::: ones (b+3) (F ::: X))) (true ::: blank))
      (cfgL lb X (tailS c (b+2) 0)) := by
  unfold tailS blk
  sLn c; gL; gL; gL; gL; sLn (b+2); gL
  simp only [ones_succ, ones_cons_true, ones_zero]; fin

/-- the whole scan: the counter, S, the zone below the marker, the marker itself -/
theorem scan_all (c b : Nat) (lo' up' : List (Nat × Nat))
    (M Z : Strm) (hZ : pzR up' (F ::: F ::: M) = F ::: F ::: Z) :
    Rch (cfgL la (ones c (F ::: true ::: F ::: ones (b+3)
        (F ::: pzR lo' (F ::: F ::: true ::: pzR up' (F ::: F ::: M))))) (true ::: blank))
      (cfgL lf Z (F ::: F ::: true ::: F ::: F ::: pz lo' (tailS c (b+2) 0))) := by
  refine Rch.tr (scan_K c b _) ?_
  refine Rch.tr (ls_zone_b lo' _ _) ?_
  rw [hZ]; gL; gL; gL; fin

end TM.BrocardPrimes
