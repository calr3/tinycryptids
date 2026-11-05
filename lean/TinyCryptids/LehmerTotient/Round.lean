import TinyCryptids.LehmerTotient.Test

/-!
# The count, the round end and the next `n`

Tape (left to right): `1 K 00 1 R 00 [D 00 P]`, with `PR d p` the pair: `D = 1 0 1^d`
(`d + 2` cells, the hole on cell 1), `P` = `p + 2` cells.
-/

namespace TM.LehmerTotient
open St TinyCryptids

local notation "F" => false

theorem PPC : ParserR delta CV1 CV2 := by constructor <;> rfl
theorem PPU : ParserR delta PU1 PU2 := by constructor <;> rfl
theorem PPD : ParserL delta PD1 PD2 := by constructor <;> rfl
theorem PPB : ParserL delta PB1 PB2 := by constructor <;> rfl

/-- the pair, from D's cell 0 -/
def PR (d p : Nat) : Strm := true ::: F ::: ones d (F ::: F ::: ones (p + 2) blank)

/-! ## back to R: from D's cell 2 going left, to `EC1` on R's slot 2 -/

theorem ret (x e a : Nat) (R : Strm) :
    Rch (cfgL PD1 (ones x (F ::: true ::: F ::: F ::: ones e (PostL a))) R)
      ⟨EC1, PostL a, ones e (F ::: F ::: true ::: F ::: ones x R)⟩ := by
  refine Rch.tr (PPD.find0 x _ _) ?_
  gL
  rcases e with _ | e
  · unfold PostL; gL; gL; gL; gR; gR; fin
  · unfold PostL
    refine Rch.tr (PPB.find2 0 e _ _) ?_
    gR; gR; fin

/-! ## a coprime pair: d += 1 -/

theorem coprime (a e d p : Nat) (hd : 1 ≤ d) :
    Rch ⟨CV1, PostL a, ones e (F ::: F ::: PR d (p + 1))⟩ ⟨EC1, PostL a, ones e (F ::: F ::: PR (d + 1) p)⟩ := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  unfold PR
  refine Rch.tr (PPC.find2 e 0 _ _) ?_
  gR; sRn c; gR; gR; gL; gL
  rw [ones_cons_true]
  exact ret (c + 2) e a (F ::: F ::: ones (p + 2) blank)

/-! ## next n: D := 1, coming from P's right end -/

/-- fill the separator and D's hole, then `1 0 1 0 0` from D's cell 0; `PD2` on cell 3 -/
theorem norm (k a b : Nat) (Lx R : Strm) (h : 2 ≤ k + a + b) :
    Rch (cfgL r1 (ones k (F ::: F ::: ones a (F ::: ones b (F ::: Lx)))) R)
      (cfgL PD2 (F ::: true ::: F ::: true ::: F ::: Lx) (F ::: ones (k + a + b - 2) R)) := by
  sLn k; gL; gL; sLn a; gL; sLn b; gR
  rw [show ones b (true ::: ones a (true ::: true ::: ones k R)) = ones ((k + a + b - 2) + 5) R by
    rw [← ones_succ', ← ones_succ', ← ones_succ', ones_add, ones_add,
      show b + 1 + (a + 1 + 1) + k = k + a + b - 2 + 5 by omega]]
  gR; gR; gR; gR; gL; fin

/-- after the normalization: back to R -/
theorem norm_ret (k a b e : Nat) (R : Strm) (h : 2 ≤ k + a + b) :
    Rch (cfgL r1 (ones k (F ::: F ::: ones a (F ::: ones b (F ::: F ::: ones e (PostL 0))))) R)
      ⟨EC1, PostL 0, ones e (F ::: F ::: true ::: F ::: ones 1 (F ::: F ::: ones (k + a + b - 2) R))⟩ := by
  refine Rch.tr (norm k a b _ R h) ?_
  gL
  exact ret 1 e 0 _

/-! ## round end: K/R `(n - 1, 1) → (1, n)`, then the test start -/

theorem to_test (n d p : Nat) (hn : 2 ≤ n) (hd : 1 ≤ d) :
    Rch ⟨EC1, PostL (n - 2), F ::: F ::: PR d p⟩ (SHT (F ::: ones (n - 1) (PostL 0)) blank d p) := by
  obtain ⟨c, rfl⟩ : ∃ c, d = c + 1 := ⟨d - 1, by omega⟩
  gL
  refine Rch.tr (reset n hn _) ?_
  unfold PR SHT
  refine Rch.tr (PPU.find2 (n - 1) 0 _ _) ?_
  gR; sRn c; gR; gR
  rw [cons_blank, ones_cons_true]; fin

/-- `p = 0` (n prime): a cell after P, then the normalization -/
theorem prime_next (Lx : Strm) (d : Nat) :
    Rch (SHT Lx blank d 0) (cfgL r1 (ones 2 (F ::: F ::: ones d (F ::: ones 1 (F ::: Lx)))) (true ::: blank)) := by
  unfold SHT
  gR; gR; rw [ones_zero, cons_blank]; refine blankR ?_; gL; fin

/-- not a divisor: to P's end, a cell after P, then the normalization -/
theorem nodiv_next (Lx : Strm) (d r c : Nat) (hc : c + 1 < d) :
    Rch (ND Lx blank d r c)
      (cfgL r1 (ones (r + 2) (F ::: F ::: ones (d - c - 1) (F ::: ones (c + 2) (F ::: Lx)))) (true ::: blank)) := by
  obtain ⟨x, hx⟩ : ∃ x, d - c - 1 = x + 1 := ⟨d - c - 2, by omega⟩
  unfold ND
  rw [hx, cons_blank]
  gR; gR; gR; sRn x; gR; gR; sRn (r + 2); refine blankR ?_; gL
  rw [ones_cons_true]; fin

end TM.LehmerTotient
