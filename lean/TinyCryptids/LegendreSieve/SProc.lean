import TinyCryptids.LegendreSieve.Sweep
namespace TM.LegendreSieve
open St

/-! ## The square counter S (after the three 0s that end the P zone) -/

/-- prime mode: S cannot wrap; its hole moves left, then F := 1 and we head
home to copy M. -/
theorem s_prime (a b : Nat) (Lz : Strm) (f : Bool) :
    Rch ⟨p3, Lz, F ::: blk (a+1) b (F ::: f ::: blank)⟩
      (cfgL hc1 (F ::: blkR a (b+1) (F ::: Lz)) (true ::: blank)) := by
  unfold blk blkR
  gR; sRn (a+2); gR; rw [ones_cons_true b]; gL; gL; gL; rw [ones_cons_true a]; gR; gR
  simp only [← ones_succ]
  sRn (b+2); gR
  cases f <;> (gL; simp only [ones_succ, ones_cons_true]; fin)

/-- composite mode, no wrap: the hole moves left, then home. -/
theorem s_comp (a b : Nat) (Lz : Strm) (f : Bool) :
    Rch ⟨q3, Lz, F ::: blk (a+1) b (F ::: f ::: blank)⟩
      (cfgL hg1 (ones a (true ::: F ::: Lz)) (F ::: ones (b+1) (true ::: F ::: f ::: blank))) := by
  unfold blk
  gR; sRn (a+2); gR; rw [ones_cons_true b]; gL; gL; gL; rw [ones_cons_true a]; gR; gL
  simp only [ones_succ, ones_cons_true]; fin

/-- composite mode, wrap (the new m is a square) and F = 1: the F cell becomes
the new right guard, so the region grows by 2 with its hole at the last index. -/
theorem s_square (b : Nat) (Lz : Strm) :
    Rch ⟨q3, Lz, F ::: blk 0 b (F ::: true ::: blank)⟩
      (cfgL hg1 (F ::: ones (b+3) (F ::: Lz)) (true ::: blank)) := by
  unfold blk
  simp only [ones_zero]
  gR; gR; gR; rw [ones_cons_true b]; gL; gL; gL; gR
  rw [show (true ::: true ::: true ::: ones b (F ::: true ::: blank) : Strm) =
    ones (b+3) (F ::: true ::: blank) by simp only [ones_succ, ones_cons_true]]
  sRn (b+3); gR; gL
  simp only [ones_succ, ones_cons_true]; fin

theorem halt_cfg (L R : Strm) : Halts delta (⟨halt, L, R⟩ : Cfg St) := halt_none rfl

/-- reaches the explicit halting state -/
def HaltAt (c : Cfg St) : Prop := ∃ L R, Rch c ⟨halt, L, R⟩

theorem HaltAt.halts {c : Cfg St} (h : HaltAt c) : Halts delta c :=
  let ⟨_, _, h⟩ := h; Reach.halts delta h (halt_cfg _ _)

theorem HaltAt.back {a b : Cfg St} (hab : Rch a b) (h : HaltAt b) : HaltAt a :=
  let ⟨L, R, h⟩ := h; ⟨L, R, Rch.tr hab h⟩

/-- composite mode, wrap and F = 0: no prime since the last square. HALT. -/
theorem s_halt (b : Nat) (Lz : Strm) : HaltAt ⟨q3, Lz, F ::: blk 0 b (F ::: F ::: blank)⟩ := by
  unfold blk
  simp only [ones_zero]
  apply Exists.intro; apply Exists.intro
  gR; gR; gR; rw [ones_cons_true b]; gL; gL; gL; gR
  rw [show (true ::: true ::: true ::: ones b (F ::: F ::: blank) : Strm) =
    ones (b+3) (F ::: F ::: blank) by simp only [ones_succ, ones_cons_true]]
  sRn (b+3); gR; gR; fin

end TM.LegendreSieve
