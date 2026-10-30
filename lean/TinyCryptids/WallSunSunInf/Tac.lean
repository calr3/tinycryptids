import TinyCryptids.Core.Lemmas
import TinyCryptids.Core.Beep
import TinyCryptids.WallSunSunInf.Machine

namespace TM.WallSunSunInf

abbrev Rch := Reach deltaNB
abbrev Rch1 := Reach1 deltaNB

set_option maxHeartbeats 4000000 in
/-- the routines are proved for `deltaNB` (no beep); they run the same in `delta` -/
theorem deltaNB_sub : ∀ q b t, deltaNB q b = some t → delta q b = some t := by
  intro q b t h; cases q <;> cases b <;> first | exact h | exact absurd h (by simp [deltaNB])

theorem sR {q q' : St} {L R : Strm} {b w : Bool} (h : deltaNB q b = some (w, Dir.R, q')) :
    Rch ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR (δ := deltaNB) (R := b ::: R) h

theorem sL {q q' : St} {s R : Strm} {b w : Bool} (h : deltaNB q b = some (w, Dir.L, q')) :
    Rch (cfgL q (b ::: s) R) (cfgL q' s (w ::: R)) := stepL' (δ := deltaNB) (s := b ::: s) h

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c := Reach.trans deltaNB h1 h2

/-- one step right / left, continuing with the remaining goal -/
macro "gR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "gL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl deltaNB _)

theorem scanR' {q : St} (h : deltaNB q true = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := scanR h n L R
theorem scanL' {q : St} (h : deltaNB q true = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch (cfgL q (ones n s) R) (cfgL q s (ones n R)) := scanL h n s R

macro "sRn" n:term : tactic => `(tactic| refine Rch.tr (scanR' (by rfl) $n _ _) ?_)
macro "sLn" n:term : tactic => `(tactic| refine Rch.tr (scanL' (by rfl) $n _ _) ?_)

theorem blankR {q : St} {L : Strm} {X : Cfg St} (h : Rch ⟨q, L, false ::: blank⟩ X) :
    Rch ⟨q, L, blank⟩ X := by rw [← cons_blank]; exact h

macro "zRn" n:term : tactic => `(tactic| refine Rch.tr (scanR0 (δ := deltaNB) (by rfl) $n _ _) ?_)
macro "zLn" n:term : tactic => `(tactic| refine Rch.tr (scanL0 (δ := deltaNB) (by rfl) $n _ _) ?_)

macro "eRn" n:term : tactic => `(tactic| refine Rch.tr (eraseR (δ := deltaNB) (by rfl) $n _ _) ?_)
macro "eLn" n:term : tactic => `(tactic| refine Rch.tr (eraseL (δ := deltaNB) (by rfl) $n _ _) ?_)

end TM.WallSunSunInf
