import TinyCryptids.Core.Lemmas
import TinyCryptids.Barker.Machine

/-! # One-step tactics for the Barker design -/

namespace TM.Barker

abbrev Rch := Reach delta
abbrev Rch1 := Reach1 delta

theorem sR {q q' : St} {L R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.R, q')) :
    Rch ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR (δ := delta) (R := b ::: R) h

theorem sL {q q' : St} {s R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.L, q')) :
    Rch (cfgL q (b ::: s) R) (cfgL q' s (w ::: R)) := stepL' (δ := delta) (s := b ::: s) h

theorem sR1 {q q' : St} {L R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.R, q')) :
    Rch1 ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR1 (δ := delta) (R := b ::: R) h

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c := Reach.trans delta h1 h2

macro "gR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "gL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)
macro "fin" : tactic => `(tactic| exact Reach.refl delta _)

theorem scanR' {q : St} (h : delta q true = some (true, Dir.R, q)) (n : Nat) (L R : Strm) :
    Rch ⟨q, L, ones n R⟩ ⟨q, ones n L, R⟩ := scanR h n L R
theorem scanL' {q : St} (h : delta q true = some (true, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch (cfgL q (ones n s) R) (cfgL q s (ones n R)) := scanL h n s R
theorem eraseL'' {q : St} (h : delta q true = some (false, Dir.L, q)) (n : Nat) (s R : Strm) :
    Rch (cfgL q (ones n s) R) (cfgL q s (zeros n R)) := eraseL h n s R

macro "sRn" n:term : tactic => `(tactic| refine Rch.tr (scanR' (by rfl) $n _ _) ?_)
macro "sLn" n:term : tactic => `(tactic| refine Rch.tr (scanL' (by rfl) $n _ _) ?_)
macro "eLn" n:term : tactic => `(tactic| refine Rch.tr (eraseL'' (by rfl) $n _ _) ?_)

end TM.Barker
