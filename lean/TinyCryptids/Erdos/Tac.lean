import TinyCryptids.Core.Lemmas
import TinyCryptids.Erdos.Machine

/-! Single steps for the Erdős machine's `delta`, as tactics. -/

namespace TM.Erdos

abbrev Rch := Reach delta
abbrev Rch1 := Reach1 delta

theorem sR {q q' : St} {L R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.R, q')) :
    Rch ⟨q, L, b ::: R⟩ ⟨q', w ::: L, R⟩ := stepR (δ := delta) (R := b ::: R) h

theorem sL {q q' : St} {s R : Strm} {b w : Bool} (h : delta q b = some (w, Dir.L, q')) :
    Rch (cfgL q (b ::: s) R) (cfgL q' s (w ::: R)) := stepL' (δ := delta) (s := b ::: s) h

theorem Rch.tr {a b c : Cfg St} (h1 : Rch a b) (h2 : Rch b c) : Rch a c := Reach.trans delta h1 h2

/-- one step right / left (left: in the `cfgL` form), continuing with the remaining goal -/
macro "goR" : tactic => `(tactic| refine Rch.tr (sR (by rfl)) ?_)
macro "goL" : tactic => `(tactic| refine Rch.tr (sL (by rfl)) ?_)

end TM.Erdos
