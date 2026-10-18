import TinyCryptids

/-! Every main theorem: its statement and the axioms it depends on
(expected: `propext`, `Classical.choice`, `Quot.sound`; never `sorryAx`).
Run `lake env lean Check.lean` after `lake build`. -/

-- hand-designed machines: the design (`halts_iff`) and the merged machines
#check @TM.WeakCollatz.halts_iff
#print axioms TM.WeakCollatz.halts_iff
#check @TM.WeakCollatz.M23.halts_iff
#print axioms TM.WeakCollatz.M23.halts_iff
