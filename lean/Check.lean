import TinyCryptids

/-! Every main theorem: its statement and the axioms it depends on
(expected: `propext`, `Classical.choice`, `Quot.sound`; never `sorryAx`).
Run `lake env lean Check.lean` after `lake build`. -/

-- hand-designed machines: the design (`halts_iff`) and the merged machines
#check @TM.WeakCollatz.halts_iff
#print axioms TM.WeakCollatz.halts_iff
#check @TM.WeakCollatz.halts_iff_counter
#print axioms TM.WeakCollatz.halts_iff_counter
#check @TM.WeakCollatz16.halts_iff
#print axioms TM.WeakCollatz16.halts_iff
#check @TM.WeakCollatzV1.halts_iff
#print axioms TM.WeakCollatzV1.halts_iff
#check @TM.WeakCollatzV1.M23.halts_iff
#print axioms TM.WeakCollatzV1.M23.halts_iff
#check @TM3.WeakCollatz.halts_iff
#print axioms TM3.WeakCollatz.halts_iff
#check @TM.Fermat.halts_iff
#print axioms TM.Fermat.halts_iff
#check @TM.Fermat.M90.halts_iff
#print axioms TM.Fermat.M90.halts_iff
