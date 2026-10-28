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
#check @TM.Sierpinski.halts_iff
#print axioms TM.Sierpinski.halts_iff
#check @TM.Sierpinski.M60.halts_iff
#print axioms TM.Sierpinski.M60.halts_iff
#check @TM.Riesel.halts_iff
#print axioms TM.Riesel.halts_iff
#check @TM.Riesel.M76.halts_iff
#print axioms TM.Riesel.M76.halts_iff
#check @TM.OddPerfect.halts_iff
#print axioms TM.OddPerfect.halts_iff
#check @TM.OddPerfect.M37.halts_iff
#print axioms TM.OddPerfect.M37.halts_iff
#check @TM.Kurepa.halts_iff
#print axioms TM.Kurepa.halts_iff
#check @TM.Kurepa.M38.halts_iff
#print axioms TM.Kurepa.M38.halts_iff
#check @TM.FermatPrimes.halts_iff
#print axioms TM.FermatPrimes.halts_iff
#check @TM.FermatPrimes.M25.halts_iff
#print axioms TM.FermatPrimes.M25.halts_iff

-- beeping machines: quasihalt (take the beep transition finitely often) iff the statement
#check @TM.TwinPrimes.quasihalts_iff
#print axioms TM.TwinPrimes.quasihalts_iff
#check @TM.TwinPrimes.never_halts
#print axioms TM.TwinPrimes.never_halts
#check @TM.TwinPrimes.M18.quasihalts_iff
#print axioms TM.TwinPrimes.M18.quasihalts_iff
#check @TM.TwinPrimes.M18.never_halts
#print axioms TM.TwinPrimes.M18.never_halts
#check @TM.TwinPrimes.M18.beep_transition
#check @TM.FermatPrimesInf.quasihalts_iff
#print axioms TM.FermatPrimesInf.quasihalts_iff
#check @TM.FermatPrimesInf.never_halts
#print axioms TM.FermatPrimesInf.never_halts
#check @TM.FermatPrimesInf.M16.quasihalts_iff
#print axioms TM.FermatPrimesInf.M16.quasihalts_iff
#check @TM.FermatPrimesInf.M16.never_halts
#print axioms TM.FermatPrimesInf.M16.never_halts
#check @TM.FermatPrimesInf.M16.beep_transition

-- beeping booping machines: some beep count between consecutive boops repeats forever iff the statement fails
#check @TM.ABC.repeats_iff
#print axioms TM.ABC.repeats_iff
#check @TM.ABC.never_halts
#print axioms TM.ABC.never_halts
#check @TM.ABC.M235.repeats_iff
#print axioms TM.ABC.M235.repeats_iff
#check @TM.ABC.M235.never_halts
#print axioms TM.ABC.M235.never_halts
#check @TM.ABC.M235.beep_transition
#check @TM.ABC.M235.boop_transition
