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
#check @TM.WallSunSun2.halts_iff
#print axioms TM.WallSunSun2.halts_iff
#check @TM.WallSunSun2.M50.halts_iff
#print axioms TM.WallSunSun2.M50.halts_iff
#check @TM.FermatPrimes.halts_iff
#print axioms TM.FermatPrimes.halts_iff
#check @TM.FermatPrimes.M25.halts_iff
#print axioms TM.FermatPrimes.M25.halts_iff
-- Goldbach with 6 symbols (goldbach): also halts_iff_not, with GoldbachConjecture
#check @TMK.Goldbach.halts_iff
#print axioms TMK.Goldbach.halts_iff
#check @TMK.Goldbach.M10.halts_iff
#print axioms TMK.Goldbach.M10.halts_iff
#check @TMK.Goldbach.M10.halts_iff_not
#print axioms TMK.Goldbach.M10.halts_iff_not

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
#check @TMK.TwinPrimes4.quasihalts_iff
#print axioms TMK.TwinPrimes4.quasihalts_iff
#check @TMK.TwinPrimes4.never_halts
#print axioms TMK.TwinPrimes4.never_halts
#check @TMK.TwinPrimes4.beeps_forever_iff
#print axioms TMK.TwinPrimes4.beeps_forever_iff
#check @TMK.TwinPrimes4.beep_transition
#check @TM.FermatPrimesInf.quasihalts_iff
#print axioms TM.FermatPrimesInf.quasihalts_iff
#check @TM.FermatPrimesInf.never_halts
#print axioms TM.FermatPrimesInf.never_halts
#check @TM.FermatPrimesInf.M16.quasihalts_iff
#print axioms TM.FermatPrimesInf.M16.quasihalts_iff
#check @TM.FermatPrimesInf.M16.never_halts
#print axioms TM.FermatPrimesInf.M16.never_halts
#check @TM.FermatPrimesInf.M16.beep_transition
#check @TM.WallSunSunInf.quasihalts_iff
#print axioms TM.WallSunSunInf.quasihalts_iff
#check @TM.WallSunSunInf.never_halts
#print axioms TM.WallSunSunInf.never_halts
#check @TM.WallSunSunInf.M48.quasihalts_iff
#print axioms TM.WallSunSunInf.M48.quasihalts_iff
#check @TM.WallSunSunInf.M48.never_halts
#print axioms TM.WallSunSunInf.M48.never_halts
#check @TM.WallSunSunInf.M48.beep_transition
#check @TM.Mersenne.quasihalts_iff
#print axioms TM.Mersenne.quasihalts_iff
#check @TM.Mersenne.never_halts
#print axioms TM.Mersenne.never_halts
#check @TM.Mersenne.M14.quasihalts_iff
#print axioms TM.Mersenne.M14.quasihalts_iff
#check @TM.Mersenne.M14.never_halts
#print axioms TM.Mersenne.M14.never_halts
#check @TM.Mersenne.M14.beep_transition
#check @TM.SophieGermain.quasihalts_iff
#print axioms TM.SophieGermain.quasihalts_iff
#check @TM.SophieGermain.never_halts
#print axioms TM.SophieGermain.never_halts
#check @TM.SophieGermain.beeps_forever_iff
#print axioms TM.SophieGermain.beeps_forever_iff
#check @TM.SophieGermain.M17.quasihalts_iff
#print axioms TM.SophieGermain.M17.quasihalts_iff
#check @TM.SophieGermain.M17.never_halts
#print axioms TM.SophieGermain.M17.never_halts
#check @TM.SophieGermain.M17.beep_transition

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

-- PA: halts iff the theory T (S2 + Friedman's E, equiconsistent with PA) proves v0 ∈ v0
#check @TM.PA.halts_iff
#print axioms TM.PA.halts_iff
#check @TM.PA.M309.halts_iff
#print axioms TM.PA.M309.halts_iff
-- PA with 10 symbols (pa_nsymbols): the same theorem for pa_10sym_470.txt
#check @TMK.PA.halts_iff
#print axioms TMK.PA.halts_iff
#check @TMK.PA.M10.halts_iff
#print axioms TMK.PA.M10.halts_iff
