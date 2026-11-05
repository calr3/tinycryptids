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
#check @TM.Legendre.halts_iff
#print axioms TM.Legendre.halts_iff
#check @TM.Legendre.M44.halts_iff
#print axioms TM.Legendre.M44.halts_iff
#check @TM.Oppermann.halts_iff
#print axioms TM.Oppermann.halts_iff
#check @TM.Oppermann.M45.halts_iff
#print axioms TM.Oppermann.M45.halts_iff
#check @TM.LegendreSieve.halts_iff
#print axioms TM.LegendreSieve.halts_iff
#check @TM.LegendreSieve.M45.halts_iff
#print axioms TM.LegendreSieve.M45.halts_iff
#check @TM.Brocard.halts_iff
#print axioms TM.Brocard.halts_iff
#check @TM.Brocard.M61.halts_iff
#print axioms TM.Brocard.M61.halts_iff
#check @TM.Erdos.halts_iff
#print axioms TM.Erdos.halts_iff
#check @TM.ZeroFree.halts_iff
#print axioms TM.ZeroFree.halts_iff
#check @TM.ZeroFree.M44.halts_iff
#print axioms TM.ZeroFree.M44.halts_iff
#check @TM.Carmichael.halts_iff
#print axioms TM.Carmichael.halts_iff
#check @TM.Carmichael.M80.halts_iff
#print axioms TM.Carmichael.M80.halts_iff
#check @TM.Beal.halts_iff
#print axioms TM.Beal.halts_iff
#check @TM.Beal.M135.halts_iff
#print axioms TM.Beal.M135.halts_iff
#check @TM.Lychrel.halts_iff
#print axioms TM.Lychrel.halts_iff
#check @TM.Lychrel.M95.halts_iff
#print axioms TM.Lychrel.M95.halts_iff
#check @TM.HardyLittlewood2.halts_iff
#print axioms TM.HardyLittlewood2.halts_iff
#check @TM.HardyLittlewood2.M79.halts_iff
#print axioms TM.HardyLittlewood2.M79.halts_iff
#check @TM.Gilbreath.halts_iff
#print axioms TM.Gilbreath.halts_iff
#check @TM.Gilbreath.M97.halts_iff
#print axioms TM.Gilbreath.M97.halts_iff
#check @TM.LehmerTau.halts_iff
#print axioms TM.LehmerTau.halts_iff
#check @TM.LehmerTau.M295.halts_iff
#print axioms TM.LehmerTau.M295.halts_iff
#check @TM.ErdosMoser.halts_iff
#print axioms TM.ErdosMoser.halts_iff
#check @TM.ErdosMoser.M71.halts_iff
#print axioms TM.ErdosMoser.M71.halts_iff
#check @TM.BrocardPrimes.halts_iff
#print axioms TM.BrocardPrimes.halts_iff
#check @TM.BrocardPrimes.M72.halts_iff
#print axioms TM.BrocardPrimes.M72.halts_iff
#check @TM.FeitThompson.halts_iff
#print axioms TM.FeitThompson.halts_iff
#check @TM.FeitThompson.M106.halts_iff
#print axioms TM.FeitThompson.M106.halts_iff
#check @TM.Singmaster.halts_iff
#print axioms TM.Singmaster.halts_iff
#check @TM.Singmaster.M77.halts_iff
#print axioms TM.Singmaster.M77.halts_iff
#check @TM.Firoozbakht.halts_iff
#print axioms TM.Firoozbakht.halts_iff
#check @TM.Firoozbakht.M117.halts_iff
#print axioms TM.Firoozbakht.M117.halts_iff
#check @TM.Lemoine.halts_iff
#print axioms TM.Lemoine.halts_iff
#check @TM.Lemoine.M54.halts_iff
#print axioms TM.Lemoine.M54.halts_iff
#check @TM.LehmerTotient.halts_iff
#print axioms TM.LehmerTotient.halts_iff
#check @TM.LehmerTotient.M67.halts_iff
#print axioms TM.LehmerTotient.M67.halts_iff
#check @TM.Andrica.halts_iff
#print axioms TM.Andrica.halts_iff
#check @TM.Andrica.M51.halts_iff
#print axioms TM.Andrica.M51.halts_iff
#check @TM.AgohGiuga.halts_iff
#print axioms TM.AgohGiuga.halts_iff
#check @TM.AgohGiuga.M100.halts_iff
#print axioms TM.AgohGiuga.M100.halts_iff
#check @TM.ErdosStraus.halts_iff
#print axioms TM.ErdosStraus.halts_iff
#check @TM.ErdosStraus.M128.halts_iff
#print axioms TM.ErdosStraus.M128.halts_iff
#check @TM.Goormaghtigh.halts_iff
#print axioms TM.Goormaghtigh.halts_iff
#check @TM.Goormaghtigh.M53.halts_iff
#print axioms TM.Goormaghtigh.M53.halts_iff
#check @TM.PerfectCuboid.halts_iff
#print axioms TM.PerfectCuboid.halts_iff
#check @TM.PerfectCuboid.M88.halts_iff
#print axioms TM.PerfectCuboid.M88.halts_iff
#check @TM.Barker.halts_iff
#print axioms TM.Barker.halts_iff
#check @TM.Barker.M84.halts_iff
#print axioms TM.Barker.M84.halts_iff
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
#check @TM.Amicable.quasihalts_iff
#print axioms TM.Amicable.quasihalts_iff
#check @TM.Amicable.never_halts
#print axioms TM.Amicable.never_halts
#check @TM.Amicable.M55.quasihalts_iff
#print axioms TM.Amicable.M55.quasihalts_iff
#check @TM.Amicable.M55.never_halts
#print axioms TM.Amicable.M55.never_halts
#check @TM.Amicable.M55.beep_transition
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
#check @TM.Pillai.repeats_iff
#print axioms TM.Pillai.repeats_iff
#check @TM.Pillai.never_halts
#print axioms TM.Pillai.never_halts
#check @TM.Pillai.M91.repeats_iff
#print axioms TM.Pillai.M91.repeats_iff
#check @TM.Pillai.M91.never_halts
#print axioms TM.Pillai.M91.never_halts
#check @TM.Pillai.M91.beep_transition
#check @TM.Pillai.M91.boop_transition

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
