"""Tuples placed on the tape, run from the setup (state su0 on x's anchor). The events must be
those of `ref.ev`: a^x - b^y - 1 beeps and a boop if a^x > b^y, none otherwise; then the machine
reaches the next enumeration step (en2) with the tuple restored.
Usage: python3 test_tuple.py"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm, ref

def tape_for(x, y, a, b):
    bl = ['10' + '1' * x] + ['1' * (v + 2) for v in (y, a, b)]
    return '000' + '00'.join(bl) + '001' + '0001' + '000'

def check(t, maxsteps=10 ** 9):
    """(status of the run to en2, its steps, the tape at en2, the events up to en2)"""
    build.build()
    tape = tape_for(*t)
    r = tm.run(build.ORDER, build.ST, start='su0', tape=tape, head=4, maxsteps=maxsteps, trace='en2', maxtrace=1)
    e = tm.run(build.ORDER, build.ST, start='su0', tape=tape, head=4, maxsteps=r[1], maxtrace=10 ** 7,
               beep=build.BEEP, boop=build.BOOP, notape=True)
    return r[0], r[1], r[5][0] if r[5] else '', ''.join(x[0] for x in e[5]), tape

CASES = [(2, 2, 2, 2), (2, 3, 3, 2), (3, 2, 2, 2), (2, 2, 3, 2), (3, 2, 3, 5), (2, 3, 5, 3), (5, 2, 2, 5),
         (2, 2, 5, 2), (4, 3, 3, 4), (3, 4, 4, 3), (2, 2, 10, 9), (3, 3, 4, 3), (2, 5, 6, 2), (5, 3, 3, 6)]

def main():
    ok = True
    for t in CASES:
        st, steps, at, evs, tape = check(t)
        # en2 is traced with the tape at that moment: the tuple is restored (anchor on x's cell 1)
        good = st == 'traced' and evs == ref.ev(t) and at.strip('0') == tape.strip('0')
        x, y, a, b = t
        print(t, f'a^x - b^y = {a ** x - b ** y}', st, steps, f'{evs.count("B")} beeps, {evs.count("O")} boops',
              'OK' if good else 'FAIL')
        ok &= good
    print('tuples:', 'ALL OK' if ok else 'FAILURES'); assert ok

if __name__ == '__main__':
    main()
