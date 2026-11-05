"""End-to-end tests of the Carmichael machine (pure Python stepping, sim_check.py).
* At every round end (state RE2) V's hole is at slot v+1-phi(M) (none if phi(M) > v), and
  K/R is (M-1, 1).  The rounds of each v are M = 2, 3, ... up to the second M with
  phi(M) = v, or all of [2, s+1] when there is at most one (there is none, for v <= 7),
  with s + 1 >= 2 v^2.
* Variants: halting at a second match halts at v = 2, M = 4 (phi 3 = phi 4 = 2); halting at
  a window without match halts at the end of v = 3's window; never aborting halts at the end
  of v = 2's window (f = 1).
* The real machine runs past 10^8 steps (C simulator).
Usage: python3 test_e2e.py [file]   (default: build.py's design)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build, sim_check as S

if __name__ == '__main__':
    text = open(sys.argv[1]).read() if len(sys.argv) > 1 else build.build()
    st, ev, steps = S.run(text, maxv=6, maxsteps=10 ** 9)
    print('real machine up to v = 6:', st, steps, 'steps'); assert st == 'ok' and S.check_events(ev)
    for var, want in (('second', (2, 4)), ('none', (3, 27)), ('atleast1', (2, 12))):
        st, ev, steps = S.run(build.build(variant=var), maxv=6, maxsteps=10 ** 9)
        print(f'variant {var}:', st, 'last round v, M =', ev[-1][:2]); assert st == 'halt' and ev[-1][:2] == want
    order, states, _ = tm.parse(text)
    res = tm.run(order, states, maxsteps=10 ** 8)
    print('C simulator, 10^8 steps:', res[0]); assert res[0] != 'halt'
    print('ALL OK')
