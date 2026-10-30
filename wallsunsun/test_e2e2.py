"""End-to-end tests of build2.py's design (no trial division) and its merged machine.
* At every check (entry to q2) for m = 2 .. 24: B clean, E's and D's holes the base-m digits
  of m - 1 + N, N = F(m - 1) if m = 1, 4 mod 5 else F(m + 1).
* Variants halt exactly at the first m the model predicts: B with `extra` cells (N = F(m - 1 +
  extra) or F(m + 1 + extra)), all residues `holes`.
* The real design and the merged machine (default machines/wallsunsun_50.txt) run 10^8 steps
  without halting and have the same tape at 10^3 .. 10^8 steps.
Usage: python3 test_e2e2.py [merged.txt]"""
import os, sys, importlib.util
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path[:0] = [HERE, os.path.join(HERE, '..', 'tools')]
import tm, build2
spec = importlib.util.spec_from_file_location('wssinf_test', os.path.join(HERE, '..', 'wallsunsuninf', 'test_e2e.py'))
W = importlib.util.module_from_spec(spec); spec.loader.exec_module(W)

if __name__ == '__main__':
    bad = 0
    o, s = build2.build()
    r = tm.run(o, s, maxsteps=10 ** 10, trace='q2', maxtrace=23)
    for m, t in zip(range(2, 25), r[5]):
        B, E, D = W.blocks(t)
        v = m - 1 + W.count(m)
        if not (B == '1' * (m + 1) and (W.hole(E, m + 2), W.hole(D, m + 2)) == (1 + v % m, 1 + (v // m) % m)):
            print('check of m =', m, 'wrong'); bad += 1
    print('checks m = 2 .. 24', 'OK' if not bad and len(r[5]) == 23 else 'FAIL')
    for kw in [dict(extra=3), dict(extra=8), dict(extra=5, holes=range(5)), dict(extra=11)]:
        o, s = build2.build(**kw)
        r = tm.run(o, s, maxsteps=2 * 10 ** 9)
        want = W.model_beeps(range(2, 40), kw.get('extra', 0), kw.get('holes', (1, 4)))[0]
        got = len(W.blocks(r[4])[0]) - 1 - kw['extra'] if r[0] == 'halt' else None
        print('variant', kw, 'halts at m =', got, '(model', want, ')', 'OK' if got == want else 'FAIL')
        bad += got != want
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(HERE, 'machines', 'wallsunsun_50.txt')
    mo, ms, _ = tm.parse(open(path).read())
    o, s = build2.build()
    for k in range(3, 9):
        a, b = tm.run(o, s, maxsteps=10 ** k), tm.run(mo, ms, maxsteps=10 ** k)
        ok = a[0] == b[0] == 'limit' and (a[3], a[4]) == (b[3], b[4])
        print(f'10^{k} steps: design and merged run on, same tape' if ok else f'10^{k}: FAIL'); bad += not ok
    print('FAIL' if bad else 'all OK')
