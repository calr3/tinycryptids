"""At every t1 / ma1 event: list the non-blank cells by absolute index (head
marked) so the block geometry can be read off without eyeballing rulers."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build

c0 = int(sys.argv[1]) if len(sys.argv) > 1 else 3
maxev = int(sys.argv[2]) if len(sys.argv) > 2 else 12
build.build(c0=c0, nf=1)
ST, ORDER = build.ST, build.ORDER

tape, h, q = {}, 0, ORDER[0]
step, ev = 0, 0
while step < 200000:
    t = ST[q][tape.get(h, 0)]
    if t is None:
        print(f'step {step}: HALT in {q}')
        break
    if q in ('t1', 'ma1'):
        cells = sorted(i for i, v in tape.items() if v)
        print(f'step {step} {q} head={h}:', ' '.join(f'{i}' if i != h else f'<{i}>' for i in cells))
        ev += 1
        if ev >= maxev:
            break
    w, d, nq = t
    tape[h] = w
    h += 1 if d == 'R' else -1
    q = nq
    step += 1
