"""End-to-end checks of the design.
 * Python stepping up to V = VMAX: at every hit (entry into Y0) the tape is read (V from Vb, b
   from K's position, r = V) and the hits of each V are compared with the bases b in
   [2, V - 2] for which V is a repunit; at every V-end (V1) V is checked to increase by 1.
 * Variant z0 = 1 halts at V = 31 (the first value with two bases), z0 = 2 would at 8191.
 * The real machine runs 10^8 steps without halting."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def rep_bases(V):
    out = []
    for b in range(2, V - 1):
        r = 1
        while r < V: r = r * b + 1
        if r == V: out.append(b)
    return out

def blocks(tape, lo, hi):
    s = ''.join(str(tape.get(i, 0)) for i in range(lo, hi))
    return s

VMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 40
ok = True
build.build()
S = build.ST
tape, head, q = {}, 0, build.ORDER[0]
V, hits, steps = None, [], 0
while True:
    b = tape.get(head, 0)
    w, mv, q2 = S[q][b]
    tape[head] = w; head += 1 if mv == 'R' else -1; qp, q = q, q2; steps += 1
    if q == 'Y0':
        # head on H, the region's last cell: ... 0 [Vb left] 0(K) [Vb right] 00 [region]
        lo = min(k for k, v in tape.items() if v == 1)
        t = blocks(tape, lo, head + 1)
        pre, reg = t.rsplit('00', 1)
        Vt = len(reg) - 1
        right = len(pre) - len(pre.rstrip('1')); pre = pre[:len(pre) - right]
        assert pre.endswith('10'); pre = pre[:-1]
        left = len(pre) - len(pre.rstrip('1'))
        if not (reg == '1' * Vt + '0' and left + 1 + right == Vt and pre[-left - 1] == '0'):
            print('bad tape at hit', t); ok = False; break
        hits.append(right)
    if q == 'VR1' and qp != 'VR1':
        hi = max(k for k, v in tape.items() if v == 1)
        Vt = 0
        while tape.get(hi - Vt, 0) == 1: Vt += 1
        Vt -= 1          # the region has V + 1 cells
        if V is not None:
            if Vt != V + 1: print('V jumped', V, Vt); ok = False; break
            if hits != rep_bases(Vt):
                print('V =', Vt, 'hits', hits, 'expected', rep_bases(Vt)); ok = False; break
        V, hits = Vt, []
        if V >= VMAX: break
print(f'hits for V = 4 .. {VMAX} ({steps} steps):', 'OK' if ok else 'FAIL')

build.build(z0=1)
r = tm.run(build.ORDER, build.ST, maxsteps=10**9)
vb = r[4].strip('0').split('00')[-1]   # the region (V + 1 cells), H on cell 1
print('z0 = 1:', r[0], r[1], 'steps, V =', len(vb) - 1, 'OK' if r[0] != 'R' and len(vb) == 32 else 'FAIL')
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('real machine, 10^8 steps:', r[0], r[1], r[2])
