"""End-to-end checks of the design.
 * at the end of each round (state ix3) the tape is D 00 X G A with D's hole at d10,
   |X| = x + 3 for x = 196, 887, 1675, ... (x := x + rev10 x) and A one cell;
 * test variants (seed x = sx instead of 1): the seed's compare (A = 195 against sx)
   halts iff sx = 195, else x starts at sx + 195 and the machine halts in the round
   of the first palindrome;
 * the real machine must run past 10^8 steps."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

def rev10(n): return int(str(n)[::-1])

def xs_of(traces):
    out = []
    for tr in traces:
        tr = tr.strip('0')
        D, rest = tr[:12], tr[14:]
        X, A = rest.split('0')[0], rest.rstrip('0').split('0')[-1]
        assert D == '1' * 10 + '01' and tr[12:14] == '00' and A == '1', tr
        out.append(len(X) - 3)
    return out

ok = True
build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**9, trace='ix3', maxtrace=8)
ref, x = [], 196
for _ in range(len(r[5])):
    ref.append(x); x += rev10(x)
got = xs_of(r[5])
print('rounds', got, 'OK' if got == ref else 'FAIL'); ok &= got == ref

for sx in (195, 5, 0, 4, 62, 85):
    build.build(seed_x=sx)
    h = tm.run(build.ORDER, build.ST, maxsteps=10**10, trace='ix3', maxtrace=100)
    ref, x = [], sx + 195
    if sx != 195:
        ref.append(x)
        while rev10(x) != x:
            x += rev10(x); ref.append(x)
    got = xs_of(h[5])
    good = h[0] == 'halt' and got == ref
    print(f'variant seed x={sx}: {h[0]} after {h[1]} steps, rounds {got}', 'OK' if good else 'FAIL')
    ok &= good

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=10**8)
print('10^8 steps:', r[0], 'OK' if r[0] == 'limit' else 'FAIL'); ok &= r[0] == 'limit'
print('ALL OK' if ok else 'FAILURES')
