"""Hand-placed tuples (a, b, c), started in a given window: the machine halts iff the
remaining windows pass; otherwise it reaches the next tuple (ea0)."""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, build
order, states, _ = tm.parse(build.build())
def blk(v, extra=0): return '1' * (2 * v + 2 + extra)
GAPS = {0: '00000000', 1: '00001100', 2: '00110000'}

def run_at(vals, idx, W=2, extra=0, steps=3 * 10**9):
    q = [blk(v, extra) for v in vals] + ['111']
    tape = '000' + '00'.join(q) + GAPS[W] + '101' + '000'
    head = 3 + sum(len(x) + 2 for x in q[:idx])
    r = tm.run(order, states, start='n5', tape=tape, head=head, maxsteps=steps, trace='ea0', maxtrace=1)
    return r[0], r[1]

def sq(n): r = int(round(n ** 0.5)); return r * r == n

if __name__ == '__main__':
    a, b, c = 44, 117, 240
    print('window 4 (b^2+c^2 square): halt', run_at((a, b, c), 1))
    print('window 4, c = 241: next tuple', run_at((a, b, c + 1), 1))
    print('window 3 (c^2+a^2, then b^2+c^2): halt', run_at((a, b, c), 2))
    print('window 2 (a^2+b^2, ...): halt', run_at((a, b, c), 3))
    print('window 2, odd lengths: halt', run_at((a, b, c), 3, extra=1))
    print('window 1 (a^2+b^2+c^2 not square): next tuple', run_at((a, b, c), 0))
    print('window 2 with b = 118: next tuple', run_at((a, 118, c), 3))
