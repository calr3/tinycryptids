"""The real machine from the blank tape (boot, prologue, lazily created registers) against
k215P from its initial state (pc 0, r0 = 4): at every return to the root with a k215P pc on the
program counter, the pc and the registers decoded from the tape are k215P's next state.
usage: test_e2e.py D [TM steps]"""
import sys, collections
import build
from compiler import P
D = int(sys.argv[1]); maxsteps = int(float(sys.argv[2])) if len(sys.argv) > 2 else 10**7
m = build.machine(D)
inv = {tuple(t): pc for pc, t in m.pc_tape.items() if pc not in m.virtual_pcs}
t = collections.defaultdict(int); q, h = m.start, 0
regs, pc, seen, base = [4] + [0] * 8, 0, 0, None
for steps in range(maxsteps):
    assert q != 'halt'
    w, d, q = (lambda a: a)(m.tm[(q, t[h])]); t[h] = w; h += 1 if d == 'R' else -1
    if q == m.root and (base is None or h == base):
        base = h if base is None else base
        tt = collections.defaultdict(int, {k - base: v for k, v in t.items() if k >= base - 1})
        norm = m.normalize(tt)
        if norm is None or tuple(norm) not in inv:
            continue                      # a prologue or rewritten-decnz slot, not a k215P pc
        r = [x or 0 for x in m.regs_of(tt)]
        if seen:
            e = P[pc]
            if e['tag'] == 0: regs[e['arg']] += 1; pc = e['pos']
            elif e['tag'] == 1:
                if regs[e['arg']]: regs[e['arg']] -= 1; pc = e['pos']
                else: pc = e['zero']
            else: pc = e['zero']
            while pc in m.virtual_pcs:    # a dropped goto
                pc = P[pc]['zero']
        assert inv[tuple(norm)] == pc and r == regs, (seen, inv[tuple(norm)], r, pc, regs)
        seen += 1
print(f'D={D}: {maxsteps} TM steps, {seen} k215P steps agree')
