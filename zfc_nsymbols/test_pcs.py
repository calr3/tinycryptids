"""Every pc of k215P, from random registers: the machine, from the configuration that represents
(pc, registers) (state = the root node, head on PC cell 0), reaches the configuration of
k215P's next state (or halts when k215P halts).  usage: test_pcs.py D [trials] [seed]"""
import sys, random
import build
from compiler import P, NP
D = int(sys.argv[1]); trials = int(sys.argv[2]) if len(sys.argv) > 2 else 3
rnd = random.Random(int(sys.argv[3]) if len(sys.argv) > 3 else 1)
m = build.machine(D)
bad = 0
for pc in range(NP):
    if pc in m.virtual_pcs:
        continue                      # a dropped goto: no configuration of its own
    for _ in range(trials):
        regs = [rnd.choice([0, 0, 1, 2, 3, rnd.randint(0, 20)]) for _ in range(9)]
        ok, _, _ = m.check_pc(pc, regs)
        if not ok:
            bad += 1
            print('mismatch', pc, P[pc], regs)
print(f'D={D}: {NP - len(m.virtual_pcs)} pcs x {trials}: {bad} mismatches ({len(m.virtual_pcs)} virtual gotos skipped)')
sys.exit(1 if bad else 0)
