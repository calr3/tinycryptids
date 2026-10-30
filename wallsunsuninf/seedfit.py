"""Fit a seed into a merged machine of the seedless design (build.build(with_seed=False)):
fill at most `depth` of its undefined transitions, and pick a start state, so that the run
from a blank tape reaches an exact round start (build.canon(m) in e1's class, the head
on D's cell 0).  From there the machine follows the design's rounds m, m + 1, ...
The search (seedfit.c) branches on each undefined slot as the run meets it.  Of the
solutions it takes the one with the fewest steps to the round start, then writes the
machine with its start state first.
Usage: python3 seedfit.py merged.txt out.txt [depth=3]"""
import sys, os, subprocess, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..', 'tools'))
import tm

def main(src, dst, depth):
    order, states, _ = tm.parse(open(src).read())
    idx = {q: i for i, q in enumerate(order)}
    tmp = tempfile.mkdtemp()
    exe = os.path.join(tmp, 'seedfit')
    subprocess.run(['gcc', '-O2', '-Wno-unused-result', '-o', exe, os.path.join(HERE, 'seedfit.c')], check=True)
    lines = [f'{len(order)} {idx["e1"]}']
    for q in order:
        for t in states[q]:
            lines.append('-1 0 0' if t is None else f'{idx.get(t[2], -2)} {t[0]} {1 if t[1] == "R" else 0}')
    out = subprocess.run([exe, str(depth), '30000'], input='\n'.join(lines) + '\n',
                         capture_output=True, text=True).stdout.splitlines()
    sols = []
    for l in out:
        if not l.startswith('FOUND'): continue
        tok = l.split()
        start, m, steps = int(tok[2]), int(tok[4]), int(tok[6])
        slots = []
        for a in tok[8:]:
            qb, act = a.strip('()').split(')->')
            q, b = map(int, qb.split(','))
            w, d, t = int(act[0]), act[1], int(act[2:])
            slots.append((order[q], b, (w, d, order[t])))
        sols.append((steps, m, order[start], slots))
    print(len(sols), 'solutions')
    steps, m, start, slots = min(sols, key=lambda x: x[0])
    for q, b, t in slots: states[q][b] = t
    order = [start] + [q for q in order if q != start]
    with open(dst, 'w') as f:
        f.write(f'; {os.path.basename(src)} with a seed fitted by seedfit.py: start {start},\n'
                f'; filled ' + ', '.join(f'{q} reading {b} -> {t[0]}{t[1]}{t[2]}' for q, b, t in slots)
                + f'.\n; Round m = {m} starts at step {steps}.\n'
                f'; {len(order)} states, 2 symbols.\n; Beep: q9 reading 0.\n\nblank_symbol: 0\n\n')
        for q in order:
            f.write(q + '\n')
            for r, t in enumerate(states[q]):
                f.write('    -\n' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}\n')
        f.write('\n')
    print('start', start, 'round', m, 'at step', steps, slots, '->', dst)

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2], int(sys.argv[3]) if len(sys.argv) > 3 else 3)
