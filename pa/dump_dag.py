"""Print the decision DAG (after factoring) of a build, one sequence per line, and a summary."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program
from collections import Counter
b = program.build()
b2 = type('X', (type(b),), {})()
b2.main()
if b2.grammar_seed is None: b2.breakout_common_subsequences()
reach = sorted(b2.reachable())
def nm(v):
    if isinstance(v, int):
        return b2.sequences[v].name or f'#{v}'
    return v.replace('3.', '')
tot = 0
for i in reach:
    q = b2.sequences[i].seq
    tot += len(q) - 1
    print(f'#{i} {b2.sequences[i].name or ""} [{len(q)-1}]: ' + ' , '.join(nm(v) for v in q)[:300])
names = {s for s, _ in b.tm.states}
fw = Counter()
for s in names:
    if s[0].isdigit():
        k = s.split('.')
        fw[k[0] + '.' + (k[1] if not k[1].isdigit() else 'N')] += 1
print('cons nodes before reduce_to_cons', tot)
print('states', len(names), 'framework', sum(fw.values()), sorted(fw.items()))
