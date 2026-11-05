import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import tm, leangen
from collections import defaultdict
o, S, _ = tm.parse(open(sys.argv[1]).read()); o2, S2, _ = tm.parse(open(sys.argv[2]).read())
phi = leangen.state_map(o, S, o2, S2)
cl = defaultdict(list)
for k, v in phi.items(): cl[v].append(k)
single = [v[0] for v in cl.values() if len(v) == 1]
print(len(cl), 'classes;', len(single), 'singletons:', ' '.join(sorted(single)))
for v in sorted(cl.values(), key=len, reverse=True)[:100]:
    if len(v) > 1: print(' '.join(v))
