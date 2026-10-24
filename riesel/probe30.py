"""Dump the tape at every ma1 checkpoint with run-length annotation."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))
import build, tm

build.build()
r = tm.run(build.ORDER, build.ST, maxsteps=2 * 10**6, trace='ma1', maxtrace=12)
prev = None
for t in r[5]:
    if t == prev:
        continue
    prev = t
    s = t.strip('0')
    # run-length encode, head position is not known from the string; just print
    out = []
    i = 0
    while i < len(s):
        j = i
        while j < len(s) and s[j] == s[i]:
            j += 1
        out.append(f"{len(s[i:j])}{s[i]}")
        i = j
    print(' '.join(out))
print('status', r[0], 'steps', r[1])
