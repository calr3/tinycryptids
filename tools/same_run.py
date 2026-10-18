"""Check two machines produce identical tapes/head positions after N steps from blank."""
import sys, tm
a = tm.parse(open(sys.argv[1]).read()); b = tm.parse(open(sys.argv[2]).read())
for n in [10**k for k in range(3, int(sys.argv[3]) + 1)]:
    ra = tm.run(a[0], a[1], maxsteps=n); rb = tm.run(b[0], b[1], maxsteps=n)
    print(n, ra[0], rb[0], 'same tape' if (ra[3], ra[4]) == (rb[3], rb[4]) else 'DIFFERENT', flush=True)
