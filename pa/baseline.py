"""Rebuild LegionMammal978's 372-state machine (legion/pa.py) with the forked builder, all
switches off, and check that it is exactly legion/pa.tm.  Writes machines/pa_372.txt."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.setrecursionlimit(100000)
import tmbuilder
sys.modules['TMBuilder'] = tmbuilder          # legion/pa.py does `import TMBuilder`
sys.path.insert(0, os.path.join(HERE, 'legion'))
import pa as legion_pa

def build(**switches):
    cls = type('PA', (legion_pa.PA,), switches)
    b = cls()
    b.build_machine()
    return b

def tm_lines(path):
    return sorted(l.strip() for l in open(path) if l.strip() and not l.startswith('#'))

if __name__ == '__main__':
    b = build()
    tmp = os.path.join(HERE, 'machines', '_rebuilt.tm')
    b.tm.save(tmp)
    same = tm_lines(tmp) == tm_lines(os.path.join(HERE, 'legion', 'pa.tm'))
    os.remove(tmp)
    print('rebuilt', b.state_count(), 'states;', 'identical to legion/pa.tm' if same else 'DIFFERENT')
    assert same
    b.write_named(os.path.join(HERE, 'machines', 'pa_372.txt'),
        '; LegionMammal978, pa.py (turing_machine_explorer @ c3d265a, 2026-02-15), 372 states.\n'
        '; Halts iff it finds a proof of v0 e. v0 in a PA-equivalent first-order theory\n'
        '; (Tarski\'s system S2 with Friedman\'s set-theoretic axiom). Built by baseline.py.')
