"""Build the improved PA machine (program.py) and write machines/pa_<N>.txt.

    python3 build.py              the default configuration
    python3 build.py key=value .. switches of program.PA / tmbuilder (e.g. order=E,B7,...)
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, HERE)
import program

HEADER = '''; Halts iff it finds a proof of v0 e. v0 (a contradiction) in a theory equiconsistent with PA:
; Tarski's system S2 of first-order logic with = and e., plus Friedman's set-theoretic axiom
; (the same theory as LegionMammal978's 372-state pa.py).  Built by pa/build.py from
; pa/program.py with pa/tmbuilder.py (a fork of A. J. Wade's TMBuilder).  {n} states.
; Switches: {sw}
'''

if __name__ == '__main__':
    kw = {}
    for a in sys.argv[1:]:
        k, v = a.split('=', 1)
        kw[k] = v if k in ('order', 'vchain', 'grammar_mode') else eval(v)
    b = program.build(**kw)
    n = b.state_count()
    sw = ', '.join(f'{k}={getattr(b, k)}' for k in (
        'order', 'variants', 'breakers', 'stack_rev', 'reload2', 'b6a2', 'shared_eq', 'cascade',
        'shallow', 'vchain', 'dispatch_reset', 'merge_equal', 'grammar_seed'))
    path = os.path.join(HERE, 'machines', f'pa_{n}.txt')
    b.write_named(path, HEADER.format(n=n, sw=sw))
    print(n, 'states ->', path)
