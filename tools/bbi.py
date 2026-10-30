"""Instruction count of a machine in the sense of the Instruction-Limited Busy Beaver
(https://wiki.bbchallenge.org/wiki/Instruction-Limited_Busy_Beaver), for the README's BBi
column: the defined transitions, not counting halting ones. BBi machines halt on reaching an
undefined transition, so a halting transition becomes '---' (one step sooner, same halting
behaviour). This is one fewer than the 'instructions' elsewhere in the repository (e.g.
pa_nsymbols/), which count the halting transition.

    python3 tools/bbi.py weakcollatz/machines/weakcollatz_23.txt landau4/landau4_2sym.tm

Takes the named-state .txt format (tm.py) or landau4's .tm format ('NAME cell cell ...'
with cells like 1LP or ---, '#' comments)."""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import tm

def table(path):
    """{state: [next state or None for undefined, ...]}"""
    text = open(path).read()
    if not path.endswith('.tm'):
        _, states, _ = tm.parse(text)
        return {s: [t and t[2] for t in v] for s, v in states.items()}
    states = {}
    for raw in text.splitlines():
        toks = raw.split('#', 1)[0].split()
        if toks:
            states[toks[0]] = [None if c == '---' else re.fullmatch(r'\d+[LR](\w+)', c).group(1)
                               for c in toks[1:]]
    return states

def bbi(path):
    states = table(path)
    return sum(1 for v in states.values() for n in v if n is not None and n in states)

if __name__ == '__main__':
    for p in sys.argv[1:]:
        print(f'{bbi(p)}\t{p}')
