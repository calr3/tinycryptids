"""Tools for Turing machines written in the named-state text format
(the format of bbchallenge's weak_Collatz_conjecture_124_2.txt).

Format: ';' starts a comment. 'key: value' header lines. A state is a name
on its own line followed by one line per read symbol (0, 1, ...): either
'read write move next' or '-' (undefined). The first state is the start
state. A transition to an undefined state name (e.g. 'halt') halts.
"""
import re, sys

def parse(text):
    states, order, header, cur = {}, [], {}, None
    for raw in text.splitlines():
        line = raw.split(';', 1)[0].strip()
        if not line:
            continue
        m = re.fullmatch(r'(\w+)\s*:\s*(\S+)', line)
        if m and cur is None:
            header[m.group(1)] = m.group(2); continue
        toks = line.split()
        if len(toks) == 1 and toks[0] != '-':
            cur = toks[0]
            assert cur not in states, f'duplicate state {cur}'
            states[cur] = []; order.append(cur); continue
        assert cur is not None, line
        if toks == ['-']:
            states[cur].append(None)
        else:
            r, w, d, n = toks
            assert int(r) == len(states[cur]), f'{cur}: read symbol out of order'
            assert d in 'LR'
            states[cur].append((int(w), d, n))
    nsym = max(len(v) for v in states.values())
    for k, v in states.items():
        assert len(v) == nsym, f'{k} has {len(v)} lines'
    return order, states, header

def to_standard(order, states):
    """bbchallenge standard text format; halting transitions -> '1RZ'-style
    with next state '-' printed as '---' when undefined."""
    if len(order) > 26:
        idx = {s: str(i) for i, s in enumerate(order)}  # fall back to numbers
        sep = ','
    else:
        idx = {s: chr(65 + i) for i, s in enumerate(order)}
        sep = ''
    rows = []
    for s in order:
        cells = []
        for t in states[s]:
            if t is None:
                cells.append('---')
            else:
                w, d, n = t
                cells.append(f'{w}{d}{idx.get(n, "Z")}')
        rows.append(sep.join(cells))
    return '_'.join(rows)

def compile_table(order, states):
    """Integer table for the C simulator: halt state = -1, undefined = -2."""
    idx = {s: i for i, s in enumerate(order)}
    out = []
    for s in order:
        for t in states[s]:
            if t is None:
                out.append((0, 0, -2))
            else:
                w, d, n = t
                out.append((w, 1 if d == 'R' else 0, idx.get(n, -1)))
    return idx, out

if __name__ == '__main__':
    order, states, header = parse(open(sys.argv[1]).read())
    print(len(order), 'states')
    print(to_standard(order, states))

import subprocess, os
SIM = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'sim')

def run(order, states, start=None, tape='', head=0, maxsteps=10**7, trace=None, maxtrace=0):
    """Run from given tape (string of 0/1) with head index into it.
    Returns (status, steps, state_name, head_index, tape_string)."""
    idx, table = compile_table(order, states)
    nsym = len(states[order[0]])
    s = idx[start or order[0]]
    lines = [f'{len(order)} {nsym} {s} {maxsteps} {head} {len(tape)} {tape or "-"}' if tape
             else f'{len(order)} {nsym} {s} {maxsteps} {head} 0']
    lines += [f'{w} {d} {n}' for w, d, n in table]
    lines.append(f'{idx[trace] if trace else -1} {maxtrace}')
    res = subprocess.run([SIM], input='\n'.join(lines) + '\n', capture_output=True, text=True).stdout.splitlines()
    traces = [l[2:] for l in res if l.startswith('T ')]
    out = [l for l in res if not l.startswith('T ')][0].split()
    status, steps, st, h, t = out[0], int(out[1]), int(out[2]), int(out[3]), out[4]
    if trace: return status, steps, order[st], h, t, traces
    return status, steps, order[st], h, t
