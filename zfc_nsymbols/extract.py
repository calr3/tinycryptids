"""Extract Glazer's register program k215P from k215-pa/pa-mm0/k215_literal_runtime_program.mm0.

The table k215PLookup is a binary search tree of defs  k215PTable<lo>_<hi> (pc: nat) =
if (pc < M) A B,  whose leaves are  k215PEntry path tag arg zero positive  (tag 0 inc, 1 decnz,
2 and 3 goto `zero`, 4 halt; pcs >= 4751 halt).  Writes k215p.json: a list, by pc, of
{path, tag, arg, zero, pos}.

usage: python3 extract.py ../../k215-pa/pa-mm0/k215_literal_runtime_program.mm0 [k215p.json]
"""
import re, sys, json


def val(tok):
    tok = tok.strip()
    if tok.isdigit():
        return int(tok)
    m = re.fullmatch(r'k215P?Num(\d+)', tok)
    if not m:
        raise ValueError(tok)
    return int(m.group(1))


def split_branches(body):
    """'(A) (B)' -> A, B"""
    assert body.startswith('(')
    depth = 0
    for i, c in enumerate(body):
        depth += c == '('
        depth -= c == ')'
        if depth == 0:
            a, b = body[1:i], body[i + 2:].strip()
            assert b.startswith('(') and b.endswith(')')
            return a, b[1:-1]
    raise ValueError(body[:80])


def entry(txt):
    m = re.fullmatch(r'k215PEntry (\(.*\)|0) (\S+) (\S+) (\S+) (\S+)', txt)
    path = [int(b) for b in re.findall(r'\((\d) :', m.group(1))]
    return dict(path=path, tag=val(m.group(2)), arg=val(m.group(3)), zero=val(m.group(4)),
                pos=val(m.group(5)))


def main(src, out):
    text = open(src).read()
    entries = {}
    for m in re.finditer(r'def k215PTable(\d+)_(\d+) \(pc: nat\): nat = \$ if \(pc < (\S+)\) (.*) \$;', text):
        lo, mid = int(m.group(1)), val(m.group(3))
        a, b = split_branches(m.group(4))
        for txt, pc in ((a, lo), (b, mid)):
            if txt.startswith('k215PEntry'):
                assert pc not in entries
                entries[pc] = entry(txt)
    n = max(entries) + 1
    assert sorted(entries) == list(range(n)), 'gaps in the table'
    m = re.search(r'def k215PLookup \(pc: nat\): nat = \$ if \(pc < (\S+)\)', text)
    assert val(m.group(1)) == n
    json.dump([entries[i] for i in range(n)], open(out, 'w'))
    print(n, 'entries ->', out)


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2] if len(sys.argv) > 2 else 'k215p.json')
