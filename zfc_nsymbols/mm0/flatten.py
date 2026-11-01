"""Linearize MM1 imports (post-order DFS), as k215-pa/pa-mm0/check.py does: one flat .mm1
importing only peano.mm1.  usage: flatten.py root.mm1 out.mm1"""
import re, sys, os
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;', re.MULTILINE)
VENDOR = os.path.realpath(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'k215-pa/lean-mm0/vendor/peano.mm1'))
def main(root, out):
    seen, chunks, order = set(), [], []
    sys.setrecursionlimit(100000)
    def visit(p):
        p = os.path.realpath(p)
        if p in seen: return
        seen.add(p)
        if p == VENDOR: return
        c = open(p, encoding='utf-8').read()
        for ch in IMPORT.findall(c):
            visit(os.path.join(os.path.dirname(p), ch))
        order.append(p)
        chunks.append('\n-- Original proof module: ' + os.path.basename(p) + '\n' + IMPORT.sub('', c))
    visit(root)
    rel = os.path.relpath(VENDOR, os.path.dirname(os.path.realpath(out)))
    open(out, 'w', encoding='utf-8').write('import "' + rel + '";\n' + '\n'.join(chunks) + '\n')
    open(out + '.order', 'w').write('\n'.join(order) + '\n')
    print(len(order), 'modules', file=sys.stderr)
if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
