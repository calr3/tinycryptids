"""The checked specification, in the order of the flattened proof (flatten.py's module order):
peano.mm0, then for every module its .mm0 without imports (kz_tm.mm0 for kz_tm.mm1, the
statements of kz_final.mm0 for kz_final.mm1; the other kz_*.mm1 modules state nothing public).
usage: join_flat.py out/kz_final-flat.mm1.order out/kz_final-joined.mm0"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
IMPORT = re.compile(r'^\s*import\s+"([^"]+)"\s*;[^\n]*\n?', re.MULTILINE)


def main(order_file, out):
    peano = os.path.realpath(os.path.join(HERE, 'k215-pa/lean-mm0/vendor/peano.mm0'))
    parts = [open(peano).read()]
    for m in open(order_file).read().split():
        base = os.path.basename(m)
        if base.startswith('kz_') and os.path.dirname(os.path.realpath(m)) == os.path.realpath(HERE):
            if base in ('kz_tm.mm1', 'kz_final.mm1'):
                parts.append(IMPORT.sub('', open(m[:-1] + '0').read()))
            continue
        spec = m[:-1] + '0'
        assert os.path.exists(spec), spec
        parts.append(IMPORT.sub('', open(spec).read()))
    open(out, 'w').write('\n'.join(parts))


if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
