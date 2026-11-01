"""lookups.json: for every pc, Glazer's lemma  k215PLookup <pc> = k215PEntry ..  (name, numeral, file)."""
import re, glob, json, os
HERE = os.path.dirname(os.path.abspath(__file__))
names = {}
for f in glob.glob(os.path.join(HERE, 'k215-pa/pa-mm0/k215_literal_runtime_lookups_norm*.mm0')):
    for m in re.finditer(r'theorem (k215PLookupNorm\d+_(\d+)): \$ k215PLookup (\S+) =', open(f).read()):
        names[int(m.group(2))] = (m.group(1), m.group(3), os.path.basename(f))
assert sorted(names) == list(range(4751))
json.dump(names, open(os.path.join(HERE, 'lookups.json'), 'w'))
