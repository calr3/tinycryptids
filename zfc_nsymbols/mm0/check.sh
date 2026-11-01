#!/bin/sh
# Build and check the proof: flatten kz_final.mm1 (post-order imports, as k215-pa's check.py),
# compile with mm0-rs, join the spec kz_final.mm0, check with mm0-c; then check that mm0-c
# rejects the same proof against a spec whose last theorem concludes F.
# usage: MM0RS=/path/to/mm0-rs MM0C=/path/to/mm0-c sh check.sh
set -eu
cd "$(dirname "$0")"
mkdir -p out
python3 -I flatten.py kz_final.mm1 out/kz_final-flat.mm1
"$MM0RS" compile --cache=false out/kz_final-flat.mm1 out/kz_final.mmb
python3 -I join_flat.py out/kz_final-flat.mm1.order out/kz_final-joined.mm0
"$MM0C" out/kz_final.mmb < out/kz_final-joined.mm0
echo "mm0-c: kz_final checked"
python3 -I - <<'PY'
s = open('out/kz_final-joined.mm0').read()
i = s.rindex('theorem kz_halts_iff_ZFC_inconsistent')
j = s.index('$ kzHalts <-> zfcInconsistent $;', i)
open('out/kz_final-false.mm0', 'w').write(s[:j] + '$ F. $;' + s[j + len('$ kzHalts <-> zfcInconsistent $;'):])
PY
if "$MM0C" out/kz_final.mmb < out/kz_final-false.mm0 > out/reject.log 2>&1; then
  echo "control FAILED: a false conclusion was accepted"; exit 1
else
  echo "control: the false conclusion is rejected"
fi
sha256sum kz_final.mm0 out/kz_final-joined.mm0 out/kz_final.mmb
