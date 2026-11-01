"""kz_final.mm1 and kz_final.mm0 (the checked statement).  usage: gen_final.py"""
import os, json
HERE = os.path.dirname(os.path.abspath(__file__))
from gen_rel import pnum

SPEC_IMPORTS = ['kz_tm.mm0',
                'k215-pa/pa-mm0/k215_literal_runtime_conditional.mm0',
                'k215-pa/pa-mm0/k215_literal_runtime_native_iteration.mm0',
                'k215-pa/pa-mm0/zfc_proofs.mm0']

STATEMENTS = '''
-- The 13-symbol machine of kz_tm.mm0 halts iff Glazer's register program k215P halts.
theorem kz_halts_iff_program: $ kzHalts <-> k215PInitialHalts $;

-- With three theorems of github.com/elliotglazer/k215-pa (checked there; their statements are
-- copied verbatim: K215_halts_iff_ZFC_inconsistent_final, k215LiteralHalts_iff_program_given_native_law,
-- k215PActualNativeLaw), the machine halts iff ZFC is inconsistent.
theorem kz_halts_iff_ZFC_inconsistent
  (hK215: $ k215LiteralHalts <-> zfcInconsistent $)
  (hProgram: $ k215PNativeLaw -> (k215LiteralHalts <-> k215PInitialHalts) $)
  (hNative: $ k215PNativeLaw $):
  $ kzHalts <-> zfcInconsistent $;
'''


def main():
    N = json.load(open(os.path.join(HERE, 'prefix_n.json')))['N']
    spec = '\n'.join(f'import "{f}";' for f in SPEC_IMPORTS) + '\n' + STATEMENTS
    open(os.path.join(HERE, 'kz_final.mm0'), 'w').write(spec)
    mm1 = ['import "kz_prefix.mm1";'] + [f'import "{f[:-1]}1";' for f in SPEC_IMPORTS[1:]] + ['']
    mm1.append('''theorem kzHF_back (c d: nat): $ kzReach c d -> kzHaltsFrom c -> kzHaltsFrom d $ =
(let ([m (dummy! 'nat)] [T (dummy! 'nat)] [k (dummy! 'nat)])
 '(!! eex ,m (!! eexd ,T (exp (!! iexde ,k
   (eqtrd (kzQeqd (kzRuneq1d anr)) (eqtrd (kzQeqd (kzRuneq2d (eqcomd (anwl anl))))
     (eqtrd (a1i (kzQeq (eqtr (eqcom kzRunAdd) (eqtr (kzRuneq1 addcom) kzRunAdd))))
       (eqtrd (kzQeqd (syl kzRun_halt (anwl anr))) (anwl anr))))))))));
theorem kzHalts_HF: $ kzHalts <-> kzHaltsFrom (kzState 0 0 0) $ =
(let ([x (dummy! 'nat)] [y (dummy! 'nat)]) '(!! cbvex ,x ,y (eqeq1d (kzQeqd (kzRuneq1d id)))));
theorem kzHF_shift (c d: nat) (h: $ kzReach c d $): $ kzHaltsFrom c <-> kzHaltsFrom d $ =
'(ibii (ax_mp kzHF_back h) (ax_mp kzHF_reach h));
theorem kzPH_shift (n s: nat): $ k215PHaltsFrom (k215PIter n s) <-> k215PHaltsFrom s $ =
'(ibii
   (!! eex ,(dummy! 'nat) (syl k215PHaltsFrom_intro (eqtrd (a1i (k215PStatuseq k215PIter_add)) id)))
   (!! eex ,(dummy! 'nat) (syl k215PHaltsFrom_intro
     (eqtrd (k215PStatuseqd (eqtrd (a1i (eqtr (eqcom k215PIter_add) (eqtr (k215PItereq1 addcom) k215PIter_add)))
       (syl k215PIter_stopped id))) id))));''')
    mm1.append(f'''pub theorem kz_halts_iff_program: $ kzHalts <-> k215PInitialHalts $ =
'(bitr kzHalts_HF (bitr (kzHF_shift (kzRP_R kzTMpre))
   (bitr (bicom (ax_mp kzEquiv kzRelpre))
     (bitr (bicom (k215PHaltsFromeq kzPI{N})) kzPH_shift))));
pub theorem kz_halts_iff_ZFC_inconsistent
  (hK215: $ k215LiteralHalts <-> zfcInconsistent $)
  (hProgram: $ k215PNativeLaw -> (k215LiteralHalts <-> k215PInitialHalts) $)
  (hNative: $ k215PNativeLaw $):
  $ kzHalts <-> zfcInconsistent $ =
'(bitr kz_halts_iff_program (bitr (bicom (ax_mp hProgram hNative)) hK215));''')
    open(os.path.join(HERE, 'kz_final.mm1'), 'w').write('\n'.join(mm1) + '\n')


if __name__ == '__main__':
    main()
