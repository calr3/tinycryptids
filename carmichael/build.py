"""Generator for a 2-symbol Turing machine that halts iff Carmichael's totient conjecture
fails: iff some m >= 1 has phi(n) != phi(m) for every n != m.

Search.  For v = 2, 3, ...: count the M in the window [2, s + 1] with phi(M) = v, and halt
if exactly one does.  The window size s grows with v so that s + 1 >= 2 v^2, and every
M with phi(M) = v satisfies M <= 2 v^2, so a single match is a counterexample.

phi(M) for M >= 2 is the number of k in [1, M-1] with gcd(k, M-k) = 1, and gcd(k, r) = 1
iff the walk 0, k, 2k, ... (mod r) reaches 1 before it returns to 0.

Tape (left to right; blocks of slots, separators 00, a hole is a single 0 in a block):

    1 K 00 1 R 00 V 1 00 f 0 B 1
    K: k slots (hole H_K), R: r slots (hole H_R), M = k + r
    V: v+1 slots, hole at slot v+1-c after c coprime pairs (none once c > v)
    f: one match found so far in this window
    B: s slots, hole at slot s+1-j after round j

Test of (k, r) (H_K, H_R on their first slots): ticks advance both holes cyclically; when
H_K wraps (every k ticks) H_R's old position decides: 0 -> coprime, r-1 -> not coprime.
Both holes end on their first slots.  Coprime: move the V hole one slot left.  Then the
separator moves right, (k, r) -> (k+1, r-1), until r = 1.

Round end: V has its hole on slot 1 iff phi(M) = v (a match).  A match with f = 1 is the
second one: start the next v.  Otherwise f |= match, and B's hole moves left; when it runs
off, the window is over: halt iff f = 1, else start the next v.  Then (M-1, 1) -> (1, M).

Next v: V gains a slot, B gains 4 slots per slot of V (s grows by 4v + 3), K/R -> (1, 1).
"""
import sys

ST, ORDER = {}, []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def build(halt_state='halt', seed_v=2, variant=None):
    """variant (tests only): 'second' halts at a second match, 'none' at a window without
    a match, 'atleast1' at a window with at least one match."""
    ST.clear(); ORDER.clear()
    # ---- seed: V with seed_v slots and its end, then the next-v routine at V's end
    for i in range(seed_v + 1):
        S(f'seed{i}', T(1, 'R', f'seed{i + 1}' if i < seed_v else 'VG4'), None)
    # ---- the test of (k, r)
    S('KA', T(1, 'R', 'KN'), T(1, 'L', 'KA'))            # find H_K (going left), advance it
    S('KN', T(0, 'L', 'KW'), T(0, 'R', 'TR1'))           # 0: off K's end, wrap
    S('KW', T(0, 'R', 'KW1'), T(1, 'L', 'KW'))
    S('KW1', None, T(1, 'R', 'KW2'))                     # K's start cell
    S('KW2', None, T(0, 'R', 'TC1'))                     # H_K on a1; a stride ends: check
    for m in 'RC':
        S(f'T{m}1', T(0, 'R', f'T{m}2'), T(1, 'R', f'T{m}1'))
        S(f'T{m}2', T(0, 'R', f'T{m}3'), None)
        S(f'T{m}3', None, T(1, 'R', f'T{m}4'))           # R's start cell
    S('TR4', T(1, 'R', 'RN'), T(1, 'R', 'TR4'))          # find H_R, advance it
    S('RN', T(0, 'L', 'RW'), T(0, 'L', 'GK1'))
    S('TC4', T(0, 'R', 'CV1'), T(1, 'R', 'TC5'))         # H_R on b1: kb = 1 (mod r), coprime
    S('TC5', T(1, 'R', 'CN'), T(1, 'R', 'TC5'))
    S('CN', T(0, 'L', 'CW'), T(0, 'L', 'GK1'))           # 0: H_R wraps, kb = 0: not coprime
    for m in 'RC':
        S(f'{m}W', T(0, 'R', f'{m}W1'), T(1, 'L', f'{m}W'))
        S(f'{m}W1', None, T(1, 'R', f'{m}W2'))
        S(f'{m}W2', None, T(0, 'L', 'GK1') if m == 'R' else T(0, 'R', 'EC1'))
    S('GK1', T(0, 'L', 'GK2'), T(1, 'L', 'GK1'))
    S('GK2', T(0, 'L', 'KA'), None)
    # ---- coprime: V's hole one slot left (none once it falls off), back to b1
    S('CV1', T(0, 'R', 'CV2'), T(1, 'R', 'CV1'))
    S('CV2', T(0, 'R', 'CV3'), None)
    S('CV3', T(0, 'R', 'CV4'), T(1, 'R', 'CV3'))
    S('CV4', T(0, 'L', 'CVS'), T(1, 'L', 'CV5'))         # 0 0: no hole
    S('CV5', T(1, 'L', 'CV6'), None)
    S('CV6', T(0, 'L', 'BK2'), T(0, 'L', 'BK1'))         # 0: off V's start
    S('CVS', T(0, 'L', 'BK1'), None)
    S('BK1', T(0, 'L', 'BK2'), T(1, 'L', 'BK1'))
    S('BK2', T(0, 'L', 'BK3'), None)
    S('BK3', T(0, 'R', 'EC1'), T(1, 'L', 'BK3'))
    # ---- r = 1: round end; else move the separator right
    S('EC1', T(0, 'R', 'RE1'), T(0, 'L', 'SH2'))
    S('SH2', T(1, 'L', 'SH3'), None)
    S('SH3', None, T(0, 'L', 'SH4'))
    S('SH4', T(0, 'L', 'SH5'), None)
    S('SH5', T(1, 'L', 'KA'), None)
    # ---- round end: match?, flag, B
    S('RE1', T(0, 'R', 'RE2'), None)
    S('RE2', T(1, 'R', 'MV1'), T(1, 'R', 'NV1'))         # 0 on V's slot 1: a match
    S('MV1', T(0, 'R', 'MV2'), T(1, 'R', 'MV1'))
    S('MV2', T(0, 'R', 'MF'), None)
    S('MF', T(1, 'R', 'F1c'), {'second': T(0, 'R', halt_state), 'atleast1': T(1, 'R', 'F1c')}.get(variant, T(0, 'R', 'VGb')))          # a second match: next v
    S('NV1', T(0, 'R', 'NV2'), T(1, 'R', 'NV1'))         # fill V's hole
    S('NV2', T(0, 'R', 'NF'), T(1, 'L', 'NV3'))
    S('NV3', T(1, 'R', 'NV1'), None)
    S('NF', T(0, 'R', 'F0c'), T(1, 'R', 'F1c'))
    S('F0c', T(0, 'R', 'F0s'), None)
    S('F1c', T(0, 'R', 'F1s'), None)
    S('F0s', T(0, 'L', halt_state if variant == 'none' else 'VG1'), T(1, 'R', 'BA1'))         # 0: B runs off, f = 0: next v
    S('F1s', T(0, 'L', halt_state), T(1, 'R', 'BA1'))    # 0: B runs off, f = 1: HALT
    S('BA1', T(1, 'L', 'BA2'), T(1, 'R', 'BA1'))
    S('BA2', None, T(0, 'L', 'RT1'))
    S('RT1', T(0, 'L', 'RT2'), T(1, 'L', 'RT1'))
    S('RT2', T(0, 'L', 'RT3'), T(1, 'L', 'RT3'))         # f
    S('RT3', T(0, 'L', 'RT4'), None)
    S('RT4', T(0, 'L', 'RT5'), None)
    S('RT5', None, T(1, 'L', 'RT6'))                     # V's end cell
    S('RT6', None, T(0, 'L', 'RT7'))                     # V's hole on slot v+1
    S('RT7', T(0, 'L', 'RT8'), T(1, 'L', 'RT7'))
    S('RT8', T(0, 'L', 'RS1'), None)
    # ---- (M-1, 1) -> (1, M)
    S('RS1', T(1, 'L', 'RS2'), None)
    S('RS2', None, T(1, 'L', 'RS3'))
    S('RS3', T(1, 'L', 'RS4'), None)
    S('RS4', T(1, 'L', 'RS5'), None)
    S('RS5', T(0, 'L', 'RS6'), T(1, 'L', 'RS5'))         # to a1
    S('RS6', None, T(0, 'L', 'RS7'))
    S('RS7', T(1, 'R', 'RS8'), None)
    S('RS8', T(0, 'R', 'RS9'), None)
    S('RS9', T(0, 'R', 'RS10'), None)
    S('RS10', None, T(0, 'R', 'RS11'))
    S('RS11', None, T(1, 'R', 'RS12'))
    S('RS12', None, T(0, 'L', 'GK1'))
    # ---- next v: V gains a slot (its hole: the cursor), B grows by 4 per cursor step
    S('VGb', T(0, 'R', 'VGc'), None)
    S('VGc', T(0, 'L', 'VG1'), T(0, 'L', 'VG1'))
    S('VG1', T(0, 'L', 'VG2'), None)
    S('VG2', T(0, 'L', 'VG3'), None)
    S('VG3', T(0, 'L', 'VG4'), None)
    S('VG4', T(1, 'L', 'VG5'), None)
    S('VG5', None, T(0, 'R', 'GR1'))
    S('GR1', T(0, 'R', 'GR2'), T(1, 'R', 'GR1'))
    S('GR2', T(0, 'R', 'GR3'), None)
    S('GR3', T(0, 'R', 'GR4'), None)
    S('GR4', T(0, 'R', 'GX'), None)
    S('GX', T(0, 'R', 'GY'), T(1, 'R', 'GX'))            # fill B's hole
    S('GY', T(0, 'L', 'A1'), T(1, 'L', 'GF'))
    S('GF', T(1, 'R', 'GX'), None)
    S('A1', T(1, 'R', 'A2'), None)
    S('A2', T(1, 'R', 'A3'), None)
    S('A3', T(0, 'R', 'A4'), None)                       # B's hole on its last slot
    S('A4', T(1, 'L', 'A5'), None)
    S('A5', T(0, 'L', 'GB1'), None)
    S('GB1', T(0, 'L', 'GB2'), T(1, 'L', 'GB1'))
    S('GB2', T(0, 'L', 'GB3'), None)
    S('GB3', T(0, 'L', 'GB4'), None)
    S('GB4', T(0, 'L', 'GB6'), None)
    S('GB6', T(1, 'L', 'GB7'), T(1, 'L', 'GB6'))         # the cursor, one slot left
    S('GB7', T(0, 'R', 'GD1'), T(0, 'R', 'GR1'))         # 0: off V's start: done
    S('GD1', T(0, 'L', 'GD2'), T(1, 'R', 'GD1'))
    S('GD2', None, T(1, 'L', 'GD3'))
    S('GD3', None, T(0, 'L', 'GD4'))                     # V's hole on its last slot
    S('GD4', T(0, 'L', 'GD5'), T(1, 'L', 'GD4'))
    S('GD5', T(0, 'L', 'EI1'), None)
    # K/R -> (1, 1): keep R, write a1 and K's start, erase the rest of K
    S('EI1', T(0, 'L', 'EI2'), None)
    S('EI2', T(1, 'L', 'EI3'), T(1, 'L', 'EI3'))
    S('EI3', T(0, 'L', 'EI4'), None)
    S('EI4', T(0, 'L', 'EI5'), None)
    S('EI5', T(0, 'L', 'EI6'), T(0, 'L', 'EI6'))
    S('EI6', T(1, 'L', 'E1'), T(1, 'L', 'E1'))
    S('E1', T(0, 'L', 'E2'), T(0, 'L', 'E1'))
    S('E2', T(0, 'L', 'E3'), T(0, 'L', 'E1'))
    S('E3', T(0, 'R', 'Z'), T(0, 'L', 'E1'))
    S('Z', T(0, 'R', 'Z'), T(1, 'R', 'KA'))
    refs = {t[2] for v in ST.values() for t in v if t}
    assert not (refs - set(ST) - {halt_state}), refs - set(ST)
    assert variant or not (set(ST) - refs - {ORDER[0]}), set(ST) - refs
    lines = ["; Halts iff Carmichael's totient conjecture fails.",
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '',
             'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'carmichael.txt', 'w').write(out)
    print(len(ORDER), 'states')
