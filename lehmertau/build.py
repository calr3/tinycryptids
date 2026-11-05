"""Generator for a 2-symbol Turing machine that halts iff Lehmer's conjecture on
Ramanujan's tau function fails: iff tau(n) = 0 for some n >= 1.

The search.  With s_k = sigma_k (the divisor power sums),
    756 tau(n) = 65 s_11(n) + 691 s_5(n) - 174132 sum_{i=1}^{n-1} s_5(i) s_5(n-i)
(`TinyCryptids.tau756`).  For n = 2, 3, ... (tau(1) = 1) the machine builds
    P = sum_{i=1}^{n-1} sum_{d | i} sum_{e | n-i} 691 * 252 * d^5 e^5
    M = sum_{d | n} (691 d^5 + 65 d^11)
and halts iff P = M.

Every product is counted by one routine, the odometer (the "run"): a list of
blocks (factors) at the right end of the tape is counted through like the
digits of a mixed-radix counter, and every count appends one cell to the
leftmost block of the tape (P, or M once it exists).  The constants are
unary blocks K65, K252, K691 that take part in a run as extra digits when they
are "active" (hold a hole); the powers are copies of d and e.

Tape (blocks of 1s separated by '00'; a hole is a single '0' in a block):
    [M] 00 P 00 K65 00 K252 00 K691 00 X 00 Z 00 D 00 Rd 00 E 00 Re 00 S0 00 V..
  - P, M: value v as v + 1 cells.  M exists only in the L phase (below).
  - K65, K252, K691: f + 2 cells.  An active K is a digit: its hole moves
    through cells 1..f (at rest: cell 1).  R phase: K252 and K691 active;
    L1 runs: K691; L2 runs: K65.
  - X: a copy counter, 13 cells; hole-free at rest.
  - Z: one cell; the block left of D (tells D from E).
  - D, Rd and E, Re: two "frames" (the mod walk of legendre/): D has d + 2
    cells with a hole at cell c + 1 (c = residue), Rd has rd + 2 cells, d + rd
    = i; E, Re likewise with e + re = j = n - i.  In the L phase (i = n) the
    J frame is a dummy: E' = 4 cells, Re' = 1 cell.
  - S0: two cells, the start of the list.  V..: the list, factor f as f + 2
    cells, hole-free at rest; while counting, position p >= 1 is a hole at
    cell p + 1.
R phase: for i = 1 .. n-1, for d | i (d-loop on D, Rd), for e | n-i (e-loop on
E, Re): the list e x5, d x5 is counted with K252, K691: P += 174132 d^5 e^5.
L phase (i = n): for d | n: d x5 with K691 (M += 691 d^5), then d x11 with K65
(M += 65 d^11).
"""
import sys
ST = {}          # name -> [t0, t1]
EXP = (11, 5)    # (a, b): M += 65 d^a, 691 d^b; P += 174132 d^b e^b
ORDER = []
def S(name, t0, t1):
    assert name not in ST, name
    ST[name] = [t0, t1]; ORDER.append(name)
def T(w, d, n): return (w, d, n)

def parser_right(p, found):
    """right to the next hole (single 0); lands on hole+1 (a 1), does `found`"""
    S(p+'1', T(0,'R',p+'2'), T(1,'R',p+'1'))
    S(p+'2', T(0,'R',p+'1'), found)
def parser_left(p, found):
    """left to the next hole; lands on hole-1 (a 1), does `found`"""
    S(p+'1', T(0,'L',p+'2'), T(1,'L',p+'1'))
    S(p+'2', T(0,'L',p+'1'), found)
def far_right(p, found):
    """right to the first run of three 0s; `found` on its third 0"""
    S(p+'1', T(0,'R',p+'2'), T(1,'R',p+'1'))
    S(p+'2', T(0,'R',p+'3'), T(1,'R',p+'1'))
    S(p+'3', found, T(1,'R',p+'1'))
def far_left(p, found):
    S(p+'1', T(0,'L',p+'2'), T(1,'L',p+'1'))
    S(p+'2', T(0,'L',p+'3'), T(1,'L',p+'1'))
    S(p+'3', found, T(1,'L',p+'1'))
def cross_right(p, nxt):
    """from inside a block (holes allowed): to the next block's cell 0"""
    S(p+'1', T(0,'R',p+'2'), T(1,'R',p+'1'))
    S(p+'2', T(0,'R',nxt), T(1,'R',p+'1'))
def cross_left(p, nxt):
    """from inside a block: to the previous block's last cell"""
    S(p+'1', T(0,'L',p+'2'), T(1,'L',p+'1'))
    S(p+'2', T(0,'L',nxt), T(1,'L',p+'1'))

def frames():
    # mod walk (legendre/): head on X's hole; advance it cyclically, then
    # the R cursor; when R's cursor runs out, test the X hole
    S('wa1', T(1,'R','wa2'), None)
    S('wa2', None, T(1,'R','wa3'))
    S('wa3', T(0,'L','waw1'), T(1,'L','wa4'))
    S('wa4', None, T(0,'R','PRw1'))
    S('waw1', T(0,'R','waw2'), T(1,'L','waw1'))
    S('waw2', None, T(1,'R','waw3'))
    S('waw3', None, T(0,'R','PRw1'))
    parser_right('PRw', T(1,'L','wr1'))
    S('wr1', T(1,'R','wr2'), None)
    S('wr2', None, T(1,'R','wr3'))
    S('wr3', T(0,'L','PKw1'), T(1,'L','wr4'))
    S('wr4', None, T(0,'L','PMw1'))
    parser_left('PMw', T(1,'R','wa1'))
    parser_left('PKw', T(1,'L','k1'))
    # k1 at X's cell -1 (0): divisor; else reset the hole to cell 1, shift
    S('k1', T(0,'L','fz1'), T(1,'R','k2'))
    S('k2', None, T(1,'R','k3'))
    S('k3', T(1,'L','rs1'), None)
    S('rs1', T(0,'R','rs2'), T(1,'L','rs1'))
    S('rs2', None, T(1,'R','rs3'))
    S('rs3', None, T(0,'R','sh1'))
    # shift x += 1, r -= 1 (from X's cell 2, hole at cell 1)
    S('sh1', T(1,'R','sh2'), T(1,'R','sh1'))
    S('sh2', T(0,'R','sh3'), None)
    S('sh3', None, T(0,'R','sh4'))
    S('sh4', None, T(1,'R','sh5'))
    S('sh5', None, T(1,'R','sh6'))
    S('sh6', T(0,'L','PDz1'), T(1,'L','sh7'))     # 0: r = 0 now: x divides
    S('sh7', None, T(0,'L','PMw1'))
    parser_left('PDz', T(1,'L','k1'))
    # resume after a divisor (from X's cell 2, hole at cell 1): r = 0 ends
    # the loop, else shift
    S('rsm', T(0,'R','rc1'), T(1,'R','rsm'))
    S('rc1', T(0,'R','rc2'), None)
    S('rc2', None, T(1,'R','rc3'))
    S('rc3', None, T(1,'R','rc4'))
    S('rc4', T(0,'L','F2a'), T(1,'L','PSx1'))
    parser_left('PSx', T(1,'R','rc6'))
    S('rc6', T(0,'R','sh1'), None)
    # loop end: unshift X(x) R(0) -> X(1) R(x-1), from X's last cell
    S('F2a', None, T(1,'L','F2b'))
    S('F2b', None, T(1,'L','F2c'))
    S('F2c', T(0,'L','F2d'), None)
    S('F2d', T(0,'L','U1'), None)
    S('U1', None, T(1,'L','U2'))
    S('U2', T(1,'L','Ux'), T(1,'R','U3'))         # 0: the hole: x = 1 (fill it)
    S('U3', None, T(0,'R','U4'))
    S('U4', T(0,'R','U5'), None)
    S('U5', T(1,'L','U6'), None)
    S('U6', T(0,'L','U7'), None)
    S('U7', T(0,'L','U1'), None)
    S('Ux', None, T(1,'L','Uy'))
    S('Uy', T(0,'L','Uz'), None)
    S('Uz', T(0,'L','Uw'), None)
    S('Uw', None, T(1,'L','Uv'))
    S('Uv', T(0,'R','UD1'), T(1,'L','UE1'))       # 0: left of X is Z: X = D
    # divisor found: which frame?
    S('fz1', T(0,'L','fz2'), None)
    S('fz2', None, T(1,'L','fz3'))
    S('fz3', T(0,'R','DD1'), T(1,'L','VE1'))      # 0: Z: D divides i

def divisors():
    # D divides i: to E; |E| = 3 (R phase) starts the e-loop at e = 1,
    # |E'| = 4 (L phase) copies D five times
    cross_right('DD', 'DE1')
    cross_right('DE', 'DF1')
    cross_right('DF', 'cE0')
    S('cE0', None, T(1,'R','cE1'))
    S('cE1', None, T(1,'R','cE2'))
    S('cE2', None, T(1,'R','cE3'))
    S('cE3', T(0,'L','rE2'), T(1,'L','LE1'))
    S('rE2', None, T(1,'L','rE1'))
    S('rE1', None, T(0,'L','rE0'))
    S('rE0', None, T(1,'L','k1'))
    cross_left('LE', 'LF1')
    cross_left('LF', 'LG1')
    cross_left('LG', 'LH1')
    cross_left('LH', 'X50')
    # E divides j: fill D's hole on the way to X, copy E five times
    cross_left('VE', 'VF1')
    S('VF1', T(0,'L','VF2'), T(1,'L','VF1'))
    S('VF2', T(0,'L','VG1'), T(1,'R','VF3'))
    S('VF3', T(1,'L','VF1'), None)
    cross_left('VG', 'X50')
    # X hole at cell 7: five copies
    for k in range(EXP[1]):
        S(f'X5{k}', None, T(1,'L',f'X5{k+1}'))
    S(f'X5{EXP[1]}', None, T(0,'R','FS1'))

def copy():
    # copy the source block (cursor at cell 1) to a new last block; the X
    # counter counts the copies
    parser_right('FS', T(1,'R','GA1'))
    far_right('GA', T(1,'R','GA4'))
    S('GA4', T(1,'R','GA5'), None)
    S('GA5', T(1,'L','BK1'), None)
    parser_left('BK', T(1,'R','AV1'))
    S('AV1', T(0,'R','AV2'), None)
    S('AV2', None, T(1,'R','AV3'))
    S('AV3', T(0,'L','CD1'), T(1,'L','AV4'))      # 0: cursor was on the last cell
    S('AV4', None, T(0,'L','AV5'))
    S('AV5', T(1,'R','GB1'), None)
    far_right('GB', T(0,'L','GB4'))
    S('GB4', T(0,'L','GB5'), None)
    S('GB5', T(1,'L','BK1'), None)
    # one copy done: cursor back to cell 1, advance X
    S('CD1', None, T(1,'L','CD2'))
    S('CD2', T(1,'L','CD3'), None)
    S('CD3', T(0,'R','CD4'), T(1,'L','CD3'))
    S('CD4', None, T(1,'R','CD5'))
    S('CD5', None, T(0,'L','FX1'))
    parser_left('FX', T(1,'R','XA1'))
    S('XA1', T(0,'R','XA2'), None)
    S('XA2', None, T(1,'R','XA3'))
    S('XA3', T(0,'L','XW1'), T(1,'L','XA4'))      # 0: X wraps: all copies made
    S('XA4', None, T(0,'L','XA5'))
    S('XA5', T(1,'R','XA6'), None)
    S('XA6', T(0,'R','FS1'), None)
    S('XW1', None, T(1,'L','XW2'))
    S('XW2', T(1,'R','FD1'), None)
    parser_right('FD', T(1,'L','CR1'))
    S('CR1', T(1,'L','CR2'), None)
    S('CR2', None, T(1,'L','CR3'))
    S('CR3', T(0,'L','CR4'), None)
    S('CR4', T(0,'L','CR5'), None)
    S('CR5', None, T(1,'L','CR6'))
    S('CR6', T(0,'L','AL1'), T(1,'L','ED1'))      # 0: Z: D copied: run (count the first tuple)
    # E copied: cursor into D, five copies of D
    cross_left('ED', 'EF1')
    S('EF1', T(0,'R','EF2'), T(1,'L','EF1'))
    S('EF2', None, T(1,'R','EF3'))
    S('EF3', None, T(0,'L','EF4'))
    S('EF4', None, T(1,'L','EG1'))
    cross_left('EG', 'EH1')
    cross_left('EH', 'X50')

def run():
    # the odometer.  var digits (right of S0): hole-free = position 0, a hole
    # at cell p + 1 = position p.  K digits: a hole at cell c = position c - 1.
    far_right('RG', T(0,'L','RG4'))
    S('RG4', T(0,'L','RG5'), None)
    S('RG5', T(0,'L','CA'), None)
    S('CA', None, T(1,'L','CB'))
    S('CB', T(1,'L','VW'), T(1,'L','CC'))         # 0: last position: wrap
    S('CC', T(0,'L','CD'), T(1,'L','CC'))
    S('CD', T(0,'R','CG'), T(1,'R','CE'))         # 0: no hole: position 0
    S('CE', T(1,'R','CF'), None)
    S('CF', None, T(0,'L','AL1'))
    S('CG', T(0,'R','CH'), None)
    S('CH', None, T(1,'R','CI'))
    S('CI', None, T(1,'R','CJ'))
    S('CJ', T(0,'L','KF1'), T(1,'R','CK'))        # 0: two cells: S0: the K digits
    S('CK', T(0,'L','VW'), T(1,'L','CL'))         # 0: factor 1: wrap
    S('CL', None, T(0,'L','AL1'))
    S('VW', T(0,'L','VW2'), T(1,'L','VW'))
    S('VW2', T(0,'L','CA'), None)
    S('KF1', T(0,'L','KF2'), T(1,'L','KF1'))
    S('KF2', T(0,'L','KF3'), T(1,'R','KA1'))
    S('KF3', T(0,'R','PE1'), T(1,'L','KF1'))      # 0: the far left: the run is over
    S('KA1', T(0,'R','KA2'), None)
    S('KA2', None, T(1,'R','KA3'))
    S('KA3', T(0,'L','KW1'), T(1,'L','KA4'))
    S('KA4', None, T(0,'L','KA5'))
    S('KA5', T(1,'L','AL1'), None)
    S('KW1', None, T(1,'L','KW2'))
    S('KW2', T(1,'L','KW3'), None)
    S('KW3', T(0,'R','KW4'), T(1,'L','KW3'))
    S('KW4', None, T(1,'R','KW5'))
    S('KW5', None, T(0,'L','KF1'))
    # one count: a cell at the far left
    far_left('AL', T(0,'R','AA1'))
    S('AA1', T(0,'R','AA2'), None)
    S('AA2', T(1,'R','RG1'), None)

def postrun():
    # erase the list back to S0; R phase: E's hole, resume E; L phase: D's
    # hole, then switch K65 and K691 (L1 -> L2 copies D 11 times; L2 -> resume D)
    far_right('PE', T(0,'L','PE4'))
    S('PE4', T(0,'L','PE5'), None)
    S('PE5', T(0,'L','EL1'), None)
    S('EL1', None, T(1,'L','EL2'))
    S('EL2', None, T(1,'L','EL3'))
    S('EL3', T(0,'L','PD1'), T(1,'R','EL4'))      # 0: two cells: S0
    S('EL4', None, T(1,'R','EL5'))
    S('EL5', None, T(0,'L','EL6'))
    S('EL6', T(0,'L','EL7'), T(0,'L','EL6'))
    S('EL7', T(0,'L','EL1'), None)
    S('PD1', T(0,'L','PD2'), None)
    S('PD2', None, T(1,'L','PD3'))
    S('PD3', T(0,'L','PL1'), T(1,'L','PRr1'))     # 0: Re' is one cell: L phase
    cross_left('PRr', 'PRe')
    S('PRe', T(0,'R','PRf'), T(1,'L','PRe'))
    S('PRf', None, T(1,'R','PRg'))
    S('PRg', None, T(0,'R','rsm'))
    S('PL1', T(0,'L','PLa1'), None)
    cross_left('PLa', 'PLb1')
    cross_left('PLb', 'PLc')
    S('PLc', T(0,'R','PLd'), T(1,'L','PLc'))
    S('PLd', None, T(1,'R','PLe'))
    S('PLe', None, T(0,'L','FL1'))
    far_left('FL', T(0,'R','FL4'))
    S('FL4', T(0,'R','FL5'), None)
    S('FL5', T(0,'R','FM1'), None)
    cross_right('FM', 'FN1')
    cross_right('FN', 'FK1')
    S('FK1', None, T(1,'R','FK2'))
    S('FK2', T(1,'R','FC1'), T(0,'R','FC1'))      # flip K65
    cross_right('FC', 'FE1')
    cross_right('FE', 'FG1')
    S('FG1', None, T(1,'R','FG2'))
    S('FG2', T(1,'R','LA1'), T(0,'R','LD1'))      # flip K691; 0: it was on: L2 next
    cross_right('LA', 'LB1')
    S('LB1', None, T(1,'R','LB2'))
    S('LB2', None, T(0,'R','FS1'))                # X hole at cell 1: eleven copies
    parser_right('LD', T(1,'R','rsm'))

def loopends():
    # e-loop end: D's hole back, resume D
    cross_left('UE', 'UF1')
    S('UF1', T(0,'R','UF2'), T(1,'L','UF1'))
    S('UF2', None, T(1,'R','UF3'))
    S('UF3', None, T(0,'R','rsm'))
    # d-loop end: to E
    cross_right('UD', 'UDh')
    S('UDh', None, T(1,'R','UDi'))                # D's hole back at cell 1
    S('UDi', None, T(0,'R','UG1'))
    cross_right('UG', 'UH1')
    cross_right('UH', 'UK1')
    S('UK1', None, T(1,'R','UK2'))
    S('UK2', None, T(1,'R','UK3'))
    S('UK3', None, T(1,'R','UK4'))
    S('UK4', T(0,'R','IA1'), T(0,'R','EN1'))      # 0: |E| = 3: R phase: next i
    # next i: Re loses a cell, E moves right, Rd gains one; or, if Re had
    # two cells (i + 1 = n), the L phase: E' = 4, Re' = 1, M created, K252 off
    S('IA1', T(0,'R','IA2'), None)
    S('IA2', None, T(1,'R','IA3'))
    S('IA3', None, T(1,'R','IA4'))
    S('IA4', T(1,'R','LT1'), T(1,'L','IB1'))
    S('IB1', None, T(1,'L','IB2'))
    S('IB2', None, T(0,'L','IB3'))
    S('IB3', T(0,'L','IB4'), None)
    S('IB4', T(1,'L','IB5'), None)
    S('IB5', None, T(1,'L','IB6'))
    S('IB6', None, T(1,'L','IB7'))
    S('IB7', None, T(0,'L','IB8'))
    S('IB8', T(0,'L','IB9'), None)
    S('IB9', T(1,'L','PDz1'), None)
    S('LT1', T(0,'R','LT2'), None)
    S('LT2', None, T(0,'R','LT3'))
    S('LT3', None, T(1,'R','LT4'))
    S('LT4', T(1,'L','LT5'), None)
    S('LT5', None, T(1,'L','LT6'))
    S('LT6', T(0,'L','LT7'), None)
    S('LT7', T(0,'L','LT8'), None)
    S('LT8', None, T(1,'L','LT9'))
    S('LT9', None, T(0,'L','LT10'))
    S('LT10', None, T(0,'L','LT11'))
    S('LT11', T(1,'L','LT12'), None)
    S('LT12', T(1,'L','LT13'), None)
    S('LT13', None, T(1,'L','LT14'))
    S('LT14', None, T(1,'L','LT15'))
    S('LT15', None, T(0,'L','LT16'))
    S('LT16', T(0,'L','LT17'), None)
    S('LT17', T(1,'L','MK1'), None)
    far_left('MK', T(1,'R','MKa1'))
    cross_right('MKa', 'MKb1')
    cross_right('MKb', 'MKc1')
    cross_right('MKc', 'MK7')
    S('MK7', None, T(1,'R','MK8'))
    S('MK8', T(1,'R','H2a1'), None)
    parser_right('H2a', T(1,'R','H2b1'))
    parser_right('H2b', T(1,'L','HK1'))
    S('HK1', T(0,'L','HK2'), None)
    S('HK2', None, T(1,'L','k1'))
    # end of n: E' Re' -> E(1) Re(0), move Rd's cells to Re, one more cell
    S('EN1', T(0,'R','EN2'), None)
    S('EN2', T(1,'L','EN3'), None)
    S('EN3', T(0,'L','EN4'), None)
    S('EN4', T(0,'L','TN1'), None)
    cross_left('TN', 'TL1')
    S('TL1', None, T(1,'L','TL2'))
    S('TL2', None, T(1,'L','TL3'))
    S('TL3', T(0,'L','CMa1'), T(1,'R','TL4'))     # 0: Rd = 0: done: compare
    S('TL4', None, T(1,'R','TL5'))
    S('TL5', None, T(0,'R','TL6'))
    S('TL6', T(0,'R','TL7'), None)
    S('TL7', T(1,'R','TL8'), None)
    S('TL8', None, T(1,'R','TL9'))
    S('TL9', None, T(1,'R','TL10'))
    S('TL10', None, T(0,'R','TL11'))
    S('TL11', T(0,'R','TL12'), None)
    S('TL12', T(1,'L','TM1'), None)
    cross_left('TM', 'TN1')
    # compare M and P (far left), one cell of each at a time
    far_left('CMa', T(0,'R','CMb'))
    S('CMb', T(0,'R','CMc'), None)
    S('CMc', T(0,'R','CM1'), None)
    S('CM1', None, T(1,'R','CM2'))
    S('CM2', T(0,'L','CQ1'), T(1,'L','CM3'))      # 0: M = 0
    S('CM3', None, T(0,'R','CM4'))
    S('CM4', T(0,'R','CM5'), T(1,'R','CM4'))
    S('CM5', T(0,'R','CM5'), T(1,'R','CM6'))
    S('CM6', T(0,'L','CB1'), T(1,'L','CM7'))      # 0: P = 0 < M
    S('CM7', None, T(0,'L','CM8'))
    S('CM8', T(0,'L','CM8'), T(1,'L','CM9'))
    S('CM9', T(0,'R','CM1'), T(1,'L','CM9'))
    S('CQ1', None, T(0,'R','CP1'))
    S('CP1', T(0,'R','CP1'), T(1,'R','CP2'))
    S('CP2', T(0,'R','halt'), T(1,'L','CA3'))     # 0: P = M: HALT
    S('CA3', None, T(0,'R','CA1'))
    S('CA1', None, T(1,'R','CA2'))
    S('CA2', T(0,'L','CX'), T(1,'L','CA3'))
    S('CB1', None, T(1,'L','CB2'))
    S('CB2', T(0,'L','CB2'), T(0,'L','CB3'))
    S('CB3', T(0,'R','CX'), T(0,'L','CB3'))
    S('CX', T(0,'R','CX'), T(1,'R','CY2'))
    S('CY2', T(0,'R','CY3'), None)
    S('CY3', T(0,'R','CK1'), None)
    cross_right('CK', 'CL1')
    S('CL1', None, T(1,'R','CL2'))
    S('CL2', None, T(0,'R','H2a1'))

def counter(v):
    """v in binary, most significant bit first, each bit b as the pair 1 b, then a 1"""
    return ''.join('1' + c for c in bin(v)[2:]) + '1'

def seed_tape(K):
    """written by the seed: the right part and the counters (K691's last)"""
    xv = EXP[0]
    right = [blk(xv), '1', blk(1, 1), blk(0), blk(1), blk(0), blk(0)]
    return '00'.join(right + [counter(k) for k in K])

def seed(K):
    pat = seed_tape(K)
    for i, ch in enumerate(pat):
        S(f'sd{i}', T(int(ch),'R', f'sd{i+1}' if i+1 < len(pat) else 'DN1'), None)
    # drain the last counter into a new block at the far left, one cell per
    # decrement; when it runs out, erase it; S0 left of it ends the seed
    far_left('DN', T(1,'L','DN4'))
    S('DN4', T(1,'R','DB1'), None)
    far_right('DB', T(0,'L','DB4'))
    S('DB4', T(0,'L','DB5'), None)
    S('DB5', T(0,'L','DB6'), None)
    S('DB6', None, T(1,'L','DC1'))
    S('DC1', T(1,'L','DC2'), T(0,'L','DA1'))      # bit 0: becomes 1, borrow
    S('DC2', None, T(1,'L','DC3'))
    S('DC3', T(0,'L','DC4'), T(0,'L','DA1'))
    S('DC4', T(0,'R','DU0'), T(1,'R','DC1'))      # 0: past the top bit: empty
    far_left('DA', T(0,'R','DA4'))
    S('DA4', T(0,'R','DA5'), None)
    S('DA5', T(1,'R','DB1'), None)
    S('DU0', T(0,'R','DU1'), None)
    S('DU1', T(0,'L','DU2'), T(0,'R','DU1'))
    S('DU2', T(0,'L','DU2'), T(1,'L','DU3'))
    S('DU3', T(0,'L','DU4'), T(1,'L','DU4'))
    S('DU4', T(0,'L','DP1'), T(1,'L','DN1'))      # 0: S0: all constants built
    far_left('DP', T(1,'R','DPa1'))               # P
    cross_right('DPa', 'DPb1')
    cross_right('DPb', 'DPc1')
    S('DPc1', None, T(1,'R','DPc2'))
    S('DPc2', None, T(0,'R','DPd1'))              # K252 active
    cross_right('DPd', 'DPe1')
    S('DPe1', None, T(1,'R','DPe2'))
    S('DPe2', None, T(0,'R','H2b1'))              # K691 active, then D's hole

def blk(v, hole=None, extra=2):
    s = ['1'] * (v + extra)
    if hole is not None: s[hole] = '0'
    return ''.join(s)

def start_tape(K=(65, 252, 691), n=2, P=0):
    xv = EXP[0]
    """the tape at the start of n (R phase, i = 1, d = 1): state k1 on D's cell -1"""
    k65, k252, k691 = K
    parts = [blk(P, extra=1), blk(k65), blk(k252, 1), blk(k691, 1), blk(xv), '1',
             blk(1, 1), blk(0), blk(1), blk(n - 2), blk(0)]
    tape = '00'.join(parts)
    head = sum(len(p) + 2 for p in parts[:6]) - 1     # cell -1 of D
    return tape, head

def build(variant=None, exp=(11, 5), K=(65, 252, 691)):
    global EXP
    EXP = exp
    ST.clear(); ORDER.clear()
    seed(K); frames(); divisors(); copy(); run(); postrun(); loopends()
    refs = {t[2] for v in ST.values() for t in v if t}
    missing = refs - set(ST) - {'halt'}
    assert not missing, missing
    unused = set(ST) - refs - {ORDER[0]}
    assert not unused, unused
    lines = ['; Halts iff tau(n) = 0 for some n >= 1 (Lehmer\'s conjecture fails).',
             f'; {len(ORDER)} states, 2 symbols. Generated by build.py.', '', 'blank_symbol: 0', '']
    for n in ORDER:
        lines.append(n)
        for r, t in enumerate(ST[n]):
            lines.append('    -' if t is None else f'    {r} {t[0]} {t[1]} {t[2]}')
    return '\n'.join(lines) + '\n'

if __name__ == '__main__':
    out = build()
    open(sys.argv[1] if len(sys.argv) > 1 else 'lehmertau.txt', 'w').write(out)
    print(len(ORDER), 'states')
