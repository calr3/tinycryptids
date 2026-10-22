"""Tuples placed directly on the tape (from the setup, state su0 on the anchor): the machine
halts iff x^E + y^E + d = z^E, where A is restored with d cells (a_init). Otherwise it reaches the
next enumeration (en1) with the tuple, M, A (d cells) and R = 1 restored."""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'tools'))  # tm.py
import build, tm
def tape_for(E, x, y, z, A=''):
    t = '000' + '00'.join('1'*(v+2) for v in (E, x, y, z)) + '001' + '00' + A + '01' + '000'
    return t[:4] + '0' + t[5:]          # the anchor (E hole) at cell 1
def check(E, x, y, z, A='', maxsteps=10**10):
    build.build(a_init=A)
    t = tape_for(E, x, y, z, A)
    r = tm.run(build.ORDER, build.ST, start='su0', tape=t, head=4, maxsteps=maxsteps, trace='en1', maxtrace=1)
    return r[0], r[1], (r[5][0] if r[5] else None), t
cases = [((2,3,4,5),'','halt'), ((2,4,3,5),'','halt'), ((1,2,3,5),'','halt'),
         ((2,3,3,5),'','traced'), ((3,1,2,3),'','traced'), ((2,5,12,13),'','halt'),
         ((3,6,8,9),'','traced'), ((3,6,8,9),'1','halt'), ((3,9,10,12),'','traced'),
         ((4,2,2,3),'','traced'), ((4,2,2,3),'1'*(81-32),'halt'), ((5,1,1,2),'','traced'),
         ((5,1,1,2),'1'*30,'halt'), ((2,7,24,25),'','halt'), ((1,1,1,1),'','traced'),
         ((3,1,1,1),'','traced'), ((1,1,1,2),'','halt'), ((4,1,1,1),'1','traced'),
         ((3,2,3,3),'','traced'), ((3,2,3,3),'1'*(27-8-27+27),'traced'), ((3,1,1,3),'1'*25,'halt'),
         ((1,1,1,3),'1','halt'), ((2,1,1,3),'1'*7,'halt'), ((3,1,1,1),'','traced')]
def main():
  ok = True
  for (tup, A, want) in cases:
    st, steps, tr, t = check(*tup, A=A)
    good = st == want
    if st == 'traced':
        good &= tr.strip('0') == t.strip('0')
    ok &= good
    print(tup, len(A), st, steps, 'OK' if good else 'FAIL')
  print('ALL OK' if ok else 'FAILURES')
if __name__ == '__main__': main()
