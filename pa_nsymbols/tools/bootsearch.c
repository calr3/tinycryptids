// Search small machines (TNF) that, from a blank tape, reach an undefined transition which we
// define as the exit (write w, move d, then dispatch's scan) such that the tape is
//   [anything] 0 1^G 0^inf   (G >= gmin), head after the exit move on the run or the blank
// just left of it.  Report machines by number of defined transitions (incl. the exit).
// usage: bootsearch STATES SYMBOLS GMIN MAXINSTR [MAXSTEPS]
// prints "<instructions> instr G=<ones> steps=<steps>: <table>" (standard format, X = the exit)
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TL 4096
#define MAXS 6
#define MAXY 4
int NS, NY, GMIN, MAXSTEPS, BEST;
int W[MAXS][MAXY], Dd[MAXS][MAXY], X[MAXS][MAXY], DEF[MAXS][MAXY];
long long found = 0;
static unsigned char tape[TL];
int check_exit(int pos, int w, int d, int lo, int hi, int *G){
  unsigned char save = tape[pos]; tape[pos] = w; int h = pos + (d ? 1 : -1);
  if(h < lo) lo = h; if(h > hi) hi = h;
  // find the rightmost nonzero
  int r = hi; while(r >= lo && tape[r] == 0) r--;
  int ok = 0;
  if(r >= lo && tape[r] == 1){
    int l = r; while(l >= lo && tape[l] == 1) l--;
    // tape[l] must be 0 (blank left of run)
    if(l < lo || tape[l] == 0){
      int g = r - l;
      if(g >= GMIN && h >= l && h <= r){ ok = 1; *G = g; }
    }
  }
  tape[pos] = save;
  return ok;
}
void report(int ndef, int w, int d, int st, int sy, int G, int steps){
  printf("%d instr G=%d steps=%d: ", ndef, G, steps);
  for(int s=0;s<NS;s++){ for(int y=0;y<NY;y++){ if(s==st&&y==sy) printf("%d%cX", w, d?'R':'L'); else if(DEF[s][y]) printf("%d%c%c", W[s][y], Dd[s][y]?'R':'L', 'A'+X[s][y]); else printf("---"); } printf("_"); }
  printf("\n"); fflush(stdout); found++;
}
// run from scratch with current partial machine; returns: -1 loop/limit, else the undefined (s,y) hit
void search(int ndef, int maxstate_used){
  // simulate
  memset(tape, 0, TL); int pos = TL/2, lo = pos, hi = pos, s = 0;
  for(int step = 0; step < MAXSTEPS; step++){
    int y = tape[pos];
    if(!DEF[s][y]){
      // try exits
      int G;
      for(int w=0; w<NY; w++) for(int d=0; d<2; d++)
        if(check_exit(pos, w, d, lo, hi, &G) && ndef + 1 <= BEST) report(ndef+1, w, d, s, y, G, step);
      // or define a transition and recurse
      if(ndef + 2 > BEST) return;      // need at least one more plus the exit
      for(int w=0; w<NY; w++) for(int d=0; d<2; d++) for(int x=0; x<=maxstate_used+1 && x<NS; x++){
        DEF[s][y]=1; W[s][y]=w; Dd[s][y]=d; X[s][y]=x;
        search(ndef+1, x > maxstate_used ? x : maxstate_used);
        DEF[s][y]=0;
      }
      return;
    }
    tape[pos] = W[s][y]; pos += Dd[s][y] ? 1 : -1; s = X[s][y];
    if(pos < lo) lo = pos; if(pos > hi) hi = pos;
    if(pos <= 1 || pos >= TL-2) return;
  }
}
int main(int argc, char **argv){
  NS = atoi(argv[1]); NY = atoi(argv[2]); GMIN = atoi(argv[3]); BEST = atoi(argv[4]); MAXSTEPS = argc > 5 ? atoi(argv[5]) : 3000;
  // first transition: A0 -> (w, d, A or B); by symmetry d = R
  search(0, 0);
  fprintf(stderr, "found %lld\n", found);
}
