// Turing machine simulator that logs register operations of a tmbuilder machine.
// stdin: "nstates maxsteps maxevents", then nstates*2 lines "write dir next" (next -1 halt,
// -2 undefined), then nstates flags (1 = a register-operation state 3.R.op).
// Each time a flagged state reads 1 (the marker: phase 2, the operation is performed) prints
// "E state". At the end prints "status steps head" (head relative to the trimmed tape) and the
// trimmed tape on one line.
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
static unsigned char tape[N];
int main(void){
  int ns; long long maxs, maxe;
  if(scanf("%d %lld %lld",&ns,&maxs,&maxe)!=3) return 1;
  int *W=malloc(sizeof(int)*ns*2),*D=malloc(sizeof(int)*ns*2),*X=malloc(sizeof(int)*ns*2),*F=malloc(sizeof(int)*ns);
  for(int i=0;i<ns*2;i++) if(scanf("%d %d %d",&W[i],&D[i],&X[i])!=3) return 1;
  for(int i=0;i<ns;i++) if(scanf("%d",&F[i])!=1) return 1;
  long pos=N/2, lo=pos, hi=pos; int s=0, on=0; long long steps=0, ne=0; const char*status="limit";
  while(steps<maxs){
    int k=s*2+tape[pos];
    if(X[k]==-2){status="undefined";break;}
    if(F[s]==2) on=1;
    if(on&&F[s]==1&&tape[pos]==1){ printf("E %d\n",s); if(++ne>=maxe){status="events";break;} }
    tape[pos]=W[k]; pos+= D[k]?1:-1; steps++;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(X[k]==-1){status="halt";break;}
    s=X[k];
    if(pos<=1||pos>=N-2){status="tapeout";break;}
  }
  while(lo<hi&&tape[lo]==0)lo++; while(hi>lo&&tape[hi]==0)hi--;
  printf("%s %lld %ld\n",status,steps,pos-lo);
  for(long i=lo;i<=hi;i++) putchar('0'+tape[i]); putchar('\n');
  return 0;
}
