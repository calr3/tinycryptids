// Simulator for kary.py's machines that logs their register operations.
// stdin: "nstates nsym maxsteps maxevents", then nstates*nsym lines "write dir next" (next -1
// halt, -2 undefined), then nstates flags (2 = a program node, 1 = a register chain state).
// Each time a node enters a chain state (one register operation starts) prints "E state"
// (the chain state, which names the register and the operation).  At the end prints "status steps head" (head relative to the
// trimmed tape) and the trimmed tape on one line (symbols 0-9, then a, b, ...).
#include <stdio.h>
#include <stdlib.h>
#define N (1<<26)
static unsigned char tape[N];
int main(void){
  int ns, nm; long long maxs, maxe;
  if(scanf("%d %d %lld %lld",&ns,&nm,&maxs,&maxe)!=4) return 1;
  int *W=malloc(sizeof(int)*ns*nm),*D=malloc(sizeof(int)*ns*nm),*X=malloc(sizeof(int)*ns*nm),*F=malloc(sizeof(int)*ns);
  for(int i=0;i<ns*nm;i++) if(scanf("%d %d %d",&W[i],&D[i],&X[i])!=3) return 1;
  for(int i=0;i<ns;i++) if(scanf("%d",&F[i])!=1) return 1;
  long pos=N/2, lo=pos, hi=pos; int s=0; long long steps=0, ne=0; const char*status="limit";
  while(steps<maxs){
    int k=s*nm+tape[pos];
    if(X[k]==-2){status="undefined";break;}
    tape[pos]=W[k]; pos+= D[k]?1:-1; steps++;
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(X[k]==-1){status="halt";break;}
    if(F[s]==2&&F[X[k]]==1){ s=X[k]; printf("E %d\n",s); if(++ne>=maxe){status="events";break;} continue; }
    s=X[k];
    if(pos<=1||pos>=N-2){status="tapeout";break;}
  }
  while(lo<hi&&tape[lo]==0&&lo<pos)lo++; while(hi>lo&&tape[hi]==0&&hi>pos)hi--;
  printf("%s %lld %ld\n",status,steps,pos-lo);
  for(long i=lo;i<=hi;i++) putchar(tape[i]<10?'0'+tape[i]:'a'+tape[i]-10);
  putchar('\n');
  return 0;
}
