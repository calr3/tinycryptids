// Fast simulator. stdin: "nstates nsym start maxsteps head tapelen tape(01..)"
// then nstates*nsym lines "write dir next". Prints: status steps state head tape
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define N (1<<26)
static unsigned char tape[N];
int main(){
  int ns, nm, st; long long maxs; long head; int tl; int trace=-1; long long maxtr=0;
  if(scanf("%d %d %d %lld %ld %d",&ns,&nm,&st,&maxs,&head,&tl)!=6) return 1;
  char *buf = malloc(tl+2); if(tl>0) scanf("%s",buf); else buf[0]=0;
  long origin = N/2; for(int i=0;i<tl;i++) tape[origin+i]=buf[i]-'0';
  long pos = origin+head;
  int *W=malloc(sizeof(int)*ns*nm),*D=malloc(sizeof(int)*ns*nm),*X=malloc(sizeof(int)*ns*nm);
  for(int i=0;i<ns*nm;i++) scanf("%d %d %d",&W[i],&D[i],&X[i]);
  if(scanf("%d %lld",&trace,&maxtr)!=2){trace=-1;}
  long long steps=0, ntr=0; long lo=pos,hi=pos; int s=st; const char*status="limit";
  while(steps<maxs){
    int k=s*nm+tape[pos];
    if(X[k]==-2){status="undefined";break;}
    tape[pos]=W[k]; pos+= D[k]?1:-1; steps++;
    if(pos<1||pos>=N-1){status="overflow";break;}
    if(pos<lo)lo=pos; if(pos>hi)hi=pos;
    if(X[k]==-1){status="halt";break;}
    s=X[k];
    if(s==trace){ long a2=lo,b2=hi; while(a2<b2&&tape[a2]==0)a2++; while(b2>a2&&tape[b2]==0)b2--; printf("T "); for(long i=a2;i<=b2;i++)putchar('0'+tape[i]); putchar('\n'); if(++ntr>=maxtr){status="traced";break;} }
  }
  long a=lo<origin?lo:origin, b=hi>origin+tl?hi:origin+tl;
  while(a<b && tape[a]==0 && a<pos) a++;
  while(b>a && tape[b]==0 && b>pos) b--;
  printf("%s %lld %d %ld ",status,steps,s,pos-a);
  for(long i=a;i<=b;i++) putchar('0'+tape[i]);
  putchar('\n'); return 0;
}
