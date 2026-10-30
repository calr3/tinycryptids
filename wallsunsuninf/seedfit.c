// seedfit.py's search: DFS over fillings of the undefined slots met on a blank-tape run, from every
// start state; success = an exact round start (build.canon(m), state START, head on D's cell 0).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#define TL 4096
#define OFF 2048
int n, START, nx[256][2], wr[256][2], mv[256][2], MAXD, LIMIT;
long nsol = 0, nruns = 0;
int startq;
static int is_canon(unsigned char *T, int lo, int hi, int head) {
  // find extremes of ones
  int a = -1, b = -1;
  for (int i = lo; i <= hi; i++) if (T[i]) { if (a < 0) a = i; b = i; }
  if (a < 0) return 0;
  int len = b - a + 1, m = (len - 9) / 3;
  if (m < 1 || 3 * m + 9 != len) return 0;
  // 1^(m+1) 00 1^(m+2) 00 1 0 1^m
  int p = a;
  for (int i = 0; i < m + 1; i++) if (!T[p++]) return 0;
  if (T[p++] || T[p++]) return 0;
  for (int i = 0; i < m + 2; i++) if (!T[p++]) return 0;
  if (T[p++] || T[p++]) return 0;
  int d0 = p;
  if (!T[p++] || T[p++]) return 0;
  for (int i = 0; i < m; i++) if (!T[p++]) return 0;
  if (head != d0) return 0;
  return m;
}
static void go(int q, unsigned char *T0, int lo, int hi, int head, int steps, int depth) {
  unsigned char T[TL]; memcpy(T, T0, TL);
  nruns++;
  while (steps < LIMIT) {
    if (q == START) { int m = is_canon(T, lo, hi, head); if (m) {
      nsol++; printf("FOUND start %d m %d steps %d slots:", startq, m, steps);
      for (int i = 0; i < n; i++) for (int b = 0; b < 2; b++) if (nx[i][b] <= -10) {}
      extern int asg[64][5], nasg;
      for (int i = 0; i < nasg; i++) printf(" (%d,%d)->%d%c%d", asg[i][0], asg[i][1], asg[i][2], asg[i][3] ? 'R' : 'L', asg[i][4]);
      printf("\n"); fflush(stdout); return; } }
    int b = T[head];
    if (nx[q][b] == -1) {
      if (depth >= MAXD) return;
      extern int asg[64][5], nasg;
      for (int w = 0; w < 2; w++) for (int d = 0; d < 2; d++) for (int t = 0; t < n; t++) {
        nx[q][b] = t; wr[q][b] = w; mv[q][b] = d;
        asg[nasg][0] = q; asg[nasg][1] = b; asg[nasg][2] = w; asg[nasg][3] = d; asg[nasg][4] = t; nasg++;
        go(q, T, lo, hi, head, steps, depth + 1);
        nasg--;
      }
      nx[q][b] = -1; return;
    }
    if (nx[q][b] == -2) return;  // halt
    T[head] = wr[q][b]; head += mv[q][b] ? 1 : -1; q = nx[q][b]; steps++;
    if (head < 2 || head >= TL - 2) return;
    if (head < lo) lo = head; if (head > hi) hi = head;
  }
}
int asg[64][5], nasg = 0;
int main(int argc, char **argv) {
  MAXD = atoi(argv[1]); LIMIT = atoi(argv[2]);
  int s0 = argc > 3 ? atoi(argv[3]) : 0, s1 = argc > 4 ? atoi(argv[4]) : 1 << 30;  // start states [s0, s1)
  scanf("%d %d", &n, &START);
  for (int i = 0; i < n; i++) for (int b = 0; b < 2; b++) scanf("%d %d %d", &nx[i][b], &wr[i][b], &mv[i][b]);
  unsigned char T[TL]; memset(T, 0, TL);
  for (startq = s0; startq < n && startq < s1; startq++) { go(startq, T, OFF, OFF, OFF, 0, 0); fprintf(stderr, "start %d done, runs %ld sols %ld\n", startq, nruns, nsol); }
  printf("solutions %ld runs %ld\n", nsol, nruns);
}
