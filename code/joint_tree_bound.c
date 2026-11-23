// joint_tree_bound.c: lower bounds for the JOINT multiplicative complexity of several sums sharing operands.
// Method = the decision tree of Theorem 3.1 / Lemma 10.1 of the paper, for multi-sum "membership heaps";
// soundness of the search and of both pruning rules is Lemma 11.4 of the paper:
//   if MC(F) <= t there is a decision tree of depth <= t whose queries are affine forms of the inputs and
//   on each leaf flat every output of F is affine (tree mode); in particular through any chosen point p
//   there is a flat of codimension <= t on which F is affine (point mode).
// This program decides exhaustively whether such a tree (or flat through p) of depth (codim) <= B exists.
// "none" is therefore a proof (by exhaustion, modulo this code) that MC(F) >= B+1.
//
// usage: joint_tree_bound SPEC B [point|-] [verbose] [rootlo roothi]
//   SPEC: columns separated by '/', each a comma list of membership masks, e.g. "3,3,1,2/3,3,1,2" =
//         (x+y+z, x+y+w) mod 8 (two carry columns; the top column is linear and omitted).
//         optional ":k0,k1,.." = constants added to the sums.
//   outputs: for every sum s and i = 1..m the carry parity C^s_i = bit i of (sum of the columns < i of s).
//   point: hex input point (bit v = variable v in SPEC order) -> point mode; "-" -> tree mode.
//   rootlo roothi: only root queries L in [rootlo, roothi) (to split a run); tree mode only.
// With the rank test (default; env JPDT_NODIM=1 disables) the node is also refuted when the
// degree-filtration rank bound fails (see rank_refutes) -- needed for JOINT functions, where the plain
// tree bound is weak (the pair (maj(x,y,z), maj(x,y,w)) has a tree of depth 1 but MC 2).
// Search: a node (truth tables on k free variables, budget B) is solvable iff all tables are affine, or
// B > 0 and for some nonzero linear form L both restrictions {L=0}, {L=1} are solvable with budget B-1
// (point mode: only the side containing the point; forms are enumerated with increasing pivots so that
// every flat through the point is generated once).  Pruning (tree mode only, valid because a function
// with such a tree of depth B has degree <= B+1): any table of degree > B+1 refutes the node.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
typedef uint64_t u64;
#define MAXV 16
#define WORDS(k) ((k) <= 6 ? 1 : (1 << ((k) - 6)))
static u64 hw[MAXV + 2][1 << (MAXV - 6)];   // hw[D]: monomials of degree > D
static long nodes = 0;
static int pointmode = 0, verbose = 0;
static void anf(u64 *t, int k) {             // in-place Moebius transform
    static const u64 M[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0f0f0f0f0f0f0f0fULL,
                             0x00ff00ff00ff00ffULL, 0x0000ffff0000ffffULL, 0x00000000ffffffffULL};
    int w = WORDS(k);
    for (int i = 0; i < 6 && i < k; i++) for (int j = 0; j < w; j++) t[j] ^= (t[j] & M[i]) << (1 << i);
    for (int i = 6; i < k; i++) { int s = 1 << (i - 6); for (int j = 0; j < w; j++) if (j & s) t[j] ^= t[j ^ s]; }
}
static int deg_gt(const u64 *t, int k, int D) {
    u64 a[1 << (MAXV - 6)];
    int w = WORDS(k);
    memcpy(a, t, w * sizeof(u64));
    if (k < 6) a[0] &= (1ULL << (1 << k)) - 1;
    anf(a, k);
    if (k < 6) a[0] &= (1ULL << (1 << k)) - 1;
    if (D < 0) D = 0;
    for (int j = 0; j < w; j++) if (a[j] & hw[D][j]) return 1;
    return 0;
}
// restriction of t (k vars) to the hyperplane L(x) = c: eliminate the pivot variable p = top bit of L
static void restr(const u64 *t, int k, unsigned L, int c, u64 *o) {
    int p = 31 - __builtin_clz(L);
    unsigned rest = L ^ (1u << p), lowm = (1u << p) - 1;
    int n2 = 1 << (k - 1);
    memset(o, 0, WORDS(k - 1) * sizeof(u64));
    for (int y = 0; y < n2; y++) {
        unsigned low = y & lowm;
        unsigned b = c ^ (__builtin_popcount(low & rest) & 1);
        unsigned x = low | (b << p) | ((unsigned)(y >> p) << (p + 1));
        if ((t[x >> 6] >> (x & 63)) & 1) o[y >> 6] |= 1ULL << (y & 63);
    }
}
// Degree-filtration rank test (Lemma 11.4 (iii) of the paper).  If MC(F) <= B then span(outputs) lies in
// affine + span(g_1..g_B) with deg g_i <= i+1, so for every d >= 1
//      dim( span(outputs) modulo polynomials of degree <= d ) <= B - d + 1      (d = 1: nonlinear rank <= B).
// returns 1 iff the test REFUTES budget B.  usedim = 0 disables it (plain flat method tree bound).
static int usedim = 1;
static int rank_refutes(u64 **tt, int nout, int k, int B) {
    int w = WORDS(k);
    u64 *a = malloc(sizeof(u64) * w * nout), *r = malloc(sizeof(u64) * w * nout);
    for (int i = 0; i < nout; i++) {
        memcpy(a + i * w, tt[i], w * sizeof(u64));
        if (k < 6) a[i * w] &= (1ULL << (1 << k)) - 1;
        anf(a + i * w, k);
        if (k < 6) a[i * w] &= (1ULL << (1 << k)) - 1;
    }
    int bad = 0;
    for (int d = 1; d <= k && !bad; d++) {
        int rank = 0;
        for (int i = 0; i < nout; i++) {
            u64 *v = r + rank * w;
            for (int j = 0; j < w; j++) v[j] = a[i * w + j] & hw[d][j];
            for (int q = 0; q < rank; q++) {        // reduce by earlier rows (each has a recorded pivot)
                u64 *u = r + q * w; int pj = -1; u64 pb = 0;
                for (int j = 0; j < w; j++) if (u[j]) { pj = j; pb = u[j] & (~u[j] + 1); break; }
                if (v[pj] & pb) for (int j = 0; j < w; j++) v[j] ^= u[j];
            }
            int nz = 0; for (int j = 0; j < w; j++) if (v[j]) { nz = 1; break; }
            if (nz) rank++;
        }
        if (rank == 0) break;
        if (rank > B - d + 1) bad = 1;
    }
    free(a); free(r);
    return bad;
}
static unsigned rootlo = 1, roothi = 0;
static int solve(u64 **tt, int nout, int k, int B, int depth, int minp) {
    nodes++;
    int aff = 1;
    for (int i = 0; i < nout; i++) {
        if (!pointmode && deg_gt(tt[i], k, B + 1)) return 0;
        if (aff && deg_gt(tt[i], k, 1)) aff = 0;
    }
    if (aff) return 1;
    if (B == 0) return 0;
    if (usedim && rank_refutes(tt, nout, k, B)) return 0;
    int w2 = WORDS(k - 1);
    u64 *buf = malloc(sizeof(u64) * w2 * nout * 2);
    u64 **t0 = malloc(sizeof(u64 *) * nout), **t1 = malloc(sizeof(u64 *) * nout);
    for (int i = 0; i < nout; i++) { t0[i] = buf + w2 * i; t1[i] = buf + w2 * (nout + i); }
    int res = 0;
    unsigned lo = pointmode ? (1u << minp) : 1, hi = 1u << k;
    if (depth == 0 && roothi) { lo = rootlo; hi = roothi; }
    for (unsigned L = lo; L < hi && !res; L++) {
        int ok = 1;
        for (int i = nout - 1; i >= 0 && ok; i--) {
            restr(tt[i], k, L, 0, t0[i]);
            if (pointmode) continue;
            if (deg_gt(t0[i], k - 1, B)) { ok = 0; break; }
            restr(tt[i], k, L, 1, t1[i]);
            if (deg_gt(t1[i], k - 1, B)) { ok = 0; break; }
        }
        if (!ok) continue;
        if (verbose && depth < verbose) { for (int d = 0; d < depth; d++) printf("  "); printf("try L=%x (k=%d,B=%d)\n", L, k, B); fflush(stdout); }
        int p = 31 - __builtin_clz(L);
        if (solve(t0, nout, k - 1, B - 1, depth + 1, p) && (pointmode || solve(t1, nout, k - 1, B - 1, depth + 1, 0))) {
            res = 1;
            if (verbose) { for (int d = 0; d < depth; d++) printf("  "); printf("OK L=%x (k=%d,B=%d)\n", L, k, B); }
        }
    }
    free(buf); free(t0); free(t1);
    return res;
}
int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: joint_tree_bound SPEC B [point|-] [verbose] [rootlo roothi]\n"); return 2; }
    char spec[256]; strncpy(spec, argv[1], 255); spec[255] = 0;
    int B = atoi(argv[2]);
    unsigned point = 0;
    if (argc > 3 && argv[3][0] != '-') { pointmode = 1; point = (unsigned)strtoul(argv[3], 0, 16); }
    if (argc > 4) verbose = atoi(argv[4]);
    if (argc > 6) { rootlo = (unsigned)strtoul(argv[5], 0, 0); roothi = (unsigned)strtoul(argv[6], 0, 0); }
    unsigned kap[8] = {0};
    char *colon = strchr(spec, ':');
    if (colon) { *colon = 0; int s = 0; for (char *q = strtok(colon + 1, ","); q; q = strtok(0, ",")) kap[s++] = (unsigned)strtoul(q, 0, 0); }
    int col[MAXV], mask[MAXV], k = 0, m = 1, nsum = 0;
    for (char *q = spec; *q;) {
        if (*q == '/') { m++; q++; continue; }
        if (*q == ',') { q++; continue; }
        int v = (int)strtol(q, &q, 10);
        if (k >= MAXV) { fprintf(stderr, "too many variables\n"); return 2; }
        col[k] = m - 1; mask[k] = v; k++;
        for (int s = 0; s < 8; s++) if (((v >> s) & 1) && s + 1 > nsum) nsum = s + 1;
    }
    for (int D = 0; D <= MAXV + 1; D++)
        for (int i = 0; i < (1 << MAXV); i++)
            if (__builtin_popcount(i) > D) hw[D][i >> 6] |= 1ULL << (i & 63);
    int w = WORDS(k), nout = nsum * m;
    u64 **tts = malloc(sizeof(u64 *) * nout);
    for (int i = 0; i < nout; i++) tts[i] = calloc(w, sizeof(u64));
    for (unsigned x0 = 0; x0 < (1u << k); x0++) {
        unsigned x = x0 ^ point;                 // tables are indexed by x ^ point (point -> origin)
        for (int s = 0; s < nsum; s++)
            for (int i = 1; i <= m; i++) {
                unsigned T = kap[s] & ((1u << i) - 1);
                for (int v = 0; v < k; v++)
                    if (col[v] < i && ((mask[v] >> s) & 1) && ((x >> v) & 1)) T += 1u << col[v];
                if ((T >> i) & 1) tts[s * m + (i - 1)][x0 >> 6] |= 1ULL << (x0 & 63);
            }
    }
    if (getenv("JPDT_NODIM")) usedim = 0;
    int r = solve(tts, nout, k, B, 0, 0);
    printf("spec=%s (%d vars, %d sums, %d carry columns) B=%d point=%s root=[%u,%u) : %s  (nodes %ld)\n", argv[1], k, nsum, m, B,
           pointmode ? argv[3] : "-", rootlo, roothi, r ? "EXISTS" : "none", nodes);
    return 0;
}
