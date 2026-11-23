// affine_tree.c: affine-leaf parity decision tree (PDT) depth for carry functions of K-operand addition.
// Decides: is there a PDT of depth <= B (queries = affine forms) such that every selected output is
// affine on every leaf?  MC(F) >= min such depth (decision tree of Theorem 3.1 of the paper; Lemma 11.4).
// usage: affine_tree COUNTS B mode [verbose [kappa [point]]]
//   COUNTS = string of digits, one per carry-generating column (low first): number of free bits in the column,
//   e.g. 333 = three operands, m = 3 columns (ADD3 mod 2^4); 2322 = a + b + 2c core.
//   mode 0 = all carries C_1..C_m, mode 1 = top carry C_m only (= top sum bit), mode 2 = C_1..C_{m-1} and
//   all bits of the carry value (sum without truncation); mode 3 = C_1..C_{m-1} affine and the carry value
//   K_m constant (point mode only).  kappa = added constant.
//   point (hex, optional, "-" = none): only the leaf containing this input point is required to be affine
//   (min codim of a flat through the point: branch c = L(point) only).
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#define MAXK 15
#define W(k) ((k) <= 6 ? 1 : (1 << ((k) - 6)))
typedef uint64_t u64;
static u64 hwmask[MAXK + 2][1 << (MAXK - 6)]; // hwmask[D]: bit i set iff popcount(i) > D
static long nodes = 0;
static void mobius(u64 *t, int k) {
    int w = W(k);
    static const u64 M[6] = {0x5555555555555555ULL, 0x3333333333333333ULL, 0x0f0f0f0f0f0f0f0fULL,
                             0x00ff00ff00ff00ffULL, 0x0000ffff0000ffffULL, 0x00000000ffffffffULL};
    for (int i = 0; i < 6 && i < k; i++)
        for (int j = 0; j < w; j++) t[j] ^= (t[j] & M[i]) << (1 << i);
    for (int i = 6; i < k; i++) {
        int s = 1 << (i - 6);
        for (int j = 0; j < w; j++)
            if (j & s) t[j] ^= t[j ^ s];
    }
}
static int deg_gt(const u64 *t, int k, int D) { // degree > D ?
    u64 a[1 << (MAXK - 6)];
    int w = W(k);
    memcpy(a, t, w * sizeof(u64));
    if (k < 6) a[0] &= (1ULL << (1 << k)) - 1;
    mobius(a, k);
    if (k < 6) a[0] &= (1ULL << (1 << k)) - 1;
    if (D < 0) D = 0;
    for (int j = 0; j < w; j++)
        if (a[j] & hwmask[D][j]) return 1;
    return 0;
}
static void restrict_tt(const u64 *t, int k, unsigned L, int c, u64 *o) {
    int p = 31 - __builtin_clz(L);
    unsigned rest = L ^ (1u << p), lowm = (1u << p) - 1;
    int n2 = 1 << (k - 1);
    memset(o, 0, W(k - 1) * sizeof(u64));
    for (int y = 0; y < n2; y++) {
        unsigned low = y & lowm;
        unsigned b = c ^ (__builtin_popcount(low & rest) & 1);
        unsigned x = low | (b << p) | ((y >> p) << (p + 1));
        if ((t[x >> 6] >> (x & 63)) & 1) o[y >> 6] |= 1ULL << (y & 63);
    }
}
static int verbose = 0, pointmode = 0, constfrom = -1;
// returns 1 iff PDT of depth <= B exists
static int solve(u64 **tt, int nout, int k, int B, int depth, int minp) {
    nodes++;
    int aff = 1;
    for (int i = 0; i < nout; i++) {
        // degree pruning is valid only when BOTH branches are required (some branch keeps degree >= d-1);
        // in point mode a single hyperplane can lower the degree arbitrarily, so no pruning there.
        if (!pointmode && deg_gt(tt[i], k, B + 1)) return 0;
        if (aff && deg_gt(tt[i], k, (constfrom >= 0 && i >= constfrom) ? 0 : 1)) aff = 0;
    }
    if (aff) return 1;
    if (B == 0) return 0;
    int w2 = W(k - 1);
    u64 *buf = malloc(sizeof(u64) * w2 * nout * 2);
    u64 **t0 = malloc(sizeof(u64 *) * nout), **t1 = malloc(sizeof(u64 *) * nout);
    for (int i = 0; i < nout; i++) { t0[i] = buf + w2 * i; t1[i] = buf + w2 * (nout + i); }
    int res = 0;
    // point mode: pivots (top bits) strictly increasing in original coordinates => each flat through the
    // point is generated exactly once (reduced echelon form of its constraint system)
    for (unsigned L = (pointmode ? (1u << minp) : 1); L < (1u << k) && !res; L++) {
        int ok = 1;
        for (int i = nout - 1; i >= 0 && ok; i--) {
            restrict_tt(tt[i], k, L, 0, t0[i]);
            if (pointmode) continue;
            if (deg_gt(t0[i], k - 1, B)) { ok = 0; break; }
            restrict_tt(tt[i], k, L, 1, t1[i]);
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
    const char *cs = argv[1];
    int m = strlen(cs), B = atoi(argv[2]), mode = atoi(argv[3]);
    if (argc > 4) verbose = atoi(argv[4]);
    unsigned kappa = argc > 5 ? (unsigned)strtoul(argv[5], 0, 0) : 0;
    unsigned point = 0;
    if (argc > 6 && argv[6][0] != '-') { pointmode = 1; point = (unsigned)strtoul(argv[6], 0, 16); }
    int cnt[32], off[32], k = 0;
    for (int j = 0; j < m; j++) { cnt[j] = cs[j] - '0'; off[j] = k; k += cnt[j]; }
    if (k > MAXK) { fprintf(stderr, "too big\n"); return 2; }
    for (int D = 0; D <= MAXK + 1; D++)
        for (int i = 0; i < (1 << MAXK); i++)
            if (__builtin_popcount(i) > D) hwmask[D][i >> 6] |= 1ULL << (i & 63);
    int w = W(k);
    u64 *tts[64]; int nout = 0;
    int nbits = m + 5;
    u64 **all = malloc(sizeof(u64 *) * (m + 1) * nbits);
    for (int i = 1; i <= m; i++)
        for (int b = 0; b < nbits; b++) { all[i * nbits + b - nbits] = calloc(w, sizeof(u64)); }
    for (unsigned x0 = 0; x0 < (1u << k); x0++) {
        unsigned x = x0 ^ point;   // table indexed by x0 = x ^ point (point -> origin)
        unsigned T = 0;
        for (int i = 1; i <= m; i++) {
            int wj = __builtin_popcount((x >> off[i - 1]) & ((1u << cnt[i - 1]) - 1));
            T += (unsigned)wj << (i - 1);
            unsigned Tk = T + (kappa & ((1u << i) - 1));
            if (i == m) Tk = T + kappa;
            for (int b = 0; b < nbits; b++)
                if ((Tk >> b) & 1) all[(i - 1) * nbits + b][x0 >> 6] |= 1ULL << (x0 & 63);
        }
    }
    if (mode == 0) for (int i = 1; i <= m; i++) tts[nout++] = all[(i - 1) * nbits + i];
    else if (mode == 1) tts[nout++] = all[(m - 1) * nbits + m];
    else { for (int i = 1; i < m; i++) tts[nout++] = all[(i - 1) * nbits + i];
           if (mode == 3) constfrom = nout;   // mode 3: carry value K_m must be CONSTANT (point mode only)
           for (int b = m; b < nbits; b++) tts[nout++] = all[(m - 1) * nbits + b]; }
    if (mode == 3 && !pointmode) { fprintf(stderr, "mode 3 needs point mode\n"); return 2; }
    int r = solve(tts, nout, k, B, 0, 0);
    printf("counts=%s (n=%d, %d vars) kappa=%u mode=%d point=%s B=%d : %s  (nodes %ld)\n", cs, m + 1, k, kappa, mode,
           pointmode ? argv[6] : "-", B, r ? "EXISTS" : "none", nodes);
    return 0;
}
