/* mc_addition_walsh_check.c -- exact numeric check of the 2-adic Walsh bound for bit heaps with a constant.
 *
 * A heap has columns j = 0..m-1 holding k_j free input bits of weight 2^j; N = sum k_j <= 24.  K is an
 * integer constant (reduced mod 2^m).  T(x) = sum_j 2^j * popcount(column j of x).  The nonlinear outputs
 * are B_i = bit_i(T(x) + K), i = 1..m (bit 0 is affine).
 *
 * For every non-zero output combination u in F_2^m (or only the top bit with -t) the program computes the
 * full Walsh spectrum of g_u = XOR_{i: u_i = 1} B_i with an in-place fast Walsh-Hadamard transform in exact
 * 64-bit integer arithmetic, and reports
 *     spectral(u) = N - min { v_2(W_{g_u}(l)) : W_{g_u}(l) != 0 },
 * which by the Walsh divisibility bound (Theorem 3.1 of the paper; Chistopolskaya-Podolskii, Lemma 5 and Theorem 6) is a
 * lower bound on the number of AND gates of any XAG computing the outputs.  It also computes the upper bound
 * U(kappa, K) of the full-adder network with the constant consumed last (Lemma 4.1 of the paper):
 *     c_0 = 0,  v_j = k_j + c_j,  U = sum_j floor(v_j / 2),  c_{j+1} = floor((v_j + K_j) / 2).
 * MATCH means max_u spectral(u) == U, i.e. the multiplicative complexity is exactly U for this instance.
 *
 * usage:
 *   mc_addition_walsh_check add k n [K] [-t]     x_1 + ... + x_k + K mod 2^n  (profile k^(n-1); the top
 *                                                 column only adds a linear term and is omitted)
 *   mc_addition_walsh_check heap k0,k1,..,k_{m-1} [K] [-t]
 *   -t : only u = top bit (Theorem 6.1 says this suffices for additions)
 * Output: one line per instance, "MATCH" or "DIFF".  Exit status 0 iff MATCH.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

static int prof[32], m, N;

static int U_of(long long K) {
    int c = 0, U = 0;
    for (int j = 0; j < m; j++) {
        int v = prof[j] + c, Kj = (int)((K >> j) & 1);
        U += v / 2;
        c = (v + Kj) / 2;
    }
    return U;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: see source header\n"); return 2; }
    int toponly = 0, argi = 1, k = 0, n = 0;
    for (int i = 1; i < argc; i++) if (!strcmp(argv[i], "-t")) toponly = 1;
    long long K = 0;
    if (!strcmp(argv[argi], "add")) {
        k = atoi(argv[argi + 1]); n = atoi(argv[argi + 2]); m = n - 1;
        for (int j = 0; j < m; j++) prof[j] = k;
        if (argc > argi + 3 && strcmp(argv[argi + 3], "-t")) K = atoll(argv[argi + 3]);
    } else if (!strcmp(argv[argi], "heap")) {
        char *s = strdup(argv[argi + 1]), *tok = strtok(s, ",");
        m = 0;
        while (tok) { prof[m++] = atoi(tok); tok = strtok(NULL, ","); }
        if (argc > argi + 2 && strcmp(argv[argi + 2], "-t")) K = atoll(argv[argi + 2]);
    } else { fprintf(stderr, "unknown mode\n"); return 2; }
    if (m < 1) { printf("m = 0: all outputs affine, MC = 0\n"); return 0; }
    K &= (1LL << m) - 1;
    N = 0; for (int j = 0; j < m; j++) N += prof[j];
    if (N > 24 || N < 1) { fprintf(stderr, "need 1 <= N <= 24 (N = %d)\n", N); return 2; }
    uint64_t sz = 1ULL << N;
    int64_t *a = malloc(sz * sizeof(int64_t));
    uint32_t *T = malloc(sz * sizeof(uint32_t));
    if (!a || !T) { fprintf(stderr, "out of memory\n"); return 2; }
    int colstart[32]; { int p = 0; for (int j = 0; j < m; j++) { colstart[j] = p; p += prof[j]; } }
    for (uint64_t x = 0; x < sz; x++) {
        uint64_t t = (uint64_t)K;
        for (int j = 0; j < m; j++) {
            uint64_t col = (x >> colstart[j]) & ((1ULL << prof[j]) - 1);
            t += (uint64_t)__builtin_popcountll(col) << j;
        }
        T[x] = (uint32_t)t;
    }
    int best = -1, bestu = 0;
    for (int u = 1; u < (1 << m); u++) {
        if (toponly && u != (1 << (m - 1))) continue;
        for (uint64_t x = 0; x < sz; x++) {
            int par = __builtin_popcount((T[x] >> 1) & (uint32_t)u) & 1;   /* u_i <-> bit i, i = 1..m */
            a[x] = par ? -1 : 1;
        }
        for (uint64_t h = 1; h < sz; h <<= 1)
            for (uint64_t i = 0; i < sz; i += 2 * h)
                for (uint64_t j = i; j < i + h; j++) { int64_t p = a[j], q = a[j + h]; a[j] = p + q; a[j + h] = p - q; }
        int mv = 1000;
        for (uint64_t l = 0; l < sz; l++)
            if (a[l]) { int64_t w = a[l] < 0 ? -a[l] : a[l]; int v = __builtin_ctzll((uint64_t)w); if (v < mv) mv = v; }
        if (mv < 1000 && N - mv > best) { best = N - mv; bestu = u; }
    }
    int U = U_of(K);
    if (k) printf("add k=%d n=%d K=%lld N=%d", k, n, K, N);
    else { printf("heap ["); for (int j = 0; j < m; j++) printf(j ? ",%d" : "%d", prof[j]); printf("] K=%lld N=%d", K, N); }
    printf(": spectral lower bound %d (u=%d), full-adder upper bound U=%d  %s\n", best, bestu, U, best == U ? "MATCH" : "DIFF");
    free(a); free(T);
    return best == U ? 0 : 1;
}
