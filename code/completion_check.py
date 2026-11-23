"""Check the uniform-completion argument (handoff step 1-3) on many heaps with constants:
- a >= max(1,k_j), a = -Tmax mod 2^m; h_j = a - k_j; every prefix sum_{i<=j} h_i 2^i divisible by 2^{j+1};
- d_{j+1} = (h_j + d_j)/2 integer; uniform carries c'_j = c_j + d_j; FA(a^m,K) = FA(kappa,K) + R;
- column j of the extension has 1 + h_j + d_j = 1 + 2 d_{j+1} wires (so d_{j+1} full adders, d_{j+1} carries).
Also: brute-force spectral bound == FA(kappa,K) on small heaps with constants (independent of the argument)."""
import itertools, random

def carries(kappa, K):
    c = [0]; paid = 0
    for j, k in enumerate(kappa):
        v = k + c[-1]; paid += v // 2; c.append((v + ((K >> j) & 1)) // 2)
    return c, paid

def v2(x): return (x & -x).bit_length() - 1

def spectral(kappa, K):
    m = len(kappa); N = sum(kappa); best = 0
    for es in itertools.product(*[range(k + 1) for k in kappa]):
        poly = {K: 1}
        for j, (k, e) in enumerate(zip(kappa, es)):
            w = 1 << j
            for sgn, cnt in ((1, k - e), (-1, e)):
                for _ in range(cnt):
                    new = {}
                    for t, a in poly.items():
                        new[t] = new.get(t, 0) + a; new[t + w] = new.get(t + w, 0) + sgn * a
                    poly = new
        for u in range(1, 1 << m):
            W = 0
            for t, a in poly.items():
                par = 0
                for i in range(m):
                    if (u >> i) & 1: par ^= (t >> (i + 1)) & 1
                W += -a if par else a
            if W: best = max(best, N - v2(abs(W)))
    return best

random.seed(1)
ok = 0
for trial in range(200000):
    m = random.randint(1, 7); kappa = [random.randint(0, 12) for _ in range(m)]
    if sum(kappa) == 0: continue
    K = random.randrange(1 << m); q = 1 << m
    Tmax = sum(k << j for j, k in enumerate(kappa))
    a = max(1, max(kappa)); a += (-Tmax - a) % q
    assert a % q == (-Tmax) % q
    h = [a - k for k in kappa]
    d = [0]
    for j in range(m):
        assert sum(h[i] << i for i in range(j + 1)) % (1 << (j + 1)) == 0
        assert (h[j] + d[-1]) % 2 == 0
        d.append((h[j] + d[-1]) // 2)
    c, F = carries(kappa, K); cu, Fu = carries([a] * m, K)
    assert all(cu[j] == c[j] + d[j] for j in range(m + 1))
    assert Fu == F + sum(d[1:])
    ok += 1
print('completion identities hold on', ok, 'random heap/constant instances')

bad = []; n = 0
for m in range(1, 4):
    for kappa in itertools.product(range(0, 5), repeat=m):
        if not (1 <= sum(kappa) <= 11): continue
        for K in range(1 << m):
            n += 1
            if spectral(list(kappa), K) != carries(list(kappa), K)[1]: bad.append((kappa, K))
print('spectral bound == FA on', n - len(bad), 'of', n, 'small heap/constant instances; mismatches:', bad[:5])
