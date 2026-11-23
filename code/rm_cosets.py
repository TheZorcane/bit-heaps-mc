"""spectral method: on which cosets r + RM(1,4) are bits 1,2 of the Hamming weight affine?  (16 bits = functions on F_2^4)"""
import itertools
pts = range(16)
aff = []
for c in range(32):
    v = 0
    for x in pts:
        b = (c >> 4) & 1
        for i in range(4):
            if c >> i & 1 and x >> i & 1: b ^= 1
        v |= b << x
    aff.append(v)            # aff[c], c = 5-bit coefficient vector: linear in c
mon = [T for T in range(16) if bin(T).count('1') >= 2]
def fn(coefs):
    v = 0
    for x in pts:
        b = 0
        for T, a in zip(mon, coefs):
            if a and (x & T) == T: b ^= 1
        v |= b << x
    return v
good = {}
for coefs in itertools.product((0, 1), repeat=11):
    r = fn(coefs); w = [bin(r ^ aff[c]).count('1') % 8 for c in range(32)]
    ok = all(((w[c] ^ w[c & (c - 1)] ^ w[c & -c] ^ w[0]) & 6) == 0 for c in range(32) if c & (c - 1))
    deg = max(bin(T).count('1') for T, a in zip(mon, coefs) if a) if any(coefs) else 1
    key = (deg, tuple(sorted(set(w))))
    good.setdefault((ok, key), 0); good[(ok, key)] += 1
for k in sorted(good): print(k, good[k])
