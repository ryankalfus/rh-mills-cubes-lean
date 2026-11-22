#!/usr/bin/env python3
"""Certificates for 'a prime between N^3 and (N+1)^3', N in [LO, HI).

For each N find a prime p = 1 (mod 6) with N^3 < p < (N+1)^3 such that the {2,3}-smooth part F
of p-1 satisfies (F+1)^2 > p, and a witness a with
    a^(p-1) = 1 (mod p),  a^((p-1)/2) != 1 (mod p),  a^((p-1)/3) != 1 (mod p).
By Pocklington's criterion these facts prove that p is prime.  The Lean kernel re-checks every
line; nothing printed by this script is trusted.
Usage: gen_cube_certs.py LO HI OUTFILE      (output lines: N p a)
"""
import sys
from bisect import bisect_left
from math import isqrt

SMALL = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
def is_prime(n):
    if n < 2: return False
    for q in SMALL:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in SMALL:                      # deterministic below 3.3e24
        x = pow(a, d, n)
        if x == 1 or x == n - 1: continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else:
            return False
    return True

SMOOTH = sorted(2**i * 3**j for i in range(1, 70) for j in range(1, 44) if 2**i * 3**j < 10**21)   # 6 | F

def smooth_part(m):
    F = 1
    while m % 2 == 0: m //= 2; F *= 2
    while m % 3 == 0: m //= 3; F *= 3
    return F

def witness(p):
    for a in range(2, 256):
        if pow(a, (p - 1) // 2, p) == 1: continue
        if pow(a, (p - 1) // 3, p) == 1: continue
        return a
    return None

def find(N):
    lo, hi = N**3, (N + 1)**3
    r = isqrt(hi)                         # F >= r  =>  (F+1)^2 > hi > p
    i = bisect_left(SMOOTH, r)
    for F in SMOOTH[i:i + 400]:
        if F >= hi: break
        k = -(-lo // F)                   # ceil(lo / F)
        kmax = (hi - 2) // F
        while k <= kmax:
            p = k * F + 1
            if lo < p < hi and is_prime(p):
                a = witness(p)
                if a is not None:
                    assert (smooth_part(p - 1) + 1) ** 2 > p
                    return p, a
            k += 1
    return None

if __name__ == '__main__':
    LO, HI, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    fails, maxa = [], 0
    with open(out, 'w') as f:
        for N in range(LO, HI):
            r = find(N)
            if r is None:
                fails.append(N); continue
            f.write(f"{N} {r[0]} {r[1]}\n")
            maxa = max(maxa, r[1])
    print(f"range [{LO},{HI}): {HI - LO - len(fails)} certificates, max witness {maxa}, failures: {fails[:50]} (count {len(fails)})")
