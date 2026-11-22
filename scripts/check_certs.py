#!/usr/bin/env python3
"""Independent sanity check of the certificate modules (NOT part of the trusted base; the Lean
kernel is). Reads only the generated Lean files, not the generator's data file:
  1. the block theorems b#### in GRHCorollaries/Cubes/Certs/*.lean are well formed,
  2. the range lemmas in GRHCorollaries/Cubes/Finite.lean tile [1, 1200001) with no gap or overlap,
  3. every packed certificate decodes to (p, a, i, j) with N^3 < p < (N+1)^3, p prime
     (deterministic Miller-Rabin, valid below 3.3e24), 2^i 3^j | p-1, (2^i 3^j + 1)^2 > p, and the
     Pocklington witness conditions.
Usage: python3 scripts/check_certs.py"""
import glob, os, re, time
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), '..')
def is_prime(n):
    if n < 2: return False
    small = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
    for q in small:
        if n % q == 0: return n == q
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in small:
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
t0 = time.time()
blocks = {}
pat = re.compile(r'theorem (b\d+) : blockOK 0x([0-9a-f]+) (\d+) (\d+) = true := by decide \+kernel\s*$')
for f in sorted(glob.glob(os.path.join(root, 'GRHCorollaries/Cubes/Certs/S*.lean'))):
    for line in open(f):
        if line.startswith('theorem '):
            m = pat.match(line); assert m, line[:80]
            blocks[m.group(1)] = (int(m.group(4)), int(m.group(3)), int(m.group(2), 16))
fin = open(os.path.join(root, 'GRHCorollaries/Cubes/Finite.lean')).read()
rs = re.findall(r'private theorem (r\d+) : ∀ N, (\d+) ≤ N → N < (\d+) → PrimeBetweenCubes N :=\n  fun N h1 h2 => exists_prime_of_blockOK \(by norm_num\) Certs\.(b\d+) N h1 \(by omega\)', fin)
pos = 1
for _, lo, hi, b in rs:
    lo, hi = int(lo), int(hi); blo, cnt, _ = blocks[b]
    assert lo == pos and blo == lo and blo + cnt == hi
    pos = hi
final = int(re.search(r'theorem exists_prime_between_cubes_of_le : ∀ N, 1 ≤ N → N < (\d+)', fin).group(1))
assert final == pos
M81 = (1 << 81) - 1
ncert = bad = 0
for b, (lo, cnt, data) in sorted(blocks.items()):
    assert data >> (81 * cnt) == 0
    for k in range(cnt):
        N = lo + k; c = (data >> (81 * k)) & M81; ncert += 1
        p, a, i, j = c & ((1 << 61) - 1), (c >> 61) & 255, (c >> 69) & 63, (c >> 75) & 63
        F = 2 ** i * 3 ** j
        ok = (N ** 3 < p < (N + 1) ** 3 and i >= 1 and j >= 1 and (p - 1) % F == 0
              and (F + 1) ** 2 > p and is_prime(p) and pow(a, p - 1, p) == 1
              and pow(a, (p - 1) // 2, p) != 1 and pow(a, (p - 1) // 3, p) != 1)
        bad += not ok
print(f"{len(blocks)} block theorems; {len(rs)} range lemmas tile [1, {pos}); "
      f"{ncert} certificates decoded and checked; bad: {bad}; {time.time() - t0:.0f} s")
