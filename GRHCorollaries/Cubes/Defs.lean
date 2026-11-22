/-
# Certificates for a prime between consecutive cubes: the checker

Executable definitions only (no theorems), so that certificate files can import this module
without loading Mathlib. The proofs that the checker is sound are in
`GRHCorollaries/Cubes/Soundness.lean`.

A certificate for `N` is one natural number
`c = p + 2^61 * a + 2^69 * i + 2^75 * j` (81 bits), where `p` is a prime with
`N^3 < p < (N+1)^3`, `2^i * 3^j` divides `p - 1` with `i, j ≥ 1` and `(2^i * 3^j + 1)^2 > p`, and
`a` is a witness for Pocklington's criterion: `a^(p-1) ≡ 1`, and `a^((p-1)/2) - 1`,
`a^((p-1)/3) - 1` are coprime to `p`.
-/

namespace GRHCorollaries.Cubes

/-- `a ^ e % m` for `e < 256 ^ n`, eight exponent bits at a time
(the kernel evaluates `x ^ 256` and `%` on literals natively). -/
def pm256 (m a : Nat) : Nat → Nat → Nat
  | 0, _ => 1 % m
  | n + 1, e => (pm256 m a n (e / 256)) ^ 256 % m * (a ^ (e % 256) % m) % m

/-- Check one packed certificate `c` for the interval `(N^3, (N+1)^3)`. -/
def certOK (N c : Nat) : Bool :=
  let p := c % 2305843009213693952
  let a := (c / 2305843009213693952) % 256
  let i := (c / 590295810358705651712) % 64
  let j := (c / 37778931862957161709568) % 64
  let F := 2 ^ i * 3 ^ j
  let y := pm256 p a 8 ((p - 1) / 6)
  let y2 := y * y % p
  let y3 := y2 * y % p
  Nat.blt (N ^ 3) p && Nat.blt p ((N + 1) ^ 3) && Nat.beq ((p - 1) % F) 0 && Nat.blt p ((F + 1) ^ 2) &&
  Nat.blt 0 i && Nat.blt 0 j &&
  Nat.beq (y3 * y3 % p) 1 &&
  Nat.beq (Nat.gcd (y3 + (p - 1)) p) 1 &&
  Nat.beq (Nat.gcd (y2 + (p - 1)) p) 1

/-- Check `cnt` consecutive certificates packed in `data` (81 bits each, lowest first),
for the intervals of `N, N + 1, …, N + cnt - 1`. -/
def blockOK (data : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | cnt + 1, N =>
      certOK N (data % 2417851639229258349412352) &&
        blockOK (data / 2417851639229258349412352) cnt (N + 1)

end GRHCorollaries.Cubes
