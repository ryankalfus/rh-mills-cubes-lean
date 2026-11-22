# Two consequences of the Riemann Hypothesis, machine-checked in Lean 4

**Status: local and unpublished.** Lean v4.35.0, Mathlib v4.35.0. Last verified 2026-11-22.
Every headline theorem here takes the Riemann Hypothesis as an explicit hypothesis.

## What is proved

```lean
-- 1. A prime between consecutive cubes
theorem GRHCorollaries.exists_prime_between_consecutive_cubes_of_RH
    (hRH : RiemannHypothesis) (n : ℕ) (hn : 0 < n) :
    ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3

-- 2. Mills' constant
namespace Mills
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

theorem lower_bound_of_RH (hRH : RiemannHypothesis) {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839
theorem exists_isMinMills_of_RH (hRH : RiemannHypothesis) : ∃ A, IsMinMills A
theorem exists_isMills_of_RH (hRH : RiemannHypothesis) : ∃ A > 1, IsMills A
end Mills
```

In words, assuming the Riemann Hypothesis:

1. For every n ≥ 1 there is a prime strictly between n³ and (n+1)³.
2. Call a real A a *Mills number* if ⌊A^(3^n)⌋ is prime for every n ≥ 1. A least Mills
   number greater than 1 exists, and it lies strictly between 1.3063778838 and 1.3063778839.

Both are due to Caldwell and Cheng, *Determining Mills' Constant and a Note on Honaker's
Problem*, J. Integer Seq. 8 (2005), Article 05.4.1 (Lemma 5 and the first ten decimals of
Theorem 1), after Mills (1947). `RiemannHypothesis` is Mathlib's definition.

`Mills.IsMills`, `Mills.IsMinMills` and the statement of `Mills.lower_bound_of_RH` are copied
character for character from
[`google-deepmind/formal-conjectures`](https://github.com/google-deepmind/formal-conjectures),
`FormalConjectures/Wikipedia/Mills.lean` (commit `2207c54`). No public Lean proof of that
statement was found on GitHub or the Lean Zulip as of 2026-11-22 17:00 UTC. For statement 1,
GitHub code search found nothing; the nearest public work is `sthubbar/goldbach-lean` (entry
`dudek2014`: Dudek's short-interval theorem under RH, with one cited zero-counting estimate
taken as an extra hypothesis), from which statement 1 would follow quickly
(GitHub repository and code search, the Lean Zulip's public API, formal-conjectures PRs; code
search lags by a day or two, and private work is invisible).

## What this is not

- **Not new mathematics.** Both results have been known, conditionally on RH, since 2005, and
  statement 1 is an easy, far-from-sharp corollary of RH (Cramér 1920; Dudek 2015). Its
  hypothesis-free part here (n ≤ 1,200,000) is tiny next to known computations: without RH a
  prime between consecutive cubes is known for all n³ ≤ 1.649·10⁴⁰ (arXiv:2601.15564) and for
  n ≥ exp(exp(32.537)), and open in between. Our threshold 1,200,000 is an artefact of the weak
  constant 7/8 in the ψ bound we use; Caldwell and Cheng needed only a hand check for small x.
- **Not a proof of RH, and not yet unconditional.** RH is a hypothesis of every headline theorem. The
  Lean proof of RH announced on 2026-11-20 lives in a 175,187-module archive on Mathlib
  v4.33.1; this project is on Mathlib v4.35.0. Joining the two needs matching versions and
  about 100 GB of RAM. That has not been done.
- **Not all ours.** The one analytic input, `|ψ(x) − x| ≤ (7/8)·√x·(log x)²` for `x ≥ 5000`
  under RH, is proved in six modules of
  [`google-deepmind/cryptids`](https://github.com/google-deepmind/cryptids) (Apache-2.0),
  vendored byte for byte in `vendor-cryptids/`. (7/8 is about 22 times weaker than
  Schoenfeld's constant; it is enough here.) Our own hand-written Lean is about 920 lines
  (plus 1,200 generated certificate theorems).

Not proved here: the unconditional statements `Mills.exists'` and `Mills.exists_least` of
formal-conjectures (ours assume RH), `Mills.irrational`, digits of Mills' constant beyond the
tenth, and Caldwell–Cheng's Lemma 5 for non-integer x. The proof has been compiled against
Mathlib v4.35.0 only, not inside formal-conjectures (which pins Mathlib v4.33.1).

## How the proofs go

*Primes between cubes.* For n ≥ 1,200,001: with x = n³ and y = (n+1)³ − 2, the ψ bound and
Mathlib's `0 ≤ ψ − θ ≤ 2√x·log x` give θ(y) > θ(x), so a prime lies in between
(`PrimeBetweenCubes.lean`; the only use of RH). For 1 ≤ n ≤ 1,200,000, no hypothesis: each n
has a Pocklington certificate, a prime p in the interval with a 3-smooth factor F = 2^i·3^j
of p − 1, (F+1)² > p, and a witness a; a 40-line checker is proved sound
(`Cubes/Soundness.lean`) and the Lean kernel runs it on all 1,200,000 certificates
(`Cubes/Certs/`, `decide +kernel`, no `native_decide`). The trust base for the certificates is
the Lean kernel and its built-in arithmetic on natural-number literals; no compiled code runs.
(Pocklington's criterion, 1914. The exponents i, j in a certificate need not be the full 2- and
3-adic valuations of p − 1; any i, j ≥ 1 with the stated properties suffice.)

*Mills' constant.* (a) The floors q_n = ⌊A^(3^n)⌋ satisfy q_n³ ≤ q_{n+1} < (q_n+1)³, so
primality forces q₁ ≥ 2, q₂ ≥ 11, q₃ ≥ 1361, q₄ ≥ 2521008887 and A^81 ≥ 2521008887 >
1.3063778838^81; no hypothesis (`Mills/LowerBound.lean`). (b) The chain 2, 11, 1361,
2521008887 continued by primes between cubes is the floor sequence of a real A₀ (nested
compact intervals) with A₀^81 < 2521008888 < 1.3063778839^81 (`Mills/Construction.lean`,
`Mills/Main.lean`). (c) The infimum of all Mills numbers is a Mills number (`Mills/Least.lean`).

## Check it yourself

```bash
elan toolchain install leanprover/lean4:v4.35.0
```

```bash
lake exe cache get
```

```bash
lake build GRHCorollaries Challenge
```

The build ends by printing the axioms of the headline theorems (`GRHCorollaries/Audit.lean`);
every line must read `[propext, Classical.choice, Quot.sound]`. `Challenge.lean` imports only
Mathlib and states the theorems with `sorry`; `scripts/comparator.sh` runs `lake comparator`
to check that the library proves exactly those statements. What has and has not been run is
recorded in `VERIFICATION.md`. The 24 certificate modules take under a minute and about 0.7 GB each (about 20 CPU-minutes in all);
everything else builds in a few minutes on an 8 GB laptop once Mathlib's cache is in place
(on 8 GB, use `scripts/build_small.sh`, which builds the certificate modules three at a time).

## Files

| path | content |
|---|---|
| `Challenge.lean` | the statements, Mathlib-only, no proofs |
| `GRHCorollaries/PrimeBetweenCubes.lean` | RH ⟹ primes between cubes for n ≥ 1,200,001 |
| `GRHCorollaries/Cubes/` | certificate checker, its soundness proof, 1,200,000 certificates, final theorem |
| `GRHCorollaries/Mills/` | Mills' constant |
| `GRHCorollaries/PsiBound.lean` | 25-line assembly of the vendored ψ bound (upstream's own proof) |
| `vendor-cryptids/` | six unmodified modules of `google-deepmind/cryptids` @ `3647718b`, licence, notice |
| `scripts/` | certificate generator (Python; untrusted), build helpers. `python3 scripts/gen_cube_certs.py 1 1200001 data/cube-certs.txt` then `python3 scripts/gen_cube_shards.py` regenerates `GRHCorollaries/Cubes/Certs/` and `Cubes/Finite.lean` byte for byte (about 3 minutes) |
| `VERIFICATION.md`, `logs/verify/` | what was checked, with the raw logs (axiom audit, comparator runs, hashes) |

## Credits

Mathematics: W. H. Mills; C. K. Caldwell and Y. Cheng. Statement of the Mills theorem: The
Formal Conjectures Authors (Google DeepMind). Explicit ψ bound under RH: `google-deepmind/cryptids`.
Lean proofs in `GRHCorollaries/`: written by Claude (Anthropic) in Claude Code sessions run by
Ryan Kalfus. The library is called `GRHCorollaries` for historical reasons; only RH for the
Riemann zeta function is used.
