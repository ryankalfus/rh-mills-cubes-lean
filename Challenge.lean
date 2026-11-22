module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Challenge: Mills' constant and primes between cubes, assuming the Riemann Hypothesis

This file imports only Mathlib and proves nothing. It states what the project claims:
the Mills statements below, and `GRHCorollaries.exists_prime_between_consecutive_cubes_of_RH`
at the end (a prime strictly between `n ^ 3` and `(n + 1) ^ 3` for every `n ≥ 1`).

`Mills.IsMills`, `Mills.IsMinMills` and the statement `Mills.lower_bound_of_RH` are copied
character for character from `google-deepmind/formal-conjectures`,
`FormalConjectures/Wikipedia/Mills.lean` (commit 2207c54 of 2026-11-21, Apache-2.0,
Copyright 2026 The Formal Conjectures Authors). They are elaborated here against Mathlib
v4.35.0; formal-conjectures itself pins Mathlib v4.33.1, and this file has not been compiled
inside that repository. `RiemannHypothesis` is Mathlib's definition, the statement proved as
`riemannHypothesis` in the Lean archive announced on 2026-11-20 (see
https://math.mit.edu/~drew/grh/ for the verification record). Here it is only a hypothesis.

In words: a real `A` is a *Mills number* if `⌊A ^ (3 ^ n)⌋` is prime for every `n ≥ 1`.
Assuming RH, the least Mills number greater than 1 exists and lies strictly between
1.3063778838 and 1.3063778839 (Caldwell–Cheng, J. Integer Seq. 8 (2005), Article 05.4.1).
-/

@[expose] public section

namespace Mills

/--
Given any real $A$, `IsMills A` encodes the statement that $\lfloor A^{3^n}\rfloor,n > 0$ is prime.
-/
abbrev IsMills (A : ℝ) : Prop := ∀ (n : ℕ+), Prime ⌊A ^ (3 ^ (n : ℕ))⌋₊

/--
For a real $A$, `IsMinMills A` is the smallest value satisfying `IsMills A`.
-/
abbrev IsMinMills (A : ℝ) : Prop := IsLeast {x | x > 1 ∧ IsMills x} A

/--
**Mills' constant lower bound** (Caldwell–Cheng, 2005): assuming the Riemann hypothesis,
Mills' constant begins at $1.3063778838\ldots$.
-/
theorem lower_bound_of_RH (hRH : RiemannHypothesis) {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  sorry

/-- Non-vacuity of the statement above: assuming RH, a least Mills number exists. -/
theorem exists_isMinMills_of_RH (hRH : RiemannHypothesis) : ∃ A, IsMinMills A := by
  sorry

/-- A Mills number exists, assuming RH. This is weaker than Mills' 1947 theorem, which needs no
hypothesis (formal-conjectures' unconditional `Mills.exists'` is NOT proved here). -/
theorem exists_isMills_of_RH (hRH : RiemannHypothesis) : ∃ A > 1, IsMills A := by
  sorry

end Mills

namespace GRHCorollaries

/-- Assuming RH, for every `N ≥ 6 ^ 12 = 2176782336` there is a prime `p` with
`N ^ 3 < p` and `p + 1 < (N + 1) ^ 3`. (The only place where the Mills results use RH.) -/
theorem exists_prime_between_cubes_of_RH (hRH : RiemannHypothesis) {N : ℕ} (hN : 6 ^ 12 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 := by
  sorry

/-- **A prime between consecutive cubes, assuming RH.** For every `n ≥ 1` there is a prime `p`
with `n ^ 3 < p < (n + 1) ^ 3` (Caldwell–Cheng 2005, Lemma 5, conditionally on RH). -/
theorem exists_prime_between_consecutive_cubes_of_RH (hRH : RiemannHypothesis) (n : ℕ)
    (hn : 0 < n) : ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3 := by
  sorry

end GRHCorollaries
