module

public import GRHCorollaries.Cubes.Finite
public import GRHCorollaries.PrimeBetweenCubes

/-!
# A prime between consecutive cubes, assuming the Riemann Hypothesis

`GRHCorollaries.exists_prime_between_consecutive_cubes_of_RH`: assuming Mathlib's
`RiemannHypothesis`, for every `n ≥ 1` there is a prime `p` with `n ^ 3 < p < (n + 1) ^ 3`.

* `n ≥ 1200001`: `GRHCorollaries.exists_prime_between_cubes_of_RH_of_ge` (explicit ψ bound under RH).
* `1 ≤ n ≤ 1200000`: `GRHCorollaries.Cubes.exists_prime_between_cubes_of_le`, no hypothesis:
  one kernel-checked Pocklington certificate per `n`.

Known since Caldwell–Cheng (J. Integer Seq. 8 (2005), Article 05.4.1, Lemma 5), conditionally on RH.
Without RH it is known for `n ^ 3 ≤ 1.649·10⁴⁰` by computation (arXiv:2601.15564) and for
`n ≥ exp (exp 32.537)` (Dudek's method, constant of Cully-Hugill), and open in between.
-/

@[expose] public section

namespace GRHCorollaries

/-- **A prime between consecutive cubes, assuming RH.** For every `n ≥ 1` there is a prime `p`
with `n ^ 3 < p < (n + 1) ^ 3`. -/
theorem exists_prime_between_consecutive_cubes_of_RH (hRH : RiemannHypothesis) (n : ℕ)
    (hn : 0 < n) : ∃ p : ℕ, p.Prime ∧ n ^ 3 < p ∧ p < (n + 1) ^ 3 := by
  rcases Nat.lt_or_ge n 1200001 with h | h
  · exact Cubes.exists_prime_between_cubes_of_le n hn h
  · obtain ⟨p, hp, h1, h2⟩ := exists_prime_between_cubes_of_RH_of_ge hRH h
    exact ⟨p, hp, h1, by omega⟩

end GRHCorollaries
