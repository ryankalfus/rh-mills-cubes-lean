/-
# Mills' constant under the Riemann Hypothesis

Main results (statements as in `google-deepmind/formal-conjectures`, `Wikipedia/Mills.lean`):

* `Mills.lower_bound_of_RH`: assuming RH, the least Mills number lies in
  `(1.3063778838, 1.3063778839)`;
* `Mills.exists_isMinMills_of_RH`: assuming RH, a least Mills number exists;
* `Mills.exists_isMills_of_RH`: assuming RH, a Mills number exists (a conditional, weaker form
  of Mills' theorem).

RH enters only through `GRHCorollaries.exists_prime_between_cubes_of_RH`, which supplies the
primes `c₄, c₅, …` of the cube chain `2, 11, 1361, 2521008887, c₄, …`.
-/
import GRHCorollaries.Mills.LowerBound
import GRHCorollaries.Mills.Construction
import GRHCorollaries.Mills.Least
import GRHCorollaries.PrimeBetweenCubes

namespace Mills

open GRHCorollaries

/-- A prime strictly between `N³` and `(N+1)³ - 1`, chosen under RH (junk value `0` below `6¹²`). -/
private noncomputable def nextCubePrime (hRH : RiemannHypothesis) (N : ℕ) : ℕ :=
  if h : 6 ^ 12 ≤ N then (exists_prime_between_cubes_of_RH hRH h).choose else 0

private lemma nextCubePrime_spec (hRH : RiemannHypothesis) {N : ℕ} (h : 6 ^ 12 ≤ N) :
    (nextCubePrime hRH N).Prime ∧ N ^ 3 < nextCubePrime hRH N ∧
      nextCubePrime hRH N + 1 < (N + 1) ^ 3 := by
  unfold nextCubePrime
  split_ifs
  exact (exists_prime_between_cubes_of_RH hRH h).choose_spec

/-- The chain from the fourth Mills prime on: `t 0 = 2521008887`, `t (k+1)` a prime just above `(t k)³`. -/
private noncomputable def tailSeq (hRH : RiemannHypothesis) : ℕ → ℕ
  | 0 => 2521008887
  | k + 1 => nextCubePrime hRH (tailSeq hRH k)

private lemma tailSeq_ge (hRH : RiemannHypothesis) (k : ℕ) : 6 ^ 12 ≤ tailSeq hRH k := by
  induction k with
  | zero => norm_num [tailSeq]
  | succ k ih =>
    have h := (nextCubePrime_spec hRH ih).2.1
    have h1 : tailSeq hRH k ≤ tailSeq hRH k ^ 3 := Nat.le_self_pow (by norm_num) _
    show 6 ^ 12 ≤ nextCubePrime hRH (tailSeq hRH k)
    exact le_trans ih (le_trans h1 h.le)

private lemma tailSeq_prime (hRH : RiemannHypothesis) (k : ℕ) : (tailSeq hRH k).Prime := by
  cases k with
  | zero => exact prime_2521008887
  | succ k => exact (nextCubePrime_spec hRH (tailSeq_ge hRH k)).1

private lemma tailSeq_cube_lt (hRH : RiemannHypothesis) (k : ℕ) :
    tailSeq hRH k ^ 3 < tailSeq hRH (k + 1) :=
  (nextCubePrime_spec hRH (tailSeq_ge hRH k)).2.1

private lemma tailSeq_succ_lt (hRH : RiemannHypothesis) (k : ℕ) :
    tailSeq hRH (k + 1) + 1 < (tailSeq hRH k + 1) ^ 3 :=
  (nextCubePrime_spec hRH (tailSeq_ge hRH k)).2.2

/-- The full chain `2, 11, 1361, 2521008887, …`. -/
private noncomputable def chain (hRH : RiemannHypothesis) : ℕ → ℕ
  | 0 => 2
  | 1 => 11
  | 2 => 1361
  | k + 3 => tailSeq hRH k

private lemma chain_isCubeChain (hRH : RiemannHypothesis) : IsCubeChain (chain hRH) where
  prime := fun k => by
    match k with
    | 0 => exact Nat.prime_two
    | 1 => show Nat.Prime 11; norm_num
    | 2 => exact prime_1361
    | k + 3 => exact tailSeq_prime hRH k
  le := fun k => by
    match k with
    | 0 => show 2 ^ 3 ≤ 11; norm_num
    | 1 => show 11 ^ 3 ≤ 1361; norm_num
    | 2 => show 1361 ^ 3 ≤ 2521008887; norm_num
    | k + 3 => exact (tailSeq_cube_lt hRH k).le
  lt := fun k => by
    match k with
    | 0 => show 11 + 1 < (2 + 1) ^ 3; norm_num
    | 1 => show 1361 + 1 < (11 + 1) ^ 3; norm_num
    | 2 => show 2521008887 + 1 < (1361 + 1) ^ 3; norm_num
    | k + 3 => exact tailSeq_succ_lt hRH k

/-- Assuming RH there is a Mills number below `1.3063778839`. -/
theorem exists_isMills_lt_of_RH (hRH : RiemannHypothesis) :
    ∃ A : ℝ, 1 < A ∧ IsMills A ∧ A < 1.3063778839 := by
  obtain ⟨A, hA1, hAM, hfl⟩ := exists_mills_of_cubeChain (chain_isCubeChain hRH)
  refine ⟨A, hA1, hAM, ?_⟩
  have h3 : ⌊A ^ (3 ^ (3 + 1))⌋₊ = 2521008887 := hfl 3
  have h81 : A ^ 81 < 2521008888 := by
    have h := Nat.lt_floor_add_one (A ^ (3 ^ (3 + 1)))
    rw [h3] at h
    norm_num at h
    exact h
  by_contra hge
  push Not at hge
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1.3063778839) hge 81
  linarith [pow_81_upper]

/-- A Mills number exists, assuming RH: some real `A > 1` has `⌊A ^ 3 ^ n⌋` prime for all `n ≥ 1`.
This is weaker than Mills' 1947 theorem, which needs no hypothesis. -/
theorem exists_isMills_of_RH (hRH : RiemannHypothesis) : ∃ A > 1, IsMills A := by
  obtain ⟨A, hA1, hAM, -⟩ := exists_isMills_lt_of_RH hRH
  exact ⟨A, hA1, hAM⟩

/-- Assuming RH, a least Mills number exists. -/
theorem exists_isMinMills_of_RH (hRH : RiemannHypothesis) : ∃ A, IsMinMills A := by
  obtain ⟨A, hA1, hAM, -⟩ := exists_isMills_lt_of_RH hRH
  exact exists_isMinMills_of_exists ⟨A, hA1, hAM⟩

/--
**Mills' constant lower bound** (Caldwell–Cheng, 2005): assuming the Riemann hypothesis,
Mills' constant begins at $1.3063778838\ldots$.
-/
theorem lower_bound_of_RH (hRH : RiemannHypothesis) {A} (hA : IsMinMills A) :
    A ∈ Set.Ioo (1.3063778838 : ℝ) 1.3063778839 := by
  obtain ⟨A₀, h1, hM, hlt⟩ := exists_isMills_lt_of_RH hRH
  have hmem : A > 1 ∧ IsMills A := hA.1
  exact ⟨lower_bound hmem.1 hmem.2, lt_of_le_of_lt (hA.2 ⟨h1, hM⟩) hlt⟩

end Mills
