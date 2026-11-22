module

public import GRHCorollaries.PsiBound
public import Mathlib.NumberTheory.PrimeCounting

/-!
# RH implies a prime strictly between consecutive cubes (large range)

For every natural `N ≥ 1200001`, Mathlib's `RiemannHypothesis` gives a prime `p` with
`N ^ 3 < p` and `p + 1 < (N + 1) ^ 3`.

Proof. Put `m = N + 1`, `x = N ^ 3`, `y = m ^ 3 - 2`. By the explicit bound
`|ψ t - t| ≤ (7/8) √t log² t` (`GRHCorollaries.abs_psi_sub_self_le_of_RH`) and Mathlib's
`0 ≤ ψ - θ ≤ 2 √t log t`,

  `θ y - θ x ≥ (y - x) - (7/8) (√y log² y + √x log² x) - 2 √y log y`
          `≥ 3 m² - 3 m - 1 - m √m ((63/4) log² m + 6 log m)`.

For `m ≥ 1200000` one has `(63/4) log² m + 6 log m + 1 ≤ 3 √m` (`log_sq_le_sqrt`), so the right
side is at least `m (√m - 3) - 1 > 0`. Hence `θ y > θ x`, and the two sums over primes cannot agree.

This is the only place where the Mills and cube results use RH.
-/

@[expose] public section

namespace GRHCorollaries

open Real Chebyshev

/-- For `m ≥ 1200000`: `(63/4) log² m + 6 log m + 1 ≤ 3 √m`.
Write `m = 1200000 · r⁴` with `r ≥ 1`; then `log m ≤ 14 + 4 (r - 1)` and `√m ≥ 1095 r²`. -/
private lemma log_sq_le_sqrt {m : ℝ} (hm : 1200000 ≤ m) :
    63 / 4 * (Real.log m) ^ 2 + 6 * Real.log m + 1 ≤ 3 * Real.sqrt m := by
  set q : ℝ := m / 1200000 with hq
  have hq1 : 1 ≤ q := by
    rw [hq, le_div_iff₀ (by norm_num)]
    linarith
  set t : ℝ := Real.sqrt q with ht
  set r : ℝ := Real.sqrt t with hr
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have htq : t ^ 2 = q := Real.sq_sqrt (by linarith)
  have hrt : r ^ 2 = t := Real.sq_sqrt ht0
  have ht1 : 1 ≤ t := Real.one_le_sqrt.mpr hq1
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr ht1
  have hrpos : 0 < r := by linarith
  have hlogq : Real.log q = 4 * Real.log r := by
    have hqr : q = r ^ 4 := by
      rw [← htq, ← hrt]
      ring
    rw [hqr, Real.log_pow]
    norm_num
  have hlogr : Real.log r ≤ r - 1 := Real.log_le_sub_one_of_pos hrpos
  have hlogr0 : 0 ≤ Real.log r := Real.log_nonneg hr1
  have hmq : m = 1200000 * q := by
    rw [hq]
    field_simp
  have hlogm : Real.log m = Real.log 1200000 + Real.log q := by
    rw [hmq, Real.log_mul (by norm_num) (by linarith)]
  have hL0 : Real.log 1200000 ≤ 14 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have h1 : (2.7182818283 : ℝ) ^ 14 ≤ Real.exp 1 ^ 14 :=
      pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 14
    have h2 : Real.exp 1 ^ 14 = Real.exp 14 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : (1200000 : ℝ) ≤ (2.7182818283 : ℝ) ^ 14 := by norm_num
    linarith
  have hL0' : 0 ≤ Real.log 1200000 := Real.log_nonneg (by norm_num)
  have hsqrt : Real.sqrt m = Real.sqrt 1200000 * r ^ 2 := by
    rw [hmq, Real.sqrt_mul (by norm_num), hrt]
  have h1095 : (1095 : ℝ) ≤ Real.sqrt 1200000 := Real.le_sqrt_of_sq_le (by norm_num)
  set v : ℝ := r - 1 with hv
  have hv0 : 0 ≤ v := by linarith
  have hrv : r = 1 + v := by
    rw [hv]
    ring
  have hL : Real.log m ≤ 14 + 4 * v := by
    rw [hlogm, hlogq]
    linarith
  have hLnn : 0 ≤ Real.log m := by
    rw [hlogm, hlogq]
    linarith
  have hsq : (Real.log m) ^ 2 ≤ 196 + 112 * v + 16 * v ^ 2 := by
    have h := pow_le_pow_left₀ hLnn hL 2
    calc (Real.log m) ^ 2 ≤ (14 + 4 * v) ^ 2 := h
      _ = 196 + 112 * v + 16 * v ^ 2 := by ring
  have hS : 1095 + 2190 * v + 1095 * v ^ 2 ≤ Real.sqrt m := by
    have h : 1095 * (1 + v) ^ 2 ≤ Real.sqrt 1200000 * (1 + v) ^ 2 :=
      mul_le_mul_of_nonneg_right h1095 (by positivity)
    rw [hsqrt, hrv]
    calc 1095 + 2190 * v + 1095 * v ^ 2 = 1095 * (1 + v) ^ 2 := by ring
      _ ≤ Real.sqrt 1200000 * (1 + v) ^ 2 := h
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  linarith

/-- Under RH, Chebyshev's `θ` strictly increases from `N³` to `(N+1)³ - 2` once `N ≥ 1200001`. -/
theorem theta_cube_gap_pos (hRH : RiemannHypothesis) {N : ℕ} (hN : 1200001 ≤ N) :
    θ ((N : ℝ) ^ 3) < θ (((N : ℝ) + 1) ^ 3 - 2) := by
  have hNr : (1200001 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  set m : ℝ := (N : ℝ) + 1 with hm_def
  have hm : (1200000 : ℝ) ≤ m := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  -- the square root of `m`
  set s : ℝ := Real.sqrt m with hs_def
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hs1095 : (1095 : ℝ) ≤ s := Real.le_sqrt_of_sq_le (by nlinarith)
  set L : ℝ := Real.log m with hL_def
  have hkey : 63 / 4 * L ^ 2 + 6 * L + 1 ≤ 3 * s := log_sq_le_sqrt hm
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  -- the two points
  set x : ℝ := (N : ℝ) ^ 3 with hx_def
  set y : ℝ := m ^ 3 - 2 with hy_def
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by linarith
  have hx5000 : (5000 : ℝ) ≤ x := by
    have h1 : (N : ℝ) ^ 1 ≤ (N : ℝ) ^ 3 := pow_le_pow_right₀ hN1 (by norm_num)
    rw [pow_one] at h1
    linarith
  have hdiff : y - x = 3 * m ^ 2 - 3 * m - 1 := by
    have hNm : (N : ℝ) = m - 1 := by
      rw [hm_def]
      ring
    rw [hy_def, hx_def, hNm]
    ring
  have hxy : x ≤ y := by nlinarith
  have hy5000 : (5000 : ℝ) ≤ y := le_trans hx5000 hxy
  have hx1 : (1 : ℝ) ≤ x := by linarith
  have hy1 : (1 : ℝ) ≤ y := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hym : y ≤ m ^ 3 := by
    rw [hy_def]
    linarith
  -- size bounds in terms of `K = m √m` and `L = log m`
  set K : ℝ := m * s with hK_def
  have hK0 : (0 : ℝ) ≤ K := mul_nonneg hm0.le hs0
  have hsqrty : Real.sqrt y ≤ K := by
    have h1 : Real.sqrt y ≤ Real.sqrt (m ^ 3) := Real.sqrt_le_sqrt hym
    have h2 : m ^ 3 = K ^ 2 := by
      rw [hK_def, mul_pow, hs2]
      ring
    have h3 : Real.sqrt (K ^ 2) = K := Real.sqrt_sq hK0
    rw [h2, h3] at h1
    exact h1
  have hsqrtxy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hlogxy : Real.log x ≤ Real.log y := Real.log_le_log hx0 hxy
  have hlogy : Real.log y ≤ 3 * L := by
    have h1 : Real.log y ≤ Real.log (m ^ 3) := Real.log_le_log hy0 hym
    have h2 : Real.log (m ^ 3) = 3 * Real.log m := by
      rw [Real.log_pow]
      norm_num
    rw [h2] at h1
    exact h1
  have hlogy0 : 0 ≤ Real.log y := le_trans hlogx0 hlogxy
  have hsy0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
  -- the three error terms
  have hT1 : Real.sqrt y * (Real.log y) ^ 2 ≤ 9 * (K * L ^ 2) := by
    have hsq : (Real.log y) ^ 2 ≤ (3 * L) ^ 2 := pow_le_pow_left₀ hlogy0 hlogy 2
    have h := mul_le_mul hsqrty hsq (by positivity) hK0
    calc Real.sqrt y * (Real.log y) ^ 2 ≤ K * (3 * L) ^ 2 := h
      _ = 9 * (K * L ^ 2) := by ring
  have hT1' : Real.sqrt x * (Real.log x) ^ 2 ≤ Real.sqrt y * (Real.log y) ^ 2 := by
    have hsq : (Real.log x) ^ 2 ≤ (Real.log y) ^ 2 := pow_le_pow_left₀ hlogx0 hlogxy 2
    exact mul_le_mul hsqrtxy hsq (by positivity) hsy0
  have hT2 : Real.sqrt y * Real.log y ≤ 3 * (K * L) := by
    have h := mul_le_mul hsqrty hlogy hlogy0 hK0
    calc Real.sqrt y * Real.log y ≤ K * (3 * L) := h
      _ = 3 * (K * L) := by ring
  -- explicit ψ bounds at `x` and `y`, and ψ versus θ
  have hψx := abs_psi_sub_self_le_of_RH hRH hx5000
  have hψy := abs_psi_sub_self_le_of_RH hRH hy5000
  have hψx' : ψ x ≤ x + 7 / 8 * Real.sqrt x * (Real.log x) ^ 2 := by
    have := (abs_le.mp hψx).2
    linarith
  have hψy' : y - 7 / 8 * Real.sqrt y * (Real.log y) ^ 2 ≤ ψ y := by
    have := (abs_le.mp hψy).1
    linarith
  have hθx : θ x ≤ ψ x := theta_le_psi x
  have hθy : ψ y - θ y ≤ 2 * Real.sqrt y * Real.log y := psi_sub_theta_le hy1
  -- `K ((63/4) L² + 6 L) ≤ K (3 s - 1) = 3 m² - K`
  have hKL : K * (63 / 4 * L ^ 2 + 6 * L) ≤ K * (3 * s - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hK0
  have hKs : K * (3 * s - 1) = 3 * m ^ 2 - K := by
    rw [hK_def]
    calc m * s * (3 * s - 1) = 3 * m * s ^ 2 - m * s := by ring
      _ = 3 * m ^ 2 - m * s := by rw [hs2]; ring
  have hKm : 1095 * m ≤ K := by
    rw [hK_def, mul_comm]
    exact mul_le_mul_of_nonneg_left hs1095 hm0.le
  nlinarith [hT1, hT1', hT2, hψx', hψy', hθx, hθy, hdiff, hKL, hKs, hKm]

/-- If `θ` strictly increases from `N³` to `(N+1)³ - 2`, a prime lies strictly in between. -/
theorem exists_prime_of_theta_cube_gap {N : ℕ} (hN1 : 1 ≤ N)
    (hgap : θ ((N : ℝ) ^ 3) < θ (((N : ℝ) + 1) ^ 3 - 2)) :
    ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 := by
  by_contra hno
  push Not at hno
  have hcube : (N + 1) ^ 3 = N ^ 3 + 3 * N ^ 2 + 3 * N + 1 := by ring
  have hab : N ^ 3 + 2 ≤ (N + 1) ^ 3 := by
    rw [hcube]
    have : 0 ≤ 3 * N ^ 2 := Nat.zero_le _
    omega
  have e1 : (N : ℝ) ^ 3 = ((N ^ 3 : ℕ) : ℝ) := by push_cast; ring
  have e2 : ((N : ℝ) + 1) ^ 3 - 2 = (((N + 1) ^ 3 - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [e1, e2, theta_eq_sum_primesLE_log, theta_eq_sum_primesLE_log] at hgap
  have hset : Nat.primesLE ((N + 1) ^ 3 - 2) = Nat.primesLE (N ^ 3) := by
    ext p
    simp only [Nat.mem_primesLE]
    constructor
    · rintro ⟨hp1, hp⟩
      refine ⟨?_, hp⟩
      by_contra hlt
      push Not at hlt
      have := hno p hp hlt
      omega
    · rintro ⟨hp1, hp⟩
      exact ⟨by omega, hp⟩
  rw [hset] at hgap
  exact lt_irrefl _ hgap

/-- **A prime strictly between consecutive cubes, under RH, for `N ≥ 1200001`.** -/
theorem exists_prime_between_cubes_of_RH_of_ge (hRH : RiemannHypothesis) {N : ℕ}
    (hN : 1200001 ≤ N) : ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 :=
  exists_prime_of_theta_cube_gap (le_trans (by norm_num) hN) (theta_cube_gap_pos hRH hN)

/-- **A prime strictly between consecutive cubes, under RH.** For `N ≥ 6 ^ 12` there is a prime `p`
with `N ^ 3 < p` and `p + 1 < (N + 1) ^ 3`. (Kept in this form for the Mills development.) -/
theorem exists_prime_between_cubes_of_RH (hRH : RiemannHypothesis) {N : ℕ} (hN : 6 ^ 12 ≤ N) :
    ∃ p : ℕ, p.Prime ∧ N ^ 3 < p ∧ p + 1 < (N + 1) ^ 3 :=
  exists_prime_between_cubes_of_RH_of_ge hRH (le_trans (by norm_num) hN)

end GRHCorollaries
