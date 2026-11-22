module

public import GRHCorollaries.Mills.Defs

/-!
# A least Mills number exists as soon as one exists

The set of Mills numbers `> 1` is bounded below by `5/4` (because `⌊x ^ 3⌋₊` is a prime, so
`x ^ 3 ≥ 2`), and it is closed under taking the infimum: for each `n` the floor
`⌊x ^ 3 ^ n⌋₊` is locally constant to the right of the infimum.
-/

@[expose] public section

namespace Mills

/-- If there is a Mills number, there is a least one. -/
theorem exists_isMinMills_of_exists (h : ∃ A : ℝ, 1 < A ∧ IsMills A) : ∃ A, IsMinMills A := by
  obtain ⟨A₀, hA₀, hM₀⟩ := h
  have hne : {x : ℝ | x > 1 ∧ IsMills x}.Nonempty := ⟨A₀, hA₀, hM₀⟩
  -- Every Mills number `> 1` is at least `5/4`.
  have hlow : ∀ x ∈ {x : ℝ | x > 1 ∧ IsMills x}, (5 / 4 : ℝ) ≤ x := by
    rintro x ⟨hx1, hxM⟩
    by_contra hlt
    rw [not_le] at hlt
    have hx0 : (0 : ℝ) ≤ x := by linarith
    have h2 : 2 ≤ ⌊x ^ 3⌋₊ := (Nat.prime_iff.mpr (hxM 1)).two_le
    have h3 : (2 : ℝ) ≤ x ^ 3 :=
      (by exact_mod_cast h2 : (2 : ℝ) ≤ (⌊x ^ 3⌋₊ : ℝ)).trans (Nat.floor_le (by positivity))
    have h4 : x ^ 3 < (5 / 4 : ℝ) ^ 3 := pow_lt_pow_left₀ hlt hx0 (by norm_num)
    norm_num at h4
    linarith
  have hbdd : BddBelow {x : ℝ | x > 1 ∧ IsMills x} := ⟨5 / 4, hlow⟩
  set A := sInf {x : ℝ | x > 1 ∧ IsMills x}
  have hA : (5 / 4 : ℝ) ≤ A := le_csInf hne hlow
  have hA0 : (0 : ℝ) ≤ A := by linarith
  refine ⟨A, ⟨by linarith, fun n => ?_⟩, fun x hx => csInf_le hbdd hx⟩
  -- `A` is a Mills number: some `x` in the set has the same floor of `x ^ 3 ^ n` as `A`.
  have hlt : A ^ 3 ^ (n : ℕ) < (⌊A ^ 3 ^ (n : ℕ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hev : ∀ᶠ x in nhds A, x ^ 3 ^ (n : ℕ) < (⌊A ^ 3 ^ (n : ℕ)⌋₊ : ℝ) + 1 :=
    (continuous_pow (3 ^ (n : ℕ))).continuousAt.eventually (gt_mem_nhds hlt)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨x, hxS, hx⟩ := exists_lt_of_csInf_lt hne (show A < A + ε by linarith)
  have hAx : A ≤ x := csInf_le hbdd hxS
  have h1 : x ^ 3 ^ (n : ℕ) < (⌊A ^ 3 ^ (n : ℕ)⌋₊ : ℝ) + 1 :=
    hball (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
  have h2 : (⌊A ^ 3 ^ (n : ℕ)⌋₊ : ℝ) ≤ x ^ 3 ^ (n : ℕ) :=
    (Nat.floor_le (pow_nonneg hA0 _)).trans (pow_le_pow_left₀ hA0 hAx _)
  rw [← (Nat.floor_eq_iff (pow_nonneg (hA0.trans hAx) _)).mpr ⟨h2, h1⟩]
  exact hxS.2 n

end Mills
