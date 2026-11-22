/-
# Mills' construction

A *cube chain* is a sequence of primes `c 0, c 1, …` with `c k ^ 3 ≤ c (k+1)` and
`c (k+1) + 1 < (c k + 1) ^ 3`.  This file proves that every cube chain comes from a Mills number
`A > 1`, in the sense that `⌊A ^ 3 ^ (k+1)⌋₊ = c k` for all `k`.  The number `A` is a point of the
intersection of the nested compact sets `{x ≥ 0 | c k ≤ x ^ 3 ^ (k+1) ≤ c k + 1}`.
-/
import GRHCorollaries.Mills.Defs
import Mathlib.Topology.Compactness.Compact

namespace Mills

/-- A cube chain: primes `c 0, c 1, …` with `c k ^ 3 ≤ c (k+1)` and `c (k+1) + 1 < (c k + 1) ^ 3`. -/
structure IsCubeChain (c : ℕ → ℕ) : Prop where
  prime : ∀ k, (c k).Prime
  le : ∀ k, c k ^ 3 ≤ c (k + 1)
  lt : ∀ k, c (k + 1) + 1 < (c k + 1) ^ 3

/-- One step down a cube chain: if `x ^ 3 ^ (k+2)` lies in `[c (k+1), c (k+1) + 1]`, then
`x ^ 3 ^ (k+1)` lies in `[c k, c k + 1)`. -/
private lemma IsCubeChain.step {c : ℕ → ℕ} (hc : IsCubeChain c) (k : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (h₁ : (c (k + 1) : ℝ) ≤ x ^ 3 ^ (k + 1 + 1)) (h₂ : x ^ 3 ^ (k + 1 + 1) ≤ c (k + 1) + 1) :
    (c k : ℝ) ≤ x ^ 3 ^ (k + 1) ∧ x ^ 3 ^ (k + 1) < c k + 1 := by
  have hy : (0 : ℝ) ≤ x ^ 3 ^ (k + 1) := pow_nonneg hx _
  have hpow : x ^ 3 ^ (k + 1 + 1) = (x ^ 3 ^ (k + 1)) ^ 3 := by rw [← pow_mul, ← pow_succ]
  rw [hpow] at h₁ h₂
  have hle : ((c k : ℝ)) ^ 3 ≤ c (k + 1) := by exact_mod_cast hc.le k
  have hlt : (c (k + 1) : ℝ) + 1 < ((c k : ℝ) + 1) ^ 3 := by exact_mod_cast hc.lt k
  exact ⟨le_of_pow_le_pow_left₀ (by norm_num) hy (hle.trans h₁),
    lt_of_pow_lt_pow_left₀ 3 (by positivity) (h₂.trans_lt hlt)⟩

/-- **Mills' construction.** A cube chain is the sequence of floors `⌊A ^ 3 ^ (k+1)⌋₊` of a Mills number. -/
theorem exists_mills_of_cubeChain {c : ℕ → ℕ} (hc : IsCubeChain c) :
    ∃ A : ℝ, 1 < A ∧ IsMills A ∧ ∀ k : ℕ, ⌊A ^ (3 ^ (k + 1))⌋₊ = c k := by
  -- The nested compact sets whose intersection contains `A`.
  let I : ℕ → Set ℝ := fun k =>
    Set.Ici 0 ∩ (fun x : ℝ => x ^ 3 ^ (k + 1)) ⁻¹' Set.Icc (c k : ℝ) (c k + 1)
  have hsub : ∀ k, I (k + 1) ⊆ I k := fun k x hx =>
    ⟨hx.1, (hc.step k hx.1 hx.2.1 hx.2.2).1, (hc.step k hx.1 hx.2.1 hx.2.2).2.le⟩
  have hne : ∀ k, (I k).Nonempty := fun k => by
    have hroot : ((c k : ℝ) ^ (((3 ^ (k + 1) : ℕ) : ℝ)⁻¹)) ^ 3 ^ (k + 1) = c k :=
      Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by positivity)
    exact ⟨(c k : ℝ) ^ (((3 ^ (k + 1) : ℕ) : ℝ)⁻¹), Real.rpow_nonneg (Nat.cast_nonneg _) _,
      hroot.ge, hroot.le.trans (by linarith)⟩
  have hcl : ∀ k, IsClosed (I k) := fun k =>
    isClosed_Ici.inter (isClosed_Icc.preimage (continuous_pow _))
  have hcpt : IsCompact (I 0) := by
    refine (isCompact_Icc (a := (0 : ℝ)) (b := c 0 + 1)).of_isClosed_subset (hcl 0)
      (fun x hx => ⟨hx.1, ?_⟩)
    by_contra hlt
    rw [not_le] at hlt
    have h1 : (1 : ℝ) ≤ x := by linarith [(Nat.cast_nonneg (c 0) : (0 : ℝ) ≤ c 0)]
    have h2 : x ≤ x ^ 3 ^ (0 + 1) := le_self_pow₀ h1 (by positivity)
    linarith [hx.2.2]
  obtain ⟨A, hA⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed I hsub hne hcpt hcl
  rw [Set.mem_iInter] at hA
  have hA0 : 0 ≤ A := (hA 0).1
  have hfloor : ∀ k : ℕ, ⌊A ^ (3 ^ (k + 1))⌋₊ = c k := fun k =>
    (Nat.floor_eq_iff (pow_nonneg hA0 _)).mpr (hc.step k hA0 (hA (k + 1)).2.1 (hA (k + 1)).2.2)
  refine ⟨A, ?_, fun n => ?_, hfloor⟩
  · -- `A ^ 3 ≥ c 0 ≥ 2`, so `A > 1`.
    by_contra hle
    rw [not_lt] at hle
    have h1 : A ^ 3 ^ (0 + 1) ≤ 1 := pow_le_one₀ hA0 hle
    have h2 : (2 : ℝ) ≤ c 0 := by exact_mod_cast (hc.prime 0).two_le
    linarith [(hA 0).2.1]
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero n.ne_zero
    rw [hk, Nat.succ_eq_add_one, hfloor k]
    exact Nat.prime_iff.mp (hc.prime k)

end Mills
