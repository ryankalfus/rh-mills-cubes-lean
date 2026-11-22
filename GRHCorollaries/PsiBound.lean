module

public import Cryptids.Semantics.Riemann.ExplicitLarge
public import Cryptids.Semantics.Riemann.HorizontalBounds
public import Cryptids.Semantics.Riemann.VonMangoldtCount
public import Cryptids.Semantics.Riemann.DigammaBinet
public import Cryptids.Semantics.Riemann.WeightedStieltjes

/-!
# RH implies an explicit bound for Chebyshev's ψ

`|ψ(x) - x| ≤ (7/8) √x (log x)²` for all real `x ≥ 5000`, assuming Mathlib's `RiemannHypothesis`.
The constant 7/8 is about 22 times weaker than Schoenfeld's 1/(8π) (1976, for `x ≥ 73.2`); this
is not Schoenfeld's theorem.

All of the mathematics is in six modules vendored unmodified from
`google-deepmind/cryptids` (commit 3647718b, Apache-2.0, Copyright (c) 2026 Google LLC);
see `vendor-cryptids/NOTICE.md`. The proof below is the body of upstream's
`abs_psi_sub_self_le_seven_eighths_of_five_thousand_le`
(`Cryptids/Semantics/Riemann/Analytic.lean`), repeated here so that the register-machine
half of that file does not have to be imported. Nothing in it is ours.
-/

@[expose] public section

namespace GRHCorollaries

open ConjectureMachines.Semantics.Riemann

/-- **Explicit von Koch bound.** Under RH, `|ψ(x) - x| ≤ (7/8) √x (log x)²` for `x ≥ 5000`. -/
theorem abs_psi_sub_self_le_of_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 5000 ≤ x) :
    |Chebyshev.psi x - x| ≤ (7 / 8 : ℝ) * Real.sqrt x * (Real.log x) ^ 2 := by
  obtain ⟨⟨hx_sub, hh_pos, h6T⟩, h_rhs⟩ :=
    ExplicitLarge.explicit_rhs_le_seven_eighths_of_five_thousand_le hx
  obtain ⟨C_h, hCh, h_heights_hb⟩ :=
    HorizontalBounds.exists_zero_free_height_with_log_pow_five_bound hRH h6T
  have hN_bound : ∀ t ≥ 6,
      (WeightedStieltjes.weightedZeroCountingFunction t : ℝ) ≤
        (16 / 5 : ℝ) * t * Real.log t + (11 / 5 : ℝ) * t + (0 : ℝ) := by
    intro t ht
    rw [add_zero]
    exact VonMangoldtCount.weightedZeroCountingFunction_le_sixteen_fifths hRH ht
  have h_left_zeta : ∀ t : ℝ,
      ‖-deriv riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        (1 : ℝ) * Real.log (|t| + 2) + (85 : ℝ) := by
    intro t
    have h_eq : (((-1 / 4 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (-1 / 4 : ℂ) + (t : ℂ) * Complex.I := by push_cast; ring
    rw [h_eq, neg_div, norm_neg, ← logDeriv_apply, one_mul]
    exact DigammaBinet.norm_logDeriv_riemannZeta_leftVertical_le_eighty_five t
  have h_explicit :=
    WeightedStieltjes.abs_psi_sub_self_le_weighted_riemannVonMangoldt_six_neg_one_fourth
      hRH hx_sub hh_pos h6T (by norm_num) (by norm_num) (by norm_num) (by norm_num) hCh
      hN_bound h_left_zeta h_heights_hb
  exact h_explicit.trans h_rhs

end GRHCorollaries
