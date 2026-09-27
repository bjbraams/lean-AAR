/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import AAR.Gamma.Digamma
public import AAR.Gamma.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Series expansions (DLMF §5.7)

The Weierstrass/digamma series 5.7.6 is already `digamma_eq_tsum` in `Digamma.lean`.
The Taylor coefficients of `1/Γ` and the ζ-expansions of `log Γ` and `ψ` are
described here. The reciprocal Gamma Taylor series converges on all of `ℂ`;
the logarithmic and digamma expansions retain their disk and pole restrictions.
The alternating half-argument digamma series is grouped into absolutely summable pairs.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Taylor coefficients of `1/Γ` at zero, DLMF 5.7.1. -/
@[dlmf 5.7.E1]
def invGammaCoeff (k : ℕ) : ℂ :=
  iteratedDeriv k (fun z : ℂ => (Complex.Gamma z)⁻¹) 0 / k.factorial

/-- The reciprocal Gamma Taylor series at zero converges at every complex argument. -/
@[dlmf 5.7.E1]
theorem hasSum_invGammaCoeff (z : ℂ) :
    HasSum (fun k : ℕ => invGammaCoeff k * z ^ k) (Complex.Gamma z)⁻¹ := by
  simpa [invGammaCoeff, div_eq_mul_inv, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    Complex.hasSum_taylorSeries_of_entire Complex.differentiable_one_div_Gamma 0 z

/-- The reciprocal Gamma Taylor expansion on the unit disk.
The global version is `hasSum_invGammaCoeff`; this statement retains the original API. -/
@[dlmf 5.7.E1]
theorem inv_Gamma_hasSum (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => invGammaCoeff k * z ^ k) (Complex.Gamma z)⁻¹ :=
  hasSum_invGammaCoeff z

@[dlmf 5.7.E2]
theorem invGammaCoeff_recurrence {k : ℕ} (hk : 1 < k) :
    (k - 1 : ℂ) * invGammaCoeff k =
      Real.eulerMascheroniConstant * invGammaCoeff (k - 1) -
        ∑ j ∈ Finset.Icc 2 (k - 1),
          (-1 : ℂ) ^ j * (riemannZeta j) * invGammaCoeff (k - j) := by
  sorry

@[dlmf 5.7.E3]
theorem log_Gamma_one_add {z : ℂ} (hz : ‖z‖ < 1) :
    log (Complex.Gamma (1 + z)) =
      -log (1 + z) + z * (1 - Real.eulerMascheroniConstant) +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2) := by
  sorry

@[dlmf 5.7.E4]
theorem digamma_one_add_zeta {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.digamma (1 + z) =
      -Real.eulerMascheroniConstant +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) := by
  sorry

@[dlmf 5.7.E5]
theorem digamma_one_add_odd_zeta {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzm : z ≠ -1) :
    Complex.digamma (1 + z) =
      1 / (2 * z) - π / 2 * cot (π * z) + 1 / (z ^ 2 - 1) + 1 -
        Real.eulerMascheroniConstant -
        ∑' k : ℕ, (riemannZeta (2 * k + 3) - 1) * z ^ (2 * k + 2) := by
  sorry

/-- The half-argument digamma difference as an absolutely convergent series.
Adjacent terms of the classical alternating series are paired before taking `tsum`. -/
@[dlmf 5.7.E7]
theorem digamma_half_diff (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.digamma ((z + 1) / 2) - Complex.digamma (z / 2) =
      2 * ∑' k : ℕ, (1 / (2 * k + z) - 1 / (2 * k + 1 + z)) := by
  sorry

@[dlmf 5.7.E8]
theorem digamma_one_add_mul_I_im_series (y : ℝ) :
    (Complex.digamma (1 + I * y)).im = ∑' k : ℕ, y / ((k + 1 : ℝ) ^ 2 + y ^ 2) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Complex.digamma_one]
  have hx : (I * (y : ℂ)) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    exact hy this.symm
  have h := cot_series_rep' hx
  have hs : Summable fun n : ℕ => 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) :=
    summable_cotTerm hx
  have hcot := AAR.Gamma.cot_pi_mul_I y hy
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hL : ((π : ℂ) * cot (π * (I * y)) - 1 / (I * y)).im =
      1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) := by
    rw [hcot]
    have : (π : ℂ) * (-I * (Real.cosh (π * y) / Real.sinh (π * y))) - 1 / (I * y) =
        ((1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hterm : ∀ n : ℕ, (1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1))).im =
      -2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) := by
    intro n
    have hd : ((n + 1 : ℝ) ^ 2 + y ^ 2) ≠ 0 := by positivity
    have hd' : ((n : ℂ) + 1) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have h1 : I * (y : ℂ) - (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have h2 : I * (y : ℂ) + (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have : 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) =
        ((-2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (2 * I * (y : ℂ) ^ 3) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him := congrArg Complex.im h
  rw [hL, Complex.im_tsum hs] at him
  simp_rw [hterm] at him
  rw [tsum_mul_left] at him
  rw [AAR.Gamma.digamma_one_add_mul_I_im y hy]
  linear_combination (-1 / 2 : ℝ) * him

end AAR.Gamma
