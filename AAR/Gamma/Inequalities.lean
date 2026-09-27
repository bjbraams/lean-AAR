/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Inequalities (DLMF §5.6)

Real-variable inequalities and complex Gamma bounds from DLMF §5.6.
The Gamma-ratio bound has real shifts `0 ≤ a` and `1 ≤ b - a` and holds
on the open right half-plane. The final Gamma bound assumes `0 ≤ z.re`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace AAR.Gamma

@[dlmf 5.6.E1]
theorem Gamma_stirling_bounds {x : ℝ} (hx : 0 < x) :
    1 < (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x ∧
      (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x <
        Real.exp (1 / (12 * x)) := by
  sorry

@[dlmf 5.6.E2]
theorem inv_Gamma_add_inv_Gamma_inv {x : ℝ} (hx : 0 < x) :
    1 / Real.Gamma x + 1 / Real.Gamma x⁻¹ ≤ 2 := by
  sorry

@[dlmf 5.6.E3]
theorem inv_Gamma_sq_add {x : ℝ} (hx : 0 < x) :
    (1 / Real.Gamma x) ^ 2 + (1 / Real.Gamma x⁻¹) ^ 2 ≤ 2 := by
  sorry

@[dlmf 5.6.E4]
theorem Gamma_ratio_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) < (x + 1) ^ (1 - s) := by
  sorry

@[dlmf 5.6.E5]
theorem Gamma_ratio_digamma_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp ((1 - s) * Real.digamma (x + Real.sqrt s)) ≤
        Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) ≤
        Real.exp ((1 - s) * Real.digamma (x + (s + 1) / 2)) := by
  sorry

@[dlmf 5.6.E6]
theorem norm_Gamma_add_mul_I_le {x y : ℝ} (hx : 0 < x) :
    ‖Complex.Gamma (x + I * y)‖ ≤ |Real.Gamma x| := by
  have hre : (0 : ℝ) < (x + I * y : ℂ).re := by simpa using hx
  rw [Complex.Gamma_eq_integral hre, Complex.GammaIntegral,
    abs_of_pos (Real.Gamma_pos_of_pos hx), Real.Gamma_eq_integral hx]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp

@[dlmf 5.6.E7]
theorem norm_Gamma_add_mul_I_ge {x y : ℝ} (hx : 1 / 2 ≤ x) :
    ‖Complex.Gamma (x + I * y)‖ ≥ Real.sqrt (1 / Real.cosh (π * y)) * Real.Gamma x := by
  sorry

/-- A Gamma-ratio bound on the right half-plane for nonnegative real shifts
separated by at least one. These restrictions are essential in DLMF 5.6.8. -/
@[dlmf 5.6.E8]
theorem Gamma_ratio_norm_le {a b : ℝ} {z : ℂ} (hz : 0 < z.re)
    (ha : 0 ≤ a) (hba : 1 ≤ b - a) :
    ‖Complex.Gamma (z + a) / Complex.Gamma (z + b)‖ ≤ ‖z‖ ^ (-(b - a)) := by
  sorry

/-- A complex Gamma bound in the closed right half-plane, away from zero. -/
@[dlmf 5.6.E9]
theorem norm_Gamma_bound {z : ℂ} (hz : z ∈ slitPlane) (habs : 1 ≤ ‖z‖)
    (hre : 0 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤
      Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) * Real.exp (-π * |z.im| / 2) *
        Real.exp (1 / (6 * ‖z‖)) := by
  sorry

end AAR.Gamma
