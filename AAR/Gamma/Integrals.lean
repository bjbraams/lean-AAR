/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin–Barnes and related integrals; sums (DLMF §§5.13, 5.16)

Vertical-line integrals are acquired with a real parameter `t` in place of the
source's `c±i∞` contour, on the indicated real-part strips. The inversion
contour 5.13.1 is restricted to positive real `z`. Parametrizing `s = σ + it`
converts the factor `1/(2πi) ds` into `1/(2π) dt`.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

noncomputable section

namespace AAR.Gamma

@[dlmf 5.13.E1]
theorem mellin_barnes_beta {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hab : 0 < (a + b).re) (hσa : -a.re < σ) (hσb : σ < b.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (σ + I * t + a) * Complex.Gamma (b - (σ + I * t)) *
          (x : ℂ) ^ (-(σ + I * t)) =
      Complex.Gamma (a + b) * (x : ℂ) ^ a / (1 + (x : ℂ)) ^ (a + b) := by
  sorry

@[dlmf 5.13.E2]
theorem mellin_barnes_norm_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hbπ : b < π / 2) :
    (1 / (2 * π)) * ∫ t : ℝ,
        ‖Complex.Gamma (a + I * t)‖ ^ 2 * Real.exp ((2 * b - π) * t) =
      Real.Gamma (2 * a) / (2 * Real.sin b) ^ (2 * a) := by
  sorry

@[dlmf 5.13.E3]
theorem mellin_barnes_four {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (a + I * t) * Complex.Gamma (b + I * t) *
          Complex.Gamma (c - I * t) * Complex.Gamma (d - I * t) =
      Complex.Gamma (a + c) * Complex.Gamma (a + d) * Complex.Gamma (b + c) *
        Complex.Gamma (b + d) / Complex.Gamma (a + b + c + d) := by
  sorry

@[dlmf 5.13.E4]
theorem mellin_barnes_inv_four {a b c d : ℂ}
    (h : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, 1 /
        (Complex.Gamma (a + t) * Complex.Gamma (b + t) *
          Complex.Gamma (c - t) * Complex.Gamma (d - t)) =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  sorry

@[dlmf 5.13.E5]
theorem mellin_barnes_selberg {a : Fin 4 → ℂ} (ha : ∀ k, 0 < (a k).re) :
    (1 / (4 * π)) * ∫ t : ℝ,
        (∏ k : Fin 4, Complex.Gamma (a k + I * t) * Complex.Gamma (a k - I * t)) /
          (Complex.Gamma (2 * I * t) * Complex.Gamma (-2 * I * t)) =
      (∏ j : Fin 4, ∏ k : Fin 4, if j.val < k.val then Complex.Gamma (a j + a k) else 1) /
        Complex.Gamma (∑ k : Fin 4, a k) := by
  sorry

/-- The alternating trigamma series. It converges only conditionally, so it is stated with
ordered partial sums; Lean's unordered `tsum` of the series would be `0`. -/
@[dlmf 5.16.E1]
theorem sum_alternating_trigamma :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1))
      Filter.atTop (nhds (-π ^ 2 / 8)) := by
  sorry

@[dlmf 5.16.E2]
theorem sum_trigamma_div :
    ∑' k : ℕ, (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) = (riemannZeta 3).re := by
  sorry

end AAR.Gamma
