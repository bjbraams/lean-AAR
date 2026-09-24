/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Integral representations (DLMF §5.9)

Euler's integral 5.2.1 is Mathlib `Gamma_eq_integral`. Real-line Laplace,
Fourier, and Binet-type integrals are acquired below. The Hankel loop 5.9.2
and the Mellin–Barnes formulae 5.9.11, 5.9.17 are deferred.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

@[dlmf 5.9.E1]
theorem Gamma_laplace_power {μ ν z : ℂ} (hμ : 0 < μ.re) (hν : 0 < ν.re)
    (hz : 0 < z.re) :
    (1 / μ) * Complex.Gamma (ν / μ) * z ^ (-(ν / μ)) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ) ^ μ) * (t : ℂ) ^ (ν - 1) := by
  sorry

/-- Binet's integrand. -/
@[dlmf 5.9.E2_5]
def binetPhi (t : ℝ) : ℝ :=
  1 - t * Real.cot t + Real.log (t / Real.sin t)

@[dlmf 5.9.E2_5]
theorem inv_Gamma_binet {x : ℝ} (hx : 0 < x) :
    (Real.Gamma x)⁻¹ =
      Real.exp x * x ^ (1 - x) / (2 * π) *
        ∫ t : ℝ in (-π)..π, Real.exp (-x * binetPhi t) := by
  sorry

@[dlmf 5.9.E3]
theorem Gamma_gaussian {c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    c ^ (-z) * Complex.Gamma z =
      ∫ t : ℝ, ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2) := by
  sorry

@[dlmf 5.9.E4]
theorem Gamma_incomplete_sum {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ)) +
        ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  sorry

@[dlmf 5.9.E5]
theorem Gamma_truncated_exp {z : ℂ} {n : ℕ}
    (hlo : -((n + 1 : ℕ) : ℝ) < z.re) (hhi : z.re < -n) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (z - 1) *
          (Complex.exp (-(t : ℂ)) -
            ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) := by
  sorry

@[dlmf 5.9.E6]
theorem Gamma_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Real.Gamma x * Real.cos (π * x / 2) =
      ∫ t : ℝ in Set.Ioi 0, t ^ (x - 1) * Real.cos t := by
  sorry

@[dlmf 5.9.E7]
theorem Gamma_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Real.Gamma x * Real.sin (π * x / 2) =
      ∫ t : ℝ in Set.Ioi 0, t ^ (x - 1) * Real.sin t := by
  sorry

@[dlmf 5.9.E8]
theorem Gamma_cos_pow (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma (1 + 1 / n) * Real.cos (π / (2 * n)) =
      ∫ t : ℝ in Set.Ioi 0, Real.cos (t ^ n) := by
  sorry

@[dlmf 5.9.E9]
theorem Gamma_sin_pow (n : ℕ) (hn : 2 ≤ n) :
    Real.Gamma (1 + 1 / n) * Real.sin (π / (2 * n)) =
      ∫ t : ℝ in Set.Ioi 0, Real.sin (t ^ n) := by
  sorry

@[dlmf 5.9.E10]
theorem log_Gamma_binet_arctan {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        2 * ∫ t : ℝ in Set.Ioi 0,
          Real.arctan (t / x) / (Real.exp (2 * π * t) - 1) := by
  sorry

@[dlmf 5.9.E10_1]
theorem log_Gamma_binet_log {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) -
        x / π * ∫ t : ℝ in Set.Ioi 0,
          Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2) := by
  sorry

@[dlmf 5.9.E10_2]
theorem log_Gamma_binet_exp {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-x * t) * (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
  sorry

@[dlmf 5.9.E12]
theorem digamma_gauss {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)) := by
  sorry

@[dlmf 5.9.E13]
theorem digamma_binet {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x +
        ∫ t : ℝ in Set.Ioi 0,
          (1 / t - 1 / (1 - Real.exp (-t))) * Real.exp (-t * x) := by
  sorry

@[dlmf 5.9.E14]
theorem digamma_frullani {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) - (1 + t) ^ (-x)) / t := by
  sorry

@[dlmf 5.9.E15]
theorem digamma_coth {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x - 1 / (2 * x) -
        2 * ∫ t : ℝ in Set.Ioi 0,
          t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) := by
  sorry

@[dlmf 5.9.E16]
theorem digamma_add_euler {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) ∧
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t ^ (x - 1)) / (1 - t) := by
  sorry

@[dlmf 5.9.E18]
theorem eulerMascheroni_integrals :
    Real.eulerMascheroniConstant =
      -∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * Real.log t ∧
    Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0, (1 / (1 + t) - Real.exp (-t)) / t := by
  sorry

@[dlmf 5.9.E19]
theorem iteratedDeriv_Gamma {n : ℕ} {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.Gamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.log t) ^ n * Real.exp (-t) * t ^ (x - 1) := by
  sorry

@[dlmf 5.9.E20]
theorem integral_Gamma {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∫ t : ℝ in c..x, Real.Gamma t =
      ∫ t : ℝ in Set.Ioi 0,
        (t ^ (x - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  sorry

end AAR.Gamma
