/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Bessel.Basic
/-!
# Limits between families and Mehler–Heine formulas

Statements from NIST DLMF Chapter 18. See `DLMFCoverage.md` for the source inventory.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.6.E2]
theorem jacobi_limit_alpha {β : ℂ} (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => jacobiP a β n x / jacobiP a β n 1) atTop (𝓝 (((1 + x) / 2) ^ n)) := by
  sorry

@[dlmf 18.6.E3]
theorem jacobi_limit_beta {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => jacobiP α b n x / jacobiP α b n (-1)) atTop (𝓝 (((1 - x) / 2) ^ n)) := by
  sorry

@[dlmf 18.6.E4]
theorem gegenbauer_limit_monomial (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => gegenbauer a n x / gegenbauer a n 1) atTop (𝓝 (x ^ n)) := by
  sorry

@[dlmf 18.6.E5]
theorem laguerre_limit_monomial (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => laguerre a n (a * x) / laguerre a n 0) atTop (𝓝 ((1 - x) ^ n)) := by
  sorry

@[dlmf 18.7.E21]
theorem jacobi_limit_laguerre {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => jacobiP α b n (1 - 2 * x / b)) atTop (𝓝 (laguerre α n x)) := by
  sorry

@[dlmf 18.7.E22]
theorem jacobi_limit_laguerre_reflected {β : ℂ} (hβ : -1 < β.re) (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => jacobiP a β n (2 * x / a - 1)) atTop (𝓝 ((-1 : ℂ) ^ n * laguerre β n x)) := by
  sorry

@[dlmf 18.7.E23]
theorem jacobi_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * jacobiP a a n (x / Real.sqrt a)) atTop
      (𝓝 (aeval x (hermitePhys n) / ((2 : ℂ) ^ n * n.factorial))) := by
  sorry

@[dlmf 18.7.E24]
theorem gegenbauer_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt a : ℂ)⁻¹ ^ n * gegenbauer a n (x / Real.sqrt a)) atTop
      (𝓝 (aeval x (hermitePhys n) / (n.factorial : ℂ))) := by
  sorry

@[dlmf 18.7.E25]
theorem gegenbauer_limit_chebyshev (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℂ => (n + a) / a * gegenbauer a n x) (𝓝[≠] 0)
      (𝓝 (if n = 0 then 1 else 2 * (Chebyshev.T ℂ n).eval x)) := by
  sorry

@[dlmf 18.7.E26]
theorem laguerre_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 / a) : ℂ) ^ n * laguerre a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop
      (𝓝 ((-1 : ℂ) ^ n / n.factorial * aeval x (hermitePhys n))) := by
  sorry

@[dlmf 18.11.E5]
theorem jacobi_mehler_heine {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * jacobiP α β n (cos ((z : ℂ) / n))) atTop
      (𝓝 ((Real.rpow (2 / z) α : ℂ) * besselJ α z)) := by
  sorry

@[dlmf 18.11.E6]
theorem laguerre_mehler_heine {α : ℝ} (hα : -1 < α) {z : ℝ} (hz : 0 < z) :
    Tendsto (fun n : ℕ => (Real.rpow (n : ℝ) (-α) : ℂ) * laguerre α n ((z : ℂ) / n)) atTop
      (𝓝 ((Real.rpow z (-α / 2) : ℂ) * besselJ α (2 * Real.sqrt z))) := by
  sorry

@[dlmf 18.11.E7]
theorem hermite_even_mehler_heine (z : ℂ) :
    Tendsto (fun n : ℕ => (-1 : ℂ) ^ n * Real.sqrt n / (2 ^ (2 * n) * (n.factorial : ℂ)) *
      aeval (z / (2 * (Real.sqrt n : ℂ))) (hermitePhys (2 * n))) atTop (𝓝 (cos z / (Real.sqrt Real.pi : ℂ))) := by
  sorry

@[dlmf 18.11.E8]
theorem hermite_odd_mehler_heine (z : ℂ) :
    Tendsto (fun n : ℕ => (-1 : ℂ) ^ n / (2 ^ (2 * n) * (n.factorial : ℂ)) *
      aeval (z / (2 * (Real.sqrt n : ℂ))) (hermitePhys (2 * n + 1))) atTop (𝓝 (2 * sin z / (Real.sqrt Real.pi : ℂ))) := by
  sorry


end AAR.OrthogonalPolynomials
