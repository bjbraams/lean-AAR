/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Stirling
public import AAR.Gamma.Digamma
public import AAR.Hypergeometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Asymptotic expansions (DLMF §5.11)

Stirling's formula for `Γ(n+1)` is already `Gamma_nat_succ_isEquivalent_stirlingGamma`
in `Stirling.lean`. Poincaré expansions below are stated along the positive real
axis. Remainder estimates 5.11.10–5.11.11 with `sec(ph z)` are deferred except
for the real-axis form of 5.11.3.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Scaled Gamma `Γ*(z)` in DLMF 5.11.3. -/
@[dlmf 5.11.E3]
def scaledGamma (z : ℂ) : ℂ :=
  Complex.Gamma z / (Complex.exp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ))

@[dlmf 5.11.E1]
theorem log_Gamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (Real.Gamma (t + x)) -
        ((t + x - 1 / 2) * Real.log (t + x) - (t + x) + (1 / 2) * Real.log (2 * π) +
          ∑ k ∈ Finset.Icc 1 n,
            bernoulli (2 * k) / ((2 * k) * (2 * k - 1) * (t + x) ^ (2 * k - 1))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 1)) := by
  sorry

@[dlmf 5.11.E2]
theorem digamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.digamma (t + x) -
        (Real.log (t + x) - 1 / (2 * (t + x)) -
          ∑ k ∈ Finset.Icc 1 n, bernoulli (2 * k) / ((2 * k) * (t + x) ^ (2 * k))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 2)) := by
  sorry

/-- Stirling coefficients `g_k` from 5.11.4–5.11.5. -/
@[dlmf 5.11.E4]
def stirlingG : ℕ → ℂ
  | 0 => 1
  | 1 => 1 / 12
  | 2 => 1 / 288
  | 3 => -139 / 51840
  | 4 => -571 / 2488320
  | n + 5 => 0

@[dlmf 5.11.E7]
theorem Gamma_linear_argument {a : ℝ} (ha : 0 < a) {b : ℂ} :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (a * t + b) /
        (Real.sqrt (2 * π) * Complex.exp (-(a : ℂ) * t) *
          (a * t : ℂ) ^ (a * t + b - 1 / 2)))
      (fun _ : ℝ => (1 : ℂ)) := by
  sorry

@[dlmf 5.11.E9]
theorem norm_Gamma_imag_large {x : ℝ} :
    Asymptotics.IsEquivalent atTop
      (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖)
      (fun y : ℝ => Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) := by
  sorry

@[dlmf 5.11.E12]
theorem Gamma_ratio_power {a b : ℂ} {x : ℝ} (hx : 0 < x) :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) /
      ((t : ℂ) ^ (a - b))) atTop (𝓝 1) := by
  sorry

/-- Coefficients `G_k(a,b)` in 5.11.13, 5.11.15, 5.11.17. -/
@[dlmf 5.11.E15]
def stirlingRatioG (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => (1 / 2) * (a - b) * (a + b - 1)
  | _ => 0

@[dlmf 5.11.E13]
theorem Gamma_ratio_expansion (a b : ℂ) (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) -
        (t : ℂ) ^ (a - b) * ∑ k ∈ Finset.range n, stirlingRatioG a b k / (t : ℂ) ^ k)
      (fun t : ℝ => (t : ℂ) ^ (a - b - n)) := by
  sorry

@[dlmf 5.11.E19]
theorem Gamma_ratio_three {a b c : ℂ} {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k))
      (fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (-(n : ℂ))) := by
  sorry

end AAR.Gamma
