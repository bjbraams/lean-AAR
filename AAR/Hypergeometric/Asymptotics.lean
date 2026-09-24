/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Solutions
public import AAR.Bessel.Modified
public import Mathlib.Analysis.SpecialFunctions.Arcosh

/-!
# Large-parameter asymptotics (DLMF §15.12)

The large-denominator expansions are stated along the positive real axis, with
the variable in the series disk. Remainders use Mathlib's `Asymptotics.IsBigO`.
The Bessel approximation E5–E6 uses existing `besselI` and `Real.arcosh`, with
`1 < x < 3` ensuring the hypergeometric series argument is in the disk.
E1 defines the larger complex-sector boundary; those sector domains are deferred.
E6 uses Mathlib's `Real.arcosh` (https://dlmf.nist.gov/15.12.E6); no
duplicate inverse-hyperbolic-function definition is introduced.
E7–E13 require parabolic-cylinder/Airy functions and continuous choices of
turning-point branches not yet available in this project's hypergeometric API.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.12.E2]
theorem large_denominator_expansion (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun c : ℝ => ₂F₁ a b (c : ℂ) z -
        ∑ k ∈ Finset.range m, gaussHGCoeff a b c k * z ^ k)
      (fun c : ℝ => (c : ℂ)⁻¹ ^ m) := by
  sorry

/-- The removable quotient in the generating function has value `1` at zero. -/
def expSubOneDiv (t : ℂ) : ℂ := if t = 0 then 1 else (exp t - 1) / t

/-- Generating function for the large-denominator coefficients. -/
@[dlmf 15.12.E4]
def largeDenominatorGenerating (a b c z t : ℂ) : ℂ :=
  expSubOneDiv t ^ (b - 1) * exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a)

/-- Taylor coefficients of DLMF's generating function. -/
@[dlmf 15.12.E4]
def largeDenominatorCoeff (a b c z : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (largeDenominatorGenerating a b c z) 0 / (n.factorial : ℂ)

@[dlmf 15.12.E4]
theorem large_denominator_generating_hasSum (a b c z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      HasSum (fun n : ℕ => largeDenominatorCoeff a b c z n * t ^ n)
        (largeDenominatorGenerating a b c z t) := by
  sorry

@[dlmf 15.12.E3]
theorem large_denominator_shift_expansion (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z -
        ∑ k ∈ Finset.range m, largeDenominatorCoeff a b c z k * poch b k / (l : ℂ) ^ k)
      (fun l : ℝ => (l : ℂ)⁻¹ ^ m) := by
  sorry

@[dlmf 15.12.E5]
theorem large_opposite_parameters_bessel (a b c : ℝ) {x : ℝ} (hx : 1 < x) (hx3 : x < 3) :
    let ζ : ℂ := Real.arcosh x
    ∃ r₁ r₂ : ℝ → ℂ,
      Asymptotics.IsBigO atTop r₁ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      Asymptotics.IsBigO atTop r₂ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      ∀ᶠ l : ℝ in atTop,
        regularizedGaussHGFun (a + l) (b - l) c ((1 - (x : ℂ)) / 2) =
          (2 : ℂ) ^ (((a : ℂ) + b - 1) / 2) * (x + 1 : ℂ) ^ (((c : ℂ) - a - b - 1) / 2) /
            (x - 1 : ℂ) ^ ((c : ℂ) / 2) * (ζ * sinh ζ) ^ (1 / 2 : ℂ) *
            ((l : ℂ) + a / 2 - b / 2) ^ (1 - (c : ℂ)) *
            (besselI (c - 1) (((l : ℂ) + a / 2 - b / 2) * ζ) * (1 + r₁ l) +
              besselI (c - 2) (((l : ℂ) + a / 2 - b / 2) * ζ) / (2 * (l : ℂ) + a - b) *
                (((c : ℂ) - 1 / 2) * (c - 3 / 2) * (1 / ζ - cosh ζ / sinh ζ) +
                  (2 * (c : ℂ) - a - b - 1) * (a + b - 1) / 2 * tanh (ζ / 2) + r₂ l)) := by
  sorry

end AAR.Hypergeometric
