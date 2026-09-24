/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.FurtherTransformations
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Quadratic and logarithmic connection formulas (DLMF §15.8)

The logarithmic formulas are stated on intersections of convergence regions.
Nonintegrality assumptions avoid products involving the totalized value of
digamma at its poles. They can later be weakened using the source's explicitly
prescribed limits. Finite sums use `range m`, including the empty sum at `m = 0`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.8.E24]
theorem quadratic_connection_well_poised
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖((z + 1) /
    (z - 1)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 - z) ^ (-a) * Gamma (a - b + 1) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma (a / 2 - b + 1)) *
        ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (1 / 2) (((z + 1) / (z - 1)) ^ 2) +
      (1 + z) * (1 - z) ^ (-a - 1) * Gamma (a - b + 1) * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (a / 2 - b
        + 1 / 2)) * ₂F₁ ((a + 1) / 2) (a / 2 - b + 1) (3 / 2) (((z + 1) / (z - 1)) ^ 2) := by
  sorry

@[dlmf 15.8.E25]
theorem quadratic_connection_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      Gamma ((a + b + 1) / 2) * Gamma (1 / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) * ₂F₁ (a / 2) (b
        / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * Gamma ((a + b + 1) / 2) * Gamma (-1 / 2) / (Gamma (a / 2) * Gamma (b / 2)) * ₂F₁ ((a +
        1) / 2) ((b + 1) / 2) (3 / 2) ((1 - 2 * z) ^ 2) := by
  sorry

@[dlmf 15.8.E26]
theorem quadratic_connection_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖(1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * Gamma c * Gamma (1 / 2) / (Gamma ((c - a + 1) / 2) * Gamma ((c + a) / 2)) * ₂F₁
        ((c - a) / 2) ((c + a - 1) / 2) (1 / 2) ((1 - 2 * z) ^ 2) +
      (1 - 2 * z) * (1 - z) ^ (c - 1) * Gamma c * Gamma (-1 / 2) / (Gamma ((c - a) / 2) * Gamma ((c + a - 1)
        / 2)) * ₂F₁ ((c - a + 1) / 2) ((c + a) / 2) (3 / 2) ((1 - 2 * z) ^ 2) := by
  sorry

@[dlmf 15.8.E27]
theorem quadratic_even_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b + 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * Gamma (1 / 2) * Gamma (a + b + 1 / 2) / (Gamma (a + 1 / 2) * Gamma (b + 1 / 2)) * ₂F₁ a b (1 / 2) (x
      : ℂ) =
      ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) + ₂F₁ (2 * a) (2 * b) (a + b + 1 / 2)
        ((1 + Real.sqrt x) / 2 : ℂ) := by
  sorry

@[dlmf 15.8.E28]
theorem quadratic_odd_connection
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, a + b - 1 / 2 ≠ -(k : ℂ))
    (hx : 0 < x)
    (hx1 : x < 1) :
    2 * (Real.sqrt x : ℂ) * Gamma (-1 / 2) * Gamma (a + b - 1 / 2) / (Gamma (a - 1 / 2) * Gamma (b - 1 / 2))
      * ₂F₁ a b (3 / 2) (x : ℂ) =
      ₂F₁ (2 * a - 1) (2 * b - 1) (a + b - 1 / 2) ((1 - Real.sqrt x) / 2 : ℂ) - ₂F₁ (2 * a - 1) (2 * b - 1)
        (a + b - 1 / 2) ((1 + Real.sqrt x) / 2 : ℂ) := by
  sorry

@[dlmf 15.8.E9]
theorem logarithmic_connection_one_div_one_sub {a c z : ℂ} (m : ℕ)
    (ha : ∀ k : ℤ, a ≠ (k : ℂ)) (hca : ∀ k : ℤ, c - a ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) :
    regularizedGaussHGFun a (a + m) c z =
      (1 - z) ^ (-a) / (Gamma (a + m) * Gamma (c - a)) *
        (∑ k ∈ Finset.range m, poch a k * poch (c - a - m) k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * ((z - 1)⁻¹) ^ k) +
      (-1 : ℂ) ^ m * (1 - z) ^ (-a - m) / (Gamma a * Gamma (c - a - m)) *
        ∑' k : ℕ, poch (a + m) k * poch (c - a) k /
          ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) * ((1 - z)⁻¹) ^ k *
          (log (1 - z) + digamma (k + 1) + digamma (k + m + 1) - digamma (a + k + m) - digamma (c - a + k))
            := by
  sorry

@[dlmf 15.8.E10]
theorem logarithmic_connection_one_sub {a b z : ℂ} (m : ℕ)
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      (1 / (Gamma (a + m) * Gamma (b + m))) *
        (∑ k ∈ Finset.range m, poch a k * poch b k * ((m - k - 1).factorial : ℂ)/
          (k.factorial : ℂ) * (z - 1) ^ k) -
      (z - 1) ^ m / (Gamma a * Gamma b) * ∑' k : ℕ,
        poch (a + m) k * poch (b + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ)) *
          (1 - z) ^ k * (log (1 - z) - digamma (k + 1) - digamma (k + m + 1)+
            digamma (a + k + m) + digamma (b + k + m)) := by
  sorry

@[dlmf 15.8.E11]
theorem logarithmic_connection_one_sub_inv {a b z : ℂ} (m : ℕ)
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hb : ∀ k : ℤ, b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : ‖1 - 1 / z‖ < 1) :
    regularizedGaussHGFun a b (a + b + m) z =
      z ^ (-a) / Gamma (a + m) *
        (∑ k ∈ Finset.range m, poch a k * ((m - k - 1).factorial : ℂ)/
          ((k.factorial : ℂ) * Gamma (b + m - k)) * (1 - 1 / z) ^ k) -
      z ^ (-a) / Gamma a * ∑' k : ℕ,
        poch (a + m) k / ((k.factorial : ℂ) * ((k + m).factorial : ℂ) * Gamma (b - k)) *
          (-1 : ℂ) ^ k * (1 - 1 / z) ^ (k + m) * (log ((1 - z) / z) - digamma (k + 1) - digamma (k + m + 1)+
            digamma (a + k + m) + digamma (b - k)) := by
  sorry

@[dlmf 15.8.E32]
theorem cubic_connection {a : ℂ} {x : ℝ} (hx : x < -1)
    (hc : ∀ k : ℕ, 2 * a + 2 / 3 ≠ -(k : ℂ)) (ha : ∀ k : ℕ, a + 1 / 3 ≠ -(k : ℂ)) :
    let z : ℂ := x
    let ζ := exp (2 * Real.pi * I / 3) * (1 - z) / (z - exp (4 * Real.pi * I / 3))
    (1 - z ^ 3) ^ a / (-z) ^ (3 * a) *
      (₂F₁ a (a + 1 / 3) (2 / 3) ((z⁻¹) ^ 3) / (Gamma (a + 2 / 3) * Gamma (2 / 3)) +
        exp (Real.pi * I / 3) / (z * Gamma a * Gamma (4 / 3)) * ₂F₁ (a + 1 / 3) (a + 2 / 3) (4 / 3) ((z⁻¹) ^
          3)) =
      (3 : ℂ) ^ (3 * a / 2 + 1 / 2) * exp (a * Real.pi * I / 2) * Gamma (a + 1 / 3) * (1 - ζ) ^ a /
        (2 * Real.pi * Gamma (2 * a + 2 / 3) * (-ζ) ^ (2 * a)) * ₂F₁ (a + 1 / 3) (3 * a) (2 * a + 2 / 3) (1
          / ζ) := by
  sorry

end AAR.Hypergeometric
