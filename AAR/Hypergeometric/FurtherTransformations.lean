/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Transformations
public import AAR.Hypergeometric.Continuation

/-!
# Further transformations (DLMF §15.8)

All nonterminating series arguments are restricted to their convergence disks.
Regularized linear transformations retain singular denominator parameters.
Terminating transformations have no disk restriction, but denominator parameters
must still avoid undefined cancellations. E18 is already `gauss_quadratic` and its
inverse `kummer_quadratic`. E12 is `regularized_euler` with `c = a+b-m`.
E29 and E30 are specializations of E21 and of E13/E15, respectively.
Remaining two-term quadratic and logarithmic formulas are in `ConnectionFormulas`.
See `DLMFCoverage.md` for formulas requiring global continuation.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.8.E1]
theorem regularized_euler (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (c - a - b) * regularizedGaussHGFun (c - a) (c - b) c z :=
  regularizedGaussHGFun_euler a b c hz

@[dlmf 15.8.E1]
theorem regularized_pfaff (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (ht : ‖z / (z - 1)‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) * regularizedGaussHGFun a (c - b) c (z / (z - 1)) :=
  regularizedGaussHGFun_pfaff a b c hz ht

@[dlmf 15.8.E3]
theorem regularized_connection_one_div_one_sub
    (a b c : ℂ)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (ht : ‖1 /
    (1 - z)‖ < 1) :
    sin (Real.pi * (b - a)) / Real.pi * regularizedGaussHGFun a b c z =
      (1 - z) ^ (-a) / (Gamma b * Gamma (c - a)) * regularizedGaussHGFun a (c - b) (a - b + 1) (1 / (1 - z))
        - (1 - z) ^ (-b) / (Gamma a * Gamma (c - b)) * regularizedGaussHGFun b (c - a) (b - a + 1) (1 / (1 -
        z)) := by
  sorry

@[dlmf 15.8.E4]
theorem regularized_connection_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (ht : ‖1 - z‖ < 1) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a b (a + b - c + 1) (1 - z) / (Gamma (c - a) * Gamma (c - b)) - (1 - z) ^ (c - a
        - b) / (Gamma a * Gamma b) * regularizedGaussHGFun (c - a) (c - b) (c - a - b + 1) (1 - z) := by
  sorry

@[dlmf 15.8.E5]
theorem regularized_connection_one_sub_inv
    (a b c : ℂ)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (ht : ‖1 - 1 / z‖ < 1) :
    sin (Real.pi * (c - a - b)) / Real.pi * regularizedGaussHGFun a b c z =
      z ^ (-a) / (Gamma (c - a) * Gamma (c - b)) * regularizedGaussHGFun a (a - c + 1) (a + b - c + 1) (1 -
        1 / z) - (1 - z) ^ (c - a - b) * z ^ (a - c) / (Gamma a * Gamma b) * regularizedGaussHGFun (c - a)
        (1 - a) (c - a - b + 1) (1 - 1 / z) := by
  sorry

@[dlmf 15.8.E6]
theorem terminating_inverse
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 1 - b - m ≠ -(k : ℂ))
    (hz : z ≠ 0) :
    ₂F₁ (-m : ℂ) b c z =
      poch b m / poch c m * (-z) ^ m * ₂F₁ (-m : ℂ) (1 - c - m) (1 - b - m) (1 / z) := by
  sorry

@[dlmf 15.8.E6]
theorem terminating_inverse_one_sub
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 1 - b - m ≠ -(k : ℂ))
    (hz : z ≠ 1) :
    ₂F₁ (-m : ℂ) b c z =
      poch b m / poch c m * (1 - z) ^ m * ₂F₁ (-m : ℂ) (c - b) (1 - b - m) (1 / (1 - z)) := by
  sorry

@[dlmf 15.8.E7]
theorem terminating_one_sub
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b - c - m + 1 ≠ -(k : ℂ)) :
    ₂F₁ (-m : ℂ) b c z =
      poch (c - b) m / poch c m * ₂F₁ (-m : ℂ) b (b - c - m + 1) (1 - z) := by
  sorry

@[dlmf 15.8.E7]
theorem terminating_one_sub_inv
    {b c z : ℂ}
    (m : ℕ)
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b - c - m + 1 ≠ -(k : ℂ))
    (hz : z ≠ 0) :
    ₂F₁ (-m : ℂ) b c z =
      poch (c - b) m / poch c m * z ^ m * ₂F₁ (-m : ℂ) (1 - c - m) (b - c - m + 1) (1 - 1 / z) := by
  sorry

@[dlmf 15.8.E13]
theorem quadratic_double_denominator
    {a b z : ℂ}
    (hc : ∀ k : ℕ, 2 * b ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b + 1 / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1) :
    ₂F₁ a b (2 * b) z =
      (1 - z / 2) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) (b + 1 / 2) ((z / (2 - z)) ^ 2) := by
  sorry

@[dlmf 15.8.E14]
theorem quadratic_double_denominator_one_sub
    {a b z : ℂ}
    (hc : ∀ k : ℕ, 2 * b ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, b + 1 / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖z ^ 2 /
    (4 * z - 4)‖ < 1) :
    ₂F₁ a b (2 * b) z =
      (1 - z) ^ (-a / 2) * ₂F₁ (a / 2) (b - a / 2) (b + 1 / 2) (z ^ 2 / (4 * z - 4)) := by
  sorry

@[dlmf 15.8.E15]
theorem quadratic_well_poised_plus
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖4 * z /
    (1 + z) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 + z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) (a - b + 1) (4 * z / (1 + z) ^ 2) := by
  sorry

@[dlmf 15.8.E16]
theorem quadratic_well_poised_minus
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hw : ‖-4 * z /
    (1 - z) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 - z) ^ (-a) * ₂F₁ (a / 2) (a / 2 - b + 1 / 2) (a - b + 1) (-4 * z / (1 - z) ^ 2) := by
  sorry

@[dlmf 15.8.E17]
theorem quadratic_half_sum
    {a b z : ℂ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a b ((a + b + 1) / 2) z =
      (1 - 2 * z) ^ (-a) * ₂F₁ (a / 2) ((a + 1) / 2) ((a + b + 1) / 2) (4 * z * (z - 1) / (1 - 2 * z) ^ 2) := by
  sorry

@[dlmf 15.8.E19]
theorem quadratic_complementary
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (z - 1) /
    (1 - 2 * z) ^ 2‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - 2 * z) ^ (1 - a - c) * (1 - z) ^ (c - 1) * ₂F₁ ((a + c) / 2) ((a + c - 1) / 2) c (4 * z * (z - 1)
        / (1 - 2 * z) ^ 2) := by
  sorry

@[dlmf 15.8.E20]
theorem quadratic_complementary_four_mul
    {a c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 1 / 2)
    (hw : ‖4 * z *
    (1 - z)‖ < 1) :
    ₂F₁ a (1 - a) c z =
      (1 - z) ^ (c - 1) * ₂F₁ ((c - a) / 2) ((a + c - 1) / 2) c (4 * z * (1 - z)) := by
  sorry

@[dlmf 15.8.E21]
theorem quadratic_sqrt
    {a b z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a - 2 * b + 1 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane)
    (hw : ‖4 * z ^
    (1 / 2 : ℂ) /
    (1 + z ^
    (1 / 2 : ℂ)) ^ 2‖ < 1) :
    ₂F₁ a b (a - b + 1) z =
      (1 + z ^ (1 / 2 : ℂ)) ^ (-2 * a) * ₂F₁ a (a - b + 1 / 2) (2 * a - 2 * b + 1) (4 * z ^ (1 / 2 : ℂ) / (1
        + z ^ (1 / 2 : ℂ)) ^ 2) := by
  sorry

@[dlmf 15.8.E22]
theorem quadratic_inverse_sqrt
    {a b : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ,
    (a + b + 1) / 2 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, a + b ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a b ((a + b + 1) / 2) (x : ℂ) =
      ((((1 - 1 / x).sqrt - 1) / ((1 - 1 / x).sqrt + 1) : ℝ) : ℂ) ^ a * ₂F₁ a ((a + b) / 2) (a + b) ((4 * (1
        - 1 / x).sqrt / ((1 - 1 / x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  sorry

@[dlmf 15.8.E23]
theorem quadratic_inverse_sqrt_complementary
    {a c : ℂ}
    {x : ℝ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * c - 1 ≠ -(k : ℂ))
    (hx : -1 < x)
    (hx0 : x < 0) :
    ₂F₁ a (1 - a) c (x : ℂ) =
      (((1 - 1 / x).sqrt - 1 : ℝ) : ℂ) ^ (1 - a) * (((1 - 1 / x).sqrt + 1 : ℝ) : ℂ) ^ (a - 2 * c + 1) * ((1
        - 1 / x : ℝ) : ℂ) ^ (c - 1) * ₂F₁ (c - a) (c - 1 / 2) (2 * c - 1) ((4 * (1 - 1 / x).sqrt / ((1 - 1 /
        x).sqrt + 1) ^ 2 : ℝ) : ℂ) := by
  sorry

@[dlmf 15.8.E31]
theorem cubic_transformation
    {a z : ℂ}
    (hc : ∀ k : ℕ, 4 * a + 2 / 3 ≠ -(k : ℂ))
    (ht : ∀ k : ℕ, 2 * a + 5 / 6 ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hr : z.re < 8 / 9)
    (hw : ‖27 * z ^ 2 *
    (z - 1) /
    (9 * z - 8) ^ 2‖ < 1) :
    ₂F₁ (3 * a) (3 * a + 1 / 2) (4 * a + 2 / 3) z =
      (1 - 9 * z / 8) ^ (-2 * a) * ₂F₁ a (a + 1 / 2) (2 * a + 5 / 6) (27 * z ^ 2 * (z - 1) / (9 * z - 8) ^
        2) := by
  sorry

@[dlmf 15.8.E33]
theorem ramanujan_cubic {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 (1 - (((1 - x) / (1 + 2 * x) : ℝ) : ℂ) ^ 3) =
      (1 + 2 * (x : ℂ)) * ₂F₁ (1 / 3 : ℂ) (2 / 3) 1 ((x : ℂ) ^ 3) := by
  sorry

attribute [dlmf 15.8.E12] regularized_euler
attribute [dlmf 15.8.E29] quadratic_sqrt
attribute [dlmf 15.8.E30] quadratic_double_denominator quadratic_well_poised_plus
attribute [dlmf 15.10.E11] regularized_euler regularized_pfaff

end AAR.Hypergeometric
