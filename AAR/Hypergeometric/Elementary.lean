/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Contiguous
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Elementary evaluations and special arguments (DLMF §15.4)

These are statement acquisitions; proofs marked `sorry` remain to be supplied.
Existing evaluations are in `Basic`, `DiffEq`, `EulerIntegral`, and `Identities`.
Powers use the principal complex logarithm. Trigonometric substitutions are stated
for real arguments, so their transformed arguments stay in the convergence disk.
Equations with removable quotients (E2, E5, E9, E10, E15, E16) are multiplied
through by their elementary denominators; thus they also hold at the removable points.
The unit-circle evaluations E33–E34 assume absolute convergence and exclude poles
of numerator Gamma factors; DLMF's broader continuation/limit interpretations are
not the totalized series definition in Mathlib.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.4.E2]
theorem log_ratio {z : ℂ} (hz : ‖z‖ < 1) :
    2 * z * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (z ^ 2) =
      log ((1 + z) / (1 - z)) := by
  have h := arctan_eq_ordinaryHypergeometric (x := -I * z) (by simpa using hz)
  have hi : -I * z * I = z := by
    calc
      _ = -(I * I) * z := by ring
      _ = z := by simp
  have hs : -((-I * z) ^ 2) = z ^ 2 := by simp [mul_pow, I_sq]
  rw [Complex.arctan, hi, hs] at h
  have hh := congrArg (fun w : ℂ => 2 * I * w) h
  ring_nf at hh
  simp only [I_sq] at hh
  convert hh.symm using 1 <;> ring

@[dlmf 15.4.E5]
theorem log_add_sqrt {z : ℂ} (hz : ‖z‖ < 1) :
    z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-z ^ 2) =
      log (z + (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 15.4.E7]
theorem even_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (z ^ 2) =
      ((1 + z) ^ (-2 * a) + (1 - z) ^ (-2 * a)) / 2 := by
  sorry

@[dlmf 15.4.E8]
theorem tan_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * cos (2 * a * x) := by
  sorry

@[dlmf 15.4.E9]
theorem odd_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (a + 1 / 2) (3 / 2) (z ^ 2) =
      (1 + z) ^ (1 - 2 * a) - (1 - z) ^ (1 - 2 * a) := by
  sorry

@[dlmf 15.4.E10]
theorem tan_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    (1 - 2 * a) * (Real.sin x : ℂ) * ₂F₁ a (a + 1 / 2) (3 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2 * a) * x) := by
  sorry

@[dlmf 15.4.E11]
theorem opposite_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ (-a) a (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a)) / 2 := by
  sorry

@[dlmf 15.4.E12]
theorem sin_sq_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ (-a) a (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos (2 * a * x) := by
  sorry

@[dlmf 15.4.E13]
theorem complementary_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (1 - a) (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a - 1) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a - 1)) / (2 *
        (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 15.4.E14]
theorem sin_sq_cos_quotient (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ a (1 - a) (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos ((2 * a - 1) * x) / (Real.cos x : ℂ) := by
  sorry

@[dlmf 15.4.E15]
theorem complementary_parameters_odd_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (1 - a) (3 / 2) (-z ^ 2) =
      ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (1 - 2 * a) - ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (1 - 2 * a) := by
  sorry

@[dlmf 15.4.E16]
theorem sin_sq_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    (2 * a - 1) * (Real.sin x : ℂ) * ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2) =
      sin ((2 * a - 1) * x) := by
  sorry

@[dlmf 15.4.E17]
theorem quadratic_binomial {a z : ℂ} (hc : ∀ k : ℕ, 1 + 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 + 2 * a) z =
      ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (-2 * a) := by
  sorry

@[dlmf 15.4.E18]
theorem quadratic_binomial_derivative {a z : ℂ} (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (2 * a) z =
      (1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (1 - 2 * a) := by
  sorry

@[dlmf 15.4.E19]
theorem successor_binomial {a b z : ℂ} (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ (a + 1) b a z =
      (1 - (1 - b / a) * z) * (1 - z) ^ (-1 - b) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have ha1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat ha 1
  have h := contiguous_shift_b (a := b) (b := a) ha hz
  have hsymm : ₂F₁ b (a + 1) a z = ₂F₁ (a + 1) b a z := by
    unfold ordinaryHypergeometric
    rw [ordinaryHypergeometricSeries_symm]
  rw [hsymm, ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha k (neg_eq_iff_eq_neg.mp hk.symm)) hz,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha1 k (neg_eq_iff_eq_neg.mp hk.symm)) hz] at h
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hp : (1 - z) ^ (-b) = (1 - z) * (1 - z) ^ (-1 - b) := by
    calc
      _ = (1 - z) ^ ((1 : ℂ) + (-1 - b)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (sub_ne_zero.mpr hz1.symm), cpow_one]
  rw [hp, show -(b + 1) = -1 - b by ring] at h
  apply mul_left_cancel₀ ha0
  field_simp [ha0]
  linear_combination -h

@[dlmf 15.4.E28]
theorem gauss_second_summation {a b : ℂ} (hc : ∀ k : ℕ, (a + b + 1) / 2 ≠ -(k : ℂ)) :
    ₂F₁ a b ((a + b + 1) / 2) (1 / 2) =
      (Real.sqrt Real.pi : ℂ) * Gamma ((a + b + 1) / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) := by
  sorry

@[dlmf 15.4.E29]
theorem gauss_second_summation_contiguous
    {a b : ℂ}
    (hc : ∀ k : ℕ,
    (a + b) / 2 + 1 ≠ -(k : ℂ))
    (hab : a ≠ b) :
    ₂F₁ a b ((a + b) / 2 + 1) (1 / 2) =
      2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma ((a + b) / 2 + 1) * (1 / (Gamma (a / 2) * Gamma ((b + 1)
        / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) := by
  sorry

@[dlmf 15.4.E30]
theorem bailey_summation {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) :
    ₂F₁ a (1 - a) b (1 / 2) =
      (2 : ℂ) ^ (1 - b) * (Real.sqrt Real.pi : ℂ) * Gamma b / (Gamma ((a + b) / 2) * Gamma ((b - a + 1) /
        2)) := by
  sorry

@[dlmf 15.4.E31]
theorem value_neg_one_third {a : ℂ} (hc : ∀ k : ℕ, 3 / 2 - 2 * a ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (3 / 2 - 2 * a) (-1 / 3) =
      (8 / 9 : ℂ) ^ (-2 * a) * Gamma (4 / 3) * Gamma (3 / 2 - 2 * a) / (Gamma (3 / 2) * Gamma (4 / 3 - 2 *
        a)) := by
  sorry

@[dlmf 15.4.E32]
theorem value_one_ninth {a : ℂ} (hc : ∀ k : ℕ, 5 / 6 + 2 * a / 3 ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (5 / 6 + 2 * a / 3) (1 / 9) =
      (Real.sqrt Real.pi : ℂ) * (3 / 4 : ℂ) ^ a * Gamma (5 / 6 + 2 * a / 3) / (Gamma (1 / 2 + a / 3) * Gamma
        (5 / 6 + a / 3)) := by
  sorry

@[dlmf 15.4.E33]
theorem value_sixth_root
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 / 3 + 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 1 / 6)
    (hg : ∀ k : ℕ, 5 / 6 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) (1 / 3 + a) (2 / 3 + 2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (16 / 27 : ℂ) ^ ((3 * a + 1) / 6) * Gamma (5 / 6
        + a) / (Gamma (2 / 3 + a) * Gamma (2 / 3)) := by
  sorry

@[dlmf 15.4.E34]
theorem value_sixth_root_contiguous
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 0)
    (hg : ∀ k : ℕ, 1 / 2 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) a (2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (2 : ℂ) ^ (2 * a) * Gamma (1 / 2 + a) / (3 : ℂ)
        ^ ((3 * a + 1) / 2) * (1 / (Gamma (1 / 3 + a) * Gamma (2 / 3)) + 1 / (Gamma (2 / 3 + a) * Gamma (1 /
        3))) := by
  sorry

@[dlmf 15.4.E27]
theorem half_argument_digamma {a : ℂ} (ha : 0 < a.re) :
    (2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2) =
      a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) := by
  sorry

/-- Ordered partial sums are essential here: the series is only conditionally convergent. -/
@[dlmf 15.4.E27]
theorem alternating_digamma {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k) atTop
      (𝓝 (a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)))) := by
  sorry

end AAR.Hypergeometric
