/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.OrthogonalPolynomials.Differential
public import AAR.Bessel.Basic
/-!
# Classical orthogonality, Rodrigues formulas, and integral identities

Integral identities from NIST DLMF Chapter 18. The Hermite and weighted Jacobi antiderivatives
are proved by the fundamental theorem of calculus. The Laguerre squared norm
is obtained from the already proved monomial moments;
other declarations below still include admitted results.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.3.T1]
theorem jacobi_norm {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, jacobiP α β (n + 1) x ^ 2 *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (2 : ℂ) ^ ((α : ℂ) + β + 1) * Gamma (n + (α : ℂ) + 2) * Gamma (n + (β : ℂ) + 2) /
      ((2 * n + α + β + 3) * (n + 1).factorial * Gamma (n + (α : ℂ) + β + 2)) := by
  sorry

/-- The squared Laguerre norm for the weight `x^α exp (-x)` on the positive ray. -/
@[dlmf 18.3.T1]
theorem laguerre_norm {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, laguerre α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (n + (α : ℂ) + 1) / n.factorial := by
  have heq : (fun x : ℝ => laguerre α n x ^ 2 * exp (-x) * (x : ℂ) ^ (α : ℂ)) =
      fun x : ℝ => ∑ k ∈ Finset.range (n + 1),
        (poch ((α : ℂ) + 1) n / n.factorial * confluentHGCoeff (-(n : ℂ)) (α + 1) k) *
          (laguerre α n x * (x : ℂ) ^ k * (x : ℂ) ^ (α : ℂ) * exp (-(x : ℂ))) := by
    funext x
    rw [pow_two]
    conv_lhs => arg 1; arg 1; arg 1; rw [laguerre_eq_sum_coeff (α : ℂ) n]
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [heq, integral_finsetSum _ (fun k _ =>
    (integrable_laguerre_mul_monomial hα n k).const_mul _)]
  simp_rw [MeasureTheory.integral_const_mul, integral_laguerre_mul_monomial hα]
  rw [Finset.sum_eq_single n]
  · have hc : ∀ j : ℕ, (α : ℂ) + 1 ≠ -j := not_neg_nat_of_re_pos (by
      simp only [add_re, ofReal_re, one_re]; linarith)
    have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hp := poch_ne_zero_of_not_neg_nat hc n
    change (poch ((α : ℂ) + 1) n / n.factorial *
      (poch (-(n : ℂ)) n / (poch ((α : ℂ) + 1) n * n.factorial))) *
      (Gamma ((α : ℂ) + n + 1) * poch (-(n : ℂ)) n / n.factorial) = _
    rw [poch_neg_coe_nat, Nat.descFactorial_self]
    have hs : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; simp
    rw [show (α : ℂ) + n + 1 = n + (α : ℂ) + 1 by ring]
    field_simp [hn, hp]
    linear_combination (Gamma (n + (α : ℂ) + 1)) * hs
  · intro k hk hkn
    have hlt : k < n := by have := Finset.mem_range.mp hk; omega
    rw [poch_neg_nat_eq_zero hlt]
    simp
  · simp

@[dlmf 18.3.T1]
theorem hermitePhys_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePhys m) : ℝ) * aeval x (hermitePhys n) * Real.exp (-(x ^ 2)) =
      if m = n then Real.sqrt Real.pi * 2 ^ n * n.factorial else 0 := by
  sorry

@[dlmf 18.3.T1]
theorem hermite_orthogonality (m n : ℕ) :
    ∫ x : ℝ, (aeval x (hermite m) : ℝ) * aeval x (hermite n) * Real.exp (-(x ^ 2) / 2) =
      if m = n then Real.sqrt (2 * Real.pi) * n.factorial else 0 := by
  sorry

@[dlmf 18.3.T1]
theorem legendre_orthogonality (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendreP m x * legendreP n x =
      if m = n then 2 / (2 * (n : ℂ) + 1) else 0 := by
  sorry

@[dlmf 18.3.T1]
theorem gegenbauer_orthogonality {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, gegenbauer lam m x * gegenbauer lam n x *
      (1 - (x : ℂ) ^ 2) ^ ((lam : ℂ) - 1 / 2) =
      if m = n then (2 : ℂ) ^ (1 - 2 * (lam : ℂ)) * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((n + lam) * Gamma (lam : ℂ) ^ 2 * n.factorial) else 0 := by
  sorry

@[dlmf 18.5.E5]
theorem jacobi_rodrigues {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ)
    {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    jacobiP α β n x = (deriv^[n] (fun t : ℝ => (1 - t) ^ (α + n) * (1 + t) ^ (β + n)) x : ℝ) /
      ((-2 : ℂ) ^ n * n.factorial * (1 - x : ℂ) ^ (α : ℂ) * (1 + x : ℂ) ^ (β : ℂ)) := by
  sorry

@[dlmf 18.5.E5]
theorem laguerre_rodrigues {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerre α n x = (Real.exp x * x ^ (-α) *
      deriv^[n] (fun t : ℝ => Real.exp (-t) * t ^ (n + α)) x / n.factorial : ℝ) := by
  sorry

@[dlmf 18.10.E2]
theorem legendre_dirichlet_mehler (n : ℕ) {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    legendreP n (Real.cos θ) = (Real.sqrt 2 / Real.pi *
      ∫ phi : ℝ in (0 : ℝ)..θ, Real.cos ((n + 1 / 2) * phi) / Real.sqrt (Real.cos phi - Real.cos θ) : ℝ) := by
  sorry

@[dlmf 18.10.E4]
theorem gegenbauer_laplace_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ : ℝ) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
        ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  sorry

@[dlmf 18.10.E5]
theorem legendre_laplace_integral (n : ℕ) (θ : ℝ) :
    legendreP n (Real.cos θ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, (Real.cos θ + I * Real.sin θ * Real.cos phi) ^ n := by
  sorry

@[dlmf 18.10.E7]
theorem hermitePhys_laplace_integral (n : ℕ) (x : ℂ) :
    aeval x (hermitePhys n) = (2 : ℂ) ^ n / Real.sqrt Real.pi *
      ∫ t : ℝ, (x + I * t) ^ n * Real.exp (-(t ^ 2)) := by
  sorry

@[dlmf 18.10.E10]
theorem hermitePhys_fourier_integral (n : ℕ) (x : ℝ) :
    (aeval (x : ℂ) (hermitePhys n) : ℂ) = (-2 * I) ^ n * exp ((x : ℂ) ^ 2) / Real.sqrt Real.pi *
      ∫ t : ℝ, Real.exp (-(t ^ 2)) * (t : ℂ) ^ n * exp (2 * I * x * t) := by
  sorry

/-- An interval antiderivative of the physicists’ Hermite polynomial. -/
@[dlmf 18.17.E3]
theorem hermitePhys_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, (aeval y (hermitePhys n) : ℝ) =
      (aeval x (hermitePhys (n + 1)) - aeval (0 : ℝ) (hermitePhys (n + 1))) / (2 * (n + 1)) := by
  have hd (t : ℝ) : HasDerivAt (fun y : ℝ => aeval y (hermitePhys (n + 1)))
      (2 * (n + 1) * aeval t (hermitePhys n)) t := by
    have h := (hermitePhys (n + 1)).hasDerivAt_aeval t
    rw [hermitePhys_derivative] at h
    simpa only [map_mul, aeval_C, map_ofNat, map_add, map_natCast, map_one] using h
  have hi : IntervalIntegrable (fun t : ℝ => 2 * (n + 1) * aeval t (hermitePhys n))
      volume 0 x := (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  rw [intervalIntegral.integral_const_mul] at h
  apply (eq_div_iff (by positivity : (2 * (n + 1) : ℝ) ≠ 0)).mpr
  nlinarith [h]

/-- An interval antiderivative of a Gaussian-weighted physicists’ Hermite polynomial. -/
@[dlmf 18.17.E4]
theorem hermitePhys_weighted_integral (n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, Real.exp (-(y ^ 2)) * (aeval y (hermitePhys (n + 1)) : ℝ) =
      aeval (0 : ℝ) (hermitePhys n) - Real.exp (-(x ^ 2)) * aeval x (hermitePhys n) := by
  let g : ℝ → ℝ := fun t => Real.exp (-(t ^ 2)) * aeval t (hermitePhys n)
  have hd (t : ℝ) : HasDerivAt (fun y => -g y)
      (Real.exp (-(t ^ 2)) * aeval t (hermitePhys (n + 1))) t := by
    have hg : DifferentiableAt ℝ g t :=
      (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2))) t).mul
        ((hermitePhys n).hasDerivAt_aeval t).differentiableAt
    have ht := hg.hasDerivAt.neg
    change HasDerivAt (fun y => -g y) (-deriv g t) t at ht
    simpa only [g, AAR.OrthogonalPolynomials.hermitePhys_weighted_derivative, neg_mul, neg_neg]
      using ht
  have hi : IntervalIntegrable
      (fun y : ℝ => Real.exp (-(y ^ 2)) * (aeval y (hermitePhys (n + 1)) : ℝ)) volume 0 x :=
    (by fun_prop : Continuous _).intervalIntegrable _ _
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) hi
  simpa only [g, zero_pow (by decide : 2 ≠ 0), neg_zero, Real.exp_zero, one_mul,
    neg_sub_neg] using h

@[dlmf 18.17.E6]
theorem legendre_product_integral (n : ℕ) (θ ψ : ℝ) :
    legendreP n (Real.cos θ) * legendreP n (Real.cos ψ) = (Real.pi : ℂ)⁻¹ *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, legendreP n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) := by
  sorry

@[dlmf 18.17.E14]
theorem laguerre_fractional_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 < x) (n : ℕ) :
    (x : ℂ) ^ ((α : ℂ) + μ) * laguerre (α + μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in (0 : ℝ)..x, (y : ℂ) ^ (α : ℂ) * laguerre α n y / Gamma (α + n + 1 : ℂ) *
        (x - y : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  sorry

@[dlmf 18.17.E15]
theorem laguerre_fractional_tail_integral {α μ x : ℝ} (hα : -1 < α) (hμ : 0 < μ) (hx : 0 ≤ x) (n : ℕ) :
    exp (-x) * laguerre α n x = ∫ y : ℝ in Set.Ioi x,
      exp (-y) * laguerre (α + μ) n y * (y - x : ℂ) ^ ((μ : ℂ) - 1) / Gamma (μ : ℂ) := by
  sorry

@[dlmf 18.17.E21_2]
theorem hermitePhys_fourier_transform (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (I * x * y)) /
      Real.sqrt Real.pi = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * (y : ℂ) ^ n := by
  sorry

@[dlmf 18.17.E21_3]
theorem hermitePhys_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (I * x * y)) /
      Real.sqrt (2 * Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 2) * aeval (y : ℂ) (hermitePhys n) := by
  sorry

@[dlmf 18.17.E28_5]
theorem laguerre_fourier_transform {α : ℝ} (hα : -1 < α) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x) * (x : ℂ) ^ (α : ℂ) * laguerre α n x * exp (I * x * y) =
      Gamma (α + n + 1 : ℂ) * (-I * y) ^ n / (n.factorial * (1 - I * y) ^ (α + n + 1 : ℂ)) := by
  sorry

@[dlmf 18.17.E35]
theorem hermitePhys_laplace_transform (n : ℕ) (z : ℂ) :
    ∫ x : ℝ, exp (-x * z) * (aeval (x : ℂ) (hermitePhys n) : ℂ) * exp (-(x : ℂ) ^ 2) =
      Real.sqrt Real.pi * (-z) ^ n * exp (z ^ 2 / 4) := by
  sorry

@[dlmf 18.17.E36]
theorem jacobi_mellin_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (z - 1) * (1 + (x : ℂ)) ^ (β : ℂ) * jacobiP α β n x =
      (2 : ℂ) ^ ((β : ℂ) + z) * Gamma z * Gamma (1 + (β : ℂ) + n) * poch (1 + α - z) n /
      (n.factorial * Gamma (1 + β + z + n)) := by
  sorry

@[dlmf 18.17.E38]
theorem legendre_even_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP (2 * n) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 / 2 - z / 2) n / (2 * poch (z / 2) (n + 1)) := by
  sorry

@[dlmf 18.17.E39]
theorem legendre_odd_mellin_transform {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP (2 * n + 1) x * (x : ℂ) ^ (z - 1) =
      (-1 : ℂ) ^ n * poch (1 - z / 2) n / (2 * poch (1 / 2 + z / 2) (n + 1)) := by
  sorry

@[dlmf 18.17.E44]
theorem legendre_singular_integral (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    ∫ t : ℝ in (-1 : ℝ)..1, (legendreP n x - legendreP n t) / (|x - t| : ℝ) =
      2 * (∑ k ∈ Finset.range n, ((k + 1 : ℂ)⁻¹)) * legendreP n x := by
  sorry

@[dlmf 18.17.E47]
theorem laguerre_convolution {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β) (hx : 0 < x) (m n : ℕ) :
    ∫ t : ℝ in (0 : ℝ)..x, (t : ℂ) ^ (α : ℂ) * laguerre α m t / laguerre α m 0 *
      (x - t : ℂ) ^ (β : ℂ) * laguerre β n (x - t) / laguerre β n 0 =
      Gamma (α + 1 : ℂ) * Gamma (β + 1 : ℂ) / Gamma (α + β + 2 : ℂ) *
      (x : ℂ) ^ (α + β + 1 : ℂ) * laguerre (α + β + 1) (m + n) x / laguerre (α + β + 1) (m + n) 0 := by
  sorry

@[dlmf 18.17.E48]
theorem hermitePhys_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ, (aeval y (hermitePhys m) : ℝ) * Real.exp (-(y ^ 2)) *
      aeval (x - y) (hermitePhys n) * Real.exp (-((x - y) ^ 2)) =
      Real.sqrt Real.pi * (2 : ℝ) ^ (-((m : ℝ) + n + 1) / 2) *
      aeval (x / Real.sqrt 2) (hermitePhys (m + n)) * Real.exp (-(x ^ 2) / 2) := by
  sorry

@[dlmf 18.17.E49]
theorem hermitePhys_triple_integral (a b c : ℕ) :
    ∫ x : ℝ, (aeval x (hermitePhys (a + b)) : ℝ) * aeval x (hermitePhys (b + c)) *
      aeval x (hermitePhys (c + a)) * Real.exp (-(x ^ 2)) =
      2 ^ (a + b + c) * (a + b).factorial * (b + c).factorial * (c + a).factorial *
      Real.sqrt Real.pi / ((a.factorial : ℝ) * b.factorial * c.factorial) := by
  sorry


/-- The weighted Jacobi antiderivative on an interval contained in `(-1,1)`. -/
@[dlmf 18.17.E1]
theorem jacobi_weighted_integral {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    2 * (n + 1 : ℂ) * (∫ y : ℝ in (0 : ℝ)..x, (1 - (y : ℂ)) ^ (α : ℂ) *
      (1 + (y : ℂ)) ^ (β : ℂ) * jacobiP α β (n + 1) y) =
      jacobiP (α + 1) (β + 1) n 0 - (1 - (x : ℂ)) ^ (α + 1 : ℂ) *
        (1 + (x : ℂ)) ^ (β + 1 : ℂ) * jacobiP (α + 1) (β + 1) n x := by
  have hreg (a b : ℝ) (m : ℕ) (t : ℝ) (ht : t ∈ Set.Ioo (-1) 1) :
      DifferentiableAt ℝ (fun y : ℝ => (1 - (y : ℂ)) ^ (a : ℂ) *
        (1 + (y : ℂ)) ^ (b : ℂ) * jacobiP a b m y) t := by
    have h1 : (1 - (t : ℂ)) ∈ slitPlane := by
      rw [show (1 - (t : ℂ)) = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.2])
    have h2 : (1 + (t : ℂ)) ∈ slitPlane := by
      rw [show (1 + (t : ℂ)) = ((1 + t : ℝ) : ℂ) by push_cast; ring]
      exact Complex.ofReal_mem_slitPlane.mpr (by linarith [ht.1])
    exact (((((hasDerivAt_id' (t : ℂ)).const_sub 1).cpow_const h1).comp_ofReal).mul
      ((((hasDerivAt_id' (t : ℂ)).const_add 1).cpow_const h2).comp_ofReal)).differentiableAt.mul
      (((analyticOnNhd_jacobiP a b m) t (Set.mem_univ _)).differentiableAt.hasDerivAt.comp_ofReal).differentiableAt
  have hmem (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : t ∈ Set.Ioo (-1) 1 := by
    rcases Set.mem_uIcc.mp ht with ht | ht <;> constructor <;>
      linarith [ht.1, ht.2, hx.1, hx.2]
  let g : ℝ → ℂ := fun y => (1 - (y : ℂ)) ^ (α + 1 : ℂ) *
    (1 + (y : ℂ)) ^ (β + 1 : ℂ) * jacobiP (α + 1) (β + 1) n y
  have hd (t : ℝ) (ht : t ∈ Set.uIcc 0 x) : HasDerivAt (fun y => -g y)
      (2 * (n + 1 : ℂ) * ((1 - (t : ℂ)) ^ (α : ℂ) *
        (1 + (t : ℂ)) ^ (β : ℂ) * jacobiP α β (n + 1) t)) t := by
    have hg : DifferentiableAt ℝ g t := by
      simpa only [g, ofReal_add, ofReal_one] using hreg (α + 1) (β + 1) n t (hmem t ht)
    have hh := hg.hasDerivAt.neg
    have he := jacobi_weighted_derivative (α := α + 1) (β := β + 1)
      (by linarith) (by linarith) n (hmem t ht)
    simp only [ofReal_add, ofReal_one, add_sub_cancel_right] at he
    change deriv g t = _ at he
    rw [he] at hh
    convert hh using 1; ring
  have hi : IntervalIntegrable (fun y : ℝ => 2 * (n + 1 : ℂ) *
      ((1 - (y : ℂ)) ^ (α : ℂ) * (1 + (y : ℂ)) ^ (β : ℂ) *
        jacobiP α β (n + 1) y)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    exact (continuousAt_const.mul (hreg α β (n + 1) t (hmem t ht)).continuousAt).continuousWithinAt
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi
  rw [intervalIntegral.integral_const_mul] at hh
  simpa [g, sub_eq_add_neg, add_comm] using hh

@[dlmf 18.17.E2]
theorem laguerre_unweighted_convolution (m n : ℕ) (x : ℝ) :
    ∫ y : ℝ in (0 : ℝ)..x, laguerre 0 m y * laguerre 0 n (x - y) =
      laguerre 0 (m + n) x - laguerre 0 (m + n + 1) x := by
  sorry

@[dlmf 18.17.E5]
theorem gegenbauer_product_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (θ ψ : ℝ) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 *
      (gegenbauer lam n (Real.cos ψ) / gegenbauer lam n 1) =
      Gamma (lam + 1 / 2 : ℂ) / (Real.sqrt Real.pi * Gamma (lam : ℂ)) *
      ∫ phi : ℝ in (0 : ℝ)..Real.pi, gegenbauer lam n
        (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) / gegenbauer lam n 1 *
          (Real.rpow (Real.sin phi) (2 * lam - 1) : ℂ) := by
  sorry

@[dlmf 18.17.E9]
theorem jacobi_fractional_integral {α β μ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hμ : 0 < μ)
    (n : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (-1) 1) :
    (1 - (x : ℂ)) ^ (α + μ : ℂ) * jacobiP (α + μ) (β - μ) n x / Gamma (α + μ + n + 1 : ℂ) =
      ∫ y : ℝ in x..1, (1 - (y : ℂ)) ^ (α : ℂ) * jacobiP α β n y / Gamma (α + n + 1 : ℂ) *
        ((y - x : ℂ) ^ (μ - 1 : ℂ) / Gamma (μ : ℂ)) := by
  sorry

@[dlmf 18.17.E16_5]
theorem gegenbauer_fourier_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam n x * exp (I * x * y) =
      2 * Real.pi * I ^ n * Gamma (n + 2 * (lam : ℂ)) * besselJ (n + (lam : ℂ)) y /
        (n.factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E21]
theorem legendre_bessel_square_integral (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (0 : ℝ)..1, legendreP n (1 - 2 * (x : ℂ) ^ 2) * Real.sin (x * y) =
      Real.pi / 2 * besselJ (n + 1 / 2 : ℂ) ((y : ℂ) / 2) ^ 2 := by
  sorry

@[dlmf 18.17.E22]
theorem hermite_fourier_eigenfunction (n : ℕ) (y : ℝ) :
    (∫ x : ℝ, exp (-(x : ℂ) ^ 2 / 4) * (aeval (x : ℂ) (hermite n) : ℂ) * exp (I * x * y / 2)) /
      (2 * Real.sqrt Real.pi) = I ^ n * exp (-(y : ℂ) ^ 2 / 4) * aeval (y : ℂ) (hermite n) := by
  sorry

@[dlmf 18.17.E23]
theorem hermite_even_cosine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n)) : ℝ) * Real.cos (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n) * Real.exp (-(y ^ 2) / 2) := by
  sorry

@[dlmf 18.17.E27]
theorem hermite_odd_sine_transform (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, Real.exp (-(x ^ 2) / 2) * (aeval x (hermite (2 * n + 1)) : ℝ) * Real.sin (x * y) =
      (-1 : ℝ) ^ n * Real.sqrt (Real.pi / 2) * y ^ (2 * n + 1) * Real.exp (-(y ^ 2) / 2) := by
  sorry

@[dlmf 18.17.E25]
theorem hermite_product_cosine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m)) * Real.cos (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m) n ((y : ℂ) ^ 2) := by
  sorry

@[dlmf 18.17.E26]
theorem hermite_product_sine_transform (m n : ℕ) (y : ℝ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-(x : ℂ) ^ 2 / 2) * (aeval (x : ℂ) (hermite n) : ℂ) *
      aeval (x : ℂ) (hermite (n + 2 * m + 1)) * Real.sin (x * y) =
      (-1 : ℂ) ^ m * Real.sqrt (Real.pi / 2) * n.factorial * (y : ℂ) ^ (2 * m + 1) *
        exp (-(y : ℂ) ^ 2 / 2) * laguerre (2 * m + 1) n ((y : ℂ) ^ 2) := by
  sorry

@[dlmf 18.17.E33]
theorem jacobi_laplace_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (z : ℂ) :
    ∫ x : ℝ in (-1 : ℝ)..1, exp (-((x : ℂ) + 1) * z) * jacobiP α β n x *
      (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) =
      (-1 : ℂ) ^ n * (2 : ℂ) ^ (α + β + n + 1 : ℂ) * Gamma (α + n + 1 : ℂ) *
      Gamma (β + n + 1 : ℂ) / (Gamma (α + β + 2 * n + 2 : ℂ) * n.factorial) *
      z ^ n * confluentM (β + n + 1 : ℂ) (α + β + 2 * n + 2 : ℂ) (-2 * z) := by
  sorry

@[dlmf 18.17.E34_5]
theorem laguerre_product_laplace_transform {α : ℝ} (hα : -1 < α) (m n : ℕ) {z : ℂ}
    (hz : -1 < z.re) (hz0 : z ≠ 0) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerre α m x * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + m + 1 : ℂ) * Gamma (α + n + 1 : ℂ) /
      (Gamma (α + 1 : ℂ) * m.factorial * n.factorial) * z ^ (m + n) /
      (z + 1) ^ (α + m + n + 1 : ℂ) * ₂F₁ (-(m : ℂ)) (-(n : ℂ)) (α + 1 : ℂ) (z⁻¹ ^ 2) := by
  sorry

/-- Corrected finite-sum form of DLMF 18.17.41 (checked 2026-09-16).
The displayed DLMF formula is incorrect: at `n = 0` its power `a^(-n-2)`
would give `Γ(z)/a²`, whereas the integral is `Γ(z)/a^z`.
The terminating ₂F₂ denominator parameters also require a shift: they should be
`(1-z-n)/2` and `(2-z-n)/2`. This sum avoids their removable singularities. -/
@[dlmf 18.17.E41]
theorem hermite_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * (aeval (x : ℂ) (hermite n) : ℂ) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n / 2 + 1), (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) *
        Gamma (z + (n - 2 * k : ℕ)) / (a : ℂ) ^ (z + (n - 2 * k : ℕ)) := by
  sorry



@[dlmf 18.10.E1]
theorem gegenbauer_dirichlet_integral {lam : ℝ} (hlam : 0 < lam) (n : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    gegenbauer lam n (Real.cos θ) / gegenbauer lam n 1 =
      (2 : ℂ) ^ (lam : ℂ) * Gamma (lam + 1 / 2 : ℂ) /
        (Real.sqrt Real.pi * Gamma (lam : ℂ)) * (Real.sin θ : ℂ) ^ (1 - 2 * lam : ℂ) *
      ∫ phi : ℝ in (0 : ℝ)..θ, (Real.cos ((n + lam) * phi) : ℂ) *
        (Real.cos phi - Real.cos θ : ℂ) ^ (lam - 1 : ℂ) := by
  sorry

@[dlmf 18.10.E3]
theorem jacobi_double_laplace_integral {α β : ℝ} (hαβ : β < α) (hβ : -1 / 2 < β)
    (n : ℕ) (θ : ℝ) :
    jacobiP α β n (Real.cos θ) / jacobiP α β n 1 =
      2 * Gamma (α + 1 : ℂ) / (Real.sqrt Real.pi * Gamma (α - β : ℂ) * Gamma (β + 1 / 2 : ℂ)) *
      ∫ r : ℝ in (0 : ℝ)..1, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((Real.cos (θ / 2) : ℂ) ^ 2 - r ^ 2 * (Real.sin (θ / 2) : ℂ) ^ 2 +
          I * r * Real.sin θ * Real.cos phi) ^ n *
        (1 - r ^ 2 : ℂ) ^ (α - β - 1 : ℂ) * (r : ℂ) ^ (2 * β + 1 : ℂ) *
        (Real.sin phi : ℂ) ^ (2 * β : ℂ) := by
  sorry

@[dlmf 18.10.E6]
theorem laguerre_double_laplace_integral {α : ℝ} (hα : -1 / 2 < α) (n : ℕ) (x : ℝ) :
    laguerre α n ((x : ℂ) ^ 2) =
      2 * (-1 : ℂ) ^ n / (Real.sqrt Real.pi * Gamma (α + 1 / 2 : ℂ) * n.factorial) *
      ∫ r : ℝ in Set.Ioi 0, ∫ phi : ℝ in (0 : ℝ)..Real.pi,
        ((x : ℂ) ^ 2 - r ^ 2 + 2 * I * x * r * Real.cos phi) ^ n * exp (-(r : ℂ) ^ 2) *
        (r : ℂ) ^ (2 * α + 1 : ℂ) * (Real.sin phi : ℂ) ^ (2 * α : ℂ) := by
  sorry

@[dlmf 18.10.E9]
theorem laguerre_bessel_integral {α : ℝ} (hα : -1 < α) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    laguerre α n x = exp (x : ℂ) * (x : ℂ) ^ (-α / 2 : ℂ) / n.factorial *
      ∫ t : ℝ in Set.Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (n + α / 2 : ℂ) *
        besselJ α (2 * Real.sqrt (x * t)) := by
  sorry

@[dlmf 18.17.E16]
theorem jacobi_fourier_transform {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (y : ℝ) :
    ∫ x : ℝ in (-1 : ℝ)..1, (1 - (x : ℂ)) ^ (α : ℂ) * (1 + (x : ℂ)) ^ (β : ℂ) *
      jacobiP α β n x * exp (I * x * y) =
      (I * y) ^ n * exp (I * y) / n.factorial * (2 : ℂ) ^ (n + α + β + 1 : ℂ) *
        Gamma (n + α + 1 : ℂ) * Gamma (n + β + 1 : ℂ) / Gamma (2 * n + α + β + 2 : ℂ) *
        confluentM (n + α + 1) (2 * n + α + β + 2) (-2 * I * y) := by
  sorry

@[dlmf 18.17.E17]
theorem gegenbauer_even_cosine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam (2 * n) x * Real.cos (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam : ℂ) * besselJ (lam + 2 * n) y /
        ((2 * n).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E18]
theorem gegenbauer_odd_sine_transform {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam (2 * n + 1) x * Real.sin (x * y) =
      (-1 : ℂ) ^ n * Real.pi * Gamma (2 * n + 2 * lam + 1 : ℂ) * besselJ (2 * n + lam + 1) y /
        ((2 * n + 1).factorial * Gamma (lam : ℂ) * (2 * y : ℂ) ^ (lam : ℂ)) := by
  sorry

@[dlmf 18.17.E19]
theorem legendre_fourier_transform (n : ℕ) {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ in (-1 : ℝ)..1, legendreP n x * exp (I * x * y) =
      I ^ n * Real.sqrt (2 * Real.pi / y) * besselJ (n + 1 / 2 : ℂ) y := by
  sorry

@[dlmf 18.17.E34]
theorem laguerre_laplace_transform {α : ℝ} (hα : -1 < α) (n : ℕ) {z : ℂ} (hz : -1 < z.re) :
    ∫ x : ℝ in Set.Ioi 0, exp (-x * z) * laguerre α n x * exp (-x) * (x : ℂ) ^ (α : ℂ) =
      Gamma (α + n + 1 : ℂ) * z ^ n / (n.factorial * (z + 1) ^ (α + n + 1 : ℂ)) := by
  sorry

@[dlmf 18.17.E37]
theorem gegenbauer_mellin_transform {lam : ℝ} (hlam : 0 < lam) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in (0 : ℝ)..1, (1 - (x : ℂ) ^ 2) ^ (lam - 1 / 2 : ℂ) *
      gegenbauer lam n x * (x : ℂ) ^ (z - 1) =
      Real.pi * (2 : ℂ) ^ (1 - 2 * lam - z) * Gamma (n + 2 * lam : ℂ) * Gamma z /
        (n.factorial * Gamma (lam : ℂ) * Gamma (1 / 2 + n / 2 + lam + z / 2) *
          Gamma (1 / 2 + z / 2 - n / 2)) := by
  sorry

/-- Finite-sum version, including parameters where the displayed hypergeometric quotient
has removable singularities. -/
@[dlmf 18.17.E40]
theorem laguerre_mellin_laplace_transform {a : ℝ} (ha : 0 < a) {α : ℂ} (hα : -1 < α.re)
    (b : ℂ) {z : ℂ} (hz : 0 < z.re) (n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exp (-a * x) * laguerre α n (b * x) * (x : ℂ) ^ (z - 1) =
      ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) * (-b) ^ k /
        ((n - k).factorial * (k.factorial : ℂ)) * Gamma (z + k) / (a : ℂ) ^ (z + k) := by
  sorry

end AAR.OrthogonalPolynomials
