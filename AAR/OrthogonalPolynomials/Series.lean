/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.Bessel.Basic
public import AAR.OrthogonalPolynomials.Differential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
/-!
# Generating functions, connection formulas, and linearization

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.12.E1]
theorem jacobi_generating_function {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => jacobiP α β n x * z ^ n)
      ((2 : ℂ) ^ (α + β) / ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ α *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β)) := by
  sorry

@[dlmf 18.12.E4]
theorem gegenbauer_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => gegenbauer lam n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-lam)) := by
  sorry

@[dlmf 18.12.E5]
theorem gegenbauer_weighted_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) (hlam0 : lam ≠ 0)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n + 2 * lam) / (2 * lam) * gegenbauer lam n x * z ^ n)
      ((1 - x * z) / (1 - 2 * x * z + z ^ 2) ^ (lam + 1)) := by
  sorry

/-- Generating function of a sequence with constant-coefficient three-term recurrence. -/
lemma hasSum_of_three_term {a : ℕ → ℂ} {p q z : ℂ}
    (hrec : ∀ n, a (n + 2) = p * a (n + 1) + q * a n) (hs : Summable fun n => a n * z ^ n)
    (hD : 1 - p * z - q * z ^ 2 ≠ 0) :
    HasSum (fun n => a n * z ^ n) ((a 0 + (a 1 - p * a 0) * z) / (1 - p * z - q * z ^ 2)) := by
  set S := ∑' n, a n * z ^ n
  have h0 := hs.hasSum
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  have h2 := (hasSum_nat_add_iff' 2).mpr h0
  have h2' : HasSum (fun n => a (n + 2) * z ^ (n + 2))
      (p * z * (S - ∑ i ∈ Finset.range 1, a i * z ^ i) + q * z ^ 2 * S) := by
    have := (h1.mul_left (p * z)).add (h0.mul_left (q * z ^ 2))
    refine this.congr_fun fun n => ?_
    simp only [hrec]
    ring
  have heq := h2.unique h2'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at heq
  convert h0 using 1
  rw [div_eq_iff hD]
  linear_combination -heq

/-- `1 - 2xz + z²` does not vanish for `|x| ≤ 1` and `‖z‖ < 1`. -/
lemma one_sub_two_mul_add_sq_ne_zero {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - 2 * x * z + z ^ 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hn : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  rcases mul_eq_zero.mp (show z.im * (z.re - x) = 0 by linarith) with hb | ha
  · rw [hb] at hre hn
    nlinarith [sq_nonneg (z.re - x)]
  · have : z.re = x := by linarith
    rw [this] at hre hn
    nlinarith

/-- Chebyshev polynomials at a real point are real. -/
lemma chebyshevT_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.T ℂ n).eval (x : ℂ) = ((Chebyshev.T ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_T (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- Chebyshev polynomials of the second kind at a real point are real. -/
lemma chebyshevU_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.U ℂ n).eval (x : ℂ) = ((Chebyshev.U ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_U (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- `|Uₙ(x)| ≤ n + 1` on `[-1, 1]`. -/
lemma abs_eval_U_real_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    |(Chebyshev.U ℝ n).eval x| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Chebyshev.U_eq_X_mul_U_add_T ℝ (n : ℤ)
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
    rw [h, eval_add, eval_mul, eval_X]
    have hT := Chebyshev.abs_eval_T_real_le_one ((n + 1 : ℕ) : ℤ) hx
    calc |x * (Chebyshev.U ℝ n).eval x + (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x|
        ≤ |x| * |(Chebyshev.U ℝ n).eval x| + 1 := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith)
      _ ≤ 1 * (n + 1) + 1 := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

@[dlmf 18.12.E8]
theorem chebyshevT_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n) ((1 - x * z) / (1 - 2 * x * z + z ^ 2)) := by
  have hs : Summable fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevT_eval_ofReal, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (by positivity) (Chebyshev.abs_eval_T_real_le_one _ hx)
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.T_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  · simp; ring
  · ring

@[dlmf 18.12.E9]
theorem chebyshevT_log_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) / (n + 1) * z ^ (n + 1))
      (-log (1 - 2 * x * z + z ^ 2)) := by
  sorry

@[dlmf 18.12.E10]
theorem chebyshevU_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n) ((1 - 2 * x * z + z ^ 2)⁻¹) := by
  have hs : Summable fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (((summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖‖z‖‖ < 1 by simpa using hz)).add
      (summable_geometric_of_lt_one (norm_nonneg z) hz))) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevU_eval_ofReal, norm_real, Real.norm_eq_abs, pow_one]
    have := abs_eval_U_real_le hx n
    nlinarith [pow_nonneg (norm_nonneg z) n]
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.U_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  simp

@[dlmf 18.12.E11]
theorem legendre_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => legendreP n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-1 / 2 : ℂ)) := by
  sorry

@[dlmf 18.12.E12]
theorem legendre_exponential_generating_function {x : ℝ} (hx : |x| ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => legendreP n x / n.factorial * z ^ n)
      (exp (x * z) * besselJ 0 (z * Real.sqrt (1 - x ^ 2))) := by
  sorry

@[dlmf 18.12.E16]
theorem hermite_generating_function (x z : ℂ) :
    HasSum (fun n : ℕ => aeval x (hermite n) / (n.factorial : ℂ) * z ^ n)
      (exp (x * z - z ^ 2 / 2)) := by
  have hf : Differentiable ℂ (fun y : ℂ => exp (-(y ^ 2 / 2))) := by fun_prop
  have hne : exp (-(x ^ 2 / 2)) ≠ 0 := exp_ne_zero _
  have hderiv (n : ℕ) (y : ℂ) :
      iteratedDeriv n (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
        (-1 : ℂ) ^ n * (aeval y (hermite n) : ℂ) * exp (-(y ^ 2 / 2)) := by
    rw [iteratedDeriv_eq_iterate, mul_assoc]
    induction n generalizing y with
    | zero => simp [hermite_zero]
    | succ n ih =>
      replace ih : deriv^[n] _ = _ := funext ih
      have hgaussian : deriv (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
          -y * exp (-(y ^ 2 / 2)) := by
        rw [deriv_cexp (by fun_prop)]
        simp [pow_two]
        ring
      rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
        pow_succ, hgaussian, hermite_succ, map_sub, map_mul, aeval_X,
        Polynomial.deriv_aeval]
      · ring
      · apply Polynomial.differentiable_aeval
      · fun_prop
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - z)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - z) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2 / 2))) x) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [hderiv, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2 / 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) *
        (exp (-(x ^ 2 / 2)))⁻¹) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - z) ^ 2 / 2)) * (exp (-(x ^ 2 / 2)))⁻¹ =
      exp (x * z - z ^ 2 / 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  rw [hval] at hs'
  convert hs' using 1
  funext n
  ring

@[dlmf 18.18.E10, dlmf 18.18.E38]
theorem laguerre_addition (α β x y : ℂ) (n : ℕ) :
    laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
  sorry

@[dlmf 18.18.E11, dlmf 18.18.E39]
theorem hermitePhys_addition (a b x y : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) :
    (aeval (a * x + b * y) (hermitePhys n) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) *
        aeval x (hermitePhys k) * aeval y (hermitePhys (n - k)) := by
  sorry

@[dlmf 18.18.E12]
theorem laguerre_multiplication {α : ℂ} (hα : -1 < α.re) (lam x : ℂ) (n : ℕ) :
    laguerre α n (lam * x) / laguerre α n 0 = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * lam ^ k * (1 - lam) ^ (n - k) * laguerre α k x / laguerre α k 0 := by
  sorry

@[dlmf 18.18.E13]
theorem hermitePhys_multiplication (lam x : ℂ) (n : ℕ) :
    aeval (lam * x) (hermitePhys n) = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * lam ^ (n - 2 * k) * (lam ^ 2 - 1) ^ k *
        aeval x (hermitePhys (n - 2 * k)) := by
  sorry

@[dlmf 18.18.E16]
theorem gegenbauer_connection {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : -1 / 2 < μ.re) (n : ℕ) (x : ℂ) :
    gegenbauer μ n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam * poch μ (n - k) / poch (lam + 1) (n - k) *
      (poch (μ - lam) k / k.factorial) * gegenbauer lam (n - 2 * k) x := by
  sorry

@[dlmf 18.18.E17]
theorem monomial_gegenbauer_expansion {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = n.factorial * ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) * gegenbauer lam (n - 2 * k) x := by
  sorry

@[dlmf 18.18.E18]
theorem laguerre_connection (α β : ℂ) (n : ℕ) (x : ℂ) :
    laguerreExtended β n x = ∑ k ∈ Finset.range (n + 1),
      poch (β - α) (n - k) / (n - k).factorial * laguerreExtended α k x := by
  unfold laguerreExtended
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
  have hv := poch_add_eq_sum (α + j + 1) (β - α) (n - j)
  rw [show α + j + 1 + (β - α) = β + j + 1 by ring] at hv
  rw [hv, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ n - j := by simp at hm; omega
  rw [show n - (j + m) = n - j - m by omega, show j + m - j = m by omega,
    Nat.cast_choose ℂ hmN]
  have h1 : ((n - j - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

@[dlmf 18.18.E19]
theorem monomial_laguerre_expansion {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x ^ n = poch (α + 1) n * ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / poch (α + 1) k * laguerre α k x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  simp_rw [laguerre_eq_sum hc, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have hterm : ∀ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
      poch (α + 1) n * (poch (-(n : ℂ)) k / poch (α + 1) k *
        (poch (α + 1 + j) (k - j) / ((k - j).factorial * j.factorial : ℂ) * (-x) ^ j)) =
      poch (α + 1) n * (-x) ^ j * poch (-(n : ℂ)) j / (poch (α + 1) j * j.factorial) *
        0 ^ (n - j) := by
    intro j hj
    have hjn : j ≤ n := by simp at hj; omega
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
    have hs := sum_poch_neg_nat_div_factorial_mul_pow (n - j) 1
    rw [sub_self] at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show j + m - j = m by omega, poch_add (α + 1) j m, poch_add (-(n : ℂ)) j m,
      show -(n : ℂ) + j = -((n - j : ℕ) : ℂ) by push_cast [Nat.cast_sub hjn]; ring]
    have h1 := hpk j
    have h2 : poch (α + 1 + j) m ≠ 0 := by
      have := hpk (j + m); rw [poch_add] at this; exact right_ne_zero_of_mul this
    have h3 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single n]
  · rw [Nat.sub_self, pow_zero, mul_one, poch_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    have h4 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hpk n]
    rw [← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  · intro j hj hjn
    have : 0 < n - j := by simp at hj; omega
    simp [zero_pow this.ne']
  · simp

@[dlmf 18.18.E20]
theorem monomial_hermitePhys_expansion (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * aeval x (hermitePhys (n - 2 * k)) := by
  sorry

@[dlmf 18.18.E23]
theorem hermitePhys_linearization (m n : ℕ) (x : ℂ) :
    (aeval x (hermitePhys m) : ℂ) * aeval x (hermitePhys n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k * k.factorial *
        aeval x (hermitePhys (m + n - 2 * k)) := by
  sorry

@[dlmf 18.18.E28]
theorem mehler_formula (x y : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (aeval (x : ℂ) (hermitePhys n) : ℂ) * aeval (y : ℂ) (hermitePhys n) /
      (2 ^ n * (n.factorial : ℂ)) * z ^ n)
      ((1 - z ^ 2) ^ (-1 / 2 : ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2))) := by
  sorry


@[dlmf 18.18.E9]
theorem legendre_addition (n : ℕ) (θ ψ phi : ℝ) :
    legendreP n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) =
      legendreP n (Real.cos θ) * legendreP n (Real.cos ψ) +
      2 * ∑ k ∈ Finset.Icc 1 n, ((n - k).factorial : ℂ) * (n + k).factorial /
        (2 ^ (2 * k) * (n.factorial : ℂ) ^ 2) * (Real.sin θ : ℂ) ^ k *
        jacobiP k k (n - k) (Real.cos θ) * (Real.sin ψ : ℂ) ^ k *
        jacobiP k k (n - k) (Real.cos ψ) * Real.cos (k * phi) := by
  sorry

@[dlmf 18.18.E22]
theorem gegenbauer_linearization {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) (x : ℂ) :
    gegenbauer lam m x * gegenbauer lam n x = ∑ k ∈ Finset.range (min m n + 1),
      (m + n + (lam : ℂ) - 2 * k) * (m + n - 2 * k).factorial /
      ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
      (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
       (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k))) * gegenbauer lam (m + n - 2 * k) x := by
  sorry


@[dlmf 18.18.E29]
theorem gegenbauer_convolution {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : 0 < μ.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), gegenbauer lam k x * gegenbauer μ (n - k) x = gegenbauer (lam + μ) n x := by
  sorry

@[dlmf 18.18.E30]
theorem gegenbauer_geometric_convolution {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) * gegenbauer lam k x * x ^ (n - k) =
      gegenbauer (lam + 1) n x := by
  sorry

/-- `U_{n+2} = 2 T_{n+2} + U_n`. -/
lemma chebyshevU_eq_two_T_add_U (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (n + 2)).eval x =
      2 * (Chebyshev.T ℂ (n + 2)).eval x + (Chebyshev.U ℂ n).eval x := by
  have hT := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.T_eq_X_mul_U_sub_U (R := ℂ) n)
  have hU := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.U_add_two (R := ℂ) n)
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at hT hU
  linear_combination hU - 2 * hT

@[dlmf 18.18.E31]
theorem chebyshev_geometric_sum (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) =
      (Chebyshev.U ℂ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n + 1 - k) =
        x * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    rw [hsum, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.U_eq_X_mul_U_add_T ℂ n)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at h
    push_cast
    linear_combination -h

@[dlmf 18.18.E32]
theorem chebyshevT_even_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k)).eval x =
      1 + (Chebyshev.U ℂ (2 * n)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_zero, Chebyshev.U_zero]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hU := chebyshevU_eq_two_T_add_U (2 * n) x
    have hU' : (Chebyshev.U ℂ (2 * (n + 1))).eval x =
        2 * (Chebyshev.T ℂ (2 * (n + 1))).eval x + (Chebyshev.U ℂ (2 * n)).eval x := by
      convert hU <;> (push_cast; ring)
    simp only [Nat.cast_succ] at hU' ⊢
    rw [hU']
    ring

@[dlmf 18.18.E33]
theorem chebyshevT_odd_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k + 1)).eval x =
      (Chebyshev.U ℂ (2 * n + 1)).eval x := by
  induction n with
  | zero => simp [Chebyshev.T_one, Chebyshev.U_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.two_mul_T_eq_U_sub_U ℂ (2 * n + 1))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 1 + 2 by push_cast; ring]
    linear_combination h

@[dlmf 18.18.E34]
theorem chebyshevU_even_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k)).eval x =
      1 - (Chebyshev.T ℂ (2 * n + 2)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_two]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 2))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 2))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E35]
theorem chebyshevU_odd_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k + 1)).eval x =
      x - (Chebyshev.T ℂ (2 * n + 3)).eval x := by
  induction n with
  | zero =>
    have h := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ 1)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h
    norm_num [Chebyshev.T_two, Chebyshev.T_one] at h
    simp [Chebyshev.U_one]
    rw [h]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 3))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 3))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 3 by push_cast; ring,
      show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 3 = 2 * (n : ℤ) + 3 + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E36]
theorem legendre_convolution (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), legendreP k x * legendreP (n - k) x = (Chebyshev.U ℂ n).eval x := by
  sorry

@[dlmf 18.18.E37]
theorem laguerre_sum (α : ℂ) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x = laguerreExtended (α + 1) n x := by
  -- the polynomial identity in `α` is proved for `Re α > 0` and extended by analyticity
  have hana : ∀ m : ℕ, AnalyticOnNhd ℂ (fun a : ℂ => laguerreExtended a m x) Set.univ := by
    intro m a _
    unfold laguerreExtended
    refine Finset.analyticAt_fun_sum (Finset.range (m + 1)) fun k _ => ?_
    have h : AnalyticAt ℂ (fun a : ℂ => poch (a + k + 1) (m - k)) a :=
      (((Polynomial.differentiable (ascPochhammer ℂ (m - k))).comp
        ((differentiable_id.add_const _).add_const _))).analyticAt a
    exact (h.div_const).mul analyticAt_const
  have key : (fun a : ℂ => ∑ k ∈ Finset.range (n + 1), laguerreExtended a k x) =
      fun a => laguerreExtended (a + 1) n x := by
    refine AAR.Hypergeometric.eq_of_eqOn_re_pos ?_ ?_ ?_
    · intro a _
      exact Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k _ => hana k a (Set.mem_univ a)
    · intro a _
      exact ((hana n) (a + 1) (Set.mem_univ _)).comp (f := fun a : ℂ => a + 1) (by fun_prop)
    intro a ha
    have h1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have h2 : ∀ k : ℕ, a + 1 + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have ha' : -1 < a.re := by linarith
    simp only [laguerreExtended_eq h1, laguerreExtended_eq h2]
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, laguerre_raise_parameter ha']
      ring
  exact congrFun key α

@[dlmf 18.18.E40]
theorem hermitePhys_even_convolution (n : ℕ) (x y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (aeval x (hermitePhys (2 * k)) : ℂ) *
      aeval y (hermitePhys (2 * n - 2 * k)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial * laguerre 0 n (x ^ 2 + y ^ 2) := by
  sorry



@[dlmf 18.12.E2]
theorem jacobi_regularized_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (x z : ℂ) :
    HasSum (fun n : ℕ => jacobiP α β n x / (Gamma (n + α + 1) * Gamma (n + β + 1)) * z ^ n)
      (regularizedHGFun (∅ : Multiset ℂ) {α + 1} ((x - 1) * z / 2) *
       regularizedHGFun (∅ : Multiset ℂ) {β + 1} ((x + 1) * z / 2)) := by
  sorry

@[dlmf 18.12.E2_5]
theorem jacobi_brafman_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ < 1)
    (hv : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ < 1) :
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  sorry

@[dlmf 18.12.E3]
theorem jacobi_weighted_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖2 * (x + 1 : ℂ) * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  sorry

@[dlmf 18.12.E3_5]
theorem jacobi_adjacent_generating_function {β : ℂ} (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch (2 * β + 2) n / poch (β + 1) n * jacobiP (β + 1) β n x * z ^ n)
      ((1 + z) / (1 - 2 * x * z + z ^ 2) ^ (β + 3 / 2)) := by
  sorry

@[dlmf 18.12.E6]
theorem gegenbauer_bessel_generating_function {lam : ℝ} (hlam : 0 < lam)
    {θ z : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) (hz : 0 < z) :
    HasSum (fun n : ℕ => gegenbauer lam n (Real.cos θ) / poch (2 * lam) n * (z : ℂ) ^ n)
      (Gamma (lam + 1 / 2 : ℂ) * exp (z * Real.cos θ : ℂ) *
        (z * Real.sin θ / 2 : ℂ) ^ (1 / 2 - lam : ℂ) * besselJ (lam - 1 / 2) (z * Real.sin θ)) := by
  sorry

@[dlmf 18.12.E7]
theorem chebyshevT_poisson_generating_function {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) * z ^ (n + 1))
      ((1 - z ^ 2) / (1 - 2 * x * z + z ^ 2) - 1) := by
  sorry

@[dlmf 18.12.E14]
theorem laguerre_bessel_generating_function {α : ℝ} (hα : -1 < α)
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    HasSum (fun n : ℕ => laguerre α n x / poch (α + 1) n * (z : ℂ) ^ n)
      (Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
        besselJ α (2 * Real.sqrt (x * z))) := by
  sorry

/-- DLMF 18.12.17 prints the incorrect convergence condition `|z| < 1`
(checked 2026-09-16). The disk is `|z| < 1/2`: already at `x = 0`,
the even coefficients are `(-1)^k * (2*k)! / (k!)²`, with radius `1/2`. -/
@[dlmf 18.12.E17]
theorem hermitePhys_half_factorial_generating_function (x : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun n : ℕ => aeval x (hermitePhys n) / ((n / 2).factorial : ℂ) * z ^ n)
      ((1 + 2 * x * z + 4 * z ^ 2) / (1 + 4 * z ^ 2) ^ (3 / 2 : ℂ) *
        exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))) := by
  sorry

end AAR.OrthogonalPolynomials
