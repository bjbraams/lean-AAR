/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import AAR.Confluent.Relations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Explicit formulas, symmetry, and transformations (DLMF §§18.5–18.7)

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

/-- Polynomial continuation of Laguerre in its parameter, including negative
integers. The existing `laguerre` uses a totalized hypergeometric quotient and
agrees with this definition only at regular denominator parameters. -/
@[dlmf 18.5.E12]
def laguerreExtended (α : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (α + k + 1) (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * (-x) ^ k

@[dlmf 18.5.E12]
theorem laguerreExtended_eq {α : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ)) (n : ℕ) (x : ℂ) :
    laguerreExtended α n x = laguerre α n x := by
  rw [laguerre_eq_sum hα]
  unfold laguerreExtended
  apply Finset.sum_congr rfl
  intro k _
  congr 2 <;> ring

/-- Chebyshev polynomials of the third kind, in the DLMF normalization. -/
@[dlmf 18.7.E5]
def chebyshevV (n : ℕ) (x : ℂ) : ℂ :=
  jacobiP (-1 / 2) (1 / 2) n x / jacobiP (-1 / 2) (1 / 2) n 1

/-- Chebyshev polynomials of the fourth kind, in the DLMF normalization. -/
@[dlmf 18.7.E6]
def chebyshevW (n : ℕ) (x : ℂ) : ℂ :=
  (2 * n + 1) * jacobiP (1 / 2) (-1 / 2) n x / jacobiP (1 / 2) (-1 / 2) n 1

@[dlmf 18.5.E7]
theorem jacobi_finite_sum {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiP α β n x = ∑ k ∈ Finset.range (n + 1),
      poch (n + α + β + 1) k * poch (α + k + 1) (n - k) /
        ((k.factorial : ℂ) * (n - k).factorial) * ((x - 1) / 2) ^ k := by
  have hα' : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re]
    linarith)
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  unfold jacobiP
  rw [ordinaryHypergeometric_eq_sum_neg_nat, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hck := poch_ne_zero_of_not_neg_nat hα' k
  have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hnk : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
  have hadd := poch_add (α + 1) k (n - k)
  rw [Nat.add_sub_of_le hkn] at hadd
  have hdesc : (n.descFactorial k : ℂ) * (n - k).factorial = n.factorial := by
    have he := congrArg (Nat.cast : ℕ → ℂ)
      (show n.descFactorial k * (n - k).factorial = n.factorial by
        rw [Nat.descFactorial_eq_factorial_mul_choose]
        convert Nat.choose_mul_factorial_mul_factorial hkn using 1
        ring)
    simpa [Nat.cast_mul] using he
  have hz : ((x - 1) / 2) ^ k = (-1 : ℂ) ^ k * ((1 - x) / 2) ^ k := by
    rw [← mul_pow]
    congr 1
    ring
  rw [gaussHGCoeff, poch_neg_coe_nat, hadd, eq_div_of_mul_eq hnk hdesc, hz,
    show α + k + 1 = α + 1 + k by ring]
  field_simp [hck, hn, hk0, hnk]

@[dlmf 18.5.E8]
theorem jacobi_binomial_sum {α β : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiP α β n x = ((2 : ℂ) ^ n)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      (poch (α + n - k + 1) k / k.factorial) *
      (poch (β + k + 1) (n - k) / (n - k).factorial) *
      (x - 1) ^ (n - k) * (x + 1) ^ k := by
  sorry

@[dlmf 18.5.E10]
theorem gegenbauer_finite_sum {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    gegenbauer lam n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * poch lam (n - k) /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  sorry

@[dlmf 18.5.E11]
theorem gegenbauer_cos_sum {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (θ : ℂ) :
    gegenbauer lam n (cos θ) = ∑ k ∈ Finset.range (n + 1),
      poch lam k * poch lam (n - k) / ((k.factorial : ℂ) * (n - k).factorial) *
        cos (((n : ℂ) - 2 * k) * θ) := by
  sorry

@[dlmf 18.5.E13]
theorem hermitePhys_finite_sum (n : ℕ) (x : ℂ) :
    aeval x (hermitePhys n) = (n.factorial : ℂ) * ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (2 * x) ^ (n - 2 * k) /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) := by
  sorry

@[dlmf 18.6.E1]
theorem laguerre_at_zero (α : ℂ) (n : ℕ) : laguerre α n 0 = poch (α + 1) n / n.factorial := by
  simp [laguerre]

@[dlmf 18.6.T1]
theorem jacobi_at_one {α β : ℂ} (hα : -1 < α.re) (n : ℕ) :
    jacobiP α β n 1 = poch (α + 1) n / n.factorial := by
  simp [jacobiP]

private lemma jacobi_at_one_ne_zero {α β : ℂ} (hα : -1 < α.re) (n : ℕ) :
    jacobiP α β n 1 ≠ 0 := by
  rw [jacobi_at_one hα]
  apply div_ne_zero
  · apply poch_ne_zero_of_not_neg_nat
    apply not_neg_nat_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith
  · exact Nat.cast_ne_zero.mpr n.factorial_ne_zero

@[dlmf 18.6.T1]
theorem gegenbauer_at_one {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) :
    gegenbauer lam n 1 = poch (2 * lam) n / n.factorial := by
  simp [gegenbauer]

@[dlmf 18.6.T1]
theorem hermitePhys_reflection (n : ℕ) (x : ℂ) :
    aeval (-x) (hermitePhys n) = (-1 : ℂ) ^ n * aeval x (hermitePhys n) := by
  have hp (n : ℕ) : (hermitePhys n).comp (-X) = C ((-1 : ℤ) ^ n) * hermitePhys n := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := congrArg derivative ih
      simp only [derivative_comp, derivative_neg, derivative_X, derivative_C_mul,
        neg_mul, one_mul] at hd
      have hd' := congrArg Neg.neg hd
      simp only [neg_neg] at hd'
      simp only [hermitePhys_succ, sub_comp, mul_comp, ofNat_comp, X_comp, ih, hd',
        pow_succ, map_mul, map_neg, map_one]
      ring
  have he := congrArg (aeval x : ℤ[X] → ℂ) (hp n)
  simpa [aeval_comp] using he

@[dlmf 18.6.T1]
theorem hermitePhys_even_at_zero (n : ℕ) :
    (hermitePhys (2 * n)).eval 0 = (-1 : ℤ) ^ n * ((2 * n).factorial / n.factorial : ℕ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hstep : (hermitePhys (2 * (n + 1))).eval 0 =
        -(2 * (2 * n + 1)) * (hermitePhys (2 * n)).eval 0 := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, hermitePhys_succ, hermitePhys_derivative]
      simp only [eval_sub, eval_mul, eval_ofNat, eval_X, eval_C, mul_zero, zero_mul, zero_sub]
      push_cast
      ring
    obtain ⟨q, hq⟩ := Nat.factorial_dvd_factorial (show n ≤ 2 * n by omega)
    have h1 : (2 * n).factorial / n.factorial = q := by
      rw [hq, Nat.mul_div_cancel_left _ (Nat.factorial_pos n)]
    have h2 : (2 * (n + 1)).factorial / (n + 1).factorial = 2 * (2 * n + 1) * q := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ,
        Nat.factorial_succ n, hq,
        show (2 * n + 1 + 1) * ((2 * n + 1) * (n.factorial * q)) =
          ((n + 1) * n.factorial) * (2 * (2 * n + 1) * q) by ring]
      exact Nat.mul_div_cancel_left _ (by positivity)
    rw [hstep, ih, h1, h2]
    push_cast
    ring

@[dlmf 18.6.T1]
theorem chebyshevV_at_one (n : ℕ) : chebyshevV n 1 = 1 := by
  exact div_self (jacobi_at_one_ne_zero (by norm_num) n)

@[dlmf 18.6.T1]
theorem chebyshevW_at_one (n : ℕ) : chebyshevW n 1 = 2 * n + 1 := by
  unfold chebyshevW
  exact mul_div_cancel_right₀ _ (jacobi_at_one_ne_zero (by norm_num) n)

@[dlmf 18.7.E9]
theorem legendre_eq_gegenbauer (n : ℕ) (x : ℂ) : legendreP n x = gegenbauer (1 / 2) n x := by
  norm_num [legendreP, jacobiP, gegenbauer]

@[dlmf 18.7.E13]
theorem jacobi_quadratic_even {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiP α α (2 * n) x / jacobiP α α (2 * n) 1 =
      jacobiP α (-1 / 2) n (2 * x ^ 2 - 1) / jacobiP α (-1 / 2) n 1 := by
  sorry

@[dlmf 18.7.E14]
theorem jacobi_quadratic_odd {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    jacobiP α α (2 * n + 1) x / jacobiP α α (2 * n + 1) 1 =
      x * jacobiP α (1 / 2) n (2 * x ^ 2 - 1) / jacobiP α (1 / 2) n 1 := by
  sorry

@[dlmf 18.7.E15]
theorem gegenbauer_quadratic_even {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    gegenbauer lam (2 * n) x = poch lam n / poch (1 / 2) n * jacobiP (lam - 1 / 2) (-1 / 2) n (2 * x ^ 2 - 1) := by
  sorry

@[dlmf 18.7.E16]
theorem gegenbauer_quadratic_odd {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    gegenbauer lam (2 * n + 1) x = poch lam (n + 1) / poch (1 / 2) (n + 1) * x *
      jacobiP (lam - 1 / 2) (1 / 2) n (2 * x ^ 2 - 1) := by
  sorry

/-- `4^n (1/2)_n n! = (2n)!`. -/
lemma two_pow_mul_poch_half (n : ℕ) :
    (2 : ℂ) ^ (2 * n) * poch (1 / 2) n * n.factorial = (2 * n).factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, pow_succ, pow_succ, poch_succ, Nat.factorial_succ,
      Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    linear_combination (4 * (1 / 2 + (n : ℂ)) * ((n : ℂ) + 1)) * ih

/-- `4^n (3/2)_n n! = (2n+1)!`. -/
lemma two_pow_mul_poch_three_half (n : ℕ) :
    (2 : ℂ) ^ (2 * n) * poch (3 / 2) n * n.factorial = (2 * n + 1).factorial := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      pow_succ, pow_succ, poch_succ, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    linear_combination (4 * (3 / 2 + (n : ℂ)) * ((n : ℂ) + 1)) * ih

@[dlmf 18.7.E19]
theorem hermitePhys_even_eq_laguerre (n : ℕ) (x : ℂ) :
    aeval x (hermitePhys (2 * n)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial * laguerre (-1 / 2) n (x ^ 2) := by
  have h := AAR.Confluent.hermitePhysEval_even_mul n x
  rw [AAR.Confluent.hermitePhysEval_eq_aeval] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hL : laguerre (-1 / 2) n (x ^ 2) * n.factorial =
      poch (1 / 2) n * confluentM (-(n : ℂ)) (1 / 2) (x ^ 2) := by
    unfold laguerre
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by norm_num]
    field_simp
  have hp := two_pow_mul_poch_half n
  apply mul_right_cancel₀ hf
  linear_combination h - ((-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial) * hL -
    ((-1 : ℂ) ^ n * confluentM (-(n : ℂ)) (1 / 2) (x ^ 2)) * hp

@[dlmf 18.7.E20]
theorem hermitePhys_odd_eq_laguerre (n : ℕ) (x : ℂ) :
    aeval x (hermitePhys (2 * n + 1)) = (-1 : ℂ) ^ n * 2 ^ (2 * n + 1) * n.factorial * x * laguerre (1 / 2) n (x ^ 2) := by
  have h := AAR.Confluent.hermitePhysEval_odd_mul n x
  rw [AAR.Confluent.hermitePhysEval_eq_aeval] at h
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hL : laguerre (1 / 2) n (x ^ 2) * n.factorial =
      poch (3 / 2) n * confluentM (-(n : ℂ)) (3 / 2) (x ^ 2) := by
    unfold laguerre
    rw [show (1 / 2 : ℂ) + 1 = 3 / 2 by norm_num]
    field_simp
  have hp := two_pow_mul_poch_three_half n
  apply mul_right_cancel₀ hf
  linear_combination h - ((-1 : ℂ) ^ n * 2 ^ (2 * n + 1) * n.factorial * x) * hL -
    ((-1 : ℂ) ^ n * 2 * x * confluentM (-(n : ℂ)) (3 / 2) (x ^ 2)) * hp


@[dlmf 18.3.E1]
theorem chebyshevT_discrete_orthogonality {N m n : ℕ} (hm : m ≤ N) (hn : n ≤ N)
    (hmn : m ≠ n) :
    ∑ i : Fin (N + 1),
      (Chebyshev.T ℝ m).eval (Real.cos ((i.val + 1 / 2) * Real.pi / (N + 1))) *
      (Chebyshev.T ℝ n).eval (Real.cos ((i.val + 1 / 2) * Real.pi / (N + 1))) = 0 := by
  sorry

@[dlmf 18.5.E11_1]
theorem chebyshevT_finite_sum {n : ℕ} (hn : 0 < n) (x : ℂ) :
    (Chebyshev.T ℂ n).eval x = (n : ℂ) / 2 * ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (n - k - 1).factorial /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  sorry

@[dlmf 18.5.E11_3]
theorem chebyshevU_finite_sum (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ n).eval x = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * (n - k).factorial /
        ((k.factorial : ℂ) * (n - 2 * k).factorial) * (2 * x) ^ (n - 2 * k) := by
  sorry

end AAR.OrthogonalPolynomials
