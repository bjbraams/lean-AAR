/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import AAR.Confluent.Recurrence
public import AAR.Bessel.Basic
public import AAR.Bessel.Modified
public import AAR.OrthogonalPolynomials.Classical
public import AAR.OrthogonalPolynomials.Hahn

/-!
# Relations to other functions (DLMF §§13.6, 13.18)

Elementary, error-function, incomplete-gamma, Bessel, Hermite, Laguerre, and
Charlier identities are recorded against existing project definitions.
Parabolic-cylinder identities 13.6.12–13.6.15 and 13.18.11–13.18.13, Airy
identities 13.6.11 and 13.18.10, and Coulomb-wave identities in 13.6(vii) are
deferred: those functions are not yet in the project's API.
-/

@[expose] public section

open Complex Polynomial Filter
open scoped Real Topology ENNReal

noncomputable section

namespace AAR.Confluent

/-- Physicists' Hermite polynomial evaluated in `ℂ`. -/
def hermitePhysEval (n : ℕ) (z : ℂ) : ℂ :=
  eval z ((hermitePhys n).map (Int.castRingHom ℂ))

@[dlmf 13.6.E2]
theorem confluentM_one_two (z : ℂ) (hz : z ≠ 0) :
    confluentM 1 2 (2 * z) = exp z * sinh z / z := by
  have h1 : ∀ k : ℕ, (1 : ℂ) ≠ -k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have h := AAR.Confluent.confluentM_contiguous_shift_a (a := 1) (b := 1) h1 (z := 2 * z)
  rw [sub_self, confluentM_of_zero_param, confluentM_self h1, one_add_one_eq_two] at h
  have key : 2 * z * confluentM 1 2 (2 * z) = exp (2 * z) - 1 := by linear_combination -h
  have h2 := Complex.two_sinh z
  have hexp : exp (2 * z) = exp z * exp z := by rw [← exp_add]; ring_nf
  have hexpneg : exp z * exp (-z) = 1 := by rw [← exp_add]; simp
  rw [eq_div_iff hz]
  linear_combination (1 / 2 : ℂ) * key - (exp z / 2) * h2 + (1 / 2 : ℂ) * hexp +
    (1 / 2 : ℂ) * hexpneg

/-- Tricomi U at zero first parameter, including integer second parameters. -/
@[dlmf 13.6.E3]
theorem confluentU_of_zero_param (b z : ℂ) : confluentU 0 b z = 1 :=
  confluentU_zero b z

/-- The elementary shifted-parameter specialization of the continued Tricomi function. -/
@[dlmf 13.6.E4]
theorem confluentU_shift_one (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    confluentU a (a + 1) z = z ^ (-a) := by
  sorry

/-- Upper incomplete gamma via Tricomi's `U`, from DLMF 13.6.6. -/
def GammaInc (s z : ℂ) : ℂ := exp (-z) * confluentU (1 - s) (1 - s) z

/-- Lower incomplete-Gamma identities with a regular denominator for Kummer M. -/
@[dlmf 13.6.E5]
theorem confluentM_lowerIncompleteGamma (a z : ℂ) (ha : a ≠ 0) {w : ℂ}
    (hw : w ∈ slitPlane) (hz : w = z) (hden : ∀ k : ℕ, a + 1 ≠ -k) :
    confluentM a (a + 1) (-z) = exp (-z) * confluentM 1 (a + 1) z ∧
      confluentM a (a + 1) (-z) = a * z ^ (-a) * lowerIncompleteGamma a z := by
  sorry

/-- Incomplete-Gamma relations for U at noninteger parameter. -/
@[dlmf 13.6.E6]
theorem confluentU_upperIncompleteGamma (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℤ, a ≠ k) :
    confluentU a a z = z ^ (1 - a) * confluentU 1 (2 - a) z ∧
      confluentU a a z = exp z * GammaInc (1 - a) z := by
  refine ⟨?_, ?_⟩
  · simpa using confluentU_kummer_transform a a hz ha
  · unfold GammaInc
    have : (1 : ℂ) - (1 - a) = a := by ring
    simp only [this]
    rw [← mul_assoc, ← exp_add]
    convert (one_mul (confluentU a a z)).symm using 2
    convert exp_zero using 2
    ring

@[dlmf 13.6.E7]
theorem confluentM_errorFn {z : ℂ} (hz : z ≠ 0) :
    confluentM (1 / 2) (3 / 2) (-(z ^ 2)) = (Real.sqrt π : ℂ) / (2 * z) * errorFn z := by
  unfold errorFn
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    ofReal_ne_zero.2 (ne_of_gt (Real.sqrt_pos.2 Real.pi_pos))
  field_simp [hz, hπ]
  try ring

/-- Tricomi U at `a = b = 1/2` and complementary error function. The left side depends only on `z ^
2`, so the identity needs `0 < Re z`. -/
@[dlmf 13.6.E8]
theorem confluentU_erfcFn {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    confluentU (1 / 2) (1 / 2) (z ^ 2) = (Real.sqrt π : ℂ) * exp (z ^ 2) * erfcFn z := by
  sorry

@[dlmf 13.6.E9]
theorem confluentM_besselI (ν z : ℂ) (hz : z ∈ slitPlane) (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    confluentM (ν + 1 / 2) (2 * ν + 1) (2 * z) =
      Gamma (1 + ν) * exp z * (z / 2) ^ (-ν) * besselI ν z := by
  sorry

@[dlmf 13.6.E10]
theorem confluentU_besselK (ν z : ℂ) (hz : z ∈ slitPlane) :
    confluentU (ν + 1 / 2) (2 * ν + 1) (2 * z) =
      1 / (Real.sqrt π : ℂ) * exp z * (2 * z) ^ (-ν) * besselK ν z := by
  sorry

@[dlmf 13.6.E11_1]
theorem confluentM_besselI_sum (ν : ℂ) (n : ℕ) (z : ℂ)
    (hν : ∀ k : ℕ, 2 * ν + 1 + n ≠ -k) (hz : z ∈ slitPlane) :
    confluentM (ν + 1 / 2) (2 * ν + 1 + n) (2 * z) =
      Gamma ν * exp z * (z / 2) ^ (-ν) *
        ∑ k ∈ Finset.range (n + 1),
          poch (-(n : ℂ)) k * poch (2 * ν) k * (ν + k) /
            (poch (2 * ν + 1 + n) k * k.factorial) * besselI (ν + k) z := by
  sorry

@[dlmf 13.6.E11_2]
theorem confluentM_besselI_sum_neg (ν : ℂ) (n : ℕ) (z : ℂ)
    (hν : ∀ k : ℕ, 2 * ν + 1 - n ≠ -k) (hz : z ∈ slitPlane) :
    confluentM (ν + 1 / 2) (2 * ν + 1 - n) (2 * z) =
      Gamma (ν - n) * exp z * (z / 2) ^ (n - ν : ℂ) *
        ∑ k ∈ Finset.range (n + 1),
          (-1 : ℂ) ^ k * poch (-(n : ℂ)) k * poch (2 * ν - 2 * n) k * (ν - n + k) /
            (poch (2 * ν + 1 - n) k * k.factorial) * besselI (ν + k - n) z := by
  sorry

/-- `hermitePhysEval` is the algebra evaluation. -/
lemma hermitePhysEval_eq_aeval (n : ℕ) (z : ℂ) :
    hermitePhysEval n z = Polynomial.aeval z (hermitePhys n) := by
  rw [hermitePhysEval, Polynomial.eval_map, Polynomial.aeval_def, algebraMap_int_eq]

lemma hermitePhysEval_zero (z : ℂ) : hermitePhysEval 0 z = 1 := by
  simp [hermitePhysEval]

lemma hermitePhysEval_one (z : ℂ) : hermitePhysEval 1 z = 2 * z := by
  simp [hermitePhysEval, hermitePhys_one]

lemma hermitePhysEval_two (z : ℂ) : hermitePhysEval 2 z = 4 * z ^ 2 - 2 := by
  simp [hermitePhysEval]
  ring

/-- The three-term recurrence `H_{k+2} = 2z H_{k+1} - 2(k+1) H_k`. -/
lemma hermitePhysEval_succ_succ (k : ℕ) (z : ℂ) :
    hermitePhysEval (k + 2) z =
      2 * z * hermitePhysEval (k + 1) z - 2 * (k + 1) * hermitePhysEval k z := by
  show hermitePhysEval (k + 1 + 1) z = _
  unfold hermitePhysEval
  rw [hermitePhys_succ (k + 1), hermitePhys_derivative]
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.map_C, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C, Int.coe_castRingHom]
  push_cast
  ring

lemma hermitePhysEval_three (z : ℂ) : hermitePhysEval 3 z = 8 * z ^ 3 - 12 * z := by
  rw [show (3 : ℕ) = 1 + 2 from rfl, hermitePhysEval_succ_succ, hermitePhysEval_two,
    hermitePhysEval_one]
  push_cast
  ring

/-- The two-step recurrence `H_{k+4} = (4z² - 4k - 10) H_{k+2} - 4(k+1)(k+2) H_k`. -/
lemma hermitePhysEval_two_step (k : ℕ) (z : ℂ) :
    hermitePhysEval (k + 4) z =
      (4 * z ^ 2 - (4 * k + 10)) * hermitePhysEval (k + 2) z -
        4 * (k + 1) * (k + 2) * hermitePhysEval k z := by
  have r1 := hermitePhysEval_succ_succ (k + 2) z
  have r2 := hermitePhysEval_succ_succ (k + 1) z
  have r3 := hermitePhysEval_succ_succ k z
  rw [show k + 2 + 2 = k + 4 by ring, show k + 2 + 1 = k + 3 by ring] at r1
  rw [show k + 1 + 2 = k + 3 by ring, show k + 1 + 1 = k + 2 by ring] at r2
  push_cast at r1 r2 r3
  linear_combination r1 + 2 * z * r2 + 2 * ((k : ℂ) + 2) * r3

lemma half_ne_neg_nat : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k hk => by
  have := congrArg Complex.re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma three_half_ne_neg_nat : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k hk => by
  have := congrArg Complex.re hk
  simp at this
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- 13.6.16 in division-free form: `H_{2n}(z) · n! = (-1)^n (2n)! M(-n, 1/2, z²)`. -/
theorem hermitePhysEval_even_mul (n : ℕ) (z : ℂ) :
    hermitePhysEval (2 * n) z * n.factorial =
      (-1 : ℂ) ^ n * (2 * n).factorial * confluentM (-(n : ℂ)) (1 / 2) (z ^ 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermitePhysEval_zero, confluentM_of_zero_param]
  | one =>
    rw [confluentM_eq_sum_neg_nat]
    simp [hermitePhysEval_two, Finset.sum_range_succ, poch_zero, poch_one]
    ring
  | more n ih0 ih1 =>
    have K := confluentM_contiguous_a (a := -((n : ℂ) + 1)) (b := 1 / 2) (z := z ^ 2)
      half_ne_neg_nat
    rw [show -((n : ℂ) + 1) - 1 = -((n : ℂ) + 2) by ring,
      show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring] at K
    have hrec := hermitePhysEval_two_step (2 * n) z
    rw [show 2 * n + 4 = 2 * (n + 2) by ring, show 2 * n + 2 = 2 * (n + 1) by ring] at hrec
    have hf4 : ((2 * (n + 2)).factorial : ℂ) =
        (2 * n + 4) * (2 * n + 3) * (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 2) = 2 * n + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hf2 : ((2 * (n + 1)).factorial : ℂ) = (2 * n + 2) * (2 * n + 1) * (2 * n).factorial := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2, hn1] at ih1
    rw [hf4, hn2]
    push_cast at ih0 ih1 hrec ⊢
    linear_combination (((n : ℂ) + 2) * (n + 1) * (n.factorial : ℂ)) * hrec +
      (((n : ℂ) + 2) * (4 * z ^ 2 - 8 * n - 10)) * ih1 -
      (8 * ((n : ℂ) + 1) ^ 2 * (2 * n + 1) * (n + 2)) * ih0 -
      (4 * (-1 : ℂ) ^ n * ((2 * n).factorial : ℂ) * (2 * n + 1) * (n + 2) * (2 * n + 2)) * K

/-- 13.6.17 in division-free form: `H_{2n+1}(z) · n! = (-1)^n (2n+1)! (2z) M(-n, 3/2, z²)`. -/
theorem hermitePhysEval_odd_mul (n : ℕ) (z : ℂ) :
    hermitePhysEval (2 * n + 1) z * n.factorial =
      (-1 : ℂ) ^ n * (2 * n + 1).factorial * (2 * z) * confluentM (-(n : ℂ)) (3 / 2) (z ^ 2) := by
  induction n using Nat.twoStepInduction with
  | zero => simp [hermitePhysEval_one, confluentM_of_zero_param]
  | one =>
    rw [confluentM_eq_sum_neg_nat, show 2 * 1 + 1 = 3 from rfl, hermitePhysEval_three]
    simp [Finset.sum_range_succ, poch_zero, poch_one]
    ring
  | more n ih0 ih1 =>
    have K := confluentM_contiguous_a (a := -((n : ℂ) + 1)) (b := 3 / 2) (z := z ^ 2)
      three_half_ne_neg_nat
    rw [show -((n : ℂ) + 1) - 1 = -((n : ℂ) + 2) by ring,
      show -((n : ℂ) + 1) + 1 = -(n : ℂ) by ring] at K
    have hrec := hermitePhysEval_two_step (2 * n + 1) z
    rw [show 2 * n + 1 + 4 = 2 * (n + 2) + 1 by ring,
      show 2 * n + 1 + 2 = 2 * (n + 1) + 1 by ring] at hrec
    have hf4 : ((2 * (n + 2) + 1).factorial : ℂ) =
        (2 * n + 5) * (2 * n + 4) * (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 2) + 1 = 2 * n + 1 + 1 + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hf2 : ((2 * (n + 1) + 1).factorial : ℂ) =
        (2 * n + 3) * (2 * n + 2) * (2 * n + 1).factorial := by
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn2 : ((n + 2).factorial : ℂ) = (n + 2) * (n + 1) * n.factorial := by
      rw [show n + 2 = n + 1 + 1 by ring]
      simp only [Nat.factorial_succ]
      push_cast
      ring
    have hn1 : ((n + 1).factorial : ℂ) = (n + 1) * n.factorial := by
      simp only [Nat.factorial_succ]
      push_cast
      ring
    rw [hf2, hn1] at ih1
    rw [hf4, hn2]
    push_cast at ih0 ih1 hrec ⊢
    linear_combination (((n : ℂ) + 2) * (n + 1) * (n.factorial : ℂ)) * hrec +
      (((n : ℂ) + 2) * (4 * z ^ 2 - 8 * n - 14)) * ih1 -
      (8 * ((n : ℂ) + 1) ^ 2 * (2 * n + 3) * (n + 2)) * ih0 -
      (4 * (-1 : ℂ) ^ n * ((2 * n + 1).factorial : ℂ) * (2 * z) * (2 * n + 3) * (n + 2) *
        (2 * n + 2)) * K

@[dlmf 13.6.E16]
theorem confluentM_hermite_even (n : ℕ) (z : ℂ) :
    confluentM (-(n : ℂ)) (1 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n).factorial * hermitePhysEval (2 * n) z := by
  have h := hermitePhysEval_even_mul n z
  have hsq : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((2 * n).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have this : ((2 * n).factorial : ℂ) * confluentM (-(n : ℂ)) (1 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial * hermitePhysEval (2 * n) z := by
    linear_combination (-(-1 : ℂ) ^ n) * h -
      (((2 * n).factorial : ℂ) * confluentM (-(n : ℂ)) (1 / 2) (z ^ 2)) * hsq
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hf]
  linear_combination -this

@[dlmf 13.6.E17]
theorem confluentM_hermite_odd (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    confluentM (-(n : ℂ)) (3 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / ((2 * n + 1).factorial * 2 * z) *
        hermitePhysEval (2 * n + 1) z := by
  have h := hermitePhysEval_odd_mul n z
  have hsq : (-1 : ℂ) ^ n * (-1) ^ n = 1 := by
    rw [← mul_pow]
    simp
  have hf : ((2 * n + 1).factorial : ℂ) * 2 * z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)) two_ne_zero) hz
  have this : ((2 * n + 1).factorial : ℂ) * 2 * z * confluentM (-(n : ℂ)) (3 / 2) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial * hermitePhysEval (2 * n + 1) z := by
    linear_combination (-(-1 : ℂ) ^ n) * h -
      (((2 * n + 1).factorial : ℂ) * 2 * z * confluentM (-(n : ℂ)) (3 / 2) (z ^ 2)) * hsq
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff hf]
  linear_combination -this

/-- Tricomi U and Hermite polynomials. The left side depends only on `z ^ 2`, so the identity needs
`0 < Re z`. -/
@[dlmf 13.6.E18]
theorem confluentU_hermite (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    confluentU (1 / 2 - n / 2) (3 / 2) (z ^ 2) =
      (2 : ℂ) ^ (-(n : ℂ)) * z⁻¹ * hermitePhysEval n z := by
  sorry

/-- Laguerre specialization of continued U, with a regular ordinary-M denominator. -/
@[dlmf 13.6.E19]
theorem confluentU_laguerre (n : ℕ) (α z : ℂ) (hα : ∀ k : ℕ, α + 1 ≠ -k) :
    confluentU (-(n : ℂ)) (α + 1) z =
      (-1 : ℂ) ^ n * poch (α + 1) n * confluentM (-(n : ℂ)) (α + 1) z ∧
      confluentU (-(n : ℂ)) (α + 1) z = (-1 : ℂ) ^ n * n.factorial * laguerre α n z := by
  sorry

/-- Charlier specialization with nonzero scale and a regular ordinary-M denominator. -/
@[dlmf 13.6.E20]
theorem confluentU_charlier (n : ℕ) (z a : ℂ) (ha : a ≠ 0)
    (hz : ∀ k : ℕ, z - n + 1 ≠ -k) :
    confluentU (-(n : ℂ)) (z - n + 1) a =
      poch (-z) n * confluentM (-(n : ℂ)) (z - n + 1) a ∧
      confluentU (-(n : ℂ)) (z - n + 1) a = a ^ n * AAR.OrthogonalPolynomials.charlier a n z := by
  sorry

/-- The terminating `₂F₀` expression for polynomial Tricomi U.
A nonterminating `₂F₀` is generally divergent and cannot be interpreted as
Mathlib's ordinary regularized hypergeometric power-series sum. -/
@[dlmf 13.6.E21]
theorem confluentU_eq_twoFzero (n : ℕ) (b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    confluentU (-(n : ℂ)) b z =
      z ^ n * regularizedHGFun {-(n : ℂ), -(n : ℂ) - b + 1}
        (∅ : Multiset ℂ) (-z⁻¹) := by
  sorry

@[dlmf 13.18.E1]
theorem whittakerM_sinh {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerM 0 (1 / 2) (2 * z) = 2 * sinh z := by
  have hz0 : z ≠ 0 := by
    intro h
    exact slitPlane_ne_zero hz (by simp [h])
  unfold whittakerM
  have hμ : (1 / 2 : ℂ) - 0 + 1 / 2 = 1 := by ring
  have hb : (1 : ℂ) + 2 * (1 / 2) = 2 := by ring
  have hr : (1 / 2 : ℂ) + 1 / 2 = 1 := by ring
  rw [hμ, hb, hr, cpow_one, confluentM_one_two z hz0]
  have : exp (-(2 * z) / 2) = exp (-z) := by ring_nf
  rw [this]
  field_simp [hz0]
  rw [← exp_add, neg_add_cancel, exp_zero, one_mul]

@[dlmf 13.18.E2]
theorem whittakerM_exp (κ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerM κ (κ - 1 / 2) z = exp (-z / 2) * z ^ κ ∧
      whittakerW κ (κ - 1 / 2) z = exp (-z / 2) * z ^ κ ∧
      whittakerW κ (-κ + 1 / 2) z = exp (-z / 2) * z ^ κ := by
  sorry

/-- An exponential Whittaker-M specialization with a regular denominator parameter. -/
@[dlmf 13.18.E3]
theorem whittakerM_exp_neg (κ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hκ : ∀ k : ℕ, -2 * κ ≠ -k) :
    whittakerM κ (-κ - 1 / 2) z = exp (z / 2) * z ^ (-κ) := by
  sorry

/-- Whittaker M and the lower incomplete Gamma function. At `μ = 0` the right side is the
removable limit `2μ γ(2μ,z) → 1`, which the totalized `lowerIncompleteGamma` does not take. -/
@[dlmf 13.18.E4]
theorem whittakerM_lowerIncompleteGamma (μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hμ0 : μ ≠ 0) :
    whittakerM (μ - 1 / 2) μ z =
      2 * μ * exp (z / 2) * z ^ (1 / 2 - μ) * lowerIncompleteGamma (2 * μ) z := by
  sorry

@[dlmf 13.18.E5]
theorem whittakerW_upperIncompleteGamma (μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (μ - 1 / 2) μ z =
      exp (z / 2) * z ^ (1 / 2 - μ) * GammaInc (2 * μ) z := by
  sorry

/-- Whittaker function and error functions. The left side depends only on `z ^ 2`, so the identity
needs `0 < Re z`. -/
@[dlmf 13.18.E6]
theorem whittakerM_errorFn {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (-1 / 4) (1 / 4) (z ^ 2) =
      (1 / 2) * exp (z ^ 2 / 2) * (Real.sqrt π : ℂ) * z ^ (1 / 2 : ℂ) * errorFn z := by
  sorry

/-- Whittaker function and error functions. The left side depends only on `z ^ 2`, so the identity
needs `0 < Re z`. -/
@[dlmf 13.18.E7]
theorem whittakerW_erfcFn {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerW (-1 / 4) (1 / 4) (z ^ 2) =
      exp (z ^ 2 / 2) * (Real.sqrt π : ℂ) * z ^ (1 / 2 : ℂ) * erfcFn z := by
  sorry

@[dlmf 13.18.E8]
theorem whittakerM_besselI (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hν : ∀ k : ℕ, 1 + 2 * ν ≠ -k) :
    whittakerM 0 ν (2 * z) =
      (2 : ℂ) ^ (2 * ν + 1 / 2) * Gamma (1 + ν) * z ^ (1 / 2 : ℂ) * besselI ν z := by
  sorry

@[dlmf 13.18.E9]
theorem whittakerW_besselK (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW 0 ν (2 * z) =
      ((2 * z) / π) ^ (1 / 2 : ℂ) * besselK ν z := by
  sorry

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E14]
theorem whittakerM_hermite_even (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (1 / 4 + n) (-1 / 4) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n).factorial * exp (-z ^ 2 / 2) *
        z ^ (1 / 2 : ℂ) * hermitePhysEval (2 * n) z := by
  sorry

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E15]
theorem whittakerM_hermite_odd (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerM (3 / 4 + n) (1 / 4) (z ^ 2) =
      (-1 : ℂ) ^ n * n.factorial / (2 * n + 1).factorial *
        exp (-z ^ 2 / 2) * z ^ (1 / 2 : ℂ) / 2 * hermitePhysEval (2 * n + 1) z := by
  sorry

/-- Whittaker function and Hermite polynomials. The left side depends only on `z ^ 2`, so the
identity needs `0 < Re z`. -/
@[dlmf 13.18.E16]
theorem whittakerW_hermite (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) (hre : 0 < z.re) :
    whittakerW (1 / 4 + n / 2) (1 / 4) (z ^ 2) =
      (2 : ℂ) ^ (-(n : ℂ)) * exp (-z ^ 2 / 2) * z ^ (1 / 2 : ℂ) * hermitePhysEval n z := by
  sorry

/-- Laguerre specialization of W with a regular Kummer-M denominator. -/
@[dlmf 13.18.E17]
theorem whittakerW_laguerre (α : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (hα : ∀ k : ℕ, α + 1 ≠ -k) :
    whittakerW (α / 2 + 1 / 2 + n) (α / 2) z =
      (-1 : ℂ) ^ n * poch (α + 1) n * whittakerM (α / 2 + 1 / 2 + n) (α / 2) z ∧
      whittakerW (α / 2 + 1 / 2 + n) (α / 2) z =
        (-1 : ℂ) ^ n * n.factorial * exp (-z / 2) * z ^ (α / 2 + 1 / 2) * laguerre α n z := by
  sorry

end AAR.Confluent
