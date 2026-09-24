/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Classical
public import AAR.QSeries.Identities
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality

/-!
# DLMF Chapter 18 results already in Mathlib 4.35.0-rc2

The following statement excerpts are deliberately commented out: the declarations
belong to Mathlib. Variables implicit in the excerpts retain their upstream context.
DLMF tags are included in the commented excerpts; Mathlib’s cross-reference
attribute cannot modify documentation on imported declarations. Some polynomial normalizations differ; notably
Mathlib's shifted Legendre is `P_n(1 - 2x)`, and `hermite` is the probabilists' family.
-/

public section

/- Already in Mathlib: `Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X`.
@[dlmf 18.1.E3]
theorem C_eq_two_mul_T_comp_half_mul_X [Invertible (2 : R)] (n : ℤ) :
    C R n = 2 * (T R n).comp (Polynomial.C ⅟2 * X)
-/
-- Mathlib: Polynomial.Chebyshev.C_eq_two_mul_T_comp_half_mul_X

/- Already in Mathlib: `Polynomial.Chebyshev.S_eq_U_comp_half_mul_X`.
@[dlmf 18.1.E3]
theorem S_eq_U_comp_half_mul_X [Invertible (2 : R)] (n : ℤ) :
    S R n = (U R n).comp (Polynomial.C ⅟2 * X)
-/
-- Mathlib: Polynomial.Chebyshev.S_eq_U_comp_half_mul_X

/- Already in Mathlib: `Polynomial.Chebyshev.leadingCoeff_T`.
@[dlmf 18.3.T1]
theorem leadingCoeff_T [IsDomain R] [NeZero (2 : R)] (n : ℤ) :
    (T R n).leadingCoeff = 2 ^ (n.natAbs - 1)
-/
-- Mathlib: Polynomial.Chebyshev.leadingCoeff_T

/- Already in Mathlib: `Polynomial.Chebyshev.leadingCoeff_U_natCast`.
@[dlmf 18.3.T1]
theorem leadingCoeff_U_natCast [IsDomain R] [NeZero (2 : R)] (n : ℕ) :
    (U R n).leadingCoeff = 2 ^ n
-/
-- Mathlib: Polynomial.Chebyshev.leadingCoeff_U_natCast

/- Already in Mathlib: `Polynomial.Chebyshev.T_zero`.
@[dlmf 18.5.E14]
theorem T_zero : T R 0 = 1
-/
-- Mathlib: Polynomial.Chebyshev.T_zero

/- Already in Mathlib: `Polynomial.Chebyshev.T_one`.
@[dlmf 18.5.E14]
theorem T_one : T R 1 = X
-/
-- Mathlib: Polynomial.Chebyshev.T_one

/- Already in Mathlib: `Polynomial.Chebyshev.T_two`.
@[dlmf 18.5.E14]
theorem T_two : T R 2 = 2 * X ^ 2 - 1
-/
-- Mathlib: Polynomial.Chebyshev.T_two

/- Already in Mathlib: `Polynomial.Chebyshev.U_zero`.
@[dlmf 18.5.E15]
theorem U_zero : U R 0 = 1
-/
-- Mathlib: Polynomial.Chebyshev.U_zero

/- Already in Mathlib: `Polynomial.Chebyshev.U_one`.
@[dlmf 18.5.E15]
theorem U_one : U R 1 = 2 * X
-/
-- Mathlib: Polynomial.Chebyshev.U_one

/- Already in Mathlib: `Polynomial.Chebyshev.U_two`.
@[dlmf 18.5.E15]
theorem U_two : U R 2 = 4 * X ^ 2 - 1
-/
-- Mathlib: Polynomial.Chebyshev.U_two

/- Already in Mathlib: `Polynomial.Chebyshev.T_eval_one`.
@[dlmf 18.6.T1]
theorem T_eval_one (n : ℤ) : (T R n).eval 1 = 1
-/
-- Mathlib: Polynomial.Chebyshev.T_eval_one

/- Already in Mathlib: `Polynomial.Chebyshev.T_eval_neg_one`.
@[dlmf 18.6.T1]
theorem T_eval_neg_one (n : ℤ) : (T R n).eval (-1) = n.negOnePow
-/
-- Mathlib: Polynomial.Chebyshev.T_eval_neg_one

/- Already in Mathlib: `Polynomial.Chebyshev.T_eval_neg`.
@[dlmf 18.6.T1]
theorem T_eval_neg (n : ℤ) (x : R) : (T R n).eval (-x) = n.negOnePow * (T R n).eval x
-/
-- Mathlib: Polynomial.Chebyshev.T_eval_neg

/- Already in Mathlib: `Polynomial.Chebyshev.U_eval_one`.
@[dlmf 18.6.T1]
theorem U_eval_one (n : ℤ) : (U R n).eval 1 = n + 1
-/
-- Mathlib: Polynomial.Chebyshev.U_eval_one

/- Already in Mathlib: `Polynomial.Chebyshev.U_eval_neg_one`.
@[dlmf 18.6.T1]
theorem U_eval_neg_one (n : ℤ) : (U R n).eval (-1) = n.negOnePow * (n + 1)
-/
-- Mathlib: Polynomial.Chebyshev.U_eval_neg_one

/- Already in Mathlib: `Polynomial.Chebyshev.U_eval_neg`.
@[dlmf 18.6.T1]
theorem U_eval_neg (n : ℕ) (x : R) : (U R n).eval (-x) = (n : ℤ).negOnePow * (U R n).eval x
-/
-- Mathlib: Polynomial.Chebyshev.U_eval_neg

/- Already in Mathlib: `Polynomial.Chebyshev.T_add_two`.
@[dlmf 18.9.T1]
theorem T_add_two : ∀ n, T R (n + 2) = 2 * X * T R (n + 1) - T R n
  | (k : ℕ) => T.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm
-/
-- Mathlib: Polynomial.Chebyshev.T_add_two

/- Already in Mathlib: `Polynomial.Chebyshev.U_add_two`.
@[dlmf 18.9.T1]
theorem U_add_two : ∀ n, U R (n + 2) = 2 * X * U R (n + 1) - U R n
  | (k : ℕ) => U.eq_3 R k
  | -(k + 1 : ℕ) => by linear_combination (norm
-/
-- Mathlib: Polynomial.Chebyshev.U_add_two

/- Already in Mathlib: `Polynomial.Chebyshev.U_eq_two_mul_T_add_U`.
@[dlmf 18.9.E9]
theorem U_eq_two_mul_T_add_U (n : ℤ) : U R (n + 2) = 2 * T R (n + 2) + U R n
-/
-- Mathlib: Polynomial.Chebyshev.U_eq_two_mul_T_add_U

/- Already in Mathlib: `Polynomial.Chebyshev.T_derivative_eq_U`.
@[dlmf 18.9.E21]
theorem T_derivative_eq_U (n : ℤ) : derivative (T R n) = n * U R (n - 1)
-/
-- Mathlib: Polynomial.Chebyshev.T_derivative_eq_U

/- Already in Mathlib: `Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T`.
@[dlmf 18.8.T1]
theorem one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T (n : ℤ) :
    (1 - X ^ 2) * derivative^[2] (T R n) = X * derivative (T R n) - (n ^ 2 : R[X]) * T R n
-/
-- Mathlib: Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_T_eq_poly_in_T

/- Already in Mathlib: `Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U`.
@[dlmf 18.8.T1]
theorem one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U (n : ℤ) :
    (1 - X ^ 2) * derivative^[2] (U R n) =
      3 * X * derivative (U R n) - ((n + 2) * n : R[X]) * U R n
-/
-- Mathlib: Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_derivative_U_eq_poly_in_U

/- Already in Mathlib: `Polynomial.Chebyshev.T_mul_T`.
@[dlmf 18.18.E21]
theorem T_mul_T (m k : ℤ) : 2 * T R m * T R k = T R (m + k) + T R (m - k)
-/
-- Mathlib: Polynomial.Chebyshev.T_mul_T

/- Already in Mathlib: `Polynomial.Chebyshev.T_real_cos`.
@[dlmf 18.5.E1]
theorem T_real_cos : (T ℝ n).eval (cos θ) = cos (n * θ)
-/
-- Mathlib: Polynomial.Chebyshev.T_real_cos

/- Already in Mathlib: `Polynomial.Chebyshev.T_complex_cos`.
@[dlmf 18.5.E1]
theorem T_complex_cos (n : ℤ) : (T ℂ n).eval (cos θ) = cos (n * θ)
-/
-- Mathlib: Polynomial.Chebyshev.T_complex_cos

/- Already in Mathlib: `Polynomial.Chebyshev.U_real_cos`.
@[dlmf 18.5.E2]
theorem U_real_cos : (U ℝ n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
-/
-- Mathlib: Polynomial.Chebyshev.U_real_cos

/- Already in Mathlib: `Polynomial.Chebyshev.U_complex_cos`.
@[dlmf 18.5.E2]
theorem U_complex_cos (n : ℤ) : (U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ)
-/
-- Mathlib: Polynomial.Chebyshev.U_complex_cos

/- Already in Mathlib: `Polynomial.Chebyshev.roots_T_real`.
@[dlmf 18.16.iii]
theorem roots_T_real (n : ℕ) :
    (T ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((2 * k + 1) * π / (2 * n)))).val
-/
-- Mathlib: Polynomial.Chebyshev.roots_T_real

/- Already in Mathlib: `Polynomial.Chebyshev.roots_U_real`.
@[dlmf 18.16.iii]
theorem roots_U_real (n : ℕ) :
    (U ℝ n).roots =
    ((Finset.range n).image (fun (k : ℕ) => cos ((k + 1) * π / (n + 1)))).val
-/
-- Mathlib: Polynomial.Chebyshev.roots_U_real

/- Already in Mathlib: `Polynomial.Chebyshev.rootMultiplicity_T_real`.
@[dlmf 18.16.iii]
theorem rootMultiplicity_T_real {n k : ℕ} (hk : k < n) :
    (T ℝ n).rootMultiplicity (cos ((2 * k + 1) * π / (2 * n))) = 1
-/
-- Mathlib: Polynomial.Chebyshev.rootMultiplicity_T_real

/- Already in Mathlib: `Polynomial.Chebyshev.rootMultiplicity_U_real`.
@[dlmf 18.16.iii]
theorem rootMultiplicity_U_real {n k : ℕ} (hk : k < n) :
    (U ℝ n).rootMultiplicity (cos ((k + 1) * π / (n + 1))) = 1
-/
-- Mathlib: Polynomial.Chebyshev.rootMultiplicity_U_real

/- Already in Mathlib: `Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff`.
@[dlmf 18.6.T1]
theorem abs_eval_T_real_eq_one_iff {n : ℕ} (hn : n ≠ 0) (x : ℝ) :
    |(T ℝ n).eval x| = 1 ↔ ∃ k ≤ n, x = cos (k * π / n)
-/
-- Mathlib: Polynomial.Chebyshev.abs_eval_T_real_eq_one_iff

/- Already in Mathlib: `Polynomial.Chebyshev.abs_eval_T_real_le_one`.
@[dlmf 18.14.i]
theorem abs_eval_T_real_le_one (n : ℤ) {x : ℝ} (hx : |x| ≤ 1) :
    |(T ℝ n).eval x| ≤ 1
-/
-- Mathlib: Polynomial.Chebyshev.abs_eval_T_real_le_one

/- Already in Mathlib: `Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne`.
@[dlmf 18.3.T1]
theorem integral_eval_T_real_mul_eval_T_real_measureT_of_ne {n m : ℕ} (h : n ≠ m) :
    ∫ x, (T ℝ n).eval x * (T ℝ m).eval x ∂measureT = 0
-/
-- Mathlib: Polynomial.Chebyshev.integral_eval_T_real_mul_eval_T_real_measureT_of_ne

/- Already in Mathlib: `Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero`.
@[dlmf 18.3.T1]
theorem integral_eval_T_real_mul_self_measureT_zero :
    ∫ x, (T ℝ 0).eval x * (T ℝ 0).eval x ∂measureT = π
-/
-- Mathlib: Polynomial.Chebyshev.integral_eval_T_real_mul_self_measureT_zero

/- Already in Mathlib: `Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero`.
@[dlmf 18.3.T1]
theorem integral_T_real_mul_self_measureT_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    ∫ x, (T ℝ n).eval x * (T ℝ n).eval x ∂measureT = π / 2
-/
-- Mathlib: Polynomial.Chebyshev.integral_T_real_mul_self_measureT_of_ne_zero

/- Already in Mathlib: `Polynomial.degree_hermite`.
@[dlmf 18.3.T1]
theorem degree_hermite (n : ℕ) : (hermite n).degree = n
-/
-- Mathlib: Polynomial.degree_hermite

/- Already in Mathlib: `Polynomial.hermite_monic`.
@[dlmf 18.3.T1]
theorem hermite_monic (n : ℕ) : (hermite n).Monic
-/
-- Mathlib: Polynomial.hermite_monic

/- Already in Mathlib: `Polynomial.leadingCoeff_hermite`.
@[dlmf 18.3.T1]
theorem leadingCoeff_hermite (n : ℕ) : (hermite n).leadingCoeff = 1
-/
-- Mathlib: Polynomial.leadingCoeff_hermite

/- Already in Mathlib: `Polynomial.hermite_zero`.
@[dlmf 18.5.E19]
theorem hermite_zero : hermite 0 = C 1
-/
-- Mathlib: Polynomial.hermite_zero

/- Already in Mathlib: `Polynomial.hermite_one`.
@[dlmf 18.5.E19]
theorem hermite_one : hermite 1 = X
-/
-- Mathlib: Polynomial.hermite_one

/- Already in Mathlib: `Polynomial.coeff_hermite`.
@[dlmf 18.5.E19]
theorem coeff_hermite (n k : ℕ) :
    coeff (hermite n) k =
      if Even (n + k) then (-1 : ℤ) ^ ((n - k) / 2) * (n - k - 1)‼ * Nat.choose n k else 0
-/
-- Mathlib: Polynomial.coeff_hermite

/- Already in Mathlib: `Polynomial.coeff_hermite_of_odd_add`.
@[dlmf 18.6.T1]
theorem coeff_hermite_of_odd_add {n k : ℕ} (hnk : Odd (n + k)) : coeff (hermite n) k = 0
-/
-- Mathlib: Polynomial.coeff_hermite_of_odd_add

/- Already in Mathlib: `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian`.
@[dlmf 18.5.T1]
theorem deriv_gaussian_eq_hermite_mul_gaussian (n : ℕ) (x : ℝ) :
    deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x =
    (-1 : ℝ) ^ n * aeval x (hermite n) * Real.exp (-(x ^ 2 / 2))
-/
-- Mathlib: Polynomial.deriv_gaussian_eq_hermite_mul_gaussian

/- Already in Mathlib: `Polynomial.hermite_eq_deriv_gaussian`.
@[dlmf 18.5.T1]
theorem hermite_eq_deriv_gaussian (n : ℕ) (x : ℝ) : aeval x (hermite n) =
    (-1 : ℝ) ^ n * deriv^[n] (fun y => Real.exp (-(y ^ 2 / 2))) x / Real.exp (-(x ^ 2 / 2))
-/
-- Mathlib: Polynomial.hermite_eq_deriv_gaussian

/- Already in Mathlib: `Polynomial.coeff_shiftedLegendre`.
@[dlmf 18.5.E7]
theorem coeff_shiftedLegendre (n k : ℕ) :
    (shiftedLegendre n).coeff k = (-1) ^ k * n.choose k * (n + k).choose n
-/
-- Mathlib: Polynomial.coeff_shiftedLegendre

/- Already in Mathlib: `Polynomial.shiftedLegendre_eval_symm`.
@[dlmf 18.6.T1]
lemma shiftedLegendre_eval_symm (n : ℕ) {R : Type*} [Ring R] (x : R) :
    aeval x (shiftedLegendre n) = (-1) ^ n * aeval (1 - x) (shiftedLegendre n)
-/
-- Mathlib: Polynomial.shiftedLegendre_eval_symm

/- DLMF 18.1(i) repeats the q-Pochhammer definitions from Chapter 17.
These are already in our QSeries home; retain a single definition. -/
-- @[dlmf 18.1.i] def qPochhammer — see AAR/QSeries/Pochhammer.lean
-- @[dlmf 18.1.i] def qPochhammerInf — see AAR/QSeries/Pochhammer.lean

/- DLMF 18.28.13 is the Laurent form already defined in QSeries/Identities. -/
-- @[dlmf 18.28.E13] def qGegenbauer — see AAR/QSeries/Identities.lean

/- Already in Mathlib: `Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T`.
Together with `Polynomial.Chebyshev.T_add_two`, this is DLMF 18.9.10.
@[dlmf 18.9.E10]
theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : ℤ) :
    (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2)
-/
-- Mathlib: Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T
