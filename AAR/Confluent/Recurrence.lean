/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import AAR.Hypergeometric.Derivatives

/-!
# Recurrence relations and derivatives (DLMF §§13.3, 13.15)

Denominator parameters of `confluentM` stay off the nonpositive integers.
Tricomi and Whittaker identities use the principal branch on the slit plane.
The operator `(z d/dz z)` is `mulDerivMul`, matching DLMF 13.3.29.
13.3.15 is already proved as `deriv_confluentM_regular` in
`OrthogonalPolynomials.Differential`; the pointwise form is restated here.
-/

@[expose] public section

open Complex Filter FormalMultilinearSeries
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

/-- The operator `f ↦ z (z f)'`. -/
def mulDerivMul (f : ℂ → ℂ) (z : ℂ) : ℂ := z * deriv (fun w => w * f w) z

-- NOTE (2026-09-17): the smoothness hypothesis `hf` was added; the DLMF identity is for
-- smooth `f`, and without it the two sides involve junk values of `deriv`. The proof reuses
-- the Gauss-side operator identity `AAR.Hypergeometric.iterate_mulDerivMul_eq`.
@[dlmf 13.3.E29]
theorem mulDerivMul_eq_mul_iteratedDeriv (n : ℕ) (f : ℂ → ℂ) (hf : ContDiff ℂ ⊤ f) {z : ℂ}
    (hz : z ≠ 0) :
    mulDerivMul^[n] f z = z ^ n * iteratedDeriv n (fun w => w ^ n * f w) z := by
  have h : mulDerivMul = AAR.Hypergeometric.mulDerivMul := rfl
  rw [h]
  exact AAR.Hypergeometric.iterate_mulDerivMul_eq n hf z

section KummerContiguous

/-- Kummer's series converges everywhere. -/
lemma hasSum_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n => confluentHGCoeff a b n * z ^ n) (confluentM a b z) :=
  (hasFPowerSeriesOnBall_confluentM (a := a) hb).hasSum_mul_pow (by simp)

lemma hasSum_deriv_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) * confluentHGCoeff a b (n + 1) * z ^ n)
      (deriv (confluentM a b) z) :=
  (hasFPowerSeriesOnBall_confluentM (a := a) hb).deriv_ofScalars.hasSum_mul_pow (by simp)

lemma hasSum_z_mul_deriv_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (n : ℂ) * confluentHGCoeff a b n * z ^ n)
      (z * deriv (confluentM a b) z) :=
  (hasFPowerSeriesOnBall_confluentM (a := a) hb).hasSum_z_mul_deriv (by simp)

lemma hasSum_z_mul_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasSum (fun n : ℕ => (if n = 0 then 0 else confluentHGCoeff a b (n - 1)) * z ^ n)
      (z * confluentM a b z) := by
  apply HasSum.mul_pow_shift (c := fun n => if n = 0 then 0 else confluentHGCoeff a b (n - 1))
    ?_ (by simp)
  simpa using hasSum_confluentM hb z

lemma confluentHGCoeff_shift_a (a b : ℂ) (n : ℕ) :
    (n : ℂ) * confluentHGCoeff a b n =
      a * confluentHGCoeff (a + 1) b n - a * confluentHGCoeff a b n := by
  simp only [confluentHGCoeff]
  rw [mul_div_assoc', mul_div_assoc', mul_div_assoc', ← sub_div]
  congr 1
  cases n with
  | zero => simp [poch_zero]
  | succ m =>
    rw [← poch_succ_left, poch_succ a (m + 1)]
    push_cast
    ring

lemma confluentHGCoeff_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (n : ℕ) :
    (n : ℂ) * confluentHGCoeff a b n =
      (b - 1) * confluentHGCoeff a (b - 1) n - (b - 1) * confluentHGCoeff a b n := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  cases n with
  | zero => simp [confluentHGCoeff, poch_zero]
  | succ m =>
    have hb0 : b - 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : ((m + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [confluentHGCoeff]
    rw [poch_succ_left (b - 1), sub_add_cancel, poch_succ b m]
    push_cast
    field_simp
    ring

lemma confluentHGCoeff_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (n : ℂ) * confluentHGCoeff a b n =
      (b - a) * confluentHGCoeff (a - 1) b n + (a - b) * confluentHGCoeff a b n +
        (if n = 0 then 0 else confluentHGCoeff a b (n - 1)) := by
  cases n with
  | zero => simp [confluentHGCoeff, poch_zero]
  | succ m =>
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [confluentHGCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [poch_succ_left (a - 1), sub_add_cancel, poch_succ a m, poch_succ b m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

lemma confluentHGCoeff_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * ((n + 1 : ℂ) * confluentHGCoeff a b (n + 1)) =
      (a - b) * confluentHGCoeff a (b + 1) n + b * confluentHGCoeff a b n := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hbn : b + n ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb n
  have hpb := poch_ne_zero_of_not_neg_nat hb n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hrel : b * poch (b + 1) n = poch b n * (b + n) := by rw [← poch_succ_left, poch_succ]
  have hX : poch (b + 1) n = poch b n * (b + n) / b := by
    rw [eq_div_iff hb0]; linear_combination hrel
  simp only [confluentHGCoeff]
  rw [poch_succ a n, poch_succ b n, Nat.factorial_succ, hX]
  push_cast
  field_simp
  ring

lemma confluentHGCoeff_contiguous_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    b * confluentHGCoeff a b n - b * confluentHGCoeff (a - 1) b n -
      (if n = 0 then 0 else confluentHGCoeff a (b + 1) (n - 1)) = 0 := by
  cases n with
  | zero => simp [confluentHGCoeff, poch_zero]
  | succ m =>
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hbm : b + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb m
    have hpb := poch_ne_zero_of_not_neg_nat hb m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrel : b * poch (b + 1) m = poch b m * (b + m) := by rw [← poch_succ_left, poch_succ]
    have hX : poch (b + 1) m = poch b m * (b + m) / b := by
      rw [eq_div_iff hb0]; linear_combination hrel
    simp only [confluentHGCoeff, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [poch_succ_left (a - 1), sub_add_cancel, poch_succ a m, poch_succ b m,
      Nat.factorial_succ, hX]
    push_cast
    field_simp
    ring

lemma confluentHGCoeff_ode_contiguous {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (n : ℕ) :
    (a + 1) * (if n = 0 then 0 else confluentHGCoeff (a + 2) (b + 2) (n - 1)) +
      (b + 1) * b * confluentHGCoeff (a + 1) (b + 1) n -
      (b + 1) * (if n = 0 then 0 else confluentHGCoeff (a + 1) (b + 1) (n - 1)) -
      b * (b + 1) * confluentHGCoeff a b n = 0 := by
  cases n with
  | zero => simp [confluentHGCoeff, poch_zero]; ring
  | succ m =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hb10 : b + 1 ≠ 0 := by simpa using hb1 0
    have hbm : b + 1 + m ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hb1 m
    have hpb := poch_ne_zero_of_not_neg_nat hb1 m
    have hf : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hrelA : (a + 1) * poch (a + 2) m = poch (a + 1) m * (a + 1 + m) := by
      rw [show (a + 2 : ℂ) = a + 1 + 1 by ring, ← poch_succ_left, poch_succ]
    have hrelB : (b + 1) * poch (b + 2) m = poch (b + 1) m * (b + 1 + m) := by
      rw [show (b + 2 : ℂ) = b + 1 + 1 by ring, ← poch_succ_left, poch_succ]
    have hX : poch (b + 2) m = poch (b + 1) m * (b + 1 + m) / (b + 1) := by
      rw [eq_div_iff hb10]; linear_combination hrelB
    have hA : (a + 1) * confluentHGCoeff (a + 2) (b + 2) m =
        poch (a + 1) m * (a + 1 + m) / (poch (b + 2) m * m.factorial) := by
      simp only [confluentHGCoeff]
      rw [mul_div_assoc', hrelA]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    rw [hA, hX]
    simp only [confluentHGCoeff]
    rw [poch_succ_left a, poch_succ (a + 1) m, poch_succ_left b, poch_succ (b + 1) m,
      Nat.factorial_succ]
    push_cast
    field_simp
    ring

/-- `z M'(a,b,z) = a (M(a+1,b,z) - M(a,b,z))`. -/
lemma z_mul_deriv_confluentM_eq_shift_a {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (confluentM a b) z = a * confluentM (a + 1) b z - a * confluentM a b z := by
  have h := hasSum_z_mul_deriv_confluentM (a := a) hb z
  have h' := ((hasSum_confluentM (a := a + 1) hb z).mul_left a).sub
    ((hasSum_confluentM (a := a) hb z).mul_left a)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * confluentHGCoeff_shift_a a b n

/-- `z M'(a,b,z) = (b-1) (M(a,b-1,z) - M(a,b,z))`. -/
lemma z_mul_deriv_confluentM_eq_shift_b_pred {a b : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) (z : ℂ) :
    z * deriv (confluentM a b) z =
      (b - 1) * confluentM a (b - 1) z - (b - 1) * confluentM a b z := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have h := hasSum_z_mul_deriv_confluentM (a := a) hb z
  have h' := ((hasSum_confluentM (a := a) hb1 z).mul_left (b - 1)).sub
    ((hasSum_confluentM (a := a) hb z).mul_left (b - 1))
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * confluentHGCoeff_shift_b_pred (a := a) hb1 n

/-- `z M'(a,b,z) = (b-a) M(a-1,b,z) + (a-b+z) M(a,b,z)`. -/
lemma z_mul_deriv_confluentM_eq_shift_a_pred {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    z * deriv (confluentM a b) z =
      (b - a) * confluentM (a - 1) b z + (a - b) * confluentM a b z +
        z * confluentM a b z := by
  have h := hasSum_z_mul_deriv_confluentM (a := a) hb z
  have h' := (((hasSum_confluentM (a := a - 1) hb z).mul_left (b - a)).add
    ((hasSum_confluentM (a := a) hb z).mul_left (a - b))).add (hasSum_z_mul_confluentM (a := a) hb z)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * confluentHGCoeff_shift_a_pred (a := a) hb n

/-- `b M'(a,b,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
lemma deriv_confluentM_eq_shift_b_succ {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    b * deriv (confluentM a b) z = (a - b) * confluentM a (b + 1) z + b * confluentM a b z := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (hasSum_deriv_confluentM (a := a) hb z).mul_left b
  have h' := ((hasSum_confluentM (a := a) hb1 z).mul_left (a - b)).add
    ((hasSum_confluentM (a := a) hb z).mul_left b)
  refine h.unique ?_
  convert h' using 1
  funext n
  linear_combination (z ^ n) * confluentHGCoeff_shift_b_succ (a := a) hb n

end KummerContiguous

@[dlmf 13.3.E1]
theorem confluentM_contiguous_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (b - a) * confluentM (a - 1) b z + (2 * a - b + z) * confluentM a b z -
      a * confluentM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_confluentM_eq_shift_a (a := a) hb z
  have hC := z_mul_deriv_confluentM_eq_shift_a_pred (a := a) hb z
  linear_combination hA - hC

@[dlmf 13.3.E2]
theorem confluentM_contiguous_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    b * (b - 1) * confluentM a (b - 1) z + b * (1 - b - z) * confluentM a b z +
      z * (b - a) * confluentM a (b + 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hb z
  have hD := deriv_confluentM_eq_shift_b_succ (a := a) hb' z
  linear_combination z * hD - b * hB

@[dlmf 13.3.E3]
theorem confluentM_contiguous_a_b {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - b + 1) * confluentM a b z - a * confluentM (a + 1) b z +
      (b - 1) * confluentM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hA := z_mul_deriv_confluentM_eq_shift_a (a := a) hb' z
  have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hb z
  linear_combination hA - hB

@[dlmf 13.3.E4]
theorem confluentM_contiguous_shift_a {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * confluentM a b z - b * confluentM (a - 1) b z - z * confluentM a (b + 1) z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have h := (((hasSum_confluentM (a := a) hb z).mul_left b).sub
    ((hasSum_confluentM (a := a - 1) hb z).mul_left b)).sub
    (hasSum_z_mul_confluentM (a := a) hb1 z)
  refine h.unique ?_
  convert hasSum_zero using 1
  funext n
  linear_combination (z ^ n) * confluentHGCoeff_contiguous_shift_a (a := a) hb n

@[dlmf 13.3.E5]
theorem confluentM_contiguous_mixed {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    b * (a + z) * confluentM a b z + z * (a - b) * confluentM a (b + 1) z -
      a * b * confluentM (a + 1) b z = 0 := by
  have hA := z_mul_deriv_confluentM_eq_shift_a (a := a) hb z
  have hD := deriv_confluentM_eq_shift_b_succ (a := a) hb z
  linear_combination b * hA - z * hD

@[dlmf 13.3.E6]
theorem confluentM_contiguous_down {a b z : ℂ} (hb : ∀ k : ℕ, b - 1 ≠ -k) :
    (a - 1 + z) * confluentM a b z + (b - a) * confluentM (a - 1) b z +
      (1 - b) * confluentM a (b - 1) z = 0 := by
  have hb' : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hb z
  have hC := z_mul_deriv_confluentM_eq_shift_a_pred (a := a) hb' z
  linear_combination hB - hC

@[dlmf 13.3.E7]
theorem confluentU_contiguous_a (a b z : ℂ) :
    confluentU (a - 1) b z + (b - 2 * a - z) * confluentU a b z +
      a * (a - b + 1) * confluentU (a + 1) b z = 0 := by
  sorry

@[dlmf 13.3.E8]
theorem confluentU_contiguous_b (a b z : ℂ) :
    (b - a - 1) * confluentU a (b - 1) z + (1 - b - z) * confluentU a b z +
      z * confluentU a (b + 1) z = 0 := by
  sorry

@[dlmf 13.3.E9]
theorem confluentU_contiguous_a_b (a b z : ℂ) :
    confluentU a b z - a * confluentU (a + 1) b z - confluentU a (b - 1) z = 0 := by
  sorry

@[dlmf 13.3.E10]
theorem confluentU_contiguous_shift_a (a b z : ℂ) :
    (b - a) * confluentU a b z + confluentU (a - 1) b z - z * confluentU a (b + 1) z = 0 := by
  sorry

@[dlmf 13.3.E11]
theorem confluentU_contiguous_mixed (a b z : ℂ) :
    (a + z) * confluentU a b z - z * confluentU a (b + 1) z +
      a * (b - a - 1) * confluentU (a + 1) b z = 0 := by
  sorry

@[dlmf 13.3.E12]
theorem confluentU_contiguous_down (a b z : ℂ) :
    (a - 1 + z) * confluentU a b z - confluentU (a - 1) b z +
      (a - b + 1) * confluentU a (b - 1) z = 0 := by
  sorry

@[dlmf 13.3.E13]
theorem confluentM_ode_contiguous {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    (a + 1) * z * confluentM (a + 2) (b + 2) z +
      (b + 1) * (b - z) * confluentM (a + 1) (b + 1) z -
      b * (b + 1) * confluentM a b z = 0 := by
  have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hb2 : ∀ k : ℕ, b + 2 ≠ -k := by simpa using not_neg_nat_add_nat hb 2
  have h := ((((hasSum_z_mul_confluentM (a := a + 2) hb2 z).mul_left (a + 1)).add
    ((hasSum_confluentM (a := a + 1) hb1 z).mul_left ((b + 1) * b))).sub
    ((hasSum_z_mul_confluentM (a := a + 1) hb1 z).mul_left (b + 1))).sub
    ((hasSum_confluentM (a := a) hb z).mul_left (b * (b + 1)))
  have h0 : (a + 1) * (z * confluentM (a + 2) (b + 2) z) +
      (b + 1) * b * confluentM (a + 1) (b + 1) z -
      (b + 1) * (z * confluentM (a + 1) (b + 1) z) - b * (b + 1) * confluentM a b z = 0 := by
    refine h.unique ?_
    convert hasSum_zero using 1
    funext n
    linear_combination (z ^ n) * confluentHGCoeff_ode_contiguous (a := a) hb n
  linear_combination h0

@[dlmf 13.3.E14]
theorem confluentU_ode_contiguous (a b z : ℂ) :
    (a + 1) * z * confluentU (a + 2) (b + 2) z + (z - b) * confluentU (a + 1) (b + 1) z -
      confluentU a b z = 0 := by
  sorry

@[dlmf 13.3.E15]
theorem deriv_confluentM {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb0 : b ≠ 0) :
    deriv (confluentM a b) z = a / b * confluentM (a + 1) (b + 1) z := by
  have hc1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
  have hcoeff (k : ℕ) : (k + 1 : ℂ) * confluentHGCoeff a b (k + 1) =
      a / b * confluentHGCoeff (a + 1) (b + 1) k := by
    have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hcp := poch_ne_zero_of_not_neg_nat hc1 k
    simp only [confluentHGCoeff, poch_succ_left, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp
  have hd := (hasFPowerSeriesOnBall_confluentM (a := a) hb).deriv_ofScalars.hasSum_mul_pow
    (z := z) (by simp)
  have hs := ((hasFPowerSeriesOnBall_confluentM (a := a + 1) hc1).hasSum_mul_pow
    (z := z) (by simp)).mul_left (a / b)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd hs
  exact hd.unique hs

/-- `a M(a+1,b+1,z) = (a-b) M(a,b+1,z) + b M(a,b,z)`. -/
lemma confluentM_contiguous_shift_b_succ {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    a * confluentM (a + 1) (b + 1) z =
      (a - b) * confluentM a (b + 1) z + b * confluentM a b z := by
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h1 := deriv_confluentM_eq_shift_b_succ (a := a) hb z
  have h2 := deriv_confluentM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * confluentM (a + 1) (b + 1) z) = a * confluentM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at h1
  linear_combination h1 - h3

/-- `(b-1) b (M(a,b,z) - M(a,b-1,z)) + a z M(a+1,b+1,z) = 0`. -/
lemma confluentM_contiguous_mixed_b_pred {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * confluentM a b z - (b - 1) * b * confluentM a (b - 1) z +
      a * z * confluentM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hb1 z
  have h2 := deriv_confluentM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * confluentM (a + 1) (b + 1) z) = a * confluentM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hB
  linear_combination b * hB - z * h3

/-- `(b-1) b M(a-1,b-1,z) + (z-b+1) b M(a,b,z) - a z M(a+1,b+1,z) = 0`. -/
lemma confluentM_contiguous_up_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * confluentM (a - 1) (b - 1) z + (z - b + 1) * b * confluentM a b z -
      a * z * confluentM (a + 1) (b + 1) z = 0 := by
  have hb : ∀ k : ℕ, b ≠ -k := by simpa using not_neg_nat_add_nat hb1 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have h4 := confluentM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h6 := confluentM_contiguous_down (a := a) hb1 (z := z)
  have hC := z_mul_deriv_confluentM_eq_shift_a_pred (a := a) hb z
  have h2 := deriv_confluentM (a := a) hb hb0 (z := z)
  have h3 : b * (a / b * confluentM (a + 1) (b + 1) z) = a * confluentM (a + 1) (b + 1) z := by
    field_simp
  rw [h2] at hC
  linear_combination z * h3 - b * hC - b * h6 - b * h4

/-- `(b-1) b M(a-1,b-1,z) - (b-1) b M(a,b,z) + (b-a) z M(a,b+1,z) = 0`. -/
lemma confluentM_contiguous_up_shift_aux {a b z : ℂ} (hb1 : ∀ k : ℕ, b - 1 ≠ -k) :
    (b - 1) * b * confluentM (a - 1) (b - 1) z - (b - 1) * b * confluentM a b z +
      (b - a) * z * confluentM a (b + 1) z = 0 := by
  have h4 := confluentM_contiguous_shift_a (a := a) hb1 (z := z)
  rw [sub_add_cancel] at h4
  have h2 := confluentM_contiguous_b (a := a) hb1 (z := z)
  linear_combination h2 - b * h4

@[dlmf 13.3.E16]
theorem iteratedDeriv_confluentM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (confluentM a b) =
      fun z => poch a n / poch b n * confluentM (a + n) (b + n) z := by
  induction n with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb' : ∀ k : ℕ, b + n ≠ -k := not_neg_nat_add_nat hb n
    have hb0 : b + n ≠ 0 := by
      intro h
      exact hb n ((eq_neg_iff_add_eq_zero).2 h)
    funext z
    rw [iteratedDeriv_succ, ih, deriv_const_mul_field, deriv_confluentM hb' hb0]
    simp only [poch_succ, Nat.cast_add, Nat.cast_one, div_eq_mul_inv, mul_inv_rev]
    ring

private lemma mul_cpow_pred' {z : ℂ} (hz : z ≠ 0) (s : ℂ) : z * z ^ (s - 1) = z ^ s := by
  calc
    z * z ^ (s - 1) = z ^ (1 : ℂ) * z ^ (s - 1) := by rw [cpow_one]
    _ = z ^ ((1 : ℂ) + (s - 1)) := (cpow_add _ _ hz).symm
    _ = z ^ s := by congr 1; ring

/-- Kummer's function is differentiable everywhere. -/
private lemma hasDerivAt_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (confluentM a b) (deriv (confluentM a b) z) z := by
  have h := (hasFPowerSeriesOnBall_confluentM (a := a) hb).analyticAt_of_mem (y := z) (by simp)
  exact h.differentiableAt.hasDerivAt

private lemma deriv_cpow_mul_confluentM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k) {z : ℂ}
    (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * confluentM a b w) z =
      s * z ^ (s - 1) * confluentM a b z + z ^ s * deriv (confluentM a b) z := by
  have hM := hasDerivAt_confluentM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have h := (hp.mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]

private lemma deriv_exp_neg_mul_confluentM {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    deriv (fun w => exp (-w) * confluentM a b w) z =
      -(exp (-z) * confluentM a b z) + exp (-z) * deriv (confluentM a b) z := by
  have hM := hasDerivAt_confluentM (a := a) hb z
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := (he.mul hM).deriv
  simp only [Pi.mul_def] at h
  rw [h]
  ring

private lemma deriv_cpow_mul_exp_neg_mul_confluentM {a b : ℂ} (s : ℂ) (hb : ∀ k : ℕ, b ≠ -k)
    {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (fun w => w ^ s * exp (-w) * confluentM a b w) z =
      s * z ^ (s - 1) * exp (-z) * confluentM a b z - z ^ s * exp (-z) * confluentM a b z +
        z ^ s * exp (-z) * deriv (confluentM a b) z := by
  have hM := hasDerivAt_confluentM (a := a) hb z
  have hp := (hasDerivAt_id z).cpow_const (c := s) hz
  have he : HasDerivAt (fun w : ℂ => exp (-w)) (exp (-z) * -1) z := (hasDerivAt_id z).neg.cexp
  have h := ((hp.mul he).mul hM).deriv
  simp only [id_eq, Pi.mul_def, mul_one] at h
  rw [h]
  ring

@[dlmf 13.3.E17]
theorem iterate_mulDerivMul_confluentM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * confluentM a b w) z =
      poch a n * z ^ (a + n - 1) * confluentM (a + n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n] (fun t => t ^ (a - 1) * confluentM a b t) w)
        =ᶠ[𝓝 z] (fun w => poch a n * (w ^ (a + n) * confluentM (a + n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_confluentM (a + n) hb hz]
    have hA := z_mul_deriv_confluentM_eq_shift_a (a := a + n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (a + n) := by congr 1; push_cast; ring
    have e2 : a + ((n + 1 : ℕ) : ℂ) = a + n + 1 := by push_cast; ring
    have e4 : z ^ (a + n) = z * z ^ (a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch a n * z * z ^ (a + n - 1)) * hA

@[dlmf 13.3.E18]
theorem iteratedDeriv_mul_cpow_confluentM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * confluentM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * confluentM a (b - n) z := by
  induction n generalizing b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * confluentM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * confluentM a (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_confluentM (b - 1) hb0 hw]
      have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hbm w
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1)) * hB
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

@[dlmf 13.3.E19]
theorem iterate_mulDerivMul_exp_neg_confluentM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * confluentM a b w) z =
      poch (b - a) n * z ^ (b - a + n - 1) * exp (-z) * confluentM (a - n) b z := by
  induction n generalizing z with
  | zero => simp [poch_zero]
  | succ n ih =>
    have heq : (fun w => w * mulDerivMul^[n]
          (fun t => t ^ (b - a - 1) * exp (-t) * confluentM a b t) w) =ᶠ[𝓝 z]
        (fun w => poch (b - a) n * (w ^ (b - a + n) * exp (-w) * confluentM (a - n) b w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [ih hw, ← mul_cpow_pred' (slitPlane_ne_zero hw) (b - a + n)]
      ring
    rw [Function.iterate_succ_apply', mulDerivMul, heq.deriv_eq, deriv_const_mul_field,
      deriv_cpow_mul_exp_neg_mul_confluentM (b - a + n) hb hz]
    have hC := z_mul_deriv_confluentM_eq_shift_a_pred (a := a - n) hb z
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    have e1 : z ^ (b - a + ((n + 1 : ℕ) : ℂ) - 1) = z ^ (b - a + n) := by
      congr 1; push_cast; ring
    have e2 : a - ((n + 1 : ℕ) : ℂ) = a - n - 1 := by push_cast; ring
    have e4 : z ^ (b - a + n) = z * z ^ (b - a + n - 1) := (mul_cpow_pred' hz0 _).symm
    rw [e1, e2, poch_succ, e4]
    linear_combination (poch (b - a) n * z * z ^ (b - a + n - 1) * exp (-z)) * hC

@[dlmf 13.3.E20]
theorem iteratedDeriv_exp_neg_confluentM {a b : ℂ} (n : ℕ) (hb : ∀ k : ℕ, b ≠ -k) :
    iteratedDeriv n (fun w => exp (-w) * confluentM a b w) =
      fun z => (-1 : ℂ) ^ n * poch (b - a) n / poch b n * exp (-z) *
        confluentM a (b + n) z := by
  induction n generalizing b with
  | zero =>
    funext z
    simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb1 : ∀ k : ℕ, b + 1 ≠ -k := by simpa using not_neg_nat_add_nat hb 1
    have hb0 : b ≠ 0 := by simpa using hb 0
    have hd : deriv (fun w => exp (-w) * confluentM a b w) =
        fun w => -(b - a) / b * (exp (-w) * confluentM a (b + 1) w) := by
      funext w
      rw [deriv_exp_neg_mul_confluentM hb w]
      have hD := deriv_confluentM_eq_shift_b_succ (a := a) hb w
      field_simp
      linear_combination hD
    funext z
    rw [iteratedDeriv_succ', hd, iteratedDeriv_const_mul_field, ih hb1]
    beta_reduce
    have hp : poch (b + 1) n ≠ 0 := poch_ne_zero_of_not_neg_nat hb1 n
    rw [show b + 1 + (n : ℂ) = b + ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show b + 1 - a = b - a + 1 by ring, poch_succ_left (b - a), poch_succ_left b, pow_succ]
    field_simp

@[dlmf 13.3.E21]
theorem iteratedDeriv_mul_cpow_exp_neg_confluentM {a b : ℂ} (n : ℕ) {z : ℂ}
    (hb : ∀ k : ℕ, b - n ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * confluentM a b w) z =
      poch (b - n) n * z ^ (b - n - 1) * exp (-z) * confluentM (a - n) (b - n) z := by
  induction n generalizing a b with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    have hb0 : ∀ k : ℕ, b ≠ -k := by
      intro k hk
      apply hb (k + (n + 1))
      push_cast
      linear_combination hk
    have hbm : ∀ k : ℕ, b - 1 ≠ -k := by
      intro k hk
      apply hb (k + n)
      push_cast
      linear_combination hk
    have hbn' : ∀ k : ℕ, b - 1 - n ≠ -k := by
      intro k hk
      apply hb k
      push_cast
      linear_combination hk
    have heq : deriv (fun w => w ^ (b - 1) * exp (-w) * confluentM a b w) =ᶠ[𝓝 z]
        (fun w => (b - 1) * (w ^ (b - 1 - 1) * exp (-w) * confluentM (a - 1) (b - 1) w)) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      rw [deriv_cpow_mul_exp_neg_mul_confluentM (b - 1) hb0 hw]
      have hB := z_mul_deriv_confluentM_eq_shift_b_pred (a := a) hbm w
      have h4 := confluentM_contiguous_shift_a (a := a) hbm (z := w)
      rw [sub_add_cancel] at h4
      have hw0 : w ≠ 0 := slitPlane_ne_zero hw
      have e : w ^ (b - 1) = w * w ^ (b - 1 - 1) := (mul_cpow_pred' hw0 _).symm
      rw [e]
      linear_combination (w ^ (b - 1 - 1) * exp (-w)) * hB + (w ^ (b - 1 - 1) * exp (-w)) * h4
    rw [iteratedDeriv_succ', heq.iteratedDeriv_eq n, iteratedDeriv_const_mul_field, ih hbn']
    rw [show b - 1 - (n : ℂ) = b - ((n + 1 : ℕ) : ℂ) by push_cast; ring,
      show a - 1 - (n : ℂ) = a - ((n + 1 : ℕ) : ℂ) by push_cast; ring, poch_succ,
      show b - ((n + 1 : ℕ) : ℂ) + (n : ℂ) = b - 1 by push_cast; ring]
    ring

/-- Derivative of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is restricted to
the slit plane. -/
@[dlmf 13.3.E22]
theorem deriv_confluentU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    deriv (confluentU a b) z = -a * confluentU (a + 1) (b + 1) z := by
  sorry

/-- Iterated derivatives of Tricomi U. `U` is not complex-differentiable on the cut, so `z` is
restricted to the slit plane. -/
@[dlmf 13.3.E23]
theorem iteratedDeriv_confluentU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (confluentU a b) z =
      (-1 : ℂ) ^ n * poch a n * confluentU (a + n) (b + n) z := by
  sorry

@[dlmf 13.3.E24]
theorem iterate_mulDerivMul_confluentU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (a - 1) * confluentU a b w) z =
      poch a n * poch (a - b + 1) n * z ^ (a + n - 1) * confluentU (a + n) b z := by
  sorry

@[dlmf 13.3.E25]
theorem iteratedDeriv_mul_cpow_confluentU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * confluentU a b w) z =
      (-1 : ℂ) ^ n * poch (a - b + 1) n * z ^ (b - n - 1) * confluentU a (b - n) z := by
  sorry

@[dlmf 13.3.E26]
theorem iterate_mulDerivMul_exp_neg_confluentU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => w ^ (b - a - 1) * exp (-w) * confluentU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - a + n - 1) * exp (-z) * confluentU (a - n) b z := by
  sorry

/-- Iterated derivatives of `exp (-z) * U(a,b,z)`. `U` is not complex-differentiable on the cut, so
`z` is restricted to the slit plane. -/
@[dlmf 13.3.E27]
theorem iteratedDeriv_exp_neg_confluentU (a b : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w) * confluentU a b w) z =
      (-1 : ℂ) ^ n * exp (-z) * confluentU a (b + n) z := by
  sorry

@[dlmf 13.3.E28]
theorem iteratedDeriv_mul_cpow_exp_neg_confluentU (a b : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (b - 1) * exp (-w) * confluentU a b w) z =
      (-1 : ℂ) ^ n * z ^ (b - n - 1) * exp (-z) * confluentU (a - n) (b - n) z := by
  sorry

@[dlmf 13.15.E1]
theorem whittakerM_contiguous_kappa {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1) μ z + (z - 2 * κ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * whittakerM (κ + 1) μ z = 0 := by
  have hM := confluentM_contiguous_a (a := μ - κ + 1 / 2) hμ (z := z)
  rw [show μ - κ + 1 / 2 - 1 = μ - (κ + 1) + 1 / 2 by ring,
    show μ - κ + 1 / 2 + 1 = μ - (κ - 1) + 1 / 2 by ring] at hM
  unfold whittakerM
  linear_combination (exp (-z / 2) * z ^ (μ + 1 / 2)) * hM

@[dlmf 13.15.E2]
theorem whittakerM_contiguous_mu {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * (z : ℂ) ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := confluentM_contiguous_b (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E3]
theorem whittakerM_contiguous_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z +
      (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM κ μ z -
      (κ + μ + 1 / 2) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hM := confluentM_contiguous_shift_b_succ (a := μ - κ + 1 / 2) hμ (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  unfold whittakerM
  rw [show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP]
  linear_combination (-(exp (-z / 2) * z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ))) * hM

@[dlmf 13.15.E4]
theorem whittakerM_contiguous_half {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      2 * μ * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      z ^ (1 / 2 : ℂ) * whittakerM κ μ z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := confluentM_contiguous_shift_a (a := μ - κ + 1 / 2) hb1 (z := z)
  rw [sub_add_cancel] at hM
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) z) * hs

@[dlmf 13.15.E5]
theorem whittakerM_contiguous_mixed {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * whittakerM κ μ z -
      2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ - 1 / 2) z -
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := confluentM_contiguous_mixed_b_pred (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      confluentM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E6]
theorem whittakerM_contiguous_up {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z +
      (z - 2 * μ) * (1 + 2 * μ) * whittakerM κ μ z +
      (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := confluentM_contiguous_up_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ - 1 / 2) + 1 / 2 = μ - κ + 1 / 2 + 1 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM -
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (μ - κ + 1 / 2) *
      confluentM (μ - κ + 1 / 2 + 1) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E7]
theorem whittakerM_contiguous_up_shift {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    2 * μ * (1 + 2 * μ) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ - 1 / 2) z -
      2 * μ * (1 + 2 * μ) * whittakerM κ μ z +
      (κ + μ + 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerM (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hb1 : ∀ k : ℕ, 1 + 2 * μ - 1 ≠ -k := by simpa using hμ
  have hM := confluentM_contiguous_up_shift_aux (a := μ - κ + 1 / 2) hb1 (z := z)
  have hP : z ^ (μ + 1 / 2 + 1 / 2) = z ^ (μ + 1 / 2) * z ^ (1 / 2 : ℂ) := cpow_add _ _ hz0
  have hQ : z ^ (μ + 1 / 2) = z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  have hs : z ^ (1 / 2 : ℂ) * z ^ (1 / 2 : ℂ) = z := by
    rw [← cpow_add _ _ hz0]; norm_num
  unfold whittakerM
  rw [show μ - 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 - 1 by ring,
    show μ + 1 / 2 - (κ + 1 / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show 1 + 2 * (μ - 1 / 2) = 1 + 2 * μ - 1 by ring,
    show 1 + 2 * (μ + 1 / 2) = 1 + 2 * μ + 1 by ring, hP, hQ]
  linear_combination (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ)) * hM +
    (exp (-z / 2) * z ^ (μ - 1 / 2 + 1 / 2) * z ^ (1 / 2 : ℂ) * (1 + 2 * μ - (μ - κ + 1 / 2)) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ + 1) z) * hs

@[dlmf 13.15.E8]
theorem whittakerW_contiguous_up (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ + 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z = 0 := by
  sorry

@[dlmf 13.15.E9]
theorem whittakerW_contiguous_down (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    whittakerW (κ + 1 / 2) (μ - 1 / 2) z - z ^ (1 / 2 : ℂ) * whittakerW κ μ z +
      (κ + μ - 1 / 2) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  sorry

@[dlmf 13.15.E10]
theorem whittakerW_contiguous_mu (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    2 * μ * whittakerW κ μ z - z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  sorry

@[dlmf 13.15.E11]
theorem whittakerW_contiguous_kappa (κ μ z : ℂ) :
    whittakerW (κ + 1) μ z + (2 * κ - z) * whittakerW κ μ z +
      (κ - μ - 1 / 2) * (κ + μ - 1 / 2) * whittakerW (κ - 1) μ z = 0 := by
  sorry

@[dlmf 13.15.E12]
theorem whittakerW_contiguous_mixed (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z +
      2 * μ * whittakerW κ μ z -
      (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z = 0 := by
  sorry

@[dlmf 13.15.E13]
theorem whittakerW_contiguous_sum (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ + μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ - 1 / 2) z -
      (z + 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ + 1 / 2) z = 0 := by
  sorry

@[dlmf 13.15.E14]
theorem whittakerW_contiguous_diff (κ μ : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    (κ - μ - 1 / 2) * z ^ (1 / 2 : ℂ) * whittakerW (κ - 1 / 2) (μ + 1 / 2) z -
      (z - 2 * μ) * whittakerW κ μ z +
      z ^ (1 / 2 : ℂ) * whittakerW (κ + 1 / 2) (μ - 1 / 2) z = 0 := by
  sorry

/-- Iterates of `mulDerivMul` only depend on the function near the point. -/
private lemma iterate_mulDerivMul_congr {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (h : ∀ w ∈ U, f w = g w) (n : ℕ) :
    ∀ w ∈ U, mulDerivMul^[n] f w = mulDerivMul^[n] g w := by
  induction n with
  | zero => intro w hw; simpa using h w hw
  | succ n ih =>
    intro w hw
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', mulDerivMul, mulDerivMul]
    congr 1
    apply Filter.EventuallyEq.deriv_eq
    filter_upwards [hU.mem_nhds hw] with t ht
    rw [ih t ht]

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E15]
theorem iteratedDeriv_exp_mul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ - n / 2) (μ - n / 2) z := by
  sorry

@[dlmf 13.15.E16]
theorem iteratedDeriv_exp_mul_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n / poch (1 + 2 * μ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ - n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_confluentM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ - n / 2) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-(poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      confluentM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z)) * h1 -
    (poch (μ - κ + 1 / 2) n / poch (1 + 2 * μ) n *
      confluentM (μ - κ + 1 / 2 + n) (1 + 2 * μ + n) z * exp (z / 2) * exp (-z / 2)) * h2

@[dlmf 13.15.E17]
theorem iterate_mulDerivMul_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ - κ) n * exp (z / 2) * z ^ (n - κ - 1) *
        whittakerM (κ - n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (w / 2) * w ^ (-κ - 1) * whittakerM κ μ w =
      w ^ (μ - κ + 1 / 2 - 1) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (w / 2) * exp (-w / 2) = 1 := by
      rw [← Complex.exp_add, show w / 2 + -w / 2 = (0 : ℂ) by ring, Complex.exp_zero]
    have h2 : w ^ (-κ - 1) * w ^ (μ + 1 / 2) = w ^ (μ - κ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (-κ - 1) * w ^ (μ + 1 / 2) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_confluentM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ - (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 + n by ring,
    show (1 : ℂ) / 2 + μ - κ = μ - κ + 1 / 2 by ring]
  have h1 : exp (z / 2) * exp (-z / 2) = 1 := by
    rw [← Complex.exp_add, show z / 2 + -z / 2 = (0 : ℂ) by ring, Complex.exp_zero]
  have h2 : z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2) = z ^ (μ - κ + 1 / 2 + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (μ - κ + 1 / 2) n * confluentM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z *
      z ^ ((n : ℂ) - κ - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (μ - κ + 1 / 2) n * confluentM (μ - κ + 1 / 2 + n) (1 + 2 * μ) z) * h2

/-- An iterated Whittaker-M derivative with regular initial and shifted denominators. -/
@[dlmf 13.15.E18]
theorem iteratedDeriv_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane)
    (hshift : ∀ k : ℕ, 1 + 2 * μ - n ≠ -k) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (-2 * μ) n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerM (κ + n / 2) (μ - n / 2) z := by
  sorry

@[dlmf 13.15.E19]
theorem iteratedDeriv_exp_neg_whittakerM_neg {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n * exp (-z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerM (κ + n / 2) (μ + n / 2) z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have heq : (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerM κ μ w) =ᶠ[𝓝 z]
      (fun w => exp (-w) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) = 1 := by
      rw [← cpow_add _ _ hw0, show -μ - 1 / 2 + (μ + 1 / 2) = (0 : ℂ) by ring, cpow_zero]
    unfold whittakerM
    linear_combination (w ^ (-μ - 1 / 2) * w ^ (μ + 1 / 2) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [heq.iteratedDeriv_eq n, iteratedDeriv_exp_neg_confluentM n hμ]
  beta_reduce
  unfold whittakerM
  rw [show μ + (n : ℂ) / 2 - (κ + n / 2) + 1 / 2 = μ - κ + 1 / 2 by ring,
    show (1 : ℂ) + 2 * (μ + n / 2) = 1 + 2 * μ + n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2) = 1 := by
    rw [← cpow_add _ _ hz0, show -μ - ((n : ℂ) + 1) / 2 + (μ + n / 2 + 1 / 2) = (0 : ℂ) by ring,
      cpow_zero]
  linear_combination (-((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ + n) z *
      z ^ (-μ - ((n : ℂ) + 1) / 2) * z ^ (μ + n / 2 + 1 / 2))) * h1 -
    ((-1 : ℂ) ^ n * poch (1 / 2 + μ + κ) n / poch (1 + 2 * μ) n *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ + n) z * exp (-z)) * h2

@[dlmf 13.15.E20]
theorem iterate_mulDerivMul_exp_neg_whittakerM {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w) z =
      poch (1 / 2 + μ + κ) n * exp (-z / 2) * z ^ (κ + n - 1) *
        whittakerM (κ + n) μ z := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hfun : ∀ w ∈ slitPlane, exp (-w / 2) * w ^ (κ - 1) * whittakerM κ μ w =
      w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) * exp (-w) *
        confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w := by
    intro w hw
    have hw0 : w ≠ 0 := slitPlane_ne_zero hw
    have h1 : exp (-w / 2) * exp (-w / 2) = exp (-w) := by
      rw [← Complex.exp_add]; congr 1; ring
    have h2 : w ^ (κ - 1) * w ^ (μ + 1 / 2) = w ^ (1 + 2 * μ - (μ - κ + 1 / 2) - 1) := by
      rw [← cpow_add _ _ hw0]; congr 1; ring
    unfold whittakerM
    linear_combination (w ^ (κ - 1) * w ^ (μ + 1 / 2) *
      confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h1 +
      (exp (-w) * confluentM (μ - κ + 1 / 2) (1 + 2 * μ) w) * h2
  rw [iterate_mulDerivMul_congr isOpen_slitPlane hfun n z hz,
    iterate_mulDerivMul_exp_neg_confluentM n hμ hz]
  unfold whittakerM
  rw [show μ - (κ + (n : ℂ)) + 1 / 2 = μ - κ + 1 / 2 - n by ring,
    show (1 : ℂ) + 2 * μ - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring]
  have h1 : exp (-z / 2) * exp (-z / 2) = exp (-z) := by
    rw [← Complex.exp_add]; congr 1; ring
  have h2 : z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2) = z ^ (1 / 2 + μ + κ + n - 1) := by
    rw [← cpow_add _ _ hz0]; congr 1; ring
  linear_combination (-(poch (1 / 2 + μ + κ) n * confluentM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z *
      z ^ (κ + (n : ℂ) - 1) * z ^ (μ + 1 / 2))) * h1 -
    (poch (1 / 2 + μ + κ) n * confluentM (μ - κ + 1 / 2 - n) (1 + 2 * μ) z * exp (-z)) * h2

@[dlmf 13.15.E21]
theorem iteratedDeriv_exp_mul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 + μ - κ) n * exp (z / 2) *
        z ^ (-μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ + n / 2) z := by
  sorry

@[dlmf 13.15.E22]
theorem iteratedDeriv_exp_mul_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (μ - (n + 1) / 2) * whittakerW (κ - n / 2) (μ - n / 2) z := by
  sorry

@[dlmf 13.15.E23]
theorem iterate_mulDerivMul_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (w / 2) * w ^ (-κ - 1) * whittakerW κ μ w) z =
      poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n * exp (z / 2) *
        z ^ (n - κ - 1) * whittakerW (κ - n) μ z := by
  sorry

@[dlmf 13.15.E24]
theorem iteratedDeriv_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (-μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (-μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ + n / 2) z := by
  sorry

@[dlmf 13.15.E25]
theorem iteratedDeriv_exp_neg_whittakerW_pos {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun w => exp (-w / 2) * w ^ (μ - 1 / 2) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (μ - (n + 1) / 2) *
        whittakerW (κ + n / 2) (μ - n / 2) z := by
  sorry

@[dlmf 13.15.E26]
theorem iterate_mulDerivMul_exp_neg_whittakerW {κ μ : ℂ} (n : ℕ) {z : ℂ}
    (hz : z ∈ slitPlane) :
    mulDerivMul^[n] (fun w => exp (-w / 2) * w ^ (κ - 1) * whittakerW κ μ w) z =
      (-1 : ℂ) ^ n * exp (-z / 2) * z ^ (κ + n - 1) * whittakerW (κ + n) μ z := by
  sorry

end AAR.Confluent
