/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Bessel.Basic

/-! # Absolute convergence of the Bessel generating function

Regroup the product of two exponential series by the difference of their indices.
Mathlib's regularized hypergeometric parameter shift supplies the negative integer orders.
-/

@[expose] public noncomputable section

open Complex
open scoped Nat

/-- Reflection in an integer order, including the value at zero.
This uses Mathlib's parameter-shift identity for regularized `₀F₁`. -/
@[dlmf 10.4.E1]
lemma besselJ_neg_int (n : ℤ) (z : ℂ) : besselJ (-n) z = (-1) ^ n * besselJ n z := by
  wlog hn : 0 ≤ n
  · have he := this (-n) z (by omega)
    simp only [Int.cast_neg, neg_neg, zpow_neg] at he
    rw [he, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by norm_num)), one_mul]
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hp : (z / 2) ^ (n : ℂ) = (z / 2) ^ (-(n : ℂ)) * ((z / 2) ^ 2) ^ n := by
    by_cases hz : z = 0
    · by_cases hn : n = 0 <;> simp [hz, hn]
    rw [← pow_mul, ← cpow_natCast, ← cpow_add _ _ (by simpa using hz)]
    congr 1
    push_cast
    ring
  simp only [besselJ, Int.cast_natCast, zpow_natCast]
  have hshift := regularizedHGFun_zero_singleton_neg_nat_add_one n (-(z ^ 2 / 4))
  change regularizedHGFun ∅ {-(n : ℂ) + 1} (-(z ^ 2 / 4)) =
    (-(z ^ 2 / 4)) ^ n * regularizedHGFun ∅ {(n : ℂ) + 1} (-(z ^ 2 / 4)) at hshift
  rw [hshift, hp]
  rw [show -(z ^ 2 / 4) = -((z / 2) ^ 2) by ring, neg_pow]
  ring

private def besselDiagonalEquiv (n : ℤ) :
    ℕ ≃ {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = n} where
  toFun k := ⟨(k + n.toNat, k + (-n).toNat), by omega⟩
  invFun p := min p.val.1 p.val.2
  left_inv k := by dsimp; omega
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> dsimp
    all_goals have := p.property; omega

/-- A diagonal of the product of two exponential series is a regularized `₀F₁`. -/
private lemma bessel_diagonal_sum (x y : ℂ) (n : ℕ) :
    (∑' k : ℕ, x ^ (k + n) / (k + n) ! * (y ^ k / k !)) =
      x ^ n * regularizedHGFun ∅ {(n : ℂ) + 1} (x * y) := by
  have h := ((hasFPowerSeriesOnBall_regularized0F1 ((n : ℂ) + 1)).hasSum_mul_pow
    (z := x * y) (by simp)).mul_left (x ^ n)
  convert h.tsum_eq using 1
  apply tsum_congr
  intro k
  rw [regularizedHGFunCoeff_empty,
    show (n : ℂ) + 1 + k = (k + n : ℕ) + 1 by push_cast; ring,
    Gamma_nat_eq_factorial]
  simp only [pow_add, mul_pow]
  ring

set_option maxHeartbeats 800000 in
/-- The bilateral generating series converges absolutely and has its classical sum. -/
lemma hasSum_besselJ_generating_function (z t : ℂ) (ht : t ≠ 0) :
    HasSum (fun n : ℤ => besselJ n z * t ^ n) (exp (z / 2 * (t - t⁻¹))) := by
  let x := z / 2 * t
  let y := -(z / 2) * t⁻¹
  have hx : HasSum (fun k : ℕ => x ^ k / k !) (exp x) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp x
  have hy : HasSum (fun k : ℕ => y ^ k / k !) (exp y) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp y
  have hxy : x * y = -(z ^ 2 / 4) := by dsimp [x, y]; field_simp; ring
  have hs := hx.mul hy (summable_mul_of_summable_norm hx.summable.norm hy.summable.norm)
  have hf := hs.tsum_fiberwise (fun p : ℕ × ℕ => (p.1 : ℤ) - p.2)
  have hdiag (n : ℤ) :
      (∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = n},
        x ^ p.val.1 / p.val.1 ! * (y ^ p.val.2 / p.val.2 !)) = besselJ n z * t ^ n := by
    rw [← (besselDiagonalEquiv n).tsum_eq]
    change (∑' k : ℕ, x ^ (k + n.toNat) / (k + n.toNat) ! *
      (y ^ (k + (-n).toNat) / (k + (-n).toNat) !)) = _
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · simp only [Int.toNat_natCast, Int.toNat_neg_natCast, add_zero]
      rw [bessel_diagonal_sum, hxy]
      simp only [besselJ, Int.cast_natCast, cpow_natCast, zpow_natCast, x, mul_pow]
      ring
    · simp only [Int.toNat_natCast, Int.toNat_neg_natCast, neg_neg, add_zero]
      simp_rw [mul_comm (x ^ _ / _) (y ^ _ / _)]
      rw [bessel_diagonal_sum, mul_comm y x, hxy]
      rw [Int.cast_neg, besselJ_neg_int]
      rw [show y ^ n = (-1 : ℂ) ^ n * (z / 2) ^ n * (t ^ n)⁻¹ by
        dsimp [y]
        rw [mul_pow, neg_pow, inv_pow]]
      simp only [besselJ, Int.cast_natCast, cpow_natCast, zpow_natCast, zpow_neg]
      ring
  have he : exp x * exp y = exp (z / 2 * (t - t⁻¹)) := by
    rw [← exp_add]
    congr 1
    dsimp [x, y]
    ring
  change HasSum (fun n : ℤ => ∑' p : {p : ℕ × ℕ // (p.1 : ℤ) - p.2 = n},
    x ^ p.val.1 / p.val.1 ! * (y ^ p.val.2 / p.val.2 !)) (exp x * exp y) at hf
  simp_rw [hdiag] at hf
  rwa [he] at hf
