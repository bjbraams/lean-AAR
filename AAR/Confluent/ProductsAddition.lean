/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import AAR.Confluent.Recurrence
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Products and addition theorems (DLMF §§13.12, 13.13, 13.25, 13.26)

For U and Whittaker addition formulas, `Re x > 0` keeps the Taylor domain
on the principal branch. Downward shifts of ordinary M exclude integer denominator
parameters: the old formulas at `b = 1` discarded nonzero limiting terms as `0 * 0`.
-/

@[expose] public section

open Complex
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

/-- A disk centered in the right half-plane, with radius the distance to zero,
avoids the nonpositive real axis. -/
lemma ball_norm_subset_slitPlane {x : ℂ} (hx : 0 < x.re) :
    Metric.ball x ‖x‖ ⊆ slitPlane := by
  intro w hw
  rw [mem_slitPlane_iff]
  by_contra! h
  have hn : ‖w - x‖ < ‖x‖ := by simpa only [Metric.mem_ball, dist_eq] using hw
  have hs := (sq_lt_sq₀ (norm_nonneg (w - x)) (norm_nonneg x)).mpr hn
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq] at hs
  simp only [normSq_apply, sub_re, sub_im, h.2, zero_sub, neg_mul_neg] at hs
  nlinarith [mul_nonpos_of_nonpos_of_nonneg h.1 hx.le, sq_nonneg w.re]

/-- Principal powers multiply without a branch correction when both factors
lie in the right half-plane. -/
lemma cpow_mul_of_re_pos {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) (s : ℂ) :
    (u * v) ^ s = u ^ s * v ^ s := by
  have hu0 := slitPlane_ne_zero (Or.inl hu : u ∈ slitPlane)
  have hv0 := slitPlane_ne_zero (Or.inl hv : v ∈ slitPlane)
  have hua := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hu))
  have hva := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hv))
  rw [cpow_def_of_ne_zero (mul_ne_zero hu0 hv0), cpow_def_of_ne_zero hu0,
    cpow_def_of_ne_zero hv0, log_mul hu0 hv0 ⟨by linarith, by linarith⟩, ← exp_add]
  congr 1; ring

/-- The power factor in the downward-parameter Taylor formulas. -/
lemma cpow_add_shift_factor {x y : ℂ} (hx : 0 < x.re) (hy : ‖y‖ < ‖x‖)
    (b : ℂ) (n : ℕ) :
    (x + y) ^ (1 - b) * x ^ (b - n - 1) = ((x + y) / x) ^ (1 - b) / x ^ n := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  have hdiv : ‖y / x‖ < 1 := by
    rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hx0)).mpr hy
  have hr : 0 < ((x + y) / x).re := by
    have h := re_le_norm (-(y / x))
    simp only [neg_re, norm_neg] at h
    rw [add_div, div_self hx0]
    simp only [add_re, one_re]
    linarith
  have hp : (x + y) ^ (1 - b) = ((x + y) / x) ^ (1 - b) * x ^ (1 - b) := by
    rw [← cpow_mul_of_re_pos hr hx, div_mul_cancel₀ _ hx0]
  rw [hp, mul_assoc, ← cpow_add _ _ hx0,
    show 1 - b + (b - (n : ℂ) - 1) = -(n : ℂ) by ring, cpow_neg, cpow_natCast]
  rfl

@[dlmf 13.12.E1]
theorem confluentM_product {a b z : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (hb1 : ∀ k : ℕ, 1 - b ≠ -k)
    (hb0 : b ≠ 0) (hb2 : b ≠ 1) (hb3 : b ≠ -1) :
    confluentM a b z * confluentM (-a) (-b) (-z) +
      a * (a - b) * z ^ 2 / (b ^ 2 * (1 - b ^ 2)) *
        confluentM (1 + a) (2 + b) z * confluentM (1 - a) (2 - b) (-z) = 1 := by
  sorry

@[dlmf 13.13.E1]
theorem confluentM_addition {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      ∑' n : ℕ, poch a n * y ^ n / (poch b n * n.factorial) * confluentM (a + n) (b + n) x := by
  have hd : Differentiable ℂ (confluentM a b) := fun w =>
    ((analyticOnNhd_confluentM (a := a) hb) w (Set.mem_univ _)).differentiableAt
  rw [← Complex.taylorSeries_eq_of_entire' (c := x) (z := x + y) hd]
  congr 1
  funext n
  rw [iteratedDeriv_confluentM n hb, add_sub_cancel_left]
  ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E2]
theorem confluentM_addition_shift_b {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hb : ∀ k : ℤ, b ≠ k) :
    confluentM a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y / x) ^ n / n.factorial * confluentM a (b - n) x := by
  sorry

@[dlmf 13.13.E3]
theorem confluentM_addition_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * y ^ n / (n.factorial * (x + y) ^ n) * confluentM (a + n) b x := by
  sorry

@[dlmf 13.13.E4]
theorem confluentM_addition_exp {a b x y : ℂ} (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      exp y * ∑' n : ℕ, poch (b - a) n * (-y) ^ n / (poch b n * n.factorial) *
        confluentM a (b + n) x := by
  set f : ℂ → ℂ := fun w => exp (-w) * confluentM a b w with hf
  have hd : Differentiable ℂ f := fun w =>
    (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => exp (-w)) w).mul
      ((analyticOnNhd_confluentM (a := a) hb) w (Set.mem_univ _)).differentiableAt
  have ht := Complex.taylorSeries_eq_of_entire' (c := x) (z := x + y) hd
  have hM : confluentM a b (x + y) = exp (x + y) * f (x + y) := by
    simp only [hf, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  rw [hM, ← ht, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [hf, iteratedDeriv_exp_neg_confluentM n hb, add_sub_cancel_left, exp_add]
  beta_reduce
  rw [exp_neg]
  have hx : exp x ≠ 0 := exp_ne_zero x
  rw [neg_pow y]
  field_simp

@[dlmf 13.13.E5]
theorem confluentM_addition_exp_shift_a {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, poch (b - a) n * y ^ n / (n.factorial * (x + y) ^ n) *
          confluentM (a - n) b x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E6]
theorem confluentM_addition_exp_shift_both {a b x y : ℂ} (hx : x ∈ slitPlane)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hb : ∀ k : ℤ, b ≠ k) :
    confluentM a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 - b) n * (-y) ^ n / (n.factorial * x ^ n) *
          confluentM (a - n) (b - n) x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E7]
theorem confluentU_addition (a b : ℂ) {x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    confluentU a b (x + y) =
      ∑' n : ℕ, poch a n * (-y) ^ n / n.factorial * confluentU (a + n) (b + n) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  have hd : DifferentiableOn ℂ (confluentU a b) (Metric.ball x ‖x‖) :=
    fun w hw => (differentiableAt_confluentU a b (ball_norm_subset_slitPlane hx hw)).differentiableWithinAt
  rw [← Complex.taylorSeries_eq_on_ball' (c := x) (z := x + y)
    (by simpa [mem_ball_iff_norm] using hyx) hd]
  congr 1
  funext n
  rw [iteratedDeriv_confluentU a b n hx', add_sub_cancel_left, neg_pow]
  ring

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E8]
theorem confluentU_addition_shift_b {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    confluentU a b (x + y) =
      ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, poch (1 + a - b) n * (-y / x) ^ n / n.factorial * confluentU a (b - n) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  rw [confluentU_kummer_transform_all a b (slitPlane_ne_zero hxy),
    confluentU_addition (a - b + 1) (2 - b) hx hxy hyx,
    ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [confluentU_kummer_transform_all (a - b + 1 + n) (2 - b + n) hx0,
    show (a - b + 1 + n) - (2 - b + n) + 1 = a by ring,
    show 2 - (2 - b + (n : ℂ)) = b - n by ring,
    show 1 - (2 - b + (n : ℂ)) = b - n - 1 by ring]
  have hp := cpow_add_shift_factor hx hyx b n
  rw [div_pow, show (1 : ℂ) + a - b = a - b + 1 by ring]
  linear_combination (poch (a - b + 1) n * (-y) ^ n / n.factorial * confluentU a (b - n) x) * hp

@[dlmf 13.13.E9]
theorem confluentU_addition_shift_a {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    confluentU a b (x + y) =
      (x / (x + y)) ^ a *
        ∑' n : ℕ, poch a n * poch (1 + a - b) n * y ^ n / (n.factorial * (x + y) ^ n) *
          confluentU (a + n) b x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E10]
theorem confluentU_addition_exp (a b : ℂ) {x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    confluentU a b (x + y) =
      exp y * ∑' n : ℕ, (-y) ^ n / n.factorial * confluentU a (b + n) x := by
  have hx' : x ∈ slitPlane := Or.inl hx
  set f : ℂ → ℂ := fun w => exp (-w) * confluentU a b w with hf
  have hd : DifferentiableOn ℂ f (Metric.ball x ‖x‖) := by
    intro w hw
    exact ((by fun_prop : DifferentiableAt ℂ (fun w : ℂ => exp (-w)) w).mul
      (differentiableAt_confluentU a b (ball_norm_subset_slitPlane hx hw))).differentiableWithinAt
  have ht := Complex.taylorSeries_eq_on_ball' (c := x)
    (z := x + y) (by simpa [mem_ball_iff_norm] using hyx) hd
  have hU : confluentU a b (x + y) = exp (x + y) * f (x + y) := by
    simp only [hf, ← mul_assoc, ← exp_add, add_neg_cancel, exp_zero, one_mul]
  rw [hU, ← ht, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [hf, iteratedDeriv_exp_neg_confluentU a b n hx', add_sub_cancel_left, exp_add, exp_neg, neg_pow y]
  field_simp

@[dlmf 13.13.E11]
theorem confluentU_addition_exp_shift_a {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    confluentU a b (x + y) =
      exp y * (x / (x + y)) ^ (b - a) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * (x + y) ^ n) * confluentU (a - n) b x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.13.E12]
theorem confluentU_addition_exp_shift_both {a b x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    confluentU a b (x + y) =
      exp y * ((x + y) / x) ^ (1 - b) *
        ∑' n : ℕ, (-y) ^ n / (n.factorial * x ^ n) * confluentU (a - n) (b - n) x := by
  have hx0 := slitPlane_ne_zero (Or.inl hx : x ∈ slitPlane)
  rw [confluentU_kummer_transform_all a b (slitPlane_ne_zero hxy),
    confluentU_addition_exp (a - b + 1) (2 - b) hx hxy hyx,
    ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 1
  funext n
  rw [confluentU_kummer_transform_all (a - b + 1) (2 - b + n) hx0,
    show (a - b + 1) - (2 - b + n) + 1 = a - n by ring,
    show 2 - (2 - b + (n : ℂ)) = b - n by ring,
    show 1 - (2 - b + (n : ℂ)) = b - n - 1 by ring]
  have hp := cpow_add_shift_factor hx hyx b n
  linear_combination (exp y * (-y) ^ n / n.factorial * confluentU (a - n) (b - n) x) * hp

/-- Whittaker product formula for `2μ` not an integer, where all four `M` factors are regular. -/
@[dlmf 13.25.E1]
theorem whittakerM_product {κ μ z : ℂ} (hμ : ∀ k : ℕ, 2 * μ ≠ -k)
    (hμ1 : μ ≠ 0) (hμ2 : μ ≠ -1) (hμ3 : 1 + 2 * μ ≠ 0) (hμpos : ∀ k : ℕ, 2 * μ ≠ k + 1)
    (hz : z ∈ slitPlane) :
    whittakerM κ μ z * whittakerM κ (-μ - 1) z +
      (1 / 2 + μ + κ) * (1 / 2 + μ - κ) / (4 * μ * (1 + μ) * (1 + 2 * μ) ^ 2) *
        whittakerM κ (μ + 1) z * whittakerM κ (-μ) z = 1 := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E1]
theorem whittakerM_addition {κ μ x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖)
    (hμ : ∀ k : ℤ, 1 + 2 * μ ≠ k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ - n / 2) (μ - n / 2) x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E2]
theorem whittakerM_addition_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ - n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E3]
theorem whittakerM_addition_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ - n) μ x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E4]
theorem whittakerM_addition_exp {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℤ, 1 + 2 * μ ≠ k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (-2 * μ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerM (κ + n / 2) (μ - n / 2) x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E5]
theorem whittakerM_addition_exp_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n / (poch (1 + 2 * μ) n * n.factorial) *
          (-y / x ^ (1 / 2 : ℂ)) ^ n * whittakerM (κ + n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E6]
theorem whittakerM_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : 1 / 2 < ((y + x) / x).re)
    (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ + κ) n * y ^ n / (n.factorial * (x + y) ^ n) *
          whittakerM (κ + n) μ x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E7]
theorem whittakerW_addition {κ μ x y : ℂ} (hx : 0 < x.re) (hxy : x + y ∈ slitPlane)
    (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 - μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ - n / 2) x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E8]
theorem whittakerW_addition_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n / n.factorial * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ - n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E9]
theorem whittakerW_addition_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (-y / 2) * ((x + y) / x) ^ κ *
        ∑' n : ℕ, poch (1 / 2 + μ - κ) n * poch (1 / 2 - μ - κ) n / n.factorial *
          (y / (x + y)) ^ n * whittakerW (κ - n) μ x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E10]
theorem whittakerW_addition_exp {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ (μ - 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ - n / 2) x := by
  sorry

/-- Addition theorem; the series converges for `‖y‖ < ‖x‖`. -/
@[dlmf 13.26.E11]
theorem whittakerW_addition_exp_shift_mu {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hyx : ‖y‖ < ‖x‖) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * ((x + y) / x) ^ (μ + 1 / 2) *
        ∑' n : ℕ, (1 / n.factorial) * (-y / x ^ (1 / 2 : ℂ)) ^ n *
          whittakerW (κ + n / 2) (μ + n / 2) x := by
  sorry

@[dlmf 13.26.E12]
theorem whittakerW_addition_exp_shift_kappa {κ μ x y : ℂ} (hx : 0 < x.re)
    (hxy : x + y ∈ slitPlane) (hy : -1 / 2 < (y / x).re) :
    whittakerW κ μ (x + y) =
      exp (y / 2) * (x / (x + y)) ^ κ *
        ∑' n : ℕ, (1 / n.factorial) * (-y / (x + y)) ^ n * whittakerW (κ + n) μ x := by
  sorry

end AAR.Confluent
