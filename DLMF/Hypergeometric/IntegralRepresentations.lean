/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.EulerIntegral
public import DLMF.Hypergeometric.BarnesAux
public import DLMF.Hypergeometric.Continuation
public import DLMF.Hypergeometric.FurtherTransformations
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Integral representations (DLMF §15.6)

The source uses Olver's regularized function. Euler's E1 is already recorded,
with the equivalent ordinary-function normalization, in `EulerIntegral`.
The substitutions and vertical Barnes integrals below need no continued contour
branches. Barnes's integral E6 is proved in `DLMF.Hypergeometric.BarnesAux` from the
Mellin–Barnes integral for `(1+u)^{-a}` and analytic continuation in `c`. The loop integral E2 is
in `DLMF.Hypergeometric.LoopIntegral`, over an explicit loop about `1`; E3–E5 (Pochhammer and
other loop contours) are not recorded.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace DLMF.Hypergeometric

@[dlmf 15.6.E2_5]
theorem integral_Ioi {a b c z : ℂ} (hb : 0 < b.re) (hcb : 0 < (c - b).re) (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 / (Gamma b * Gamma (c - b))) * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (b - 1) * (t + 1 : ℂ) ^ (a - c) / ((t : ℂ) - z * t + 1) ^ a := by
  have hc0 : 0 < c.re := by
    have : c.re = b.re + (c - b).re := by simp
    linarith
  have hcn : ∀ k : ℕ, c ≠ -(k : ℂ) := not_neg_nat_of_re_pos hc0
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc0
  -- The substitution `u = t/(1+t)`.
  set f : ℝ → ℝ := fun t => t / (1 + t) with hf
  set f' : ℝ → ℝ := fun t => 1 / (1 + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Set.Ioi 0) t := by
    intro t ht
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp ht])
    have hd : HasDerivAt f (f' t) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1 using 1
      · rfl
      · simp only [hf', id]; ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioi 0) := by
    intro x hx y hy hxy
    have hx' : 1 + x ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hx])
    have hy' : 1 + y ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp hy])
    simp only [hf] at hxy
    field_simp at hxy
    linarith
  have himage : f '' Set.Ioi 0 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht' : 0 < t := ht
      refine ⟨by positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      linarith
    · rintro ⟨h0, h1⟩
      refine ⟨u / (1 - u), div_pos h0 (by linarith), ?_⟩
      have : 1 - u ≠ 0 := ne_of_gt (by linarith)
      simp only [hf]
      field_simp
      ring
  have key := MeasureTheory.integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (b - 1) * (1 - (u : ℂ)) ^ (c - b - 1) * (1 - z * u) ^ (-a))
  rw [himage] at key
  rw [regularizedGaussHGFun_eq_div_Gamma hcn, ordinaryHypergeometric_eq_integral hb hcb hz,
    intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_Ioc_eq_integral_Ioo, key]
  have hpt : ∫ t : ℝ in Set.Ioi 0, |f' t| • ((f t : ℂ) ^ (b - 1) * (1 - (f t : ℂ)) ^ (c - b - 1) *
      (1 - z * f t) ^ (-a)) = ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (b - 1) * (t + 1 : ℂ) ^ (a - c) / ((t : ℂ) - z * t + 1) ^ a := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have ht1 : 0 < 1 + t := by linarith
    set X : ℂ := 1 + t - z * t with hX
    have hXre : 0 < X.re := by
      have := (re_le_norm z).trans_lt hz
      simp only [hX, sub_re, add_re, one_re, ofReal_re, mul_re, ofReal_im, mul_zero, sub_zero]
      nlinarith
    have hX0 : X ≠ 0 := by intro h; rw [h] at hXre; simp at hXre
    have hft : 0 < f t := by simp only [hf]; positivity
    have h1ft : 1 - f t = 1 / (1 + t) := by simp only [hf]; field_simp; ring
    have e1 : (1 - (f t : ℂ)) = ((1 / (1 + t) : ℝ) : ℂ) := by rw [← h1ft]; push_cast; ring
    have e2 : 1 - z * (f t : ℂ) = X * (((1 + t)⁻¹ : ℝ) : ℂ) := by
      have h1t : (1 + (t : ℂ)) ≠ 0 := by exact_mod_cast ht1.ne'
      simp only [hf, hX]; push_cast; field_simp
    have e3 : ((t : ℂ) - z * t + 1) = X := by rw [hX]; ring
    have e4 : (t + 1 : ℂ) = ((1 + t : ℝ) : ℂ) := by push_cast; ring
    rw [e1, e2, e3, e4, abs_of_pos (by simp only [hf']; positivity), Complex.real_smul,
      ofReal_cpow_eq_exp_log hft, ofReal_cpow_eq_exp_log (by positivity),
      ofReal_cpow_eq_exp_log ht0, ofReal_cpow_eq_exp_log ht1,
      cpow_def_of_ne_zero (mul_ne_zero hX0 (ofReal_ne_zero.mpr (by positivity))),
      Complex.log_mul_ofReal _ (by positivity) _ hX0, cpow_def_of_ne_zero hX0,
      show ((f' t : ℝ) : ℂ) = Complex.exp (((-2 * Real.log (1 + t) : ℝ) : ℂ)) by
        rw [← ofReal_exp, show -2 * Real.log (1 + t) = -(Real.log (1 + t) + Real.log (1 + t)) by
          ring, Real.exp_neg, Real.exp_add, Real.exp_log ht1]
        simp only [hf']; push_cast; ring,
      show f t = t / (1 + t) from rfl, Real.log_div ht0.ne' ht1.ne', one_div,
      Real.log_inv, div_eq_mul_inv, ← Complex.exp_neg]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hpt, show ∀ Y : ℂ, Gamma c / (Gamma b * Gamma (c - b)) * Y / Gamma c =
    1 / (Gamma b * Gamma (c - b)) * Y from fun Y => by field_simp]

/-- A vertical separating line `t = σ + i y`; the factor `i` from `dt` is canceled. -/
@[dlmf 15.6.E6]
theorem barnes_integral {a b c : ℂ} {x σ : ℝ} (hx : -1 < x) (hx0 : x < 0)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0) :
    regularizedGaussHGFun a b c (x : ℂ) =
      (1 / (2 * Real.pi * Gamma a * Gamma b)) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
          Gamma (c + σ + I * y) * (-(x : ℂ)) ^ ((σ : ℂ) + I * y) :=
  barnes_integral_all hx hx0 ha hb hσ

@[dlmf 15.6.E7]
theorem barnes_integral_one_sub {a b c z : ℂ} {σ : ℝ} (hz : ‖z‖ < 1)
    (ha : 0 < a.re + σ) (hb : 0 < b.re + σ) (hσ : σ < 0)
    (hc : σ < (c - a - b).re) :
    regularizedGaussHGFun a b c z =
      (1 / (2 * Real.pi * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))) * ∫ y : ℝ,
        Gamma (a + σ + I * y) * Gamma (b + σ + I * y) * Gamma (c - a - b - σ - I * y)*
          Gamma (-((σ : ℂ) + I * y)) * (1 - z) ^ ((σ : ℂ) + I * y) := by
  sorry

/-- Absolute summability of the regularized series inside the unit disk. -/
lemma summable_norm_regularizedGaussHGFun_term (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖(ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n /
      n.factorial * (Gamma (c + n))⁻¹‖ := by
  have h := (regularizedGaussHGFunSeries a b c).summable_norm_apply
    (mem_eball_radius_regularizedGaussHGFunSeries a b c hz)
  refine h.congr fun n => ?_
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, coeff_regularizedGaussHGFunSeries,
    smul_eq_mul]
  congr 1
  ring

@[dlmf 15.6.E8]
theorem fractional_integral {a b c d z : ℂ} (hd : 0 < d.re) (hcd : 0 < (c - d).re) (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (1 / Gamma (c - d)) * ∫ t : ℝ in (0 : ℝ)..1,
        regularizedGaussHGFun a b d (z * t) * (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1)
  let e : ℕ → ℂ := fun n => (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n /
    n.factorial * (Gamma (d + n))⁻¹
  let F : ℕ → ℝ → ℂ := fun n t => w t * (e n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent hd hcd
  have he : Summable (fun n => ‖e n‖) := summable_norm_regularizedGaussHGFun_term a b d hz
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => regularizedGaussHGFun a b d (z * t) * (t : ℂ) ^ (d - 1) *
      (1 - (t : ℂ)) ^ (c - d - 1))
    (fun n t => ‖e n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => he.mul_right ‖w t‖)
    (by
      simp_rw [tsum_mul_right]
      exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t ht => ?_)
  · have hc0 : 0 < c.re := by
      have : c.re = d.re + (c - d).re := by simp
      linarith
    have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t = e n * betaIntegral (d + n) (c - d) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht.1)
      have hp : (t : ℂ) ^ (d + n - 1) = (t : ℂ) ^ (d - 1) * (t : ℂ) ^ n := by
        rw [show d + n - 1 = (d - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
      simp only [F, w, e]
      rw [hp]
      ring
    have hdn (n : ℕ) : 0 < (d + n).re := by
      have : (d + n).re = d.re + n := by simp
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hscaled (n : ℕ) : 1 / Gamma (c - d) * (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b * z ^ n / n.factorial *
          (Gamma (c + n))⁻¹ := by
      have hB := Gamma_mul_Gamma_eq_betaIntegral (hdn n) hcd
      rw [show d + n + (c - d) = c + n by ring] at hB
      have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by
        have : (c + n).re = c.re + n := by simp
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
      have hdn0 : Gamma (d + n) ≠ 0 := Gamma_ne_zero_of_re_pos (hdn n)
      have hcd0 : Gamma (c - d) ≠ 0 := Gamma_ne_zero_of_re_pos hcd
      have hBeq : betaIntegral (d + n) (c - d) = Gamma (d + n) * Gamma (c - d) / Gamma (c + n) := by
        rw [eq_div_iff hcn, mul_comm]; exact hB.symm
      rw [hterm, hBeq]
      simp only [e]
      field_simp
    have hs' := hs.mul_left (1 / Gamma (c - d))
    simp_rw [hscaled] at hs'
    rw [regularizedGaussHGFun_eq_tsum, ← hs'.tsum_eq]
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖e n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖e n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have hzt : ‖z * t‖ < 1 := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1]
      nlinarith [norm_nonneg z, ht.2]
    have h := (summable_regularizedGaussHGFun_term a b d hzt).hasSum
    rw [← regularizedGaussHGFun_eq_tsum] at h
    have h' := h.mul_left (w t)
    simp only [F, e, w]
    convert h' using 1
    · funext n
      rw [mul_pow]
      ring
    · ring

@[dlmf 15.6.E9]
theorem product_integral {a b c d : ℂ} (l : ℂ) {x : ℝ}
    (hd : 0 < d.re) (hcd : 0 < (c - d).re) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    regularizedGaussHGFun a b c (x : ℂ) =
      ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (d - 1) * (1 - (t : ℂ)) ^ (c - d - 1) / (1 - (x : ℂ) * t) ^ (a + b - l) *
          regularizedGaussHGFun (l - a) (l - b) d ((x : ℂ) * t) *
          regularizedGaussHGFun (a + b - l) (l - d) (c - d) ((1 - (t : ℂ)) * x / (1 - (x : ℂ) * t)) := by
  sorry

end DLMF.Hypergeometric
