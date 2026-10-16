/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Confluence
public import AAR.Confluent.Whittaker
public import AAR.Bessel.Basic
public import AAR.Bessel.Modified
public import AAR.Hypergeometric.EulerIntegral
public import AAR.Hypergeometric.ArgumentContinuation
public import AAR.Hypergeometric.IntegralRepresentations
public import AAR.Hypergeometric.Solutions
public import AAR.Gamma.IntegralRepresentations
public import AAR.Gamma.Asymptotics
public import TauCeti.Analysis.SpecialFunctions.Beta
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral representations (DLMF §§13.4, 13.16)

Gauss kernels use cut-plane continuation, since their arguments range over the
negative ray. Argument bounds explicitly exclude zero where needed.

Euler, Laplace, Bessel, and vertical Barnes integrals are acquired on real
intervals or vertical lines. Hankel-loop and Pochhammer-double-loop formulas
13.4.9–13.4.15 are deferred pending a contour API, matching Chapter 15.
The `M` form of 13.4.1 is already `confluentM_eq_euler_integral` in `Basic`.
Tricomi's Laplace representation is proved in its full stated region. The Gauss
connection formula tends to the defining Tricomi connection, while its Euler
integral tends to the Laplace integral. The Tau Ceti contributors' second Beta
integrability theorem supplies the fixed majorant; Mathlib's real Bernoulli
inequality and dominated convergence justify the limit. Holomorphic continuation
in the argument and continuity in the second parameter cover every parameter.
The Whittaker W Laplace representation follows by an affine substitution.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology ENNReal

noncomputable section

namespace AAR.Confluent

@[dlmf 13.4.E1]
theorem regularized_euler_integral {a b z : ℂ} (ha : 0 < a.re) (hba : 0 < (b - a).re) :
    regularizedHGFun {a} {b} z =
      1 / (Gamma a * Gamma (b - a)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) := by
  have hb : ∀ k : ℕ, b ≠ -k := not_neg_nat_of_re_pos (by
    have h : b.re = a.re + (b - a).re := by simp [sub_re]
    linarith)
  have hG : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hM := confluentM_eq_euler_integral (a := a) (c := b) (z := z) ha hba
  rw [confluentM_eq_mul_regularizedHGFun hb] at hM
  apply mul_left_cancel₀ hG
  rw [hM]
  have hinter :
      (∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) * exp (z * t)) =
      ∫ t : ℝ in (0 : ℝ)..1,
        exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [hinter]
  simp [div_eq_mul_inv, one_div, mul_assoc]

/-- Raising the denominator parameter by termwise Beta integration of the entire
regularized Kummer series. -/
@[dlmf 13.4.E2]
theorem regularized_parameter_integral {a b c z : ℂ}
    (hc : 0 < c.re) (hbc : 0 < (b - c).re) :
    regularizedHGFun {a} {b} z =
      1 / Gamma (b - c) *
        ∫ t : ℝ in (0 : ℝ)..1,
          regularizedHGFun {a} {c} (z * t) * (t : ℂ) ^ (c - 1) *
            (1 - (t : ℂ)) ^ (b - c - 1) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (c - 1) * (1 - (t : ℂ)) ^ (b - c - 1)
  let d : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n * z ^ n
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hw : IntervalIntegrable w volume 0 1 := betaIntegral_convergent hc hbc
  have hd : Summable (fun n => ‖d n‖) :=
    ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
      (z := z) (by simp)).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := volume)
    (F := F) (f := fun t => w t * regularizedHGFun {a} {c} (z * t))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t _ => ?_)
  · have hterm (n : ℕ) : (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        d n * betaIntegral (c + n) (b - c) := by
      rw [betaIntegral, ← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      dsimp only
      rw [show c + n - 1 = (c - 1) + n by ring,
        cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]
      dsimp [F, w]
      ring
    have hscaled (n : ℕ) : 1 / Gamma (b - c) * (∫ t : ℝ in (0 : ℝ)..1, F n t) =
        regularizedHGFunCoeff {a} {b} n * z ^ n := by
      have hcn : 0 < (c + n).re := by simp; positivity
      have hbn : 0 < (b + n).re := by
        have he : b.re = c.re + (b - c).re := by simp
        simp only [add_re, natCast_re]
        linarith [Nat.cast_nonneg (α := ℝ) n]
      have hbeta : betaIntegral (c + n) (b - c) =
          Gamma (c + n) * Gamma (b - c) / Gamma (b + n) := by
        apply (eq_div_iff (Gamma_ne_zero_of_re_pos hbn)).mpr
        have he := Gamma_mul_Gamma_eq_betaIntegral hcn hbc
        rw [show c + n + (b - c) = b + n by ring] at he
        simpa [mul_comm] using he.symm
      rw [hterm, hbeta]
      dsimp only [d]
      rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton]
      field_simp [Gamma_ne_zero_of_re_pos hbc, Gamma_ne_zero_of_re_pos hcn]
    have ht := hs.mul_left (1 / Gamma (b - c))
    simp_rw [hscaled] at ht
    have hseries := (hasFPowerSeriesOnBall_regularizedConfluent a b).hasSum_mul_pow
      (z := z) (by simp)
    rw [← ht.unique hseries]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only [w]
    ring
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    change ‖w t * (d n * (t : ℂ) ^ n)‖ ≤ ‖d n‖ * ‖w t‖
    simp only [norm_mul, norm_pow]
    calc
      ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) ≤ ‖w t‖ * (‖d n‖ * 1) := by
        gcongr
        exact pow_le_one₀ (norm_nonneg _) ht1
      _ = _ := by ring
  · convert ((hasFPowerSeriesOnBall_regularizedConfluent a c).hasSum_mul_pow
      (z := z * t) (by simp)).mul_left (w t) using 1
    funext n
    simp only [F, d, mul_pow]
    ring

@[dlmf 13.4.E3]
theorem regularized_bessel_integral {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    regularizedHGFun {a} {b} (-z) =
      z ^ ((1 - b) / 2) / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) * besselJ (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

/-- Absolute convergence of Tricomi's Laplace kernel throughout its stated
parameter region. A natural power of `1+t` supplies a finite Gamma majorant. -/
lemma confluentU_laplace_integrable {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => exp (-z * t) * (t : ℂ) ^ (a - 1) *
      (1 + (t : ℂ)) ^ (b - a - 1)) (Set.Ioi 0) := by
  let N : ℕ := ⌈(b - a - 1).re⌉₊
  let G : ℕ → ℝ → ℝ := fun k t => (N.choose k : ℝ) *
    (t ^ (a.re + k - 1) * Real.exp (-z.re * t))
  have hG (k : ℕ) : IntegrableOn (G k) (Set.Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := a.re + k - 1) (b := z.re)
      (by have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hz
    simp only [Real.rpow_one] at h
    exact h.const_mul _
  have hsum : IntegrableOn (fun t => ∑ k ∈ Finset.range (N + 1), G k t) (Set.Ioi 0) :=
    integrable_finsetSum _ (fun k _ => hG k)
  have hmajor (t : ℝ) (ht : 0 < t) : (∑ k ∈ Finset.range (N + 1), G k t) =
      Real.exp (-z.re * t) * t ^ (a.re - 1) * (1 + t) ^ N := by
    rw [add_comm (1 : ℝ) t, add_pow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    dsimp [G]
    rw [show a.re + k - 1 = (a.re - 1) + k by ring,
      Real.rpow_add ht, Real.rpow_natCast, one_pow]
    ring
  refine Integrable.mono' hsum (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [hmajor t ht, norm_mul, norm_mul, Complex.norm_exp,
    norm_cpow_eq_rpow_re_of_pos ht,
    show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
    norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t)]
  simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by simpa [N] using Nat.le_ceil (b - a - 1).re)

/-- Tricomi's normalized Laplace integral is continuous in the second parameter.
A fixed integer power dominates every kernel in a neighborhood of that parameter. -/
lemma continuous_confluentU_laplace_integral {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    Continuous (fun b : ℂ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1)) := by
  apply continuous_iff_continuousAt.mpr
  intro b₀
  apply ContinuousAt.const_mul
  obtain ⟨N, hN⟩ : ∃ N : ℕ, b₀.re - a.re ≤ N := exists_nat_ge _
  let F (b : ℂ) (t : ℝ) := exp (-z * t) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  have hmeas (b : ℂ) : AEStronglyMeasurable (F b) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  apply continuousAt_of_dominated (F := F) (bound := fun t => ‖F (a + N + 1) t‖)
    (Eventually.of_forall hmeas) ?_ (confluentU_laplace_integrable (b := a + N + 1) ha hz).norm ?_
  · filter_upwards [Metric.ball_mem_nhds b₀ (by norm_num : (0 : ℝ) < 1)] with b hb
    have hbR : b.re < b₀.re + 1 := by
      rw [Metric.mem_ball, dist_eq_norm] at hb
      have hh := (abs_lt.mp ((abs_re_le_norm (b - b₀)).trans_lt hb)).2
      simp only [sub_re] at hh
      linarith
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    dsimp only [F]
    rw [norm_mul, norm_mul, norm_mul, norm_mul,
      show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t),
      norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < 1 + t)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    simp only [sub_re, add_re, one_re, natCast_re]
    linarith
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hbase : 1 + (t : ℂ) ≠ 0 := by
      have hh : 0 < (1 + (t : ℂ)).re := by simp; linarith
      intro he
      simp [he] at hh
    exact ((continuousAt_id.sub continuousAt_const).sub continuousAt_const).const_cpow
      (Or.inl hbase) |>.const_mul _

/-- Once the Laplace representation is identified off the integer second parameters,
continuity supplies every integer parameter as well. -/
lemma confluentU_laplace_of_eqOn_integerComplement {a b z : ℂ}
    (ha : 0 < a.re) (hz : 0 < z.re)
    (h : ∀ c ∈ integerComplement, confluentU a c z =
      1 / Gamma a * ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (a - 1) *
        (1 + (t : ℂ)) ^ (c - a - 1)) :
    confluentU a b z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hzN : z ≠ 0 := by intro he; simp [he] at hz
  exact eq_of_continuousAt_of_integerComplement
    (continuousAt_confluentU_comp continuousAt_const continuousAt_id hzN)
    ((continuous_confluentU_laplace_integral ha hz).continuousAt) h

/-- Bernoulli's inequality compares rational approximations to the exponential. -/
private lemma rpow_one_add_div_neg_le {u B T : ℝ} (hu : 0 ≤ u) (hB : 0 < B) (hBT : B ≤ T) :
    (1 + u / T) ^ (-T) ≤ (1 + u / B) ^ (-B) := by
  have hT : 0 < T := hB.trans_le hBT
  have hp := one_add_mul_self_le_rpow_one_add (s := u / T)
    (by have hh : 0 ≤ u / T := div_nonneg hu hT.le; linarith)
    ((le_div_iff₀ hB).mpr (by simpa using hBT) : 1 ≤ T / B)
  rw [show 1 + T / B * (u / T) = 1 + u / B by field_simp] at hp
  have hpow := Real.rpow_le_rpow (by positivity) hp hB.le
  rw [← Real.rpow_mul (by positivity), div_mul_cancel₀ _ hB.ne'] at hpow
  rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity)]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr hpow

/-- The rational Euler kernels tend to Tricomi's Laplace kernel on a sufficiently
large positive real ray. The Tau Ceti contributors' second Beta integrability
theorem supplies the fixed majorant. -/
private lemma tendsto_tricomi_rational_integral {a b : ℂ} (ha : 0 < a.re) {x : ℝ}
    (hx : max 0 b.re < x) :
    Tendsto (fun T : ℝ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
        (1 + (t : ℂ)) ^ (b - a - 1)) atTop
      (𝓝 (1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
        exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))) := by
  let B : ℝ := (max 0 b.re + x) / 2
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  have hB : 0 < B := by dsimp [B]; linarith [le_max_left 0 b.re]
  have hBx : B ≤ x := by dsimp [B]; linarith
  have hBb : b.re < B := by dsimp [B]; linarith [le_max_right 0 b.re]
  let F (T t : ℝ) : ℂ := (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  let G (t : ℝ) : ℝ := t ^ (a.re - 1) * (1 + t) ^ (-(a.re + (B - b.re + 1)))
  have hG : IntegrableOn G (Set.Ioi 0) :=
    TauCeti.integrableOn_rpow_mul_one_add_rpow ha (by linarith)
  have hmeas (T : ℝ) : AEStronglyMeasurable (F T) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  have hbound : ∀ᶠ T : ℝ in atTop, ∀ᵐ t ∂volume.restrict (Set.Ioi 0), ‖F T t‖ ≤ G t := by
    filter_upwards [eventually_ge_atTop B] with T hBT
    have hT : 0 < T := hB.trans_le hBT
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    change 0 < t at ht
    have hrat : (1 + x * t / T) ^ (-T) ≤ (1 + t) ^ (-B) := by
      apply (rpow_one_add_div_neg_le (mul_nonneg hx0.le ht.le) hB hBT).trans
      apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by linarith)
      have hxt : t ≤ x * t / B := (le_div_iff₀ hB).mpr (by nlinarith)
      linarith
    dsimp only [F, G]
    rw [norm_mul, norm_mul,
      show 1 + (x : ℂ) * t / T = ((1 + x * t / T : ℝ) : ℂ) by push_cast; rfl,
      show 1 + (t : ℂ) = ((1 + t : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1 + x * t / T),
      norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos (by positivity : 0 < 1 + t)]
    simp only [neg_re, ofReal_re, sub_re, one_re]
    calc
      _ ≤ (1 + t) ^ (-B) * t ^ (a.re - 1) * (1 + t) ^ (b.re - a.re - 1) := by gcongr
      _ = _ := by
        rw [show -(a.re + (B - b.re + 1)) = -B + (b.re - a.re - 1) by ring]
        rw [Real.rpow_add (by positivity)]
        ring
  have hlim : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), Tendsto (fun T => F T t) atTop
      (𝓝 (exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))) := by
    filter_upwards with t
    have hh := (Complex.tendsto_one_add_div_cpow_exp ((x : ℂ) * t)).inv₀ (exp_ne_zero _)
    rw [← Complex.exp_neg] at hh
    simpa only [F, cpow_neg, neg_mul] using (hh.mul_const ((t : ℂ) ^ (a - 1))).mul_const
      ((1 + (t : ℂ)) ^ (b - a - 1))
  exact (tendsto_integral_filter_of_dominated_convergence G
    (Eventually.of_forall hmeas) hbound hG hlim).const_mul _

/-- Cancel only the two regular Gamma factors in the Gauss connection formula. -/
private lemma gauss_connection_cancel (C D A B E H K P Q : ℂ) (hC : C ≠ 0) (hD : D ≠ 0) :
    D / C * (C * A / (D * B) * P + C * E / (H * K) * Q) =
      A / B * P + D / K * (E / H) * Q := by
  rw [mul_add]
  congr 1
  · calc
      _ = (C * C⁻¹) * (D * D⁻¹) * (A / B * P) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [mul_inv_cancel₀ hC, mul_inv_cancel₀ hD]; ring
  · calc
      _ = (C * C⁻¹) * (D / K * (E / H) * Q) := by
        simp only [div_eq_mul_inv, mul_inv_rev]; ring
      _ = _ := by rw [mul_inv_cancel₀ hC]; ring

/-- The normalized Gauss connection formula converges to the defining Tricomi connection. -/
private lemma tendsto_gauss_tricomi_connection {a b : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) {x : ℝ} (hx : 0 < x) :
    Tendsto (fun T : ℝ => Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T)) atTop
      (𝓝 (confluentU a b x)) := by
  have hM := tendsto_ordinaryHypergeometric_add_div_atTop a b 0 (x : ℂ)
  simp only [zero_add] at hM
  have hM₂ := tendsto_ordinaryHypergeometric_add_div_atTop (a - b + 1) (2 - b) (1 - b) (x : ℂ)
  have hQ := AAR.Gamma.Gamma_ratio_power (a := 1 - b) (b := 0)
  simp only [add_zero, sub_zero] at hQ
  simp_rw [show ∀ T : ℝ, (T : ℂ) + (1 - b) = (T : ℂ) + 1 - b from fun T => by ring] at hQ
  have hsum := (hM.const_mul (Gamma (1 - b) / Gamma (a - b + 1))).add
    (((hQ.mul_const ((x : ℂ) ^ (1 - b))).mul hM₂).const_mul (Gamma (b - 1) / Gamma a))
  simp only [one_mul] at hsum
  rw [confluentU_eq_connection a b x hb, confluentUConnection]
  simp only [mul_assoc] at hsum ⊢
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (max x (max 0 b.re) + 1)] with T hT
  have hTx : x < T := by linarith [le_max_left x (max 0 b.re)]
  have hT0 : 0 < T := hx.trans hTx
  have hTb : b.re < T := by
    linarith [le_max_right x (max 0 b.re), le_max_right 0 b.re]
  have hTc : 0 < (T + a + 1 - b : ℂ).re := by simp; linarith
  have hTd : 0 < (T + 1 - b : ℂ).re := by simp; linarith
  have hC := Gamma_ne_zero_of_re_pos hTc
  have hD := Gamma_ne_zero_of_re_pos hTd
  have he : ∀ j : ℤ, (T + a + 1 - b : ℂ) - a - T ≠ j := by
    intro j hj
    apply hb (1 - j)
    push_cast
    linear_combination -hj
  have hxt : 0 < x / T := div_pos hx hT0
  have hxT : x / T < 1 := (div_lt_one hT0).mpr hTx
  have hz : ‖1 - (x : ℂ) / T‖ < 1 := by
    rw [show 1 - (x : ℂ) / T = ((1 - x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  have hw : ‖1 - (1 - (x : ℂ) / T)‖ < 1 := by
    rw [sub_sub_cancel, show (x : ℂ) / T = ((x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg hxt.le]
    exact hxT
  have hc := AAR.Hypergeometric.zero_first_connection_one_of_not_neg_nat
    (a := a) (b := (T : ℂ)) (not_neg_nat_of_re_pos hTc) he hz hw
  simp only [AAR.Hypergeometric.oneFirst, AAR.Hypergeometric.oneSecond, sub_sub_cancel] at hc
  rw [show (T + a + 1 - b : ℂ) - a - T + 1 = 2 - b by ring,
    show a + T - (T + a + 1 - b : ℂ) + 1 = b by ring,
    show (T + a + 1 - b : ℂ) - a - T = 1 - b by ring,
    show (T + a + 1 - b : ℂ) - a = T + 1 - b by ring,
    show (T + a + 1 - b : ℂ) - T = a - b + 1 by ring,
    show a + T - (T + a + 1 - b : ℂ) = b - 1 by ring] at hc
  rw [hc, gauss_connection_cancel _ _ _ _ _ _ _ _ _ hC hD,
    AAR.Hypergeometric.ordinaryHypergeometric_symm (T + 1 - b) (a - b + 1)]
  have hp : ((x : ℂ) / T) ^ (1 - b) = (x : ℂ) ^ (1 - b) / (T : ℂ) ^ (1 - b) := by
    exact div_cpow_ofReal_nonneg hx.le hT0.le _
  rw [hp, show 1 - b + (T : ℂ) = T + 1 - b by ring]
  ring

/-- Euler's half-line representation supplies the same normalized Gauss limit. -/
private lemma gauss_tricomi_rational_integral {a b : ℂ} (ha : 0 < a.re) {x T : ℝ}
    (hx : 0 < x) (hTx : x < T) (hTb : b.re < T) :
    Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) =
        1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
          (1 + (x : ℂ) * t / T) ^ (-(T : ℂ)) * (t : ℂ) ^ (a - 1) *
            (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hT : 0 < T := hx.trans hTx
  have hca : 0 < ((T + a + 1 - b : ℂ) - a).re := by simp; linarith
  have hc : 0 < (T + a + 1 - b : ℂ).re := by simp; linarith
  have hD : Gamma (T + 1 - b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  have hC := Gamma_ne_zero_of_re_pos hc
  have hz : ‖1 - (x : ℂ) / T‖ < 1 := by
    rw [show 1 - (x : ℂ) / T = ((1 - x / T : ℝ) : ℂ) by push_cast; rfl,
      norm_real, Real.norm_of_nonneg (by rw [sub_nonneg, div_le_one hT]; exact hTx.le)]
    linarith [div_pos hx hT]
  have he := AAR.Hypergeometric.integral_Ioi (a := (T : ℂ)) (b := a)
    (c := T + a + 1 - b) ha hca hz
  rw [AAR.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma (not_neg_nat_of_re_pos hc),
    AAR.Hypergeometric.ordinaryHypergeometric_symm (T : ℂ) a,
    show (T + a + 1 - b : ℂ) - a = T + 1 - b by ring,
    show (T : ℂ) - (T + a + 1 - b) = b - a - 1 by ring] at he
  have hn : Gamma (T + 1 - b) / Gamma (T + a + 1 - b) *
      ₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) =
      1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (a - 1) * (t + 1 : ℂ) ^ (b - a - 1) /
          ((t : ℂ) - (1 - (x : ℂ) / T) * t + 1) ^ (T : ℂ) := by
    have hcancel (A D I : ℂ) (hD : D ≠ 0) : D * (1 / (A * D) * I) = 1 / A * I := by
      simp only [div_eq_mul_inv, mul_inv_rev]
      calc
        _ = (D * D⁻¹) * (A⁻¹ * I) := by ring
        _ = _ := by rw [mul_inv_cancel₀ hD]; ring
    calc
      _ = Gamma (T + 1 - b) *
          (₂F₁ a (T : ℂ) (T + a + 1 - b) (1 - (x : ℂ) / T) /
            Gamma (T + a + 1 - b)) := by ring
      _ = _ := by
        rw [he]
        exact hcancel _ _ _ hD
  rw [hn]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t _
  dsimp only
  rw [show (t : ℂ) - (1 - (x : ℂ) / T) * t + 1 = 1 + (x : ℂ) * t / T by ring,
    show (t + 1 : ℂ) = 1 + t by ring, cpow_neg]
  ring

/-- Tricomi's Laplace representation on a nonempty real ray follows by comparing
the Euler and connection limits of the same Gauss function. -/
private lemma confluentU_laplace_of_real_large {a b : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) {x : ℝ} (hx : max 0 b.re < x) :
    confluentU a b x = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  have hx0 : 0 < x := (le_max_left _ _).trans_lt hx
  apply tendsto_nhds_unique (tendsto_gauss_tricomi_connection ha hb hx0)
  apply (tendsto_tricomi_rational_integral ha hx).congr'
  filter_upwards [eventually_gt_atTop (max x b.re)] with T hT
  exact (gauss_tricomi_rational_integral ha hx0
    ((le_max_left _ _).trans_lt hT) ((le_max_right _ _).trans_lt hT)).symm

/-- Holomorphic dependence of Tricomi's normalized Laplace integral on the argument. -/
lemma differentiableOn_confluentU_laplace_integral {a b : ℂ} (ha : 0 < a.re) :
    DifferentiableOn ℂ (fun z : ℂ => 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1))
      {z : ℂ | 0 < z.re} := by
  intro z₀ hz₀
  change 0 < z₀.re at hz₀
  let δ : ℝ := z₀.re / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hre (z : ℂ) (hz : z ∈ Metric.ball z₀ δ) : δ < z.re := by
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have hh := (abs_lt.mp ((abs_re_le_norm (z - z₀)).trans_lt hz)).1
    simp only [sub_re] at hh
    dsimp [δ] at *
    linarith
  let F (z : ℂ) (t : ℝ) := exp (-z * t) * (t : ℂ) ^ (a - 1) *
    (1 + (t : ℂ)) ^ (b - a - 1)
  let G (t : ℝ) := ‖exp (-(δ : ℂ) * t) * (t : ℂ) ^ a *
    (1 + (t : ℂ)) ^ (b - a - 1)‖
  have hG : IntegrableOn G (Set.Ioi 0) := by
    change Integrable G (volume.restrict (Set.Ioi 0))
    have h := (confluentU_laplace_integrable (a := a + 1) (b := b + 1) (z := (δ : ℂ))
      (by simp; linarith) (by simpa using hδ)).norm
    simpa only [G, add_sub_cancel_right, show (b + 1) - (a + 1) - 1 = b - a - 1 by ring] using h
  have hmeas (z : ℂ) : AEStronglyMeasurable (F z) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (F := F) (F' := fun z t => -(t : ℂ) * F z t)
    (bound := G) (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas)
    (confluentU_laplace_integrable ha hz₀)
    (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)) ?_ hG ?_
  · exact (hd.2.const_mul (1 / Gamma a)).differentiableAt.differentiableWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht z hz
    change 0 < t at ht
    have he : Real.exp (-z.re * t) ≤ Real.exp (-δ * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [hre z hz]
    have hp : t ^ (a.re - 1) * t = t ^ a.re := by
      have hh := Real.rpow_add_one ht.ne' (a.re - 1)
      simpa only [sub_add_cancel] using hh.symm
    dsimp only [F, G]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg ht.le]
    simp only [norm_mul, Complex.norm_exp, neg_re, mul_re, ofReal_re, ofReal_im,
      mul_zero, sub_zero, norm_cpow_eq_rpow_re_of_pos ht, sub_re, one_re]
    calc
      _ = Real.exp (-z.re * t) * (t ^ (a.re - 1) * t) *
          ‖(1 + (t : ℂ)) ^ (b - a - 1)‖ := by ring
      _ = Real.exp (-z.re * t) * t ^ a.re * ‖(1 + (t : ℂ)) ^ (b - a - 1)‖ := by rw [hp]
      _ ≤ _ := by gcongr
  · filter_upwards with t z _
    have hh := (((hasDerivAt_id z).neg.mul_const (t : ℂ)).cexp.mul_const
      ((t : ℂ) ^ (a - 1))).mul_const ((1 + (t : ℂ)) ^ (b - a - 1))
    simp only [Pi.neg_apply, id_eq] at hh
    convert hh using 1
    dsimp only [F]
    ring

/-- The real-ray identity extends holomorphically to the full right half-plane. -/
private lemma confluentU_laplace_of_not_int {a b z : ℂ} (ha : 0 < a.re)
    (hb : ∀ j : ℤ, b ≠ j) (hz : 0 < z.re) :
    confluentU a b z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  let V : Set ℂ := {z | 0 < z.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  let J (z : ℂ) := 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
    exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1)
  have hU : AnalyticOnNhd ℂ (confluentU a b) V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    exact (differentiableAt_confluentU a b (Or.inl hw)).differentiableWithinAt
  have hJ : AnalyticOnNhd ℂ J V := (differentiableOn_confluentU_laplace_integral ha).analyticOnNhd hVo
  let x₀ : ℝ := max 0 b.re + 1
  have hx₀ : max 0 b.re < x₀ := by dsimp [x₀]; linarith
  have hx₀0 : 0 < x₀ := (le_max_left _ _).trans_lt hx₀
  have hfreq : ∃ᶠ w in 𝓝[≠] (x₀ : ℂ), confluentU a b w = J w := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] x₀) (𝓝[≠] (x₀ : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact (continuous_ofReal.tendsto x₀).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds hx₀)] with r hr
    exact confluentU_laplace_of_real_large ha hb hr
  exact hU.eqOn_of_preconnected_of_frequently_eq hJ (convex_halfSpace_re_gt 0).isPreconnected
    (by change 0 < (x₀ : ℂ).re; simpa using hx₀0) hfreq hz

@[dlmf 13.4.E4]
theorem confluentU_laplace {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    confluentU a b z =
      1 / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  exact confluentU_laplace_of_eqOn_integerComplement ha hz
    (fun c hc => confluentU_laplace_of_not_int ha (forall_of_mem_integerComplement hc) hz)

/-- The nonnegative integer shifted family specializes the full Tricomi representation. -/
lemma confluentU_laplace_shift_nat {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) (N : ℕ) :
    confluentU a (a + N + 1) z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ ((a + N + 1) - a - 1) :=
  confluentU_laplace ha hz

/-- The unit parameter shift specializes the full Tricomi representation. -/
lemma confluentU_laplace_shift_one {a z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    confluentU a (a + 1) z = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ ((a + 1) - a - 1) :=
  confluentU_laplace ha hz

@[dlmf 13.4.E5]
theorem confluentU_stieltjes {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    confluentU a b z =
      z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
        ∫ t : ℝ in Set.Ioi 0,
          confluentU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
            ((t : ℂ) + z) := by
  sorry

@[dlmf 13.4.E6]
theorem confluentU_stieltjes_regularized {a b z : ℂ} (n : ℕ) (hz : z ∈ slitPlane)
    (hn0 : -b.re < n) (hn1 : (n : ℝ) < 1 + (a - b).re) :
    confluentU a b z =
      (-1 : ℂ) ^ n * z ^ (1 - b - n) / Gamma (1 + a - b) *
        ∫ t : ℝ in Set.Ioi 0,
          regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
            ((t : ℂ) + z) := by
  sorry

/-- A Bessel-K integral for Tricomi U, away from `z = 0` where the totalized values of both
sides differ. -/
@[dlmf 13.4.E7]
theorem confluentU_integral_besselK {a b z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    confluentU a b z =
      2 * z ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
            besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.4.E8]
theorem confluentU_gauss {a b c z : ℂ} (ha : 0 < c.re) (hz : 0 < z.re) :
    confluentU a b z =
      z ^ (c - a) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.gaussHGCut a (a - b + 1) c (-(t : ℂ)) := by
  sorry

open Set MeasureTheory AAR.Gamma in
/-- The Cahen–Mellin integral in Barnes's orientation: `e^{-v} = 1/(2π) ∫ Γ(-(σ+iy)) v^{σ+iy} dy`
for `σ < 0 < v`. -/
lemma exp_neg_eq_integral_barnes {σ : ℝ} (hσ : σ < 0) {v : ℝ} (hv : 0 < v) :
    exp (-(v : ℂ)) =
      1 / (2 * π) * ∫ y : ℝ, Gamma (-((σ : ℂ) + I * y)) * (v : ℂ) ^ ((σ : ℂ) + I * y) := by
  have h := exp_neg_eq_integral (σ := -σ) (by linarith) hv
  rw [ofReal_exp, ofReal_neg] at h
  rw [h, ← integral_neg_eq_self]
  congr 2; funext y
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring, neg_neg]

open Set MeasureTheory AAR.Gamma in
lemma integrable_Gamma_neg_vertical {σ : ℝ} (hσ : σ < 0) :
    Integrable (fun y : ℝ => Gamma (-((σ : ℂ) + I * y))) := by
  refine (integrable_Gamma_vertical (σ := -σ) (by linarith)).comp_neg.congr
    (Eventually.of_forall fun y => ?_)
  simp only [Function.comp_apply]
  rw [show (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) = -((σ : ℂ) + I * y) by push_cast; ring]

open Set MeasureTheory AAR.Gamma in
/-- Barnes's integral for `𝐌` (DLMF 13.4.16) when `re (b - a) > 0`, from Kummer's integral. -/
lemma regularized_barnes_integral_of_re_sub_pos {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hσ : σ < 0) (hba : 0 < (b - a).re) :
    regularizedHGFun {a} {b} (-(x : ℂ)) =
      1 / (2 * π * Gamma a) * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
  have ha0 : 0 < a.re := by linarith
  have hb0 : 0 < b.re := by simp only [sub_re] at hba; linarith
  set Ψ : ℝ → ℂ := fun y => Gamma (-((σ : ℂ) + I * y)) with hΨ
  have hΨi : Integrable Ψ := integrable_Gamma_neg_vertical hσ
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.mpr fun y =>
    (continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  set H : ℝ → ℝ → ℂ := fun t y => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
    (Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) * (t : ℂ) ^ ((σ : ℂ) + I * y)) with hH
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0
  have hGba : Gamma (b - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hba
  have hpt : ∀ t ∈ Ioo (0 : ℝ) 1,
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) =
        1 / (2 * π) * ∫ y : ℝ, H t y := by
    intro t ht
    have hxt : 0 < x * t := mul_pos hx ht.1
    have hCM := exp_neg_eq_integral_barnes hσ hxt
    have hH' : ∫ y : ℝ, H t y = (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) *
        ∫ y : ℝ, Ψ y * ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext y
      rw [hH, ofReal_mul, mul_cpow_ofReal_nonneg hx.le ht.1.le]; ring
    rw [hH', show -(x : ℂ) * t = -((x * t : ℝ) : ℂ) by push_cast; ring, hCM]
    ring
  set μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1) with hμ
  have hμprod :
      μ.prod volume = (volume.prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (a + σ - 1) * (1 - (t : ℂ)) ^ (b - a - 1)‖) μ := by
    have h := betaIntegral_convergent (u := a + σ) (v := b - a) (by simp; linarith) hba
    have h' := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp h
    exact (h'.mono_set Ioo_subset_Ioc_self).norm
  have hg : Integrable (fun y : ℝ => ‖Ψ y‖ * x ^ σ) := hΨi.norm.mul_const _
  have hcont : ContinuousOn (Function.uncurry H) (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    rintro ⟨t, y⟩ ⟨ht, -⟩
    have ht0 : (0 : ℝ) < t := ht.1
    have ht1 : t < 1 := ht.2
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hH, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    · refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
      rw [mem_slitPlane_iff]; left; simp; linarith
    · exact (hΨc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr ht0)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    refine (hf.mul_prod hg).mono' ?_ ?_
    · rw [hμprod]
      exact hcont.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
    · rw [hμprod]
      refine (ae_restrict_iff' (measurableSet_Ioo.prod MeasurableSet.univ)).mpr
        (Eventually.of_forall ?_)
      rintro ⟨t, y⟩ ⟨ht, -⟩
      have ht0 : (0 : ℝ) < t := ht.1
      simp only [hH, Function.uncurry_def, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos hx, norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
        sub_zero, mul_zero, add_zero]
      rw [show a.re + σ - 1 = (a.re - 1) + σ by ring, Real.rpow_add ht0]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  have hinner : ∀ y : ℝ, ∫ t, H t y ∂μ = Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (a + σ + I * y) * Gamma (b - a) / Gamma (b + σ + I * y)) := by
    intro y
    have has : 0 < (a + σ + I * y).re := by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith
    have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral has hba
    rw [show a + σ + I * y + (b - a) = b + σ + I * y by ring] at hB
    have hGbs : Gamma (b + σ + I * y) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero,
        add_zero]; linarith [sub_re b a])
    have hbeta : betaIntegral (a + σ + I * y) (b - a) =
        ∫ t, (t : ℂ) ^ (a + σ + I * y - 1) * (1 - (t : ℂ)) ^ (b - a - 1) ∂μ := by
      rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
    calc ∫ t, H t y ∂μ = Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
          ∫ t, (t : ℂ) ^ (a + σ + I * y - 1) * (1 - (t : ℂ)) ^ (b - a - 1) ∂μ := by
          rw [← MeasureTheory.integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
          have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
          have hsplit : (t : ℂ) ^ (a + σ + I * y - 1) =
              (t : ℂ) ^ (a - 1) * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
            rw [← cpow_add _ _ ht0]; ring_nf
          simp only [hH]
          rw [hsplit]
          ring
      _ = _ := by
          rw [← hbeta]
          congr 1
          rw [eq_div_iff hGbs, hB]; ring
  rw [regularized_euler_integral ha0 hba, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo hpt,
    MeasureTheory.integral_const_mul]
  change 1 / (Gamma a * Gamma (b - a)) * (1 / (2 * π) * ∫ t, ∫ y, H t y ∂volume ∂μ) = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Ψ y * (x : ℂ) ^ ((σ : ℂ) + I * y) *
      (Gamma (a + σ + I * y) * Gamma (b - a) / Gamma (b + σ + I * y)) =
      Gamma (b - a) * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; rw [hΨ]; ring
  rw [hlast]
  generalize (∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
    Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y)) = J
  field_simp

/-- Vertical Mellin–Barnes line; the factor `i` from `dt` is included. -/
@[dlmf 13.4.E16]
theorem regularized_barnes_integral {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hσ : σ < 0) :
    regularizedHGFun {a} {b} (-(x : ℂ)) =
      1 / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
          Gamma (b + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I := by
  set A : ℝ → ℂ := fun y => Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) *
    (x : ℂ) ^ ((σ : ℂ) + I * y) with hA
  have hAc : Continuous A := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (AAR.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (AAR.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
  obtain ⟨Ca, Ka, hCa⟩ := AAR.Gamma.exists_norm_Gamma_shift_le (x := a.re + σ) ha a.im
  obtain ⟨Cs, Ks, hCs⟩ := AAR.Gamma.exists_norm_Gamma_shift_le (x := -σ) (by linarith) 0
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (by simpa using hCs 0)
  have hAb : ∀ y : ℝ, ‖A y‖ ≤ Ca * Cs * x ^ σ * (1 + |y|) ^ (Ka + Ks) *
      Real.exp (-(π * |y|)) := by
    intro y
    have e1 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have e3 : -((σ : ℂ) + I * y) = ((-σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
      push_cast; ring
    have h1 := hCa y; rw [← e1] at h1
    have h3 := hCs (-y); rw [← e3, abs_neg] at h3
    have h4 : ‖(x : ℂ) ^ ((σ : ℂ) + I * y)‖ = x ^ σ := by
      rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
    simp only [hA, norm_mul]
    rw [h4]
    have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) = Real.exp (-(π * |y|)) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖Gamma (a + σ + I * y)‖ * ‖Gamma (-((σ : ℂ) + I * y))‖ * x ^ σ
        ≤ (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y|) / 2)) *
            (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y|) / 2)) * x ^ σ := by gcongr
      _ = _ := by rw [pow_add, ← hE]; ring
  have hR := AAR.Gamma.differentiable_integral_mul_inv_Gamma hAc hAb σ
  have hrw : ∀ b : ℂ, ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
      Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) =
      ∫ y : ℝ, A y * (Gamma (b + σ + I * y))⁻¹ := fun b => by
    congr 1; funext y; simp only [hA]; ring
  have key := AAR.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn
    (analyticOnNhd_regularizedConfluent_b a (-(x : ℂ)))
    (g := fun b => 1 / (2 * π * Gamma a) * ∫ y : ℝ, A y * (Gamma (b + σ + I * y))⁻¹)
    (fun b _ => (hR.const_mul _).analyticAt b)
    (U := {b : ℂ | 0 < (b - a).re})
    (isOpen_lt continuous_const (continuous_re.comp (continuous_id.sub continuous_const)))
    ⟨a + 1, by simp⟩
    (fun b hb => by
      simp only
      rw [regularized_barnes_integral_of_re_sub_pos hx ha hσ hb, hrw])
  have hb := congrFun key b
  rw [hb, ← hrw]
  have hrw2 : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
      Gamma (b + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I =
      I * ∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
        Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y) := by
    rw [← MeasureTheory.integral_const_mul]; congr 1; funext y; ring
  rw [hrw2]
  generalize (∫ y : ℝ, Gamma (a + σ + I * y) * Gamma (-((σ : ℂ) + I * y)) /
    Gamma (b + σ + I * y) * (x : ℂ) ^ ((σ : ℂ) + I * y)) = J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp

open Set MeasureTheory in
/-- Barnes's integral for `₁F₁`, AAR Theorem 4.2.1, along the upward vertical
line `s = σ + it`, with `-Re a < σ < 0`. -/
theorem confluentM_eq_barnes_integral {a c z : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hσ : σ < 0) (hc : ∀ k : ℕ, c ≠ -k)
    (hz : z ≠ 0) (harg : |(-z).arg| < π / 2) :
    confluentM a c z =
      Gamma c / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (-(σ + I * t)) * Gamma (a + σ + I * t) /
          Gamma (c + σ + I * t) * (-z) ^ (σ + I * t) * I := by
  set B : ℝ → ℂ := fun t => Gamma (-((σ : ℂ) + I * t)) * Gamma (a + σ + I * t) /
    Gamma (c + σ + I * t) with hBdef
  have ha : 0 < a.re + σ := by linarith
  have hBc : Continuous B := by
    refine continuous_iff_continuousAt.mpr fun y => ?_
    refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) ?_
    · exact (AAR.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (AAR.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
    · exact (AAR.Gamma.differentiable_inv_Gamma.continuous.comp (by fun_prop)).continuousAt
  -- the decay of `B`
  obtain ⟨Cs, Ks, hCs⟩ := AAR.Gamma.exists_norm_Gamma_shift_le (x := -σ) (by linarith) 0
  obtain ⟨Ca, Ka, hCa⟩ := AAR.Gamma.exists_norm_Gamma_shift_le (x := a.re + σ) ha a.im
  obtain ⟨Cc, Kc, hCc⟩ := AAR.Gamma.exists_norm_inv_Gamma_shift_le (c.re + σ) c.im
  have hCs0 : 0 ≤ Cs := (norm_nonneg _).trans (by simpa using hCs 0)
  have hCa0 : 0 ≤ Ca := (norm_nonneg _).trans (by simpa using hCa 0)
  have hBb : ∀ y : ℝ, ‖B y‖ ≤ Cs * Ca * Cc * (1 + |y|) ^ (Ks + Ka + Kc) *
      Real.exp (-(π * |y|) / 2) := by
    intro y
    have e1 : -((σ : ℂ) + I * y) = ((-σ : ℝ) : ℂ) + I * (((0 : ℝ) : ℂ) + ((-y : ℝ) : ℂ)) := by
      push_cast; ring
    have e2 : a + σ + I * y = ((a.re + σ : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have e3 : c + σ + I * y = ((c.re + σ : ℝ) : ℂ) + I * ((c.im : ℂ) + (y : ℂ)) := by
      apply Complex.ext <;> simp
    have h1 := hCs (-y); rw [← e1, abs_neg] at h1
    have h2 := hCa y; rw [← e2] at h2
    have h3 := hCc y; rw [← e3] at h3
    simp only [hBdef]
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    have hE : Real.exp (-(π * |y|) / 2) * Real.exp (-(π * |y|) / 2) * Real.exp (π * |y| / 2) =
        Real.exp (-(π * |y|) / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    calc ‖Gamma (-((σ : ℂ) + I * y))‖ * ‖Gamma (a + σ + I * y)‖ * ‖(Gamma (c + σ + I * y))⁻¹‖
        ≤ (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y|) / 2)) *
            (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y|) / 2)) *
            (Cc * (1 + |y|) ^ Kc * Real.exp (π * |y| / 2)) := by gcongr
      _ = _ := by
          rw [pow_add, pow_add]
          generalize Real.exp (-(π * |y|) / 2) = E at hE ⊢
          generalize Real.exp (π * |y| / 2) = F at hE ⊢
          linear_combination (Cs * Ca * Cc * (1 + |y|) ^ Ks * (1 + |y|) ^ Ka * (1 + |y|) ^ Kc) * hE
  have hG := AAR.Gamma.differentiableOn_integral_mul_cpow hBc hBb σ
  -- both sides are analytic on the left half-plane
  set Ω : Set ℂ := {z : ℂ | z.re < 0} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt continuous_re continuous_const
  have hzΩ : z ∈ Ω := by
    have := abs_arg_lt_pi_div_two_iff.mp harg
    rcases this with h | h
    · simpa [hΩ] using h
    · exact absurd (neg_eq_zero.mp h) hz
  set g : ℂ → ℂ := fun z => Gamma c / (2 * π * I * Gamma a) *
    (I * ∫ t : ℝ, B t * (-z) ^ ((σ : ℂ) + I * t)) with hg
  have hgd : DifferentiableOn ℂ g Ω := by
    refine (DifferentiableOn.const_mul (DifferentiableOn.const_mul ?_ _) _)
    exact hG.comp (differentiableOn_neg _) (fun w hw => by simpa [hΩ] using hw)
  have hga : AnalyticOnNhd ℂ g Ω := hgd.analyticOnNhd hΩo
  have hfa : AnalyticOnNhd ℂ (confluentM a c) Ω := fun w _ => analyticOnNhd_confluentM hc w trivial
  -- agreement on the negative axis
  have hagree : ∀ x : ℝ, 0 < x → confluentM a c (-(x : ℂ)) = g (-(x : ℂ)) := by
    intro x hx
    rw [confluentM_eq_mul_regularizedHGFun hc, regularized_barnes_integral hx ha hσ]
    simp only [hg, neg_neg]
    have hrw : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
        Gamma (c + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I =
        I * ∫ t : ℝ, B t * (x : ℂ) ^ ((σ : ℂ) + I * t) := by
      rw [← MeasureTheory.integral_const_mul]; congr 1; funext t; simp only [hBdef]; ring
    rw [hrw]
    have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hI : (I : ℂ) ≠ 0 := I_ne_zero
    field_simp
  have hfreq : ∃ᶠ w in 𝓝[≠] (-1 : ℂ), confluentM a c w = g w := by
    have ht : Tendsto (fun x : ℝ => -(x : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (-1 : ℂ)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have h1 := (continuous_ofReal.tendsto (1 : ℝ)).neg
        rw [ofReal_one] at h1
        exact h1.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with x hx
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
        intro h; apply hx; have := congrArg re h; simpa using this
    refine ht.frequently ?_
    have hpos : ∀ᶠ x in 𝓝[≠] (1 : ℝ), 0 < x :=
      (eventually_gt_nhds one_pos).filter_mono nhdsWithin_le_nhds
    exact (hpos.mono fun x hx => hagree x hx).frequently
  have hΩc : IsPreconnected Ω := (convex_halfSpace_re_lt (r := 0)).isPreconnected
  have heq := hfa.eqOn_of_preconnected_of_frequently_eq hga hΩc (by simp [hΩ]) hfreq hzΩ
  rw [heq]
  simp only [hg]
  congr 1
  rw [← MeasureTheory.integral_const_mul]; congr 1; funext t; simp only [hBdef]; push_cast; ring

open Set MeasureTheory in
@[dlmf 13.4.E17]
theorem confluentU_barnes {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hab : 0 < (1 + a - b).re + σ) (hσ : σ < 0) :
    confluentU a b x =
      (x : ℂ) ^ (-a) / (2 * π * I) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
          Gamma (-(σ + I * t)) / (Gamma a * Gamma (1 + a - b)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  have ha0 : 0 < a.re := by linarith
  have hA0 : 0 < (1 + a - b).re := by linarith
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hGa : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha0
  have hGA : Gamma (1 + a - b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hA0
  set Φ : ℝ → ℂ := fun y => Gamma (-((σ : ℂ) + I * y)) * Gamma (1 + a - b + σ + I * y) with hΦ
  have hΦi : Integrable Φ := AAR.Hypergeometric.integrable_Gamma_neg_mul_Gamma hσ hab
  have hΦc : Continuous Φ := AAR.Hypergeometric.continuous_Gamma_neg_mul_Gamma hσ hab
  set H : ℝ → ℝ → ℂ := fun t y => exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) *
    (Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y)) with hH
  -- the Laplace integral, with the Mellin–Barnes integral inserted
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) =
        (Gamma (1 + a - b))⁻¹ * (1 / (2 * π)) * ∫ y : ℝ, H t y := by
    intro t ht
    have hMB := AAR.Hypergeometric.Gamma_mul_one_add_cpow_neg_barnes (a := 1 + a - b) hσ hab ht
    have hpow : (1 + (t : ℂ)) ^ (b - a - 1) = (Gamma (1 + a - b))⁻¹ *
        (1 / (2 * π) * ∫ y : ℝ, Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y)) := by
      rw [← hMB, show b - a - 1 = -(1 + a - b) by ring]; push_cast; field_simp
    have hHt : ∫ y : ℝ, H t y = exp (-(x : ℂ) * t) * (t : ℂ) ^ (a - 1) *
        ∫ y : ℝ, Φ y * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← MeasureTheory.integral_const_mul]
    rw [hpow, hHt]; ring
  -- integrability on the product
  set μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ)) with hμ
  have hμprod : μ.prod volume = (volume.prod volume).restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rw [hμ, ← Measure.prod_restrict, Measure.restrict_univ]
  have hf : Integrable (fun t : ℝ => ‖(t : ℂ) ^ (a + σ - 1) * exp (-((x : ℂ) * t))‖) μ := by
    have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := a + σ) (z := x) (by simp; linarith)
      (by simpa using hx)
    have hi : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a + σ - 1) * exp (-((x : ℂ) * t))) (Ioi 0) := by
      by_contra hni
      rw [integral_undef hni] at h
      exact (mul_ne_zero (Complex.Gamma_ne_zero_of_re_pos (by simp; linarith))
        (by rw [cpow_def_of_ne_zero hx0]; exact exp_ne_zero _)) h.symm
    exact hi.norm
  have hg : Integrable (fun y : ℝ => ‖Φ y‖) := hΦi.norm
  have hcont : ContinuousOn (Function.uncurry H) (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
    rintro ⟨t, y⟩ ⟨ht, -⟩
    have ht0 : (0 : ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    simp only [hH, Function.uncurry_def]
    refine ContinuousAt.mul (ContinuousAt.mul (by fun_prop) ?_) (ContinuousAt.mul ?_ ?_)
    · exact ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    · exact (hΦc.comp continuous_snd).continuousAt
    · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr ht0)
  have hHi : Integrable (Function.uncurry H) (μ.prod volume) := by
    refine (hf.mul_prod hg).mono' ?_ ?_
    · rw [hμprod]
      exact hcont.aestronglyMeasurable (measurableSet_Ioi.prod MeasurableSet.univ)
    · rw [hμprod]
      refine (ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)).mpr
        (Eventually.of_forall ?_)
      rintro ⟨t, y⟩ ⟨ht, -⟩
      have ht0 : (0 : ℝ) < t := ht
      simp only [hH, Function.uncurry_def, norm_mul]
      rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0,
        norm_cpow_eq_rpow_re_of_pos ht0]
      simp only [sub_re, add_re, ofReal_re, one_re, mul_re, I_re, I_im, ofReal_im, zero_mul,
        sub_zero, mul_zero, add_zero, neg_mul]
      rw [show a.re + σ - 1 = (a.re - 1) + σ by ring, Real.rpow_add ht0]
      apply le_of_eq; ring
  have hswap := integral_integral_swap hHi
  -- the inner Gamma integrals
  have hinner : ∀ y : ℝ, ∫ t, H t y ∂μ = Φ y * (Gamma (a + σ + I * y) *
      (x : ℂ) ^ (-(a + σ + I * y))) := by
    intro y
    have h := integral_cpow_mul_cexp_neg_mul_Ioi (s := a + σ + I * y) (z := x)
      (by simp; linarith) (by simpa using hx)
    rw [← h, ← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hsplit : (t : ℂ) ^ (a + σ + I * y - 1) =
        (t : ℂ) ^ (a - 1) * (t : ℂ) ^ ((σ : ℂ) + I * y) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    simp only [hH]
    rw [hsplit, show -((x : ℂ) * t) = -(x : ℂ) * t by ring]
    ring
  -- assemble
  rw [confluentU_laplace ha0 (by simpa using hx), setIntegral_congr_fun measurableSet_Ioi hpt,
    MeasureTheory.integral_const_mul]
  change 1 / Gamma a * ((Gamma (1 + a - b))⁻¹ * (1 / (2 * π)) *
    ∫ t, ∫ y, H t y ∂volume ∂μ) = _
  rw [hswap, integral_congr_ae (ae_of_all _ hinner)]
  have hlast : ∫ y : ℝ, Φ y * (Gamma (a + σ + I * y) * (x : ℂ) ^ (-(a + σ + I * y))) =
      (x : ℂ) ^ (-a) * ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
        Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y
    rw [hΦ, show -(a + σ + I * y) = -a + -(σ + I * y) by ring, cpow_add _ _ hx0]
    ring
  have hlast' : ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
      Gamma (-(σ + I * t)) / (Gamma a * Gamma (1 + a - b)) * (x : ℂ) ^ (-(σ + I * t)) * I =
      I / (Gamma a * Gamma (1 + a - b)) * ∫ t : ℝ, Gamma (a + σ + I * t) *
        Gamma (1 + a - b + σ + I * t) * Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t)) := by
    rw [← MeasureTheory.integral_const_mul]
    congr 1; funext y; ring
  rw [hlast, hlast']
  generalize (∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
    Gamma (-(σ + I * t)) * (x : ℂ) ^ (-(σ + I * t))) = J
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

@[dlmf 13.4.E18]
theorem confluentU_barnes_exp {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hb : 0 < (b - 1).re + σ) (hσ : 0 < σ) :
    confluentU a b x =
      (x : ℂ) ^ (1 - b) * exp x / (2 * π * I) *
        ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

@[dlmf 13.16.E1]
theorem whittakerM_euler {κ μ z : ℂ}
    (hμ : 0 < μ.re + 1 / 2 - |κ.re|) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 + μ + κ)) *
        ∫ t : ℝ in (-1 : ℝ)..1,
          exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) *
            (1 - (t : ℂ)) ^ (μ - 1 / 2 + κ) := by
  let a := 1 / 2 + μ - κ
  let d := 1 / 2 + μ + κ
  have ha : 0 < a.re := by
    dsimp [a]
    norm_num
    linarith [le_abs_self κ.re]
  have hd : 0 < d.re := by
    dsimp [d]
    norm_num
    linarith [neg_abs_le κ.re]
  have hba : 1 + 2 * μ - a = d := by dsimp [a, d]; ring
  let F : ℝ → ℂ := fun t => exp (z * t) * (t : ℂ) ^ (a - 1) *
    (1 - (t : ℂ)) ^ (d - 1)
  have hsub : (∫ t : ℝ in (0 : ℝ)..1, F t) = (1 / 2 : ℂ) *
      ∫ t : ℝ in (-1 : ℝ)..1, F ((1 / 2 : ℝ) * t + 1 / 2) := by
    have he := intervalIntegral.integral_comp_mul_add (f := F) (a := (-1 : ℝ))
      (b := 1) (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2 : ℝ)
    norm_num only [smul_eq_mul] at he
    rw [he]
    simp [Complex.real_smul]
  have hi : exp (-z / 2) * (∫ t : ℝ in (0 : ℝ)..1, F t) =
      (2 : ℂ) ^ (-(2 * μ)) * ∫ t : ℝ in (-1 : ℝ)..1,
        exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) *
          (1 - (t : ℂ)) ^ (μ - 1 / 2 + κ) := by
    rw [hsub, ← mul_assoc, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only [F]
    have hp : 0 ≤ 1 + t := by linarith [ht.1]
    have hm : 0 ≤ 1 - t := by linarith [ht.2]
    have he : exp (-z / 2) * exp (z * ((1 / 2 : ℝ) * t + 1 / 2)) = exp (z * t / 2) := by
      rw [← exp_add]
      congr 1
      push_cast
      ring
    have htcast : (((1 / 2 : ℝ) * t + 1 / 2 : ℝ) : ℂ) = (1 + (t : ℂ)) / 2 := by
      push_cast; ring
    have htcast' : 1 - (((1 / 2 : ℝ) * t + 1 / 2 : ℝ) : ℂ) = (1 - (t : ℂ)) / 2 := by
      rw [htcast]; ring
    have hp' : ((1 + (t : ℂ)) / 2) ^ (a - 1) =
        (1 + (t : ℂ)) ^ (a - 1) / (2 : ℂ) ^ (a - 1) := by
      convert div_cpow_ofReal_nonneg (a := 1 + t) (b := 2) hp (by norm_num) (a - 1) using 1 <;> push_cast <;> rfl
    have hm' : ((1 - (t : ℂ)) / 2) ^ (d - 1) =
        (1 - (t : ℂ)) ^ (d - 1) / (2 : ℂ) ^ (d - 1) := by
      convert div_cpow_ofReal_nonneg (a := 1 - t) (b := 2) hm (by norm_num) (d - 1) using 1 <;> push_cast <;> rfl
    rw [htcast', htcast, hp', hm']
    have htwo : (1 / 2 : ℂ) / ((2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (d - 1)) =
        (2 : ℂ) ^ (-(2 * μ)) := by
      rw [← cpow_add _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      have hab : (a - 1) + (d - 1) = 2 * μ - 1 := by dsimp [a, d]; ring
      rw [hab, one_div, ← cpow_neg_one, ← cpow_sub _ _ (by norm_num : (2 : ℂ) ≠ 0)]
      congr 1
      ring
    have ha' : a - 1 = μ - 1 / 2 - κ := by dsimp [a]; ring
    have hd' : d - 1 = μ - 1 / 2 + κ := by dsimp [d]; ring
    calc
      _ = (exp (-z / 2) * exp (z * ((1 + (t : ℂ)) / 2))) *
          ((1 / 2 : ℂ) / ((2 : ℂ) ^ (a - 1) * (2 : ℂ) ^ (d - 1))) *
          (1 + (t : ℂ)) ^ (a - 1) * (1 - (t : ℂ)) ^ (d - 1) := by ring
      _ = _ := by
        rw [← htcast]
        push_cast
        norm_num only [ofReal_div, ofReal_one, ofReal_ofNat] at he
        rw [he, htwo, ha', hd']
        ring
  have hb : 0 < (1 + 2 * μ).re := by
    have hab : a + d = 1 + 2 * μ := by dsimp [a, d]; ring
    rw [← hab, add_re]
    exact add_pos ha hd
  rw [whittakerM, show μ - κ + 1 / 2 = a by dsimp [a]; ring,
    confluentM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hb),
    regularized_euler_integral ha (by rw [hba]; exact hd), hba]
  change exp (-z / 2) * z ^ (μ + 1 / 2) *
    (Gamma (1 + 2 * μ) * (1 / (Gamma a * Gamma d) * ∫ t : ℝ in (0 : ℝ)..1, F t)) = _
  calc
    _ = Gamma (1 + 2 * μ) * z ^ (μ + 1 / 2) / (Gamma a * Gamma d) *
        (exp (-z / 2) * ∫ t : ℝ in (0 : ℝ)..1, F t) := by ring
    _ = _ := by rw [hi]; dsimp [a, d]; ring

@[dlmf 13.16.E2]
theorem whittakerM_parameter_integral {κ μ lam z : ℂ}
    (hμ : lam.re < μ.re + 1 / 2) (hlam : 0 < lam.re) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ lam / (Gamma (1 + 2 * μ - 2 * lam) * Gamma (2 * lam)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) *
            (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1) := by
  let a := μ - κ + 1 / 2
  let b := 1 + 2 * μ
  let c := 1 + 2 * μ - 2 * lam
  let r := μ - lam + 1 / 2
  have hc : 0 < c.re := by dsimp [c]; simp only [mul_re]; norm_num; linarith
  have hb : 0 < b.re := by dsimp [b]; simp only [mul_re]; norm_num; linarith
  have hbc : b - c = 2 * lam := by dsimp [b, c]; ring
  have hl : 0 < (2 * lam).re := by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hlam
  have hM := regularized_parameter_integral (a := a) (b := b) (c := c) (z := z) hc
    (by rw [hbc]; exact hl)
  rw [hbc] at hM
  have hi : (∫ t : ℝ in (0 : ℝ)..1,
      whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) *
        (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1)) =
      (exp (-z / 2) * z ^ r * Gamma c) *
        ∫ t : ℝ in (0 : ℝ)..1, regularizedHGFun {a} {c} (z * t) *
          (t : ℂ) ^ (c - 1) * (1 - (t : ℂ)) ^ (2 * lam - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
    intro t ht
    dsimp only
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    have hp : (z * t) ^ r = z ^ r * (t : ℂ) ^ r := by
      rw [cpow_def_of_ne_zero (mul_ne_zero (slitPlane_ne_zero hz) ht0),
        log_mul_ofReal t ht.1 z (slitPlane_ne_zero hz), add_mul, exp_add,
        cpow_def_of_ne_zero (slitPlane_ne_zero hz), cpow_def_of_ne_zero ht0,
        ofReal_log ht.1.le]
      ring
    rw [whittakerM, show μ - lam - (κ - lam) + 1 / 2 = a by dsimp [a]; ring,
      show 1 + 2 * (μ - lam) = c by dsimp [c]; ring,
      confluentM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hc)]
    change exp (-(z * t) / 2) * (z * t) ^ r *
        (Gamma c * regularizedHGFun {a} {c} (z * t)) * exp (z * (t - 1) / 2) *
        (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1) = _
    rw [hp]
    have he : exp (-(z * t) / 2) * exp (z * (t - 1) / 2) = exp (-z / 2) := by
      rw [← exp_add]; congr 1; ring
    have hpow : (t : ℂ) ^ r * (t : ℂ) ^ (μ - lam - 1 / 2) = (t : ℂ) ^ (c - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      dsimp [r, c]
      ring
    calc
      _ = (exp (-(z * t) / 2) * exp (z * (t - 1) / 2)) * z ^ r * Gamma c *
          regularizedHGFun {a} {c} (z * t) *
          ((t : ℂ) ^ r * (t : ℂ) ^ (μ - lam - 1 / 2)) *
          (1 - (t : ℂ)) ^ (2 * lam - 1) := by ring
      _ = _ := by rw [he, hpow]; ring
  rw [hi, whittakerM, confluentM_eq_mul_regularizedHGFun (not_neg_nat_of_re_pos hb)]
  change exp (-z / 2) * z ^ (μ + 1 / 2) * (Gamma b * regularizedHGFun {a} {b} z) = _
  rw [hM]
  have hp : z ^ lam * z ^ r = z ^ (μ + 1 / 2) := by
    rw [← cpow_add _ _ (slitPlane_ne_zero hz)]
    congr 1
    dsimp [r]
    ring
  dsimp only [b, c] at *
  have hp' : z ^ lam * z ^ r = z ^ ((2 * μ + 1) / 2) := by
    rw [hp]
    congr 1
    ring
  field_simp [Gamma_ne_zero_of_re_pos hc, Gamma_ne_zero_of_re_pos hl]
  linear_combination -Gamma (1 + 2 * μ) *
    (∫ t : ℝ in (0 : ℝ)..1, regularizedHGFun {a} {1 + 2 * μ - 2 * lam} (z * t) *
      (t : ℂ) ^ (1 + 2 * μ - 2 * lam - 1) * (1 - (t : ℂ)) ^ (2 * lam - 1)) * hp'

@[dlmf 13.16.E3]
theorem whittakerM_integral_besselJ {κ μ z : ℂ} (hκ : 0 < (κ + μ).re + 1 / 2)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (z / 2) / Gamma (1 / 2 + μ + κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (κ - 1 / 2) *
            besselJ (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E4]
theorem whittakerM_integral_besselI {κ μ z : ℂ} (hκ : (κ - μ).re - 1 / 2 < 0)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (-z / 2) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselI (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E5]
theorem whittakerW_laplace {κ μ z : ℂ} (hμ : κ.re < μ.re + 1 / 2)
    (hz : 0 < z.re) :
    whittakerW κ μ z =
      z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 1,
          exp (-z * t / 2) * ((t : ℂ) - 1) ^ (μ - 1 / 2 - κ) *
            ((t : ℂ) + 1) ^ (μ - 1 / 2 + κ) := by
  let p : ℂ := μ - 1 / 2 - κ
  let q : ℂ := μ - 1 / 2 + κ
  let F (t : ℝ) := exp (-z * t / 2) * ((t : ℂ) - 1) ^ p * ((t : ℂ) + 1) ^ q
  have ha : 0 < (1 / 2 + μ - κ).re := by simp; linarith
  have hderiv (u : ℝ) (_hu : u ∈ Set.Ioi (0 : ℝ)) :
      HasDerivWithinAt (fun u : ℝ => 1 + 2 * u) 2 (Set.Ioi 0) u := by
    convert ((hasDerivAt_id u).const_mul 2).const_add 1 |>.hasDerivWithinAt using 1
    · rfl
    · ring
  have hinj : Set.InjOn (fun u : ℝ => 1 + 2 * u) (Set.Ioi 0) := by
    intro u _ v _ h
    linarith
  have himage : (fun u : ℝ => 1 + 2 * u) '' Set.Ioi 0 = Set.Ioi 1 := by
    ext t
    constructor
    · rintro ⟨u, hu, rfl⟩
      change 0 < u at hu
      change 1 < 1 + 2 * u
      linarith
    · intro ht
      change 1 < t at ht
      exact ⟨(t - 1) / 2, by change 0 < (t - 1) / 2; linarith, by ring⟩
  have hs := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj F
  rw [himage] at hs
  have hpoint (u : ℝ) (hu : 0 < u) : |(2 : ℝ)| • F (1 + 2 * u) =
      ((2 : ℂ) ^ (2 * μ) * exp (-z / 2)) *
        (exp (-z * u) * (u : ℂ) ^ p * (1 + (u : ℂ)) ^ q) := by
    have hpow : (2 : ℂ) ^ p * (2 : ℂ) ^ q * 2 = (2 : ℂ) ^ (2 * μ) := by
      calc
        _ = (2 : ℂ) ^ (p + q + 1) := by
          rw [cpow_add (p + q) 1 (by norm_num : (2 : ℂ) ≠ 0), cpow_one,
            cpow_add p q (by norm_num : (2 : ℂ) ≠ 0)]
        _ = _ := by congr 1; dsimp [p, q]; ring
    dsimp only [F]
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 2), Complex.real_smul]
    push_cast
    rw [show -z * (1 + 2 * (u : ℂ)) / 2 = -z / 2 + -z * u by ring,
      show (1 + 2 * (u : ℂ)) - 1 = 2 * u by ring,
      show (1 + 2 * (u : ℂ)) + 1 = 2 * (1 + u) by ring,
      Complex.exp_add,
      mul_cpow_of_re_pos (u := 2) (v := (u : ℂ)) (by norm_num) (by simpa using hu) p,
      mul_cpow_of_re_pos (u := 2) (v := 1 + (u : ℂ)) (by norm_num) (by simp; linarith) q]
    linear_combination (exp (-z / 2) * exp (-z * u) * (u : ℂ) ^ p *
      (1 + (u : ℂ)) ^ q) * hpow
  have hI : (∫ t : ℝ in Set.Ioi 1, F t) = ((2 : ℂ) ^ (2 * μ) * exp (-z / 2)) *
      ∫ u : ℝ in Set.Ioi 0, exp (-z * u) * (u : ℂ) ^ p * (1 + (u : ℂ)) ^ q := by
    rw [hs, ← MeasureTheory.integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Ioi (fun u hu => hpoint u hu)
  have h2 : (2 : ℂ) ^ (2 * μ) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl (by norm_num))
  rw [whittakerW, confluentU_laplace ha hz,
    show (1 / 2 + μ - κ) - 1 = p by dsimp [p]; ring,
    show (1 + 2 * μ) - (1 / 2 + μ - κ) - 1 = q by dsimp [q]; ring,
    show (1 / 2 : ℂ) + μ = μ + 1 / 2 by ring]
  change exp (-z / 2) * z ^ (μ + 1 / 2) * (1 / Gamma (μ + 1 / 2 - κ) * _) =
    z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (μ + 1 / 2 - κ) *
      ∫ t : ℝ in Set.Ioi 1, F t
  rw [hI, cpow_neg]
  have hcancel (A B D E I : ℂ) (hD : D ≠ 0) :
      E * B * (1 / A * I) = B * D⁻¹ / A * ((D * E) * I) := by
    simp only [div_eq_mul_inv, one_mul]
    linear_combination -(E * B * A⁻¹ * I) * (inv_mul_cancel₀ hD)
  exact hcancel _ _ _ _ _ h2

@[dlmf 13.16.E6]
theorem whittakerW_stieltjes {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : (2 * μ.re) < (1 / 2 + μ - κ).re) (hκ0 : 0 < (1 / 2 + μ - κ).re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + 1) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) /
            ((t : ℂ) + z) := by
  sorry

/-- A Bessel-K integral for Whittaker W. Both parameter bounds are necessary for the
ordinary integral: at `κ = 0`, `μ = 1/2` the omitted second bound would give a zero
Gamma prefactor although `W` is nonzero. The totalized values also differ at `z = 0`. -/
@[dlmf 13.16.E8]
theorem whittakerW_integral_besselK {κ μ z : ℂ} (hκ : 0 < (μ - κ).re + 1 / 2)
    (hκ' : 0 < (-μ - κ).re + 1 / 2)
    (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    whittakerW κ μ z =
      2 * z ^ (1 / 2 : ℂ) * exp (-z / 2) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselK (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E9]
theorem whittakerW_gauss {κ μ c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + c) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.gaussHGCut (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ)) := by
  sorry

@[dlmf 13.16.E11]
theorem whittakerW_barnes {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ)
    (hκ : κ.re + σ < 0) :
    whittakerW κ μ x =
      exp (-(x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
          Gamma (-κ - (σ + I * t)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hU := confluentU_barnes (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (σ := σ + κ.re) hx
    (by simp only [sub_re, add_re] at hμ ⊢; linarith)
    (by simp only [sub_re, add_re, mul_re] at hμ' ⊢; norm_num at hμ' ⊢; linarith)
    (by linarith)
  set F : ℝ → ℂ := fun t => Gamma (1 / 2 + μ - κ + ((σ + κ.re : ℝ) : ℂ) + I * t) *
    Gamma (1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + ((σ + κ.re : ℝ) : ℂ) + I * t) *
    Gamma (-(((σ + κ.re : ℝ) : ℂ) + I * t)) /
    (Gamma (1 / 2 + μ - κ) * Gamma (1 + (1 / 2 + μ - κ) - (1 + 2 * μ))) *
    (x : ℂ) ^ (-(((σ + κ.re : ℝ) : ℂ) + I * t)) * I with hF
  have htr := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) F κ.im
  rw [← htr] at hU
  have hpt : ∀ t : ℝ, F (t + κ.im) = (x : ℂ) ^ (-κ) *
      (Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
        Gamma (-κ - (σ + I * t)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        (x : ℂ) ^ (-(σ + I * t)) * I) := by
    intro t
    have e : ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) = σ + I * t + κ := by
      apply Complex.ext <;> simp
    simp only [hF]
    rw [show 1 / 2 + μ - κ + ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) =
        1 / 2 + μ - κ + (((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ)) by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + ((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ) =
        1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + (((σ + κ.re : ℝ) : ℂ) + I * ((t + κ.im : ℝ) : ℂ)) by
        ring, e,
      show 1 / 2 + μ - κ + (σ + I * t + κ) = 1 / 2 + μ + σ + I * t by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) + (σ + I * t + κ) = 1 / 2 - μ + σ + I * t by ring,
      show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
      show -((σ : ℂ) + I * t + κ) = -κ - (σ + I * t) by ring,
      show -κ - ((σ : ℂ) + I * t) = -κ + -(σ + I * t) by ring, cpow_add _ _ hx0]
    rw [show -κ + -((σ : ℂ) + I * t) = -κ - (σ + I * t) by ring]
    ring
  simp only [hpt] at hU
  rw [MeasureTheory.integral_const_mul] at hU
  rw [whittakerW, hU]
  have hxx : (x : ℂ) ^ (1 / 2 + μ) * (x : ℂ) ^ (-(1 / 2 + μ - κ)) * (x : ℂ) ^ (-κ) = 1 := by
    rw [← cpow_add _ _ hx0, ← cpow_add _ _ hx0]; ring_nf; exact cpow_zero _
  generalize (∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
    Gamma (-κ - (σ + I * t)) / (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
    (x : ℂ) ^ (-(σ + I * t)) * I) = J
  linear_combination (exp (-(x : ℂ) / 2) / (2 * π * I) * J) * hxx

@[dlmf 13.16.E12]
theorem whittakerW_barnes_exp {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ) (hσ : 0 < σ) :
    whittakerW κ μ x =
      exp ((x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
          Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

end AAR.Confluent
