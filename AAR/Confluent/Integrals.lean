/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import AAR.Confluent.Recurrence
public import AAR.Confluent.Growth
public import AAR.Confluent.TricomiLaplace
public import AAR.Confluent.Continuation
public import AAR.Bessel.Basic
public import AAR.Bessel.Modified
public import AAR.Hypergeometric.EulerIntegral
public import AAR.Hypergeometric.Boundary
public import AAR.Hypergeometric.ArgumentContinuation
public import AAR.Hypergeometric.IntegralRepresentations
public import AAR.Gamma.IntegralRepresentations
public import AAR.Gamma.BetaFunction
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrals (DLMF §§13.10, 13.23)

Gauss functions in the transforms use cut-plane continuation. The former series-only
statements were false when their transformed argument left the unit disk.

The general regularized Kummer Laplace transform is proved by termwise integration
when `‖k‖ < Re z` and then by holomorphic continuation throughout the full
convergence half-plane, retaining all denominator parameters, including Gamma poles.
The self-transform specializes it using the binomial identity.
Mathlib's summable-integral-norm theorem justifies the exchange, using a regularized
Gauss series to sum the absolute Gamma moments. The Whittaker M closed transform
then follows with an explicit principal-logarithm calculation in the right half-plane.
Tricomi's Mellin transform follows from its Laplace representation and Mathlib's
Fubini theorem. Absolute convergence of the double kernel reduces to the Tau Ceti
contributors' second Beta integrability theorem; the local proved Gamma and Beta
integral formulas evaluate the exchanged integrals.

The boundary Mellin transform uses a summable Gamma-moment majorant from the
proved Gamma-ratio asymptotics. Regularized Gauss summation, including singular
denominator parameters, evaluates the resulting series; the regularized Whittaker
M transform follows by combining positive-real powers and exponential factors.

Indefinite integrals are stated as derivative identities. Laplace, Mellin, and
Bessel transforms use real half-lines. Hankel-loop formulas 13.10.8–13.10.9 and
13.23.6–13.23.7, and the inversion pair 13.23.13–13.23.14, are deferred.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries
open scoped Real Topology ENNReal
open AAR.Hypergeometric
open AAR.Bessel

noncomputable section

namespace AAR.Confluent

@[dlmf 13.10.E1]
theorem deriv_regularizedHGFun_shift {a b z : ℂ} (ha : a ≠ 1) :
    deriv (regularizedHGFun {a - 1} {b - 1}) z = (a - 1) * regularizedHGFun {a} {b} z := by
  have hr : (regularizedHGFunSeries {a - 1} {b - 1}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a - 1} {b - 1})
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a - 1} {b - 1}).sum
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a - 1} {b - 1}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht : HasFPowerSeriesOnBall (regularizedHGFun {a} {b})
      (regularizedHGFunSeries {a} {b}) 0 ⊤ := by
    have hr' : (regularizedHGFunSeries {a} {b}).radius = ⊤ :=
      radius_regularizedHGFunSeries_eq_top (by simp)
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {b}).sum
      (regularizedHGFunSeries {a} {b}) 0 ⊤
    simpa only [hr'] using (regularizedHGFunSeries {a} {b}).hasFPowerSeriesOnBall
      (by rw [hr']; simp)
  have hcoeff (n : ℕ) :
      (n + 1 : ℂ) * regularizedHGFunCoeff {a - 1} {b - 1} (n + 1) =
        (a - 1) * regularizedHGFunCoeff {a} {b} n := by
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, poch_succ_left]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [show (b - 1) + (n + 1) = b + n by ring,
      show a - 1 + 1 = a by ring]
    field [hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  have hd := hs.deriv_ofScalars.hasSum_mul_pow (z := z) (by simp)
  have he := (ht.hasSum_mul_pow (z := z) (by simp)).mul_left (a - 1)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd he
  exact hd.unique he

/-- Derivative of Tricomi U with shifted parameters. `U` is not complex-differentiable on the cut,
so `z` is restricted to the slit plane. -/
@[dlmf 13.10.E2]
theorem deriv_kummerU_shift {a b z : ℂ} (ha : a ≠ 1) (hz : z ∈ slitPlane) :
    deriv (kummerU (a - 1) (b - 1)) z = -(a - 1) * kummerU a b z := by
  rw [deriv_kummerU (a - 1) (b - 1) hz, sub_add_cancel, sub_add_cancel]

/-- General Kummer Laplace transform in the region of absolute termwise integration. -/
lemma laplace_regularizedHGFun_of_norm_lt {a b c k z : ℂ}
    (hb : 0 < b.re) (hzpos : 0 < z.re) (hk : ‖k‖ < z.re) :
    (∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)) =
      Gamma b * z ^ (-b) * AAR.Hypergeometric.regularizedGaussHG a b c (k / z) := by
  let e : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n * k ^ n
  let F : ℕ → ℝ → ℂ := fun n t => e n * ((t : ℂ) ^ (b + n - 1) * exp (-(z * t)))
  let r : ℝ := z.re⁻¹
  have hz0 : z ≠ 0 := by intro h; simp [h] at hzpos
  have hrpos : 0 < r := inv_pos.mpr hzpos
  have hrlt : r * ‖k‖ < 1 := by
    dsimp [r]
    rw [inv_mul_eq_div]
    exact (div_lt_one hzpos).mpr hk
  have hbn (n : ℕ) : 0 < (b + n).re := by simp; positivity
  have hnorm (n : ℕ) (t : ℝ) (ht : 0 < t) :
      ‖F n t‖ = ‖e n‖ * (t ^ (b.re + n - 1) * Real.exp (-(z.re * t))) := by
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := b.re + n - 1) (b := z.re) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
          one_pos hzpos
    simp only [Real.rpow_one] at hreal
    apply Integrable.mono' (hreal.const_mul ‖e n‖)
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm n t ht]
    simp only [one_mul, neg_mul, le_refl]
  have hInorm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      ‖e n‖ * (r ^ (b.re + n) * Real.Gamma (b.re + n)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm n t ht), integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (by positivity) hzpos]
    simp only [r, one_div]
  have hGnorm (n : ℕ) : Real.Gamma (b.re + n) =
      ‖poch (b.re : ℂ) n‖ * Real.Gamma b.re := by
    have hp : ∀ k : ℕ, (b.re : ℂ) ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simpa using hb)
    have hG := (div_eq_iff (Gamma_ne_zero hp)).mp
      (Gamma_add_nat_div_Gamma_eq (n := n) (b.re : ℂ) hp)
    have h := congrArg norm hG
    rw [norm_mul, show (b.re : ℂ) + n = ((b.re + n : ℝ) : ℂ) by push_cast; rfl,
      Gamma_ofReal, Gamma_ofReal, norm_real, norm_real,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity)).le,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos hb).le] at h
    exact h
  have hsum : Summable (fun n => ∫ t : ℝ in Set.Ioi 0, ‖F n t‖) := by
    have h := AAR.Hypergeometric.summable_norm_regularizedGaussHGFun_term
      a (b.re : ℂ) c (z := ((r * ‖k‖ : ℝ) : ℂ))
        (by simpa only [norm_real, Real.norm_of_nonneg (mul_nonneg hrpos.le (norm_nonneg k))] using
            hrlt)
    apply (h.mul_left (r ^ b.re * Real.Gamma b.re)).congr
    intro n
    rw [hInorm, hGnorm, Real.rpow_add hrpos, Real.rpow_natCast]
    simp only [e, regularizedHGFunCoeff_singleton, norm_mul, norm_div, norm_pow, norm_inv,
      norm_real, norm_norm,
      ofReal_mul, mul_pow, Real.norm_of_nonneg hrpos.le]
    ring
  have hI (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, F n t) =
      (Gamma b * z ^ (-b)) * ((ascPochhammer ℂ n).eval a *
        (ascPochhammer ℂ n).eval b * (k / z) ^ n / n.factorial * (Gamma (c + n))⁻¹) := by
    rw [integral_const_mul, AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hbn n) hzpos]
    have hp := not_neg_nat_of_re_pos hb
    have hGb := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) b hp)
    rw [hGb, show -(b + (n : ℂ)) = -b + -(n : ℂ) by ring, cpow_add _ _ hz0]
    simp only [cpow_neg, cpow_natCast, e, regularizedHGFunCoeff_singleton, div_pow]
    simp only [poch]
    ring
  have ht (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t) := by
    rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [F, e]
    rw [show b + n - 1 = (b - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast, mul_pow]
    ring
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have harg : ‖k / z‖ < 1 := by
    rw [norm_div]
    exact (div_lt_one (norm_pos_iff.mpr hz0)).mpr (hk.trans_le (re_le_norm z))
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∑' n, F n t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht' => (ht t ht').symm)
    _ = ∑' n, ∫ t : ℝ in Set.Ioi 0, F n t := hs.tsum_eq.symm
    _ = _ := by
      simp_rw [hI]
      rw [tsum_mul_left, AAR.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun a b c harg,
        AAR.Hypergeometric.regularizedGaussHGFun_eq_tsum]

/-- The transformed argument stays on the Gauss cut plane throughout the Laplace half-plane. -/
lemma kummerLaplace_argument_mem_cutPlane {k z : ℂ}
    (hz : k.re < z.re) (hz0 : 0 < z.re) :
    k / z ∈ AAR.Hypergeometric.cutPlane := by
  have hzN : z ≠ 0 := by intro h; simp [h] at hz0
  change 1 - k / z ∈ slitPlane
  apply mem_slitPlane_iff.mpr
  by_cases hi : (1 - k / z).im = 0
  · left
    by_contra hn
    have he : k = (1 - (1 - k / z)) * z := by field_simp; ring
    have hr := congrArg Complex.re he
    simp only [mul_re, sub_re, one_re, sub_im, one_im, hi, sub_self, zero_mul, sub_zero] at hr
    have hq : (1 - k / z).re ≤ 0 := le_of_not_gt hn
    simp only [sub_re, one_re] at hq
    nlinarith
  · exact Or.inr hi

/-- The regularized Kummer Laplace transform in its full convergence half-plane. -/
@[dlmf 13.10.E3]
theorem laplace_regularizedHGFun {a b c k z : ℂ}
    (hb : 0 < b.re) (hz : z.re > k.re) (hz0 : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t) =
      Gamma b * z ^ (-b) * AAR.Hypergeometric.regularizedGaussHG a b c (k / z) := by
  let V : Set ℂ := {w | max 0 k.re < w.re}
  have hVo : IsOpen V := isOpen_lt continuous_const continuous_re
  let L (w : ℂ) := ∫ t : ℝ in Set.Ioi 0,
    exp (-w * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t)
  let R (w : ℂ) := Gamma b * w ^ (-b) * AAR.Hypergeometric.regularizedGaussHG a b c (k / w)
  have hL : AnalyticOnNhd ℂ L V :=
    (differentiableOn_laplace_regularizedHGFun a b c k hb).analyticOnNhd hVo
  have hR : AnalyticOnNhd ℂ R V := by
    apply DifferentiableOn.analyticOnNhd _ hVo
    intro w hw
    have hw0 : 0 < w.re := (le_max_left 0 k.re).trans_lt hw
    have hwk : k.re < w.re := (le_max_right 0 k.re).trans_lt hw
    have hwN : w ≠ 0 := by intro h; simp [h] at hw0
    have hpow := differentiableAt_id.cpow (differentiableAt_const (-b)) (Or.inl hw0)
    have hG := (AAR.Hypergeometric.differentiableAt_regularizedGaussHG a b c
      (kummerLaplace_argument_mem_cutPlane hwk hw0)).comp w
      ((differentiableAt_const k).div differentiableAt_id hwN)
    exact ((hpow.const_mul (Gamma b)).mul hG).differentiableWithinAt
  let w₀ : ℂ := (‖k‖ + 1 : ℝ)
  have hw₀ : w₀ ∈ V := by
    dsimp [w₀, V]
    rw [max_lt_iff]
    constructor
    · positivity
    · linarith [re_le_norm k]
  have heq : L =ᶠ[𝓝 w₀] R := by
    have hnh : {w : ℂ | ‖k‖ < w.re} ∈ 𝓝 w₀ :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by dsimp [w₀]; simp)
    filter_upwards [hnh] with w hw
    exact laplace_regularizedHGFun_of_norm_lt hb ((norm_nonneg k).trans_lt hw) hw
  exact hL.eqOn_of_preconnected_of_eventuallyEq hR
    (convex_halfSpace_re_gt (max 0 k.re)).isPreconnected hw₀ heq (max_lt hz0 hz)

@[dlmf 13.10.E4]
theorem laplace_regularizedHGFun_self {a b z : ℂ} (hb : 0 < b.re) (hz : 1 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t =
      z ^ (-b) * (1 - z⁻¹) ^ (-a) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz; linarith
  have harg : ‖z⁻¹‖ < 1 := by
    rw [norm_inv, inv_lt_one₀ (norm_pos_iff.mpr hz0)]
    exact hz.trans_le (re_le_norm z)
  have hc := not_neg_nat_of_re_pos hb
  have h := laplace_regularizedHGFun_of_norm_lt (a := a) (b := b) (c := b) (k := 1)
    hb (by linarith) (by simpa using hz)
  simp only [one_mul, one_div] at h
  rw [h, AAR.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun a b b harg,
    AAR.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hc,
    ordinaryHypergeometric_eq_one_sub_neg_cpow
      (fun k hk => hc k (by linear_combination hk)) harg]
  field [Gamma_ne_zero hc]

/-- Absolute Gamma moments of the regularized Kummer coefficients at the boundary.
The proved Gamma-ratio estimate retains the exact convergence inequality. -/
lemma summable_kummer_gamma_moments (a c : ℂ) {b : ℝ} (hb : 0 < b)
    (h : b < (c - a).re) :
    Summable (fun n : ℕ => ‖regularizedHGFunCoeff {a} {c} n‖ * Real.Gamma (b + n)) := by
  by_cases ha : ∀ k : ℕ, a ≠ -k
  · have hs := (AAR.Hypergeometric.CarlsonAux.summable_norm_Gamma_ratio a b c 1
      (by simp only [sub_re, add_re, ofReal_re, one_re] at h ⊢; linarith)).mul_left ‖Gamma a‖⁻¹
    refine hs.congr fun n => ?_
    have hg := (div_eq_iff (Gamma_ne_zero ha)).mp (Gamma_add_nat_div_Gamma_eq (n := n) a ha)
    rw [show (n : ℂ) + a = a + n by ring, hg,
      show (n : ℂ) + (b : ℂ) = ((b + n : ℝ) : ℂ) by push_cast; ring,
      Gamma_ofReal, Gamma_nat_eq_factorial, regularizedHGFunCoeff_singleton]
    simp only [norm_mul, norm_inv, Complex.norm_natCast, norm_real, norm_div,
      Real.norm_of_nonneg (Real.Gamma_pos_of_pos (by positivity : 0 < b + n)).le]
    rw [show (n : ℂ) + c = c + n by ring]
    field_simp [norm_ne_zero_iff.mpr (Gamma_ne_zero ha)]
  · push_neg at ha
    obtain ⟨m, rfl⟩ := ha
    apply (summable_nat_add_iff (m + 1)).mp
    have he : (fun n : ℕ => ‖regularizedHGFunCoeff {-(m : ℂ)} {c} (n + (m + 1))‖ *
        Real.Gamma (b + (n + (m + 1) : ℕ))) = fun _ : ℕ => 0 := by
      funext n
      simp [regularizedHGFunCoeff_singleton, poch_neg_nat_eq_zero (show m < n + (m + 1) by omega)]
    rw [he]
    exact summable_zero

@[dlmf 13.10.E5]
theorem mellin_regularizedHGFun_exp {a b c : ℂ}
    (hb : 0 < b.re) (h : b.re < (c - a).re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t =
      Gamma b * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  let e : ℕ → ℂ := fun n => regularizedHGFunCoeff {a} {c} n
  let F : ℕ → ℝ → ℂ := fun n t => e n * ((t : ℂ) ^ (b + n - 1) * exp (-(t : ℂ)))
  have hbn (n : ℕ) : 0 < (b + n).re := by simp; positivity
  have hnorm (n : ℕ) (t : ℝ) (ht : 0 < t) :
      ‖F n t‖ = ‖e n‖ * (t ^ (b.re + n - 1) * Real.exp (-t)) := by
    simp only [F, norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
    simp
  have hFi (n : ℕ) : IntegrableOn (F n) (Set.Ioi 0) := by
    have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
      (s := b.re + n - 1) (b := 1) (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)
        one_pos one_pos
    simp only [Real.rpow_one] at hreal
    apply Integrable.mono' (hreal.const_mul ‖e n‖)
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop))
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hnorm n t ht]
    simp only [one_mul, neg_mul, le_refl]
  have hInorm (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, ‖F n t‖) =
      ‖e n‖ * Real.Gamma (b.re + n) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm n t ht), integral_const_mul]
    have hi := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := b.re + n) (r := 1) (by positivity) one_pos
    simpa using congrArg (fun u : ℝ => ‖e n‖ * u) hi
  have hsum : Summable (fun n => ∫ t : ℝ in Set.Ioi 0, ‖F n t‖) := by
    simp_rw [hInorm]
    exact summable_kummer_gamma_moments a c hb h
  have hI (n : ℕ) : (∫ t : ℝ in Set.Ioi 0, F n t) =
      Gamma b * (poch a n * poch b n / (n.factorial * Gamma (c + n))) := by
    rw [integral_const_mul]
    have hi := AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hbn n) (z := 1) (by simp)
    simp only [one_mul, one_cpow, mul_one] at hi
    rw [hi]
    have hg := (div_eq_iff (Gamma_ne_zero (not_neg_nat_of_re_pos hb))).mp
      (Gamma_add_nat_div_Gamma_eq (n := n) b (not_neg_nat_of_re_pos hb))
    rw [hg]
    dsimp only [e]
    rw [regularizedHGFunCoeff_singleton]
    ring
  have ht (t : ℝ) (ht : 0 < t) : (∑' n, F n t) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t := by
    rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp [F, e]
    rw [show b + n - 1 = (b - 1) + n by ring,
      cpow_add _ _ (ofReal_ne_zero.mpr ht.ne'), cpow_natCast]
    ring
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∑' n, F n t :=
      setIntegral_congr_fun measurableSet_Ioi (fun t ht' => (ht t ht').symm)
    _ = ∑' n, ∫ t : ℝ in Set.Ioi 0, F n t := hs.tsum_eq.symm
    _ = _ := by
      simp_rw [hI]
      rw [tsum_mul_left, (AAR.Hypergeometric.hasSum_regularizedGauss_one (by simp at h ⊢; linarith)).tsum_eq]
      ring

/-- A Gaussian-weighted Laplace transform of `𝐌`; it converges for `0 < Re z`. -/
@[dlmf 13.10.E6]
theorem gauss_regularizedHGFun {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4) := by
  sorry

/-- The Laplace transform of Tricomi U; it converges for `0 < Re z`. -/
@[dlmf 13.10.E7]
theorem laplace_kummerU {a b c z : ℂ}
    (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * kummerU a c t =
      Gamma b * Gamma (b - c + 1) * z ^ (-b) *
        AAR.Hypergeometric.regularizedGaussHG a b (a + b - c + 1) (1 - z⁻¹) := by
  have hm := (laplace_kummerU_gauss (a := a) hb hbc hz).2
  change (∫ t : ℝ in Set.Ioi 0, tricomiLaplaceKernel a b c z t) = _
  rw [hm]
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  have hw : 1 - z ∈ AAR.Hypergeometric.cutPlane := by
    change 1 - (1 - z) ∈ slitPlane
    rw [sub_sub_cancel]; exact Or.inl hz
  have hp := AAR.Hypergeometric.regularizedGaussHG_pfaff b (b - c + 1) (a + b - c + 1) hw
  have hs := AAR.Hypergeometric.regularizedGaussHG_symm b a (a + b - c + 1)
    (AAR.Hypergeometric.div_sub_one_mem_cutPlane hw)
  rw [show (1 - z) / (1 - z - 1) = 1 - z⁻¹ by field_simp [hz0]; ring] at hp hs
  rw [sub_sub_cancel, show (a + b - c + 1) - (b - c + 1) = a by ring] at hp
  rw [hp, hs]
  ring

@[dlmf 13.10.E10]
theorem mellin_regularizedHGFun {a b lam : ℂ} (hlam : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * regularizedHGFun {a} {b} (-t) =
      Gamma lam * Gamma (a - lam) / (Gamma a * Gamma (b - lam)) := by
  -- Kummer's transformation reduces this to `mellin_regularizedHGFun_exp` at `(b-a, lam, b)`.
  have h := mellin_regularizedHGFun_exp (a := b - a) (b := lam) (c := b) hlam
    (by simpa using ha)
  rw [show b - (b - a) - lam = a - lam by ring, show b - (b - a) = a by ring] at h
  rw [← h]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [regularizedConfluent_kummer_transform a b (-(t : ℂ)), neg_neg]
  ring

/-- Absolute convergence of the double kernel used in Tricomi's Mellin transform.
The Tau Ceti contributors' second Beta integrability theorem controls the outer integral. -/
private lemma integrable_mellin_kummerU_kernel {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    Integrable (fun p : ℝ × ℝ =>
      (p.1 : ℂ) ^ (lam - 1) * exp (-(p.2 : ℂ) * p.1) *
        (p.2 : ℂ) ^ (a - 1) * (1 + (p.2 : ℂ)) ^ (b - a - 1))
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) := by
  let F (t u : ℝ) : ℂ := (t : ℂ) ^ (lam - 1) * exp (-(u : ℂ) * t) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)
  let C (u : ℝ) : ℝ := u ^ (a.re - 1) * (1 + u) ^ (b.re - a.re - 1)
  have hnorm (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
      ‖F t u‖ = C u * (t ^ (lam.re - 1) * Real.exp (-(u * t))) := by
    dsimp only [F, C]
    rw [norm_mul, norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hu,
      show 1 + (u : ℂ) = ((1 + u : ℝ) : ℂ) by push_cast; rfl,
      norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.norm_exp]
    simp only [sub_re, one_re, neg_re, mul_re, ofReal_re, ofReal_im]
    ring
  have hbase (u : ℝ) (hu : 0 < u) :
      IntegrableOn (fun t : ℝ => t ^ (lam.re - 1) * Real.exp (-(u * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := lam.re - 1) (b := u)
        (by linarith) one_pos hu
  have hnormIntegral (u : ℝ) (hu : 0 < u) :
      (∫ t : ℝ in Set.Ioi 0, ‖F t u‖) = Real.Gamma lam.re *
        (u ^ (a.re - lam.re - 1) * (1 + u) ^ (b.re - a.re - 1)) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hnorm t u ht hu),
      integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hlam1 hu,
      one_div, Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
    dsimp [C]
    rw [show a.re - lam.re - 1 = (a.re - 1) + -lam.re by ring, Real.rpow_add hu]
    ring
  have hmeas : AEStronglyMeasurable (Function.uncurry F)
      ((volume.restrict (Set.Ioi 0)).prod (volume.restrict (Set.Ioi 0))) :=
    Measurable.aestronglyMeasurable (by dsimp [F, Function.uncurry]; fun_prop)
  apply (integrable_prod_iff' hmeas).mpr
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    refine Integrable.mono' ((hbase u hu).const_mul (C u))
      (Measurable.aestronglyMeasurable (by dsimp [F]; fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hnorm t u ht hu).le
  · have hbeta := TauCeti.integrableOn_rpow_mul_one_add_rpow
      (a := a.re - lam.re) (b := lam.re - b.re + 1) (by linarith)
      (by simp only [sub_re, one_re] at hlam0; linarith)
    have he : -(a.re - lam.re + (lam.re - b.re + 1)) = b.re - a.re - 1 := by ring
    simp only [he] at hbeta
    refine (hbeta.const_mul (Real.Gamma lam.re)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (hnormIntegral u hu).symm

/-- Tricomi's Mellin transform is absolutely integrable throughout its stated strip. -/
lemma mellin_kummerU_integrable {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (lam - 1) * kummerU a b t) (Set.Ioi 0) := by
  have ha0 : 0 < a.re := hlam1.trans ha
  have h := (integrable_mellin_kummerU_kernel hlam0 hlam1 ha).integral_prod_left
  refine (h.const_mul (1 / Gamma a)).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [kummerU_laplace ha0 (by simpa using ht)]
  simp_rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  rw [show -(u : ℂ) * t = -(t : ℂ) * u by ring]
  ring

@[dlmf 13.10.E11]
theorem mellin_kummerU {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * kummerU a b t =
      Gamma lam * Gamma (a - lam) * Gamma (lam - b + 1) / (Gamma a * Gamma (a - b + 1)) := by
  have ha0 : 0 < a.re := hlam1.trans ha
  let F (t u : ℝ) : ℂ := (t : ℂ) ^ (lam - 1) * exp (-(u : ℂ) * t) *
    (u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)
  have hswap := integral_integral_swap (f := F) (integrable_mellin_kummerU_kernel hlam0 hlam1 ha)
  have hinner (u : ℝ) (hu : 0 < u) : (∫ t : ℝ in Set.Ioi 0, F t u) =
      Gamma lam * ((u : ℂ) ^ (a - lam - 1) / (1 + (u : ℂ)) ^ (a - b + 1)) := by
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.ne'
    have he : a - lam - 1 = -lam + (a - 1) := by ring
    have hp : (u : ℂ) ^ (-lam) * (u : ℂ) ^ (a - 1) = (u : ℂ) ^ (a - lam - 1) := by
      rw [← cpow_add _ _ hu0, ← he]
    have hf : (∫ t : ℝ in Set.Ioi 0, F t u) =
        (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * exp (-((u : ℂ) * t))) *
          ((u : ℂ) ^ (a - 1) * (1 + (u : ℂ)) ^ (b - a - 1)) := by
      rw [← integral_mul_const]
      exact setIntegral_congr_fun measurableSet_Ioi (fun t _ => by
        dsimp [F]; simp only [neg_mul]; ring)
    rw [hf, AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi hlam1 (by simpa using hu)]
    rw [show b - a - 1 = -(a - b + 1) by ring]
    simp only [cpow_neg, div_eq_mul_inv] at hp ⊢
    linear_combination (Gamma lam * ((1 + (u : ℂ)) ^ (a - b + 1))⁻¹) * hp
  calc
    _ = 1 / Gamma a * ∫ t : ℝ in Set.Ioi 0, ∫ u : ℝ in Set.Ioi 0, F t u := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [kummerU_laplace ha0 (by simpa using ht)]
      simp_rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
      dsimp [F]
      rw [show -(t : ℂ) * u = -(u : ℂ) * t by ring]
      ring
    _ = 1 / Gamma a * ∫ u : ℝ in Set.Ioi 0, ∫ t : ℝ in Set.Ioi 0, F t u := by
      rw [hswap]
    _ = 1 / Gamma a * (Gamma lam * betaIntegral (a - lam) (lam - b + 1)) := by
      rw [setIntegral_congr_fun measurableSet_Ioi (fun u hu => hinner u hu), integral_const_mul]
      congr 2
      rw [show a - b + 1 = (a - lam) + (lam - b + 1) by ring]
      exact AAR.Gamma.beta_on_Ioi (by simp; linarith)
        (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
    _ = _ := by
      have hG : Gamma ((a - lam) + (lam - b + 1)) ≠ 0 :=
        Gamma_ne_zero_of_re_pos (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
      have hbeta := Gamma_mul_Gamma_eq_betaIntegral
        (s := a - lam) (t := lam - b + 1) (by simp; linarith)
        (by simp only [sub_re, add_re, one_re] at hlam0 ⊢; linarith)
      rw [show (a - lam) + (lam - b + 1) = a - b + 1 by ring] at hbeta hG
      have heB : betaIntegral (a - lam) (lam - b + 1) =
          Gamma (a - lam) * Gamma (lam - b + 1) / Gamma (a - b + 1) := by
        apply (eq_div_iff hG).mpr
        simpa only [mul_comm] using hbeta.symm
      rw [heB]
      simp only [div_eq_mul_inv]
      ring

/-- A cosine transform of `𝐌`. For `a ≤ 1/2` the integral converges only conditionally,
which Lean's integral does not capture, so `1/2 < a` is required. -/
@[dlmf 13.10.E12]
theorem cosine_regularizedHGFun {a b x : ℝ} (hx : 0 < x) (ha : 1 / 2 < a) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {(b : ℂ)} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * (x : ℂ) ^ (2 * (a : ℂ) - 1) *
        exp (-(x : ℂ) ^ 2) *
        kummerU (b - 1 / 2) (a + 1 / 2) (x ^ 2) := by
  sorry

/-- A Hankel-type transform of `𝐌`, for real `x > 0`. For non-real `x` the Bessel kernel grows like
`exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required for
Lean's integral. -/
@[dlmf 13.10.E13]
theorem bessel_regularizedHGFun {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hb : 0 < b.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (-a + ν / 2) * exp (-x) * regularizedHGFun {ν - b + 1} {ν - a + 1} x := by
  sorry

/-- A Hankel-type transform of `𝐌` in terms of U, for real `x > 0`. For non-real `x` the Bessel
kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable,
as required for Lean's integral. -/
@[dlmf 13.10.E14]
theorem bessel_regularizedHGFun_U {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * kummerU a (a - b + ν + 2) x := by
  sorry

/-- A Hankel-type transform of Tricomi U, for real `x > 0`. For non-real `x` the Bessel kernel grows
like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required
for Lean's integral. -/
@[dlmf 13.10.E15]
theorem bessel_kummerU {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * a.re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * kummerU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) / Gamma a * x ^ (ν / 2) * kummerU (ν - b + 2) (ν - a + 2) x := by
  sorry

/-- `𝐅(a,b;c;0) = 1/Γ(c)`. -/
lemma regularizedGaussHG_zero_arg (a b c : ℂ) : regularizedGaussHG a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHG_eq_regularizedGaussHGFun a b c (by simp), regularizedGaussHGFun_eq_tsum,
    tsum_eq_single 0 (fun n hn => by simp [zero_pow hn])]
  simp

open Set in
open scoped Nat in
/-- Termwise integration of the Bessel series against the Tricomi Laplace transform; the
factor `t^n e^{-t/2} ≤ 2^n n!` gives a summable majorant. -/
@[dlmf 13.10.E16]
theorem bessel_kummerU_M {a b ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) * x ^ (ν / 2) * exp (-x) *
        regularizedHGFun {a} {a - b + ν + 2} x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  set d := regularizedHGFunCoeff (∅ : Multiset ℂ) {ν + 1} with hd
  set F : ℕ → ℝ → ℂ := fun n t => (x ^ (ν / 2) * (d n * (-x) ^ n)) *
    tricomiLaplaceKernel a (ν + n + 1) b 1 t with hF
  have hν0' : b.re - 2 < ν.re := by
    have h := hν0; simp only [sub_re] at h; norm_num at h; linarith
  have hνn : ∀ n : ℕ, 0 < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hνb : ∀ n : ℕ, (b - 1).re < (ν + n + 1).re := fun n => by
    simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hL : ∀ n : ℕ, _ := fun n =>
    laplace_kummerU_gauss (a := a) (b := ν + n + 1) (c := b) (z := 1) (hνn n) (hνb n) (by simp)
  have hFi : ∀ n : ℕ, IntegrableOn (F n) (Ioi 0) := fun n => (hL n).1.const_mul _
  -- the fixed half-weight majorant
  have hK0 := (laplace_kummerU_gauss (a := a) (b := ν + 1) (c := b) (z := (1 / 2 : ℂ))
    (by simp; linarith) (by simp; linarith) (by norm_num)).1
  set K0 := tricomiLaplaceKernel a (ν + 1) b (1 / 2) with hK0def
  have hker : ∀ n : ℕ, ∀ t : ℝ, 0 < t → tricomiLaplaceKernel a (ν + n + 1) b 1 t =
      ((t ^ n * Real.exp (-(t / 2)) : ℝ) : ℂ) * K0 t := by
    intro n t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    simp only [hK0def, tricomiLaplaceKernel]
    rw [show ν + n + 1 - 1 = (ν + 1 - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast]
    have he : exp (-1 * (t : ℂ)) = exp (-(1 / 2) * (t : ℂ)) * exp (-(t / 2 : ℝ) : ℂ) := by
      rw [← exp_add]; push_cast; ring_nf
    rw [he]; push_cast; ring
  have htn : ∀ n : ℕ, ∀ t : ℝ, 0 < t → t ^ n * Real.exp (-(t / 2)) ≤ 2 ^ n * n ! := by
    intro n t ht
    have h := Real.pow_div_factorial_le_exp (x := t / 2) (by positivity) n
    rw [div_pow, div_div, div_le_iff₀ (by positivity)] at h
    have he : Real.exp (t / 2) * Real.exp (-(t / 2)) = 1 := by rw [← Real.exp_add]; simp
    calc t ^ n * Real.exp (-(t / 2)) ≤ Real.exp (t / 2) * (2 ^ n * n !) * Real.exp (-(t / 2)) := by
          gcongr
      _ = _ := by rw [mul_comm, ← mul_assoc, mul_comm (Real.exp _), he, one_mul]
  set C0 := ∫ t : ℝ in Ioi 0, ‖K0 t‖ with hC0
  have hbound : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤
      ‖x ^ (ν / 2)‖ * C0 * (‖regularizedHGFunCoeff {(1 : ℂ)} {ν + 1} n‖ * (2 * ‖x‖) ^ n) := by
    intro n
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ ≤
        (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ := by
      intro t ht
      have ht0 : (0 : ℝ) < t := ht
      simp only [hF]
      rw [hker n t ht0, norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      have := htn n t ht0
      have h0 := norm_nonneg (K0 t)
      calc _ = (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (t ^ n * Real.exp (-(t / 2))) * ‖K0 t‖ := by ring
        _ ≤ (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n) * (2 ^ n * n !) * ‖K0 t‖ := by gcongr
        _ = _ := by ring
    calc (∫ t : ℝ in Ioi 0, ‖F n t‖) ≤ ∫ t : ℝ in Ioi 0,
          (‖x ^ (ν / 2)‖ * ‖d n‖ * ‖x‖ ^ n * (2 ^ n * n !)) * ‖K0 t‖ :=
        setIntegral_mono_on (hFi n).norm (hK0.norm.const_mul _) measurableSet_Ioi hpt
      _ = _ := by
        rw [MeasureTheory.integral_const_mul, ← hC0, regularizedHGFunCoeff_singleton, hd,
          AAR.Bessel.regularizedHGFunCoeff_empty]
        have hp : poch (1 : ℂ) n = n ! := by
          simp [poch, ascPochhammer_eval_one]
        have hfac : (n ! : ℝ) ≠ 0 := by positivity
        rw [hp]
        simp only [norm_div, norm_mul, one_div, norm_inv, Complex.norm_natCast, mul_pow]
        field_simp
  have hsum : Summable (fun n => ∫ t : ℝ in Ioi 0, ‖F n t‖) := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun t => norm_nonneg _) hbound ?_
    have h := ((hasFPowerSeriesOnBall_regularizedConfluent 1 (ν + 1)).hasSum_mul_pow
      (z := ((2 * ‖x‖ : ℝ) : ℂ)) (by simp)).summable.norm.mul_left (‖x ^ (ν / 2)‖ * C0)
    refine h.congr fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hs := hasSum_integral_of_summable_integral_norm hFi hsum
  have hc : 0 < (ν - b + 2).re := by simp; linarith
  have hterm : ∀ n : ℕ, (∫ t : ℝ in Ioi 0, F n t) = x ^ (ν / 2) * Gamma (ν - b + 2) *
      (regularizedHGFunCoeff {ν - b + 2} {a - b + ν + 2} n * (-x) ^ n) := by
    intro n
    simp only [hF]
    rw [MeasureTheory.integral_const_mul, (hL n).2, sub_self, regularizedGaussHG_zero_arg, hd,
      AAR.Bessel.regularizedHGFunCoeff_empty, regularizedHGFunCoeff_singleton]
    have hp := (Gamma_add_nat_div_Gamma_eq (n := n) (ν - b + 2) (not_neg_nat_of_re_pos hc))
    have hG1 : Gamma (ν + 1 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])
    have hG2 : Gamma (ν - b + 2) ≠ 0 := Gamma_ne_zero_of_re_pos hc
    rw [show poch (ν - b + 2) n = Gamma (ν - b + 2 + n) / Gamma (ν - b + 2) from hp.symm,
      show ν + n + 1 = ν + 1 + n by ring, show ν + 1 + n - b + 1 = ν - b + 2 + n by ring,
      show a + (ν + 1 + n) - b + 1 = a - b + ν + 2 + n by ring]
    field_simp
  simp_rw [hterm] at hs
  have hM := ((hasFPowerSeriesOnBall_regularizedConfluent (ν - b + 2) (a - b + ν + 2)).hasSum_mul_pow
    (z := -x) (by simp)).mul_left (x ^ (ν / 2) * Gamma (ν - b + 2))
  have hpt : ∀ t ∈ Ioi (0 : ℝ), exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
      besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) = ∑' n, F n t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have h0 := ((AAR.Bessel.hasFPowerSeriesOnBall_regularized0F1 (ν + 1)).hasSum_mul_pow
      (z := -x * t) (by simp)).mul_left (x ^ (ν / 2) * (exp (-(t : ℂ)) * (t : ℂ) ^ ν * kummerU a b t))
    rw [besselJ_two_sqrt hx0 ht0]
    have hνt : (t : ℂ) ^ (ν / 2) * (t : ℂ) ^ (ν / 2) = (t : ℂ) ^ ν := by
      rw [← cpow_add _ _ htc]; ring_nf
    refine Eq.trans ?_ (h0.tsum_eq.symm.trans (tsum_congr fun n => ?_))
    · linear_combination (exp (-(t : ℂ)) * kummerU a b t * x ^ (ν / 2) *
        regularizedHGFun ∅ {ν + 1} (-x * t)) * hνt
    · simp only [hF, hd, tricomiLaplaceKernel]
      rw [show ν + n + 1 - 1 = ν + n by ring, cpow_add _ _ htc, cpow_natCast, mul_pow]
      ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, hs.unique hM,
    regularizedConfluent_kummer_transform (ν - b + 2) (a - b + ν + 2) (-x), neg_neg,
    show a - b + ν + 2 - (ν - b + 2) = a by ring]
  ring

@[dlmf 13.23.E1]
theorem laplace_whittakerM {κ μ ν z : ℂ}
    (h : 0 < μ.re + ν.re + 1 / 2) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) / (z + 1 / 2) ^ (μ + ν + 1 / 2) *
        ₂F₁ (1 / 2 + μ - κ) (1 / 2 + μ + ν) (1 + 2 * μ) (1 / (z + 1 / 2)) := by
  set A := 1 / 2 + μ - κ
  set B := 1 / 2 + μ + ν
  set C := 1 + 2 * μ
  set Z := z + 1 / 2
  rw [show μ + ν + 1 / 2 = B by simp only [B]; ring]
  have hB : 0 < B.re := by simp [B]; linarith
  have hZ : 0 < Z.re := by simp [Z]; linarith
  have hZ1 : ‖(1 : ℂ)‖ < Z.re := by simp [Z]; linarith
  have hZ0 : Z ≠ 0 := by intro h; simp [h] at hZ
  have hw : ‖1 / Z‖ < 1 := by
    rw [norm_div, norm_one, div_lt_one (norm_pos_iff.mpr hZ0)]
    exact (by simpa using hZ1 : (1 : ℝ) < Z.re).trans_le (re_le_norm Z)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) = (t : ℂ) ^ (B - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; simp only [B]; ring
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-Z * t) := by
      rw [← Complex.exp_add]; congr 1; simp only [Z]; ring
    rw [whittakerM, show μ - κ + 1 / 2 = A by simp only [A]; ring, ← hp, ← he]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, div_eq_mul_inv, ← cpow_neg]
  by_cases hC : ∀ k : ℕ, C ≠ -(k : ℂ)
  · have hl := laplace_regularizedHGFun_of_norm_lt (a := A) (c := C) (k := 1) hB hZ hZ1
    simp only [one_mul] at hl
    have hG := Gamma_ne_zero hC
    rw [AAR.Hypergeometric.regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      AAR.Hypergeometric.regularizedGaussHGFun_eq_div_Gamma hC] at hl
    simp_rw [kummerM_eq_mul_regularizedHGFun hC]
    have hm : (∫ t : ℝ in Set.Ioi 0,
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * (Gamma C * regularizedHGFun {A} {C} t)) =
        Gamma C * ∫ t : ℝ in Set.Ioi 0,
          exp (-Z * t) * (t : ℂ) ^ (B - 1) * regularizedHGFun {A} {C} t := by
      rw [← integral_const_mul]; congr 1; funext t; ring
    rw [hm, hl]
    field_simp
  · push_neg at hC
    obtain ⟨m, hm⟩ := hC
    have hK : ∀ t : ℂ, kummerM A C t =
        ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) * t ^ n := by
      intro t
      unfold kummerM
      refine tsum_eq_sum fun n hn => ?_
      have hmn : m < n := by rw [Finset.mem_range] at hn; omega
      simp [hm, poch_neg_nat_eq_zero hmn]
    have hF : ₂F₁ A B C (1 / Z) =
        ∑ n ∈ Finset.range (m + 1), gaussHGCoeff A B C n * (1 / Z) ^ n := by
      rw [ordinaryHypergeometric_eq_tsum]
      simp only [smul_eq_mul]
      have hterm : (fun k : ℕ =>
          ((k.factorial : ℂ)⁻¹) * (ascPochhammer ℂ k).eval A *
            (ascPochhammer ℂ k).eval B * ((ascPochhammer ℂ k).eval C)⁻¹ * (1 / Z) ^ k) =
          fun k => gaussHGCoeff A B C k * (1 / Z) ^ k := by
        funext k
        simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
      rw [hterm]
      refine tsum_eq_sum fun k hk => ?_
      have hmk : m < k := by rw [Finset.mem_range] at hk; omega
      simp [gaussHGCoeff, hm, poch_neg_nat_eq_zero hmk]
    have hBn (n : ℕ) : 0 < (B + n).re := by simp; positivity
    have hFi (n : ℕ) : IntegrableOn
        (fun t : ℝ => poch A n / (poch C n * (n.factorial : ℂ)) *
          ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t)))) (Set.Ioi 0) := by
      refine Integrable.const_mul ?_ _
      have hreal := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1)
        (s := B.re + n - 1) (b := Z.re)
        (by have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hZ
      simp only [Real.rpow_one] at hreal
      apply Integrable.mono' hreal (Measurable.aestronglyMeasurable (by fun_prop))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp]
      simp
    have hpt : ∀ t ∈ Set.Ioi (0 : ℝ),
        exp (-Z * t) * (t : ℂ) ^ (B - 1) * kummerM A C t =
          ∑ n ∈ Finset.range (m + 1), poch A n / (poch C n * (n.factorial : ℂ)) *
            ((t : ℂ) ^ (B + n - 1) * exp (-(Z * t))) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
      rw [hK, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show B + n - 1 = (B - 1) + n by ring, cpow_add _ _ ht0, cpow_natCast,
        neg_mul]
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_finsetSum _ fun n _ => hFi n,
      hF, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, AAR.Gamma.integral_cpow_mul_exp_neg_mul_Ioi (hBn n) hZ]
    have hp := not_neg_nat_of_re_pos hB
    have hGb := (div_eq_iff (Gamma_ne_zero hp)).mp (Gamma_add_nat_div_Gamma_eq (n := n) B hp)
    rw [hGb, show -(B + (n : ℂ)) = -B + -(n : ℂ) by ring, cpow_add _ _ hZ0, cpow_neg Z (n : ℂ),
      cpow_natCast, gaussHGCoeff, one_div, inv_pow]
    simp only [poch]
    ring

@[dlmf 13.23.E2]
theorem laplace_whittakerM_closed {κ μ z : ℂ}
    (hμ : -1 / 2 < μ.re) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t =
      Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
        (z - 1 / 2) ^ (κ - μ - 1 / 2) := by
  have hb : 0 < (2 * μ + 1).re := by simp; linarith
  have hp : ∀ k : ℕ, 1 + 2 * μ ≠ -(k : ℂ) :=
    not_neg_nat_of_re_pos (by simpa [add_comm] using hb)
  have hB : 0 < (z + 1 / 2).re := by simp; linarith
  have hA : 0 < (z - 1 / 2).re := by simp; linarith
  have hB0 : z + 1 / 2 ≠ 0 := by intro h; rw [h] at hB; simpa using hB
  have hA0 : z - 1 / 2 ≠ 0 := by intro h; rw [h] at hA; simpa using hA
  have hr : 1 - (z + 1 / 2)⁻¹ = (z - 1 / 2) / (z + 1 / 2) := by
    apply (eq_div_iff hB0).mpr
    rw [sub_mul, one_mul, inv_mul_cancel₀ hB0]
    ring
  have hargA := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)))
  have hargB := (abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hB)))
  have hargBπ : (z + 1 / 2).arg ≠ Real.pi := by linarith [Real.pi_pos]
  have hlog : log ((z - 1 / 2) / (z + 1 / 2)) = log (z - 1 / 2) - log (z + 1 / 2) := by
    rw [div_eq_mul_inv, Complex.log_mul hA0 (inv_ne_zero hB0), Complex.log_inv _ hargBπ]
    · rfl
    · rw [arg_inv, if_neg hargBπ]
      constructor <;> linarith [hargA.1, hargA.2, hargB.1, hargB.2]
  have hpow : (1 - (z + 1 / 2)⁻¹) ^ (κ - μ - 1 / 2) =
      (z - 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) := by
    rw [hr, cpow_def_of_ne_zero (div_ne_zero hA0 hB0), hlog,
      sub_mul, exp_sub, cpow_def_of_ne_zero hA0, cpow_def_of_ne_zero hB0,
      mul_neg, exp_neg, div_eq_mul_inv]
  have hi : (∫ t : ℝ in Set.Ioi 0,
      exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t) =
      Gamma (2 * μ + 1) * ∫ t : ℝ in Set.Ioi 0,
        exp (-(z + 1 / 2) * t) * (t : ℂ) ^ ((2 * μ + 1) - 1) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [whittakerM, kummerM_eq_mul_regularizedHGFun hp,
      show 1 + 2 * μ = 2 * μ + 1 by ring]
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have he : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]
      congr 1
      ring
    have htP : (t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ ((2 * μ + 1) - 1) := by
      rw [← cpow_add _ _ ht0]
      congr 1
      ring
    calc
      _ = Gamma (2 * μ + 1) * (exp (-z * t) * exp (-(t : ℂ) / 2)) *
          ((t : ℂ) ^ (μ - 1 / 2) * (t : ℂ) ^ (μ + 1 / 2)) *
          regularizedHGFun {μ - κ + 1 / 2} {2 * μ + 1} t := by ring
      _ = _ := by rw [he, htP]; ring
  rw [hi, laplace_regularizedHGFun_self hb (by simp; linarith),
    show -(μ - κ + 1 / 2) = κ - μ - 1 / 2 by ring, hpow]
  rw [show -(2 * μ + 1) = (-κ - μ - 1 / 2) + (κ - μ - 1 / 2) by ring,
    cpow_add _ _ hB0]
  have hc : (z + 1 / 2) ^ (κ - μ - 1 / 2) * (z + 1 / 2) ^ (-(κ - μ - 1 / 2)) = 1 := by
    rw [cpow_neg, mul_inv_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hB0))]
  linear_combination Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
    (z - 1 / 2) ^ (κ - μ - 1 / 2) * hc

/-- The Mellin transform uses regularized M, including exceptional second parameters. -/
@[dlmf 13.23.E3]
theorem mellin_whittakerM {κ μ ν : ℂ}
    (h0 : -1 / 2 - μ.re < ν.re) (h1 : ν.re < κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) *
        regularizedWhittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) * Gamma (κ - ν) /
        (Gamma (1 / 2 + μ + κ) * Gamma (1 / 2 + μ - ν)) := by
  have hm := mellin_regularizedHGFun_exp (a := μ - κ + 1 / 2)
    (b := μ + ν + 1 / 2) (c := 1 + 2 * μ) (by simp; linarith) (by simp; linarith)
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * regularizedWhittakerM κ μ t =
      exp (-(t : ℂ)) * (t : ℂ) ^ (μ + ν + 1 / 2 - 1) *
        regularizedHGFun {μ - κ + 1 / 2} {1 + 2 * μ} t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (μ + 1 / 2) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; congr 1; ring
    rw [regularizedWhittakerM, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) - (μ + ν + 1 / 2) = κ - ν by ring,
    show (1 + 2 * μ) - (μ - κ + 1 / 2) = 1 / 2 + μ + κ by ring,
    show (1 + 2 * μ) - (μ + ν + 1 / 2) = 1 / 2 + μ - ν by ring]

@[dlmf 13.23.E4]
theorem laplace_whittakerW {κ μ ν z : ℂ}
    (h : |μ.re| < ν.re + 1 / 2) (hz : -1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) *
        AAR.Hypergeometric.regularizedGaussHG (1 / 2 - μ + ν) (1 / 2 + μ + ν) (ν - κ + 1)
            (1 / 2 - z) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := (laplace_kummerU_gauss (a := 1 / 2 + μ - κ) (b := μ + ν + 1 / 2)
    (c := 1 + 2 * μ) (z := z + 1 / 2) (by simp; linarith)
      (by simp; linarith) (by simp; linarith)).2
  have he : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        tricomiLaplaceKernel (1 / 2 + μ - κ) (μ + ν + 1 / 2) (1 + 2 * μ) (z + 1 / 2) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) =
        (t : ℂ) ^ (μ + ν + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; congr 1; ring
    have hx : exp (-z * t) * exp (-(t : ℂ) / 2) = exp (-(z + 1 / 2) * t) := by
      rw [← exp_add]; congr 1; ring
    rw [whittakerW, tricomiLaplaceKernel, ← hp, ← hx]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi he, hm,
    show μ + ν + 1 / 2 = 1 / 2 + μ + ν by ring,
    show (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring,
    show (1 / 2 + μ - κ) + (1 / 2 + μ + ν) - (1 + 2 * μ) + 1 = ν - κ + 1 by ring,
    show 1 - (z + 1 / 2) = 1 / 2 - z by ring,
    AAR.Hypergeometric.regularizedGaussHG_symm _ _ _ (by
      change 1 - (1 / 2 - z) ∈ slitPlane
      left; simp; linarith)]

@[dlmf 13.23.E5]
theorem mellin_whittakerW {κ μ ν : ℂ}
    (h0 : |μ.re| - 1 / 2 < ν.re) (h1 : ν.re < -κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) * Gamma (-κ - ν) /
        (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) := by
  have hμ := abs_le.mp (le_refl |μ.re|)
  have hm := mellin_kummerU (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) (lam := ν + μ + 1 / 2)
    (by simp; linarith) (by simp; linarith) (by simp; linarith)
  have hcongr : ∀ t ∈ Set.Ioi (0 : ℝ),
      exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
        (t : ℂ) ^ (ν + μ + 1 / 2 - 1) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have hp : (t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν + μ + 1 / 2 - 1) := by
      rw [← cpow_add _ _ ht0]; ring_nf
    have he : exp ((t : ℂ) / 2) * exp (-(t : ℂ) / 2) = 1 := by
      rw [← Complex.exp_add]; ring_nf; exact Complex.exp_zero
    rw [whittakerW, ← hp]
    linear_combination ((t : ℂ) ^ (ν - 1) * (t : ℂ) ^ (1 / 2 + μ) *
      kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t) * he
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, hm]
  congr 1
  · rw [show ν + μ + 1 / 2 = 1 / 2 + μ + ν by ring,
      show 1 / 2 + μ - κ - (1 / 2 + μ + ν) = -κ - ν by ring,
      show 1 / 2 + μ + ν - (1 + 2 * μ) + 1 = 1 / 2 - μ + ν by ring]
    ring
  · rw [show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]

/-- A cosine transform of regularized Whittaker M. For `κ + μ ≤ 0` the integral converges only
conditionally, which Lean's integral does not capture, so `0 < κ + μ` is required. -/
@[dlmf 13.23.E8]
theorem cosine_whittakerM {κ μ x : ℝ} (hx : 0 < x)
    (h : 0 < (κ + μ : ℂ).re) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) *
          (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          regularizedWhittakerM κ μ ((t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) * exp (-(x : ℂ) ^ 2 / 2) * (x : ℂ) ^ ((μ : ℂ) + κ - 1) /
        (2 * Gamma (1 / 2 + (μ : ℂ) + κ)) *
        whittakerW (κ / 2 - 3 * μ / 2) (κ / 2 + μ / 2) (x ^ 2) := by
  sorry

/-- A Hankel-type transform of regularized Whittaker M, for real `x > 0`. For non-real `x` the Bessel kernel
grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as
required for Lean's integral. -/
@[dlmf 13.23.E9]
theorem bessel_whittakerM {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hμ : -1 / 2 < μ.re) (hμ' : μ.re < κ.re + ν.re / 2 - 1 / 4) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) *
        x ^ ((κ - μ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ + 3 * μ - ν + 1 / 2) / 2) ((κ - μ + ν - 1 / 2) / 2) x := by
  sorry

/-- A Hankel-type transform of regularized Whittaker M in terms of W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E10]
theorem bessel_whittakerM_W {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (κ + μ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * regularizedWhittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-x / 2) * x ^ ((κ + μ - 3 / 2) / 2) / Gamma (1 / 2 + μ + κ) *
        whittakerW ((κ - 3 * μ + ν + 1 / 2) / 2) ((κ + μ - ν - 1 / 2) / 2) x := by
  sorry

/-- A Hankel-type transform of `e^{t/2}` times Whittaker W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E11]
theorem bessel_whittakerW {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * (μ - κ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) / Gamma (1 / 2 + μ - κ) * exp (x / 2) *
        x ^ ((μ - κ - 3 / 2) / 2) *
        whittakerW ((κ + 3 * μ - ν - 1 / 2) / 2) ((κ - μ + ν + 1 / 2) / 2) x := by
  sorry

open Set in
/-- The output M is regularized; Gamma poles in its second parameter are retained. -/
@[dlmf 13.23.E12]
theorem bessel_whittakerW_M {κ μ ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) * exp (-x / 2) *
        x ^ ((μ + κ - 3 / 2) / 2) *
        regularizedWhittakerM ((κ - 3 * μ + ν + 1 / 2) / 2) ((ν - μ - κ + 1 / 2) / 2) x := by
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU (1 / 2 + μ - κ) (1 + 2 * μ) t *
        besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) := by
    intro t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    have hp : (t : ℂ) ^ ((ν - 1) / 2 - μ) * (t : ℂ) ^ (1 / 2 + μ) = (t : ℂ) ^ (ν / 2) := by
      rw [← cpow_add _ _ htc]; ring_nf
    rw [whittakerW, ← he, ← hp]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    bessel_kummerU_M hx (by simp; linarith) hν1, regularizedWhittakerM,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + ν + 2 = 1 + 2 * ((ν - μ - κ + 1 / 2) / 2) by ring,
    show ν - (1 + 2 * μ) + 2 = ν - 2 * μ + 1 by ring,
    show 1 / 2 + μ - κ = (ν - μ - κ + 1 / 2) / 2 - (κ - 3 * μ + ν + 1 / 2) / 2 + 1 / 2 by ring]
  have he : exp (-x / 2) * exp (-x / 2) = exp (-x) := by rw [← exp_add]; ring_nf
  have hp : x ^ ((μ + κ - 3 / 2) / 2) * x ^ ((ν - μ - κ + 1 / 2) / 2 + 1 / 2) = x ^ (ν / 2) := by
    rw [← cpow_add _ _ hx0]; ring_nf
  rw [← he, ← hp]; ring


/-! ### Gauss and Stieltjes representations (DLMF 13.4.5, 13.4.8, 13.16.6, 13.16.9)

These representations from §13.4 and §13.16 are proved here, after the Laplace transforms
they use. For `Re a > 0`, two applications of the regularized Kummer Laplace transform and
Fubini reduce 13.4.8 to Tricomi's Laplace representation. Tricomi's contiguous relation in
`a`, matched by a regularized Gauss contiguous relation that also raises `c`, then removes
the restriction on `a`. The Stieltjes form follows from `1/(t+z) = ∫ e^{-(t+z)s} ds`, the
Tricomi Laplace transform, Pfaff's transformation and 13.4.8 with `c = 1`. It is first proved
for `Re z > 0` and then continued holomorphically to the slit plane. -/

section GaussStieltjes

open Set

/-- `𝐅(a,c;c;w) = (1-w)^{-a}/Γ(c)` on the cut plane. -/
lemma regularizedGaussHG_self_right (a c : ℂ) {w : ℂ} (hw : w ∈ cutPlane) :
    regularizedGaussHG a c c w = (1 - w) ^ (-a) * (Gamma c)⁻¹ := by
  have h0 : regularizedGaussHG 0 (c - a) c w = (Gamma c)⁻¹ :=
    eqOn_cutPlane_of_eqOn_disk (f := regularizedGaussHG 0 (c - a) c) (g := fun _ => (Gamma c)⁻¹)
      (analyticOnNhd_regularizedGaussHG _ _ _) analyticOnNhd_const (fun u hu => by
        rw [regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hu, regularizedGaussHGFun_eq_tsum,
          tsum_eq_single 0 (fun n hn => by
            obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
            simp [ascPochhammer_succ_left])]
        simp) hw
  rw [regularizedGaussHG_euler, show c - c = (0 : ℂ) by ring, regularizedGaussHG_symm _ _ _ hw, h0,
    show c - a - c = -a by ring]
  exact hw

lemma neg_ofReal_mem_cutPlane {t : ℝ} (ht : 0 ≤ t) : (-(t : ℂ)) ∈ cutPlane := by
  change 1 - -(t : ℂ) ∈ slitPlane
  rw [sub_neg_eq_add]
  exact Or.inl (by simp; linarith)

/-- The kernel of the Gauss–Laplace representation 13.4.8. -/
def kummerUGaussKernel (a b c z : ℂ) (t : ℝ) : ℂ :=
  exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedGaussHG a (a - b + 1) c (-(t : ℂ))

lemma kummerU_gauss_of_re_pos {a b c z : ℂ} (ha : 0 < a.re) (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  obtain ⟨β, hβ⟩ : ∃ β : ℂ, β = a - b + 1 := ⟨_, rfl⟩
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  set F : ℝ → ℝ → ℂ := fun t s => exp (-z * t) * (t : ℂ) ^ (c - 1) *
    (exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s)) with hF
  obtain ⟨C, hC, N, hM⟩ := regularizedConfluent_ray_growth β c (-z)
  have hmax : max 0 (-z).re = 0 := by simp; linarith
  have hRc : Continuous (fun q : ℝ × ℝ => regularizedHGFun {β} {c} ((-z * q.1) * q.2)) :=
    (continuous_regularizedConfluent.comp (show Continuous (fun w : ℂ => (β, c, w)) by fun_prop)).comp
      (show Continuous (fun q : ℝ × ℝ => (-z * (q.1 : ℂ)) * (q.2 : ℂ)) by fun_prop)
  have hRm := hRc.measurable
  have hmeas : AEStronglyMeasurable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine Measurable.aestronglyMeasurable ?_
    simp only [hF, Function.uncurry_def]
    fun_prop
  have hf1 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := c.re - 1) (by linarith) hz N
  have hf2 := integrableOn_rpow_mul_one_add_pow_mul_exp (s := a.re - 1) (by linarith) hz N
  have hFi : Integrable (Function.uncurry F) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine ((hf1.mul_prod hf2).const_mul C).mono' hmeas ?_
    have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))), q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
      rw [Measure.prod_restrict]
      exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
    filter_upwards [hset] with q hq
    obtain ⟨t, s⟩ := q
    obtain ⟨ht, hs⟩ := hq
    change 0 < t at ht; change 0 < s at hs
    have hb := hM (t * s) (by positivity)
    rw [hmax, zero_mul, Real.exp_zero, mul_one] at hb
    have harg : (-z * t) * s = -z * ((t * s : ℝ) : ℂ) := by push_cast; ring
    simp only [hF, Function.uncurry_def, norm_mul, Complex.norm_exp, norm_cpow_eq_rpow_re_of_pos ht,
      norm_cpow_eq_rpow_re_of_pos hs, harg]
    simp only [neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, one_re]
    have h1 : (1 + t * s) ^ N ≤ (1 + t) ^ N * (1 + s) ^ N := by
      rw [← mul_pow]; gcongr; nlinarith
    calc _ ≤ Real.exp (-(z.re * t)) * t ^ (c.re - 1) *
          (Real.exp (-(z.re * s)) * s ^ (a.re - 1) * (C * ((1 + t) ^ N * (1 + s) ^ N))) := by
          gcongr
          rw [← neg_mul]
          exact hb.trans (mul_le_mul_of_nonneg_left h1 hC)
      _ = _ := by ring
  have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
      (Gamma a)⁻¹ * z ^ a * ∫ s : ℝ in Ioi 0, F t s := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hL := laplace_regularizedHGFun (a := β) (b := a) (c := c) (k := -z * t) (z := z) ha
      (by simp; nlinarith) hz
    have harg : (-z * t) / z = -(t : ℂ) := by field_simp
    rw [harg] at hL
    have hF' : ∫ s : ℝ in Ioi 0, F t s = exp (-z * t) * (t : ℂ) ^ (c - 1) *
        ∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * regularizedHGFun {β} {c} ((-z * t) * s) := by
      simp only [hF]; rw [integral_const_mul]
    rw [hF', hL, kummerUGaussKernel, ← hβ,
      regularizedGaussHG_symm _ _ _ (neg_ofReal_mem_cutPlane ht0.le)]
    have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
    have hza : z ^ a * z ^ (-a) = 1 := by rw [← cpow_add _ _ hz0]; simp
    have e : ∀ X Y : ℂ, (Gamma a)⁻¹ * z ^ a * (X * (Gamma a * z ^ (-a) * Y)) =
        X * Y * (z ^ a * z ^ (-a)) * ((Gamma a)⁻¹ * Gamma a) := fun X Y => by ring
    rw [e, hza, inv_mul_cancel₀ hGa]; ring
  have hinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, F t s =
      z ^ (-c) * (exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_regularizedHGFun (a := β) (b := c) (c := c) (k := -z * s) (z := z) hc
      (by simp; nlinarith) hz
    have harg : (-z * s) / z = -(s : ℂ) := by field_simp
    rw [harg, regularizedGaussHG_self_right _ _ (neg_ofReal_mem_cutPlane hs0.le)] at hL
    have hF' : ∫ t : ℝ in Ioi 0, F t s = (exp (-z * s) * (s : ℂ) ^ (a - 1)) *
        ∫ t : ℝ in Ioi 0, exp (-z * t) * (t : ℂ) ^ (c - 1) * regularizedHGFun {β} {c} ((-z * s) * t) := by
      rw [← integral_const_mul]
      congr 1; funext t
      simp only [hF]
      rw [show (-z * (t : ℂ)) * s = (-z * s) * t by ring]
      ring
    rw [hF', hL, sub_neg_eq_add, hβ, show -(a - b + 1) = b - a - 1 by ring]
    field_simp [Gamma_ne_zero_of_re_pos hc]
  have hint := (hFi.integral_prod_left.const_mul ((Gamma a)⁻¹ * z ^ a)).congr (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
  refine ⟨hint, ?_⟩
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    integral_integral_swap hFi, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
    kummerU_laplace ha hz]
  have hzz : z ^ (c - a) * z ^ a * z ^ (-c) = 1 := by
    rw [← cpow_add _ _ hz0, ← cpow_add _ _ hz0]; ring_nf; exact cpow_zero _
  generalize (∫ s : ℝ in Ioi 0, exp (-z * s) * (s : ℂ) ^ (a - 1) * (1 + (s : ℂ)) ^ (b - a - 1)) = J
  linear_combination (-(Gamma a)⁻¹ * J) * hzz

/-- 13.4.8 with absolute integrability, for every first parameter, by Tricomi's
contiguous relation in `a` and the matching regularized Gauss relation. -/
lemma kummerU_gauss_aux {a b c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
      kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hshift : ∀ N : ℕ, ∀ a b c : ℂ, 0 < a.re + N → 0 < c.re →
      IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) ∧
        kummerU a b z = z ^ (c - a) * ∫ t : ℝ in Ioi 0, kummerUGaussKernel a b c z t := by
    intro N
    induction N with
    | zero => intro a b c ha hc; exact kummerU_gauss_of_re_pos (by simpa using ha) hc hz
    | succ N ih =>
      intro a b c ha hc
      have h1 := ih (a + 1) (b + 1) c (by simp at ha ⊢; linarith) hc
      have h2 := ih (a + 1) b (c + 1) (by simp at ha ⊢; linarith) (by simp; linarith)
      have hpt : ∀ t ∈ Ioi (0 : ℝ), kummerUGaussKernel a b c z t =
          kummerUGaussKernel (a + 1) (b + 1) c z t +
            (a - b + 1) * kummerUGaussKernel (a + 1) b (c + 1) z t := by
        intro t ht
        have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
        have hw := neg_ofReal_mem_cutPlane (le_of_lt (mem_Ioi.mp ht))
        have hg := regularizedGaussHG_contiguous_shift_b (a - b + 1) a c hw
        rw [regularizedGaussHG_symm _ _ _ hw, regularizedGaussHG_symm (a - b + 1) (a + 1) c hw,
          regularizedGaussHG_symm (a - b + 1 + 1) (a + 1) (c + 1) hw] at hg
        simp only [kummerUGaussKernel]
        rw [show a + 1 - (b + 1) + 1 = a - b + 1 by ring, show a + 1 - b + 1 = a - b + 1 + 1 by ring,
          show c + 1 - 1 = (c - 1) + 1 by ring, cpow_add _ _ ht0, cpow_one]
        linear_combination (exp (-z * t) * (t : ℂ) ^ (c - 1)) * hg
      have hi : IntegrableOn (kummerUGaussKernel a b c z) (Ioi 0) :=
        (h1.1.add (h2.1.const_mul (a - b + 1))).congr (by
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact (hpt t ht).symm)
      refine ⟨hi, ?_⟩
      have hU := kummerU_contiguous_shift_a (a + 1) b z hz0
      rw [add_sub_cancel_right] at hU
      rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add h1.1 (h2.1.const_mul _),
        integral_const_mul]
      have hz1 : z ^ (c - a) = z * z ^ (c - (a + 1)) := by
        rw [show c - a = 1 + (c - (a + 1)) by ring, cpow_add _ _ hz0, cpow_one]
      rw [show c + 1 - (a + 1) = c - a by ring] at h2
      rw [h1.2, h2.2] at hU
      rw [hz1] at hU ⊢
      linear_combination hU
  obtain ⟨N, hN⟩ := exists_nat_gt (-a.re)
  exact hshift N a b c (by linarith) hc

@[dlmf 13.4.E8]
theorem kummerU_gauss {a b c z : ℂ} (ha : 0 < c.re) (hz : 0 < z.re) :
    kummerU a b z =
      z ^ (c - a) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.regularizedGaussHG a (a - b + 1) c (-(t : ℂ)) :=
  (kummerU_gauss_aux ha hz).2

@[dlmf 13.16.E9]
theorem whittakerW_gauss {κ μ c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + c) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.regularizedGaussHG (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ)) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  rw [whittakerW, kummerU_gauss (b := 1 + 2 * μ) hc hz,
    show 1 / 2 + μ - κ - (1 + 2 * μ) + 1 = 1 / 2 - μ - κ by ring]
  have hp : z ^ (1 / 2 + μ) * z ^ (c - (1 / 2 + μ - κ)) = z ^ (κ + c) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

/-- Points of the slit plane stay uniformly away from the closed negative ray. -/
lemma exists_forall_le_norm_add_of_mem_slitPlane {z₀ : ℂ} (hz₀ : z₀ ∈ slitPlane) :
    ∃ δ > 0, ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, δ ≤ ‖(t : ℂ) + z‖ := by
  have hd : ∃ d > 0, ∀ t : ℝ, 0 ≤ t → d ≤ ‖(t : ℂ) + z₀‖ := by
    by_cases hre : 0 < z₀.re
    · refine ⟨z₀.re, hre, fun t ht => ?_⟩
      calc z₀.re ≤ ((t : ℂ) + z₀).re := by simp; linarith
        _ ≤ _ := re_le_norm _
    · have him : z₀.im ≠ 0 := by
        rcases mem_slitPlane_iff.mp hz₀ with h | h
        · exact absurd h hre
        · exact h
      refine ⟨|z₀.im|, abs_pos.mpr him, fun t _ => ?_⟩
      calc |z₀.im| = |((t : ℂ) + z₀).im| := by simp
        _ ≤ _ := abs_im_le_norm _
  obtain ⟨d, hd0, hd⟩ := hd
  refine ⟨d / 2, by linarith, fun t ht z hz => ?_⟩
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := hd t ht
  have h2 : ‖(t : ℂ) + z₀‖ ≤ ‖(t : ℂ) + z‖ + ‖z - z₀‖ := by
    calc ‖(t : ℂ) + z₀‖ = ‖((t : ℂ) + z) - (z - z₀)‖ := by ring_nf
      _ ≤ _ := norm_sub_le _ _
  linarith

/-- The Stieltjes transform of an integrable function on the positive half-line is
holomorphic on the slit plane. -/
lemma differentiableOn_stieltjes_integral {g : ℝ → ℂ} (hg : IntegrableOn g (Ioi 0)) :
    DifferentiableOn ℂ (fun z => ∫ t : ℝ in Ioi 0, g t / ((t : ℂ) + z)) slitPlane := by
  intro z₀ hz₀
  obtain ⟨δ, hδ, hδb⟩ := exists_forall_le_norm_add_of_mem_slitPlane hz₀
  have hpos : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))), 0 ≤ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht using le_of_lt ht
  have hne : ∀ t : ℝ, 0 ≤ t → ∀ z ∈ Metric.ball z₀ δ, (t : ℂ) + z ≠ 0 := fun t ht z hz h => by
    have := hδb t ht z hz; rw [h, norm_zero] at this; linarith
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun t : ℝ => g t / ((t : ℂ) + z))
      (volume.restrict (Ioi 0)) := fun z =>
    hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))
  have hint : Integrable (fun t : ℝ => g t / ((t : ℂ) + z₀)) (volume.restrict (Ioi 0)) := by
    refine (hg.norm.const_mul δ⁻¹).mono' (hmeas z₀) ?_
    filter_upwards [hpos] with t ht
    rw [norm_div, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z₀ (Metric.mem_ball_self hδ)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0))
    (F := fun z (t : ℝ) => g t / ((t : ℂ) + z))
    (F' := fun z (t : ℝ) => -(g t / ((t : ℂ) + z) ^ 2))
    (bound := fun t => (δ ^ 2)⁻¹ * ‖g t‖)
    (Metric.ball_mem_nhds _ hδ) (Eventually.of_forall hmeas) hint
    ((hg.aestronglyMeasurable.mul (Measurable.aestronglyMeasurable (by fun_prop))).neg)
    ?_ (hg.norm.const_mul _) ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · filter_upwards [hpos] with t ht z hz
    rw [norm_neg, norm_div, norm_pow, div_eq_mul_inv, mul_comm]
    gcongr
    exact hδb t ht z hz
  · filter_upwards [hpos] with t ht z hz
    have h0 := hne t ht z hz
    have h := ((hasDerivAt_id z).const_add (t : ℂ)).inv h0
    have h' := h.const_mul (g t)
    simp only [id_eq] at h'
    convert h' using 1
    · ext w; simp [div_eq_mul_inv]
    · field_simp


/-- Tricomi's Stieltjes representation 13.4.5 in the right half-plane, by Fubini against
`1/(t+z) = ∫ e^{-(t+z)s} ds`, the Tricomi Laplace transform and Pfaff's transformation. -/
lemma kummerU_stieltjes_of_re_pos {a b z : ℂ} (hz : 0 < z.re)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z = z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
      ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
        ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hab : 0 < (1 + a - b).re := by simp only [sub_re, add_re, one_re] at ha ⊢; linarith
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha0
  have hGab : Gamma (1 + a - b) ≠ 0 := Gamma_ne_zero_of_re_pos hab
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  set K := tricomiLaplaceKernel (b - a) a b 1 with hKdef
  set G : ℝ → ℝ → ℂ := fun t s => K t * exp (-((t : ℂ) + z) * s) with hG
  have he : IntegrableOn (fun s : ℝ => Real.exp (-z.re * s)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hz
  have hGi : Integrable (Function.uncurry G)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine (hK.norm.mul_prod he).mono' ?_ ?_
    · have hm : AEStronglyMeasurable (fun q : ℝ × ℝ => K q.1 * exp (-((q.1 : ℂ) + z) * q.2))
          ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) :=
        (hK.aestronglyMeasurable.comp_fst (ν := volume.restrict (Ioi (0:ℝ)))).mul
          (Continuous.aestronglyMeasurable (by fun_prop))
      exact hm
    · have hset : ∀ᵐ q ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))),
          q ∈ Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ) := by
        rw [Measure.prod_restrict]
        exact ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)
      filter_upwards [hset] with q hq
      obtain ⟨t, s⟩ := q
      obtain ⟨ht, hs⟩ := hq
      change 0 < t at ht; change 0 < s at hs
      simp only [hG, Function.uncurry_def, norm_mul, Complex.norm_exp]
      gcongr
      simp; nlinarith
  have hsinner : ∀ t ∈ Ioi (0 : ℝ), ∫ s : ℝ in Ioi 0, G t s = K t / ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hne : (t : ℂ) + z ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith
    simp only [hG]
    rw [integral_const_mul, integral_exp_mul_complex_Ioi (by simp; linarith) 0]
    simp only [ofReal_zero, mul_zero, exp_zero]
    field_simp
  have htinner : ∀ s ∈ Ioi (0 : ℝ), ∫ t : ℝ in Ioi 0, G t s =
      Gamma a * Gamma (1 + a - b) *
        kummerUGaussKernel a b 1 z s := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hL := laplace_kummerU (a := b - a) (b := a) (c := b) (z := 1 + s) ha0 ha
      (by simp; linarith)
    have h1s : (1 + (s : ℂ)) = ((1 + s : ℝ) : ℂ) := by push_cast; ring
    have hw : 1 - (1 + (s : ℂ))⁻¹ ∈ cutPlane := by
      change 1 - (1 - (1 + (s : ℂ))⁻¹) ∈ slitPlane
      rw [sub_sub_cancel, h1s, ← ofReal_inv]
      exact ofReal_mem_slitPlane.mpr (by positivity)
    have hp := regularizedGaussHG_pfaff a (b - a) 1 hw
    rw [regularizedGaussHG_symm _ _ _ hw] at hL
    have hq : (1 - (1 + (s : ℂ))⁻¹) / (1 - (1 + (s : ℂ))⁻¹ - 1) = -(s : ℂ) := by
      have : (1 + (s : ℂ)) ≠ 0 := by rw [h1s]; exact ofReal_ne_zero.mpr (by positivity)
      field_simp; ring
    rw [hq, sub_sub_cancel, show (1 : ℂ) - (b - a) = a - b + 1 by ring] at hp
    rw [show b - a + a - b + 1 = (1 : ℂ) by ring, hp] at hL
    have hpow : (1 + (s : ℂ)) ^ (-a) * ((1 + (s : ℂ))⁻¹) ^ (-a) = 1 := by
      rw [h1s, ← ofReal_inv, ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        ← ofReal_mul, mul_inv_cancel₀ (by positivity : (1 + s : ℝ) ≠ 0), ofReal_one, one_cpow]
    have hG' : ∀ t : ℝ, G t s = tricomiLaplaceKernel (b - a) a b (1 + s) t * exp (-z * s) := by
      intro t
      simp only [hG, hKdef, tricomiLaplaceKernel]
      have : exp (-1 * (t : ℂ)) * exp (-((t : ℂ) + z) * s) = exp (-(1 + (s : ℂ)) * t) * exp (-z * s) := by
        rw [← exp_add, ← exp_add]; ring_nf
      linear_combination ((t : ℂ) ^ (a - 1) * kummerU (b - a) b t) * this
    simp_rw [hG']
    rw [integral_mul_const]
    change (∫ t : ℝ in Ioi 0, exp (-(1 + (s : ℂ)) * t) * (t : ℂ) ^ (a - 1) * kummerU (b - a) b t) *
      exp (-z * s) = _
    rw [hL, kummerUGaussKernel, sub_self, cpow_zero,
      show a - b + 1 = 1 + a - b by ring]
    linear_combination (Gamma a * Gamma (1 + a - b) * exp (-z * s) *
      regularizedGaussHG a (1 + a - b) 1 (-(s : ℂ))) * hpow
  have hrw : ∀ t ∈ Ioi (0 : ℝ), kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) = ∫ s : ℝ in Ioi 0, G t s := by
    intro t ht
    rw [hsinner t ht, hKdef, tricomiLaplaceKernel]
    ring_nf
  rw [setIntegral_congr_fun measurableSet_Ioi hrw, integral_integral_swap hGi,
    setIntegral_congr_fun measurableSet_Ioi htinner, integral_const_mul]
  have hU := (kummerU_gauss_aux (a := a) (b := b) (c := 1) (by simp) hz).2
  rw [hU]
  field_simp

@[dlmf 13.4.E5]
theorem kummerU_stieltjes {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    kummerU a b z =
      z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
        ∫ t : ℝ in Set.Ioi 0,
          kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
            ((t : ℂ) + z) := by
  have hK := (laplace_kummerU_gauss (a := b - a) (b := a) (c := b) (z := 1) ha0 ha (by simp)).1
  have hg : IntegrableOn (fun t : ℝ => kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1))
      (Ioi 0) := hK.congr (Eventually.of_forall fun t => by
        simp only [tricomiLaplaceKernel, neg_mul, one_mul]; ring)
  have hS := differentiableOn_stieltjes_integral hg
  set h : ℂ → ℂ := fun z => z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
    ∫ t : ℝ in Set.Ioi 0, kummerU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
      ((t : ℂ) + z) with hh
  have hf : AnalyticOnNhd ℂ (kummerU a b) slitPlane :=
    (differentiableOn_kummerU a b).analyticOnNhd isOpen_slitPlane
  have hha : AnalyticOnNhd ℂ h slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    exact (((differentiableAt_id.cpow (differentiableAt_const _) hw).div_const _).differentiableWithinAt).mul
      (hS w hw)
  have heq : kummerU a b =ᶠ[𝓝 1] h := by
    have hnh : {w : ℂ | 0 < w.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const continuous_re).mem_nhds (by simp)
    filter_upwards [hnh] with w hw
    exact kummerU_stieltjes_of_re_pos hw ha ha0
  exact hf.eqOn_of_preconnected_of_eventuallyEq hha ((starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected)
    one_mem_slitPlane heq hz

@[dlmf 13.16.E6]
theorem whittakerW_stieltjes {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : (2 * μ.re) < (1 / 2 + μ - κ).re) (hκ0 : 0 < (1 / 2 + μ - κ).re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + 1) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) /
            ((t : ℂ) + z) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero hz
  have hU := kummerU_stieltjes (a := 1 / 2 + μ - κ) (b := 1 + 2 * μ) hz
    (by simpa using hκ) hκ0
  rw [show 1 + (1 / 2 + μ - κ) - (1 + 2 * μ) = 1 / 2 - μ - κ by ring,
    show 1 + 2 * μ - (1 / 2 + μ - κ) = 1 / 2 + μ - (-κ) by ring] at hU
  have hint : ∀ t ∈ Ioi (0 : ℝ),
      whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) / ((t : ℂ) + z) =
        kummerU (1 / 2 + μ - (-κ)) (1 + 2 * μ) t * exp (-(t : ℂ)) * (t : ℂ) ^ (1 / 2 + μ - κ - 1) /
          ((t : ℂ) + z) := by
    intro t ht
    have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
    rw [whittakerW, show 1 / 2 + μ - κ - 1 = (1 / 2 + μ) + (-κ - 1) by ring,
      cpow_add (x := (t : ℂ)) (1 / 2 + μ) (-κ - 1) ht0]
    have he : exp (-(t : ℂ) / 2) * exp (-(t : ℂ) / 2) = exp (-(t : ℂ)) := by
      rw [← exp_add]; ring_nf
    rw [← he]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hint, whittakerW, hU]
  have hp : z ^ (1 / 2 + μ) * z ^ (1 - (1 / 2 + μ - κ)) = z ^ (κ + 1) := by
    rw [← cpow_add _ _ hz0]; ring_nf
  rw [← hp]; ring

end GaussStieltjes

end AAR.Confluent
