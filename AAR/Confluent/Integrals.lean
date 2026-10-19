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
  sorry

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

@[dlmf 13.10.E16]
theorem bessel_kummerU_M {a b ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * kummerU a b t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) * x ^ (ν / 2) * exp (-x) *
        regularizedHGFun {a} {a - b + ν + 2} x := by
  sorry

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
  sorry

end AAR.Confluent
