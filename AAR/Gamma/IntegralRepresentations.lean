/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

/-!
# Integral representations (DLMF §5.9)

Euler's integral 5.2.1 is Mathlib `Gamma_eq_integral`. Real-line Laplace,
Fourier, and Binet-type integrals are acquired below. The Hankel loop 5.9.2
and the Mellin–Barnes formulae 5.9.11, 5.9.17 are deferred.

The digamma integrals 5.9.12, 5.9.13 and 5.9.16 are proved from the digamma series by
termwise integration (`integral_tsum_of_summable_integral_norm`; the terms do not change
sign). Mathlib's Frullani integral gives `log x`. The constant in Binet's formula is
fixed by letting `x → ∞`, using `log x - 1/x ≤ ψ(x) ≤ log x`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Helper lemma for `integral_cpow_mul_exp_neg_mul_Ioi`: the case of a positive real scale. -/
lemma integral_cpow_mul_exp_neg_mul_Ioi_of_real {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)) =
      Complex.Gamma s * (r : ℂ) ^ (-s) := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have hG : ∫ x : ℝ in Set.Ioi 0, (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ)) =
      Complex.Gamma s := by
    rw [Gamma_eq_integral hs, GammaIntegral]
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    push_cast
    ring
  have h := integral_comp_mul_left_Ioi
    (fun x : ℝ => (x : ℂ) ^ (s - 1) * Complex.exp (-(x : ℂ))) 0 hr
  rw [mul_zero, hG] at h
  have h2 : ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)) =
      (r : ℂ) ^ (-(s - 1)) * ∫ x : ℝ in Set.Ioi 0,
        ((r * x : ℝ) : ℂ) ^ (s - 1) * Complex.exp (-((r * x : ℝ) : ℂ)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hP : (r : ℂ) ^ (-(s - 1)) * (r : ℂ) ^ (s - 1) = 1 := by
      rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (Or.inl hr0))]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hr.le (le_of_lt hu)]
    linear_combination (-((u : ℂ) ^ (s - 1) * Complex.exp (-((r : ℂ) * u)))) * hP
  rw [h2, h, Complex.real_smul, ofReal_inv, show -s = -(s - 1) + -1 by ring,
    cpow_add _ _ hr0, cpow_neg_one]
  ring

/-- The Laplace transform of a power: `∫₀^∞ u^(s-1) e^(-z u) du = Γ(s) z^(-s)` for
`Re s > 0` and `Re z > 0`. Proved for real `z` by scaling and extended to the right
half-plane by analytic continuation. -/
lemma integral_cpow_mul_exp_neg_mul_Ioi {s z : ℂ} (hs : 0 < s.re) (hz : 0 < z.re) :
    ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-(z * u)) =
      Complex.Gamma s * z ^ (-s) := by
  set U : Set ℂ := {w | 0 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  let I : ℂ → ℂ := fun w => ∫ u : ℝ in Set.Ioi 0, (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))
  have hmeas (w : ℂ) : AEStronglyMeasurable
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))) (volume.restrict (Set.Ioi 0)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hnorm (w : ℂ) (u : ℝ) (hu : 0 < u) :
      ‖(u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))‖ = u ^ (s.re - 1) * Real.exp (-w.re * u) := by
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hu, Complex.norm_exp]
    simp
  have hint (w : ℂ) (hw : 0 < w.re) : Integrable
      (fun u : ℝ => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u))) (volume.restrict (Set.Ioi 0)) := by
    have hb := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re - 1) (b := w.re)
      (by linarith) one_pos hw
    refine Integrable.mono' hb (hmeas w) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    rw [hnorm w u hu, Real.rpow_one]
  have hdiff : DifferentiableOn ℂ I U := by
    intro w₀ hw₀
    have hw₀' : 0 < w₀.re := hw₀
    set δ := w₀.re / 2 with hδ
    have hδ0 : 0 < δ := by positivity
    have hball : Metric.ball w₀ δ ∈ 𝓝 w₀ := Metric.ball_mem_nhds _ hδ0
    have hre : ∀ w ∈ Metric.ball w₀ δ, δ < w.re := by
      intro w hw
      rw [Metric.mem_ball, dist_eq_norm] at hw
      have h1 := abs_re_le_norm (w - w₀)
      rw [sub_re] at h1
      have h2 := (abs_lt.mp (lt_of_le_of_lt h1 hw)).1
      linarith
    have hbint : Integrable (fun u : ℝ => u ^ s.re * Real.exp (-δ * u))
        (volume.restrict (Set.Ioi 0)) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := s.re) (b := δ)
        (by linarith) one_pos hδ0
      simp only [Real.rpow_one] at this
      exact this
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioi 0))
      (F := fun w (u : ℝ) => (u : ℂ) ^ (s - 1) * Complex.exp (-(w * u)))
      (F' := fun w (u : ℝ) => (u : ℂ) ^ (s - 1) * (Complex.exp (-(w * u)) * -(u : ℂ)))
      (bound := fun u : ℝ => u ^ s.re * Real.exp (-δ * u))
      hball (Eventually.of_forall hmeas) (hint w₀ hw₀')
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ hbint ?_
    · exact h.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu w hw
      have hu' : 0 < u := hu
      have hwre := hre w hw
      rw [norm_mul, norm_mul, norm_neg, norm_cpow_eq_rpow_re_of_pos hu', Complex.norm_exp,
        Complex.norm_real, Real.norm_of_nonneg hu'.le]
      have e : u ^ (s - 1).re * u = u ^ s.re := by
        rw [sub_re, one_re, Real.rpow_sub_one hu'.ne']
        field_simp
      have hexp : Real.exp (-(w * u)).re ≤ Real.exp (-δ * u) := by
        apply Real.exp_le_exp.mpr
        simp only [neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]
        nlinarith
      calc u ^ (s - 1).re * (Real.exp (-(w * u)).re * u)
          = u ^ s.re * Real.exp (-(w * u)).re := by rw [← e]; ring
        _ ≤ u ^ s.re * Real.exp (-δ * u) := by gcongr
    · filter_upwards with u w _
      have := ((hasDerivAt_id w).mul_const (u : ℂ)).neg.cexp.const_mul ((u : ℂ) ^ (s - 1))
      simpa using this
  have hanI : AnalyticOnNhd ℂ I U := hdiff.analyticOnNhd hUo
  have hanR : AnalyticOnNhd ℂ (fun w => Complex.Gamma s * w ^ (-s)) U := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hUo
    have hslit : w ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hw)
    exact ((differentiableAt_id.cpow (differentiableAt_const _) hslit).const_mul
      _).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = Complex.Gamma s * w ^ (-s) := by
    have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have := (continuous_ofReal.tendsto (1 : ℝ)).mono_left
          (nhdsWithin_le_nhds (s := ({1}ᶜ : Set ℝ)))
        rwa [ofReal_one] at this
      · filter_upwards [self_mem_nhdsWithin] with r hr
        simpa using hr
    apply ht.frequently
    apply Eventually.frequently
    filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with r hr
    exact integral_cpow_mul_exp_neg_mul_Ioi_of_real hs hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR (convex_halfSpace_re_gt 0).isPreconnected
    (by simp [hU]) hfreq hz

/-- A Laplace-type integral for Gamma. The exponent `μ` must be real, as in DLMF: for
non-real `μ` the factor `exp (-z t ^ μ)` grows along a sequence `t → ∞` and the integral
diverges. -/
@[dlmf 5.9.E1]
theorem Gamma_laplace_power {μ ν z : ℂ} (hμ : 0 < μ.re) (hμi : μ.im = 0) (hν : 0 < ν.re)
    (hz : 0 < z.re) :
    (1 / μ) * Complex.Gamma (ν / μ) * z ^ (-(ν / μ)) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-z * (t : ℂ) ^ μ) * (t : ℂ) ^ (ν - 1) := by
  set m := μ.re with hm
  have hμm : μ = (m : ℂ) := Complex.ext (by simp [hm]) (by simp [hμi])
  have hm0 : (m : ℂ) ≠ 0 := ofReal_ne_zero.mpr hμ.ne'
  have hνμ : 0 < (ν / μ).re := by
    rw [hμm, div_ofReal_re]
    exact div_pos hν hμ
  rw [mul_assoc, ← integral_cpow_mul_exp_neg_mul_Ioi hνμ hz,
    ← integral_comp_rpow_Ioi_of_pos (p := m) hμ, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have hcpow (x : ℝ) (hx : 0 < x) (w : ℂ) :
      (x : ℂ) ^ w = Complex.exp (Real.log x * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hT : ((t ^ m : ℝ) : ℂ) = (t : ℂ) ^ μ := by rw [ofReal_cpow ht0.le, hμm]
  rw [hcpow (t ^ m) (Real.rpow_pos_of_pos ht0 m), Real.log_rpow ht0, hT,
    Real.rpow_def_of_pos ht0, hcpow t ht0 (ν - 1), Complex.real_smul, ofReal_mul, ofReal_exp, hμm]
  rw [show ∀ A B C : ℂ, 1 / (m : ℂ) * ((m : ℂ) * A * (B * C)) = (1 / (m : ℂ) * (m : ℂ)) *
      (A * B) * C from fun A B C => by ring, one_div_mul_cancel hm0, one_mul,
    ← Complex.exp_add, neg_mul, mul_comm (Complex.exp _) (Complex.exp _)]
  congr 2
  push_cast
  field_simp
  ring

/-- Binet's integrand. -/
@[dlmf 5.9.E2_5]
def binetPhi (t : ℝ) : ℝ :=
  1 - t * Real.cot t + Real.log (t / Real.sin t)

@[dlmf 5.9.E2_5]
theorem inv_Gamma_binet {x : ℝ} (hx : 0 < x) :
    (Real.Gamma x)⁻¹ =
      Real.exp x * x ^ (1 - x) / (2 * π) *
        ∫ t : ℝ in (-π)..π, Real.exp (-x * binetPhi t) := by
  sorry

/-- Helper lemma for `Gamma_gaussian`: the complex-valued form of Mathlib's
`integral_comp_abs`. -/
lemma integral_comp_abs_complex {f : ℝ → ℂ} :
    ∫ x, f |x| = 2 * ∫ x in Set.Ioi (0 : ℝ), f x := by
  have eq : ∫ (x : ℝ) in Set.Ioi 0, f |x| = ∫ (x : ℝ) in Set.Ioi 0, f x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun _ hx => ?_)
    rw [abs_eq_self.mpr (le_of_lt (by exact hx))]
  by_cases hf : IntegrableOn (fun x => f |x|) (Set.Ioi 0)
  · have int_Iic : IntegrableOn (fun x ↦ f |x|) (Set.Iic 0) := by
      rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
      let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
      rw [m.integrableOn_map_iff]
      simp_rw [Function.comp_def, abs_neg, Set.neg_preimage, Set.neg_Iic, neg_zero]
      exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf
    calc
      _ = (∫ x in Set.Iic 0, f |x|) + ∫ x in Set.Ioi 0, f |x| := by
        rw [← setIntegral_union (Set.Iic_disjoint_Ioi le_rfl) measurableSet_Ioi int_Iic hf,
          Set.Iic_union_Ioi, Measure.restrict_univ]
      _ = 2 * ∫ x in Set.Ioi 0, f x := by
        rw [two_mul, eq]
        congr! 1
        rw [← neg_zero, ← integral_comp_neg_Iic, neg_zero]
        refine setIntegral_congr_fun measurableSet_Iic (fun _ hx => ?_)
        rw [abs_eq_neg_self.mpr (by exact hx)]
  · have : ¬ Integrable (fun x => f |x|) := by
      contrapose hf
      exact hf.integrableOn
    rw [← eq, integral_undef hf, integral_undef this, mul_zero]

@[dlmf 5.9.E3]
theorem Gamma_gaussian {c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    c ^ (-z) * Complex.Gamma z =
      ∫ t : ℝ, ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2) := by
  have hsq (t : ℝ) : (t : ℂ) ^ 2 = ((|t| : ℝ) : ℂ) ^ 2 := by
    rw [← ofReal_pow, ← ofReal_pow, sq_abs]
  have hfun : (fun t : ℝ => ((|t| : ℝ) : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2)) =
      fun t : ℝ => (fun y : ℝ => (y : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (y : ℂ) ^ 2)) |t| := by
    funext t
    rw [hsq t]
  rw [hfun, integral_comp_abs_complex (f := fun y : ℝ =>
    (y : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (y : ℂ) ^ 2))]
  have hl := Gamma_laplace_power (μ := 2) (ν := 2 * z) (z := c) (by norm_num) (by simp)
    (by simp; linarith) hc
  have h2z : 2 * z / 2 = z := by ring
  rw [h2z] at hl
  have hint : ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (2 * z - 1) * Complex.exp (-c * (t : ℂ) ^ 2) =
      ∫ t : ℝ in Set.Ioi 0, Complex.exp (-c * (t : ℂ) ^ (2 : ℂ)) * (t : ℂ) ^ (2 * z - 1) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [cpow_ofNat, mul_comm]
  rw [hint, ← hl]
  ring

@[dlmf 5.9.E4]
theorem Gamma_incomplete_sum {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 1, (t : ℂ) ^ (z - 1) * Complex.exp (-(t : ℂ)) +
        ∑' k : ℕ, (-1 : ℂ) ^ k / ((z + k) * k.factorial) := by
  sorry

@[dlmf 5.9.E5]
theorem Gamma_truncated_exp {z : ℂ} {n : ℕ}
    (hlo : -((n + 1 : ℕ) : ℝ) < z.re) (hhi : z.re < -n) :
    Complex.Gamma z =
      ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (z - 1) *
          (Complex.exp (-(t : ℂ)) -
            ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * (t : ℂ) ^ k / k.factorial) := by
  sorry

/-- A cosine integral for Gamma. The integral converges only conditionally at infinity, so it is
stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be `0`. -/
@[dlmf 5.9.E6]
theorem Gamma_cos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.cos t) atTop
      (𝓝 (Real.Gamma x * Real.cos (π * x / 2))) := by
  sorry

/-- A sine integral for Gamma. The integral converges only conditionally at infinity, so it is
stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be `0`. -/
@[dlmf 5.9.E7]
theorem Gamma_sin {x : ℝ} (hx0 : -1 < x) (hx1 : x < 1) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, t ^ (x - 1) * Real.sin t) atTop
      (𝓝 (Real.Gamma x * Real.sin (π * x / 2))) := by
  sorry

/-- The generalized Fresnel cosine integral. The integral converges only conditionally at infinity,
so it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E8]
theorem Gamma_cos_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.cos (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.cos (π / (2 * n)))) := by
  sorry

/-- The generalized Fresnel sine integral. The integral converges only conditionally at infinity, so
it is stated as the limit of integrals over `(0, R)`; Lean's integral over `(0, ∞)` would be
`0`. -/
@[dlmf 5.9.E9]
theorem Gamma_sin_pow (n : ℕ) (hn : 2 ≤ n) :
    Tendsto (fun R : ℝ => ∫ t : ℝ in (0 : ℝ)..R, Real.sin (t ^ n)) atTop
      (𝓝 (Real.Gamma (1 + 1 / n) * Real.sin (π / (2 * n)))) := by
  sorry

@[dlmf 5.9.E10]
theorem log_Gamma_binet_arctan {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        2 * ∫ t : ℝ in Set.Ioi 0,
          Real.arctan (t / x) / (Real.exp (2 * π * t) - 1) := by
  sorry

@[dlmf 5.9.E10_1]
theorem log_Gamma_binet_log {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) -
        x / π * ∫ t : ℝ in Set.Ioi 0,
          Real.log (1 - Real.exp (-2 * π * t)) / (t ^ 2 + x ^ 2) := by
  sorry

@[dlmf 5.9.E10_2]
theorem log_Gamma_binet_exp {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) =
      (x - 1 / 2) * Real.log x - x + (1 / 2) * Real.log (2 * π) +
        ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-x * t) * (1 / (Real.exp t - 1) - 1 / t + 1 / 2) / t := by
  sorry

section DigammaIntegrals

open Set

/-- `∫₀¹ (tⁿ - t^{n+x-1}) dt = 1/(n+1) - 1/(n+x)`. -/
lemma integral_pow_sub_rpow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioo (0 : ℝ) 1, (t ^ n - t ^ ((n : ℝ) + x - 1)) = Real.digammaSeriesTerm x n := by
  have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow _)
      (intervalIntegral.intervalIntegrable_rpow' h1), integral_pow,
    integral_rpow (Or.inl h1), Real.digammaSeriesTerm]
  rw [zero_pow (Nat.succ_ne_zero n), Real.one_rpow,
    Real.zero_rpow (by linarith : (n : ℝ) + x - 1 + 1 ≠ 0), one_pow,
    show (n : ℝ) + x - 1 + 1 = x + n by ring]
  have : (x + n : ℝ) ≠ 0 := by positivity
  field_simp
  ring


/-- `tⁿ - t^{n+x-1} = tⁿ (1 - t^{x-1})` for `t > 0`. -/
lemma pow_sub_rpow_eq {x t : ℝ} (ht : 0 < t) (n : ℕ) :
    t ^ n - t ^ ((n : ℝ) + x - 1) = t ^ n * (1 - t ^ (x - 1)) := by
  rw [show (n : ℝ) + x - 1 = n + (x - 1) by ring, Real.rpow_add ht, Real.rpow_natCast]; ring

/-- `ψ(x) + γ = ∫₀¹ (1 - t^{x-1})/(1 - t) dt`, from the digamma series. -/
lemma digamma_add_euler_Ioo {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioo (0 : ℝ) 1, (1 - t ^ (x - 1)) / (1 - t) := by
  set F : ℕ → ℝ → ℝ := fun n t => t ^ n - t ^ ((n : ℝ) + x - 1) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioo (0 : ℝ) 1)) := by
    intro n
    have h1 : (-1 : ℝ) < (n : ℝ) + x - 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have := ((intervalIntegral.intervalIntegrable_pow (μ := volume) (a := 0) (b := 1) n).sub
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) h1))
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Ioo_subset_Ioc_self
  -- the terms do not change sign on `(0, 1)`
  have hsign : ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∀ n, ∀ t ∈ Ioo (0 : ℝ) 1, ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, Or.inl rfl, fun n t ht => ?_⟩
      have h := Real.rpow_le_one ht.1.le ht.2.le (by linarith : (0 : ℝ) ≤ x - 1)
      simp only [hF, pow_sub_rpow_eq ht.1, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg ht.1.le _) (by linarith))]
    · refine ⟨-1, Or.inr rfl, fun n t ht => ?_⟩
      have h := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht.1 ht.2.le
        (by linarith : x - 1 ≤ 0)
      simp only [hF, pow_sub_rpow_eq ht.1]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg ht.1.le _)
        (by linarith))]
      ring
  obtain ⟨ε, hε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioo (hεF n), MeasureTheory.integral_const_mul,
      integral_pow_sub_rpow hx]
  have hsum : Summable fun n => ∫ t in Ioo (0 : ℝ) 1, ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_pow_sub_rpow hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  simp only [pow_sub_rpow_eq ht.1]
  rw [tsum_mul_right, tsum_geometric_of_lt_one ht.1.le ht.2]
  field_simp


/-- `∫₀^∞ (e^{-(n+1)t} - e^{-(n+x)t}) dt = 1/(n+1) - 1/(n+x)`. -/
lemma integral_exp_sub_exp {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ∫ t in Ioi (0 : ℝ), (Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t)) =
      Real.digammaSeriesTerm x n := by
  have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [integral_sub (integrableOn_exp_mul_Ioi h1 0) (integrableOn_exp_mul_Ioi h2 0),
    integral_exp_mul_Ioi h1, integral_exp_mul_Ioi h2, Real.digammaSeriesTerm]
  simp only [mul_zero, Real.exp_zero]
  have : (x + n : ℝ) ≠ 0 := by positivity
  have : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Factorization of the exponential series term. -/
lemma exp_sub_exp_eq {x t : ℝ} (n : ℕ) :
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) =
      Real.exp (-t) ^ n * (Real.exp (-t) - Real.exp (-x * t)) := by
  rw [← Real.exp_nat_mul, mul_sub, ← Real.exp_add, ← Real.exp_add]
  congr 2 <;> ring

/-- `ψ(x) + γ = ∫₀^∞ (e^{-t} - e^{-xt})/(1 - e^{-t}) dt`, from the digamma series. -/
lemma digamma_add_euler_Ioi {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t in Ioi (0 : ℝ), (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) := by
  set F : ℕ → ℝ → ℝ := fun n t =>
    Real.exp (-((n : ℝ) + 1) * t) - Real.exp (-((n : ℝ) + x) * t) with hF
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioi (0 : ℝ))) := by
    intro n
    have h1 : -((n : ℝ) + 1) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    have h2 : -((n : ℝ) + x) < 0 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    exact (integrableOn_exp_mul_Ioi h1 0).sub (integrableOn_exp_mul_Ioi h2 0)
  have hsign : ∃ ε : ℝ, ∀ n, ∀ t ∈ Ioi (0 : ℝ), ‖F n t‖ = ε * F n t := by
    by_cases hx1 : 1 ≤ x
    · refine ⟨1, fun n t ht => ?_⟩
      have h : Real.exp (-x * t) ≤ Real.exp (-t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq, one_mul]
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (Real.exp_pos _).le _) (by linarith))]
    · refine ⟨-1, fun n t ht => ?_⟩
      have h : Real.exp (-t) ≤ Real.exp (-x * t) :=
        Real.exp_le_exp.mpr (by nlinarith [show (0 : ℝ) < t from ht])
      simp only [hF, exp_sub_exp_eq]
      rw [Real.norm_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (pow_nonneg (Real.exp_pos _).le _)
        (by linarith))]
      ring
  obtain ⟨ε, hεF⟩ := hsign
  have hnorm : ∀ n, ∫ t in Ioi (0 : ℝ), ‖F n t‖ = ε * Real.digammaSeriesTerm x n := by
    intro n
    rw [setIntegral_congr_fun measurableSet_Ioi (hεF n), MeasureTheory.integral_const_mul,
      integral_exp_sub_exp hx]
  have hsum : Summable fun n => ∫ t in Ioi (0 : ℝ), ‖F n t‖ := by
    simp_rw [hnorm]
    exact (Real.summable_digammaSeriesTerm hx).mul_left ε
  have key := integral_tsum_of_summable_integral_norm hint hsum
  simp_rw [hF, integral_exp_sub_exp hx] at key
  rw [Real.digamma_eq_tsum hx, neg_add_cancel_comm, key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  simp only [exp_sub_exp_eq]
  have he1 : Real.exp (-t) < 1 :=
    Real.exp_lt_one_iff.mpr (by simpa using (show (0 : ℝ) < t from ht))
  rw [tsum_mul_right, tsum_geometric_of_lt_one (Real.exp_pos _).le he1]
  field_simp


/-- The digamma function is monotone on `(0, ∞)`. -/
lemma digamma_le_digamma {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    Real.digamma x ≤ Real.digamma y := by
  have hy : 0 < y := hx.trans_le hxy
  rw [Real.digamma_eq_tsum hx, Real.digamma_eq_tsum hy]
  refine add_le_add_right ((Real.summable_digammaSeriesTerm hx).tsum_le_tsum (fun n => ?_)
    (Real.summable_digammaSeriesTerm hy)) _
  simp only [Real.digammaSeriesTerm]
  have : 0 < x + n := by positivity
  gcongr

/-- `log x - 1/x ≤ ψ(x) ≤ log x`. -/
lemma digamma_le_log_and {x : ℝ} (hx : 0 < x) :
    Real.log x - 1 / x ≤ Real.digamma x ∧ Real.digamma x ≤ Real.log x := by
  -- mean value theorem for `log Γ` on `[x, x + 1]`
  have hcont : ContinuousOn (fun s => Real.log (Real.Gamma s)) (Icc x (x + 1)) := by
    intro s hs
    exact (Real.hasDerivAt_log_Gamma (hx.trans_le hs.1)).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hderiv⟩ := exists_hasDerivAt_eq_slope (fun s => Real.log (Real.Gamma s))
    Real.digamma (by linarith) hcont
    (fun s hs => Real.hasDerivAt_log_Gamma (hx.trans hs.1))
  have hslope : (Real.log (Real.Gamma (x + 1)) - Real.log (Real.Gamma x)) / (x + 1 - x) =
      Real.log x := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' (Real.Gamma_pos_of_pos hx).ne']
    ring
  rw [hslope] at hderiv
  have h1 := digamma_le_digamma hx hc.1.le
  have h2 := digamma_le_digamma (hx.trans hc.1) hc.2.le
  rw [Real.digamma_add_one hx] at h2
  constructor
  · rw [one_div]; linarith
  · linarith


/-- `|e^{-t} - e^{-xt}| ≤ |x - 1| t e^{-min(1,x) t}` for `t ≥ 0`. -/
lemma abs_exp_neg_sub_exp_neg_le {x t : ℝ} (ht : 0 ≤ t) :
    |Real.exp (-t) - Real.exp (-x * t)| ≤ |x - 1| * t * Real.exp (-min 1 x * t) := by
  have key : ∀ a b : ℝ, a ≤ b → 0 ≤ Real.exp (-a * t) - Real.exp (-b * t) ∧
      Real.exp (-a * t) - Real.exp (-b * t) ≤ (b - a) * t * Real.exp (-a * t) := by
    intro a b hab
    have h1 : Real.exp (-b * t) = Real.exp (-a * t) * Real.exp (-((b - a) * t)) := by
      rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (-((b - a) * t))
    have h3 : Real.exp (-((b - a) * t)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by nlinarith)
    have he := Real.exp_pos (-a * t)
    rw [h1]
    constructor <;> nlinarith
  rcases le_total 1 x with h | h
  · obtain ⟨k0, k1⟩ := key 1 x h
    rw [min_eq_left h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonneg k0, abs_of_nonneg (show (0 : ℝ) ≤ x - 1 by linarith)]
    exact k1
  · obtain ⟨k0, k1⟩ := key x 1 h
    rw [min_eq_right h]
    simp only [neg_mul, one_mul] at k0 k1 ⊢
    rw [abs_of_nonpos (show Real.exp (-t) - Real.exp (-(x * t)) ≤ 0 by linarith),
      abs_of_nonpos (show x - 1 ≤ 0 by linarith)]
    linarith

/-- Integrability of the Frullani integrand `(e^{-t} - e^{-xt})/t`. -/
lemma integrableOn_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
  have hm : -min 1 x < 0 := by simp [hx]
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi hm 0).const_mul |x - 1|) ?_ ?_
  · exact (ContinuousOn.mul (continuousOn_inv₀.mono fun t ht => (ne_of_gt ht))
      (by fun_prop)).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    have ht' : (0 : ℝ) < t := ht
    rw [Real.norm_eq_abs, abs_mul, abs_inv, abs_of_pos ht']
    have := abs_exp_neg_sub_exp_neg_le (x := x) ht'.le
    rw [inv_mul_le_iff₀ ht']
    nlinarith

/-- Frullani: `∫₀^∞ (e^{-t} - e^{-xt})/t dt = log x`. -/
lemma integral_exp_neg_sub_exp_neg_div {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t⁻¹ * (Real.exp (-t) - Real.exp (-x * t)) = Real.log x := by
  have hc : Continuous fun t : ℝ => Real.exp (-t) := by fun_prop
  have hloc : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) :=
    hc.locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun t : ℝ => Real.exp (-t)) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hint : IntegrableOn (fun t : ℝ => t⁻¹ • (Real.exp (-(1 * t)) - Real.exp (-(x * t))))
      (Ioi 0) := by
    simpa [neg_mul, smul_eq_mul] using integrableOn_exp_neg_sub_exp_neg_div hx
  have h := Frullani.integral_Ioi_eq hloc one_pos hx hL Real.tendsto_exp_neg_atTop_nhds_zero hint
  simpa [neg_mul, smul_eq_mul] using h


/-- The Binet kernel `1/(1 - e^{-t}) - 1/t`. -/
def binetKernel (t : ℝ) : ℝ := 1 / (1 - Real.exp (-t)) - 1 / t

/-- `0 ≤ 1/(1 - e^{-t}) - 1/t ≤ 1` for `t > 0`. -/
lemma binetKernel_mem_Icc {t : ℝ} (ht : 0 < t) : binetKernel t ∈ Icc (0 : ℝ) 1 := by
  have he : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hpos : 0 < 1 - Real.exp (-t) := by linarith
  have h1 := Real.add_one_le_exp (-t)
  have h2 : t + 1 ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
  have h3 : Real.exp t * Real.exp (-t) = 1 := by rw [← Real.exp_add]; simp
  have hep := Real.exp_pos (-t)
  unfold binetKernel
  constructor
  · rw [sub_nonneg, div_le_div_iff₀ ht hpos]; linarith
  · rw [sub_le_iff_le_add, div_le_iff₀ hpos]
    have : 1 / t * (1 - Real.exp (-t)) = (1 - Real.exp (-t)) / t := by ring
    rw [add_mul, one_mul, this, ← sub_le_iff_le_add', le_div_iff₀ ht]
    nlinarith

/-- Integrability of `e^{-xt}` times the Binet kernel. -/
lemma integrableOn_exp_mul_binetKernel {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t => Real.exp (-x * t) * binetKernel t) (Ioi 0) := by
  have hm : -x < 0 := by linarith
  refine Integrable.mono' (integrableOn_exp_mul_Ioi hm 0) ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have h2 : t ≠ 0 := ht'.ne'
    unfold binetKernel
    exact (ContinuousAt.continuousWithinAt (by fun_prop (disch := assumption)))
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    obtain ⟨h0, h1⟩ := binetKernel_mem_Icc ht
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h0]
    nlinarith [Real.exp_pos (-x * t)]

/-- `J(x) = ∫₀^∞ e^{-xt} (1/(1 - e^{-t}) - 1/t) dt` lies in `[0, 1/x]`. -/
lemma integral_exp_mul_binetKernel_mem {x : ℝ} (hx : 0 < x) :
    0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤ 1 / x := by
  have hm : -x < 0 := by linarith
  constructor
  · refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    exact mul_nonneg (Real.exp_pos _).le (binetKernel_mem_Icc ht).1
  · have hle : ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t ≤
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) := by
      refine setIntegral_mono_on (integrableOn_exp_mul_binetKernel hx)
        (integrableOn_exp_mul_Ioi hm 0) measurableSet_Ioi fun t ht => ?_
      have := (binetKernel_mem_Icc ht).2
      nlinarith [Real.exp_pos (-x * t)]
    rw [integral_exp_mul_Ioi hm] at hle
    simpa [neg_div, div_neg] using hle


/-- `ψ(x) + γ - log x = J(1) - J(x)`. -/
lemma digamma_add_euler_sub_log {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant - Real.log x =
      (∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t) -
        ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  rw [digamma_add_euler_Ioi hx, ← integral_exp_neg_sub_exp_neg_div hx,
    ← integral_sub (integrableOn_exp_mul_binetKernel one_pos) (integrableOn_exp_mul_binetKernel hx)]
  have heq : EqOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-1 * t) * binetKernel t - Real.exp (-x * t) * binetKernel t) +
        t⁻¹ * (Real.exp (-t) - Real.exp (-x * t))) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  have hi1 : IntegrableOn (fun t => Real.exp (-1 * t) * binetKernel t -
      Real.exp (-x * t) * binetKernel t) (Ioi 0) :=
    (integrableOn_exp_mul_binetKernel one_pos).sub (integrableOn_exp_mul_binetKernel hx)
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_add hi1 (integrableOn_exp_neg_sub_exp_neg_div hx)]
  ring

/-- Binet's formula for the digamma function, together with `J(1) = γ`. -/
lemma digamma_eq_log_sub {x : ℝ} (hx : 0 < x) :
    Real.digamma x = Real.log x - ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t := by
  set J : ℝ → ℝ := fun x => ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * binetKernel t with hJ
  -- `ψ(y) - log y + J(y)` is constant
  have hconst : ∀ y : ℝ, 0 < y →
      Real.digamma y - Real.log y + J y = J 1 - Real.eulerMascheroniConstant := by
    intro y hy
    have := digamma_add_euler_sub_log hy
    simp only [hJ]
    linarith
  have hlim : Tendsto (fun y : ℝ => Real.digamma y - Real.log y + J y) atTop (𝓝 0) := by
    have hinv : Tendsto (fun y : ℝ => 1 / y) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero
    have h1 : Tendsto (fun y : ℝ => Real.digamma y - Real.log y) atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (hinv.neg.trans (by simp))
        tendsto_const_nhds
        ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).1; linarith
      · filter_upwards [eventually_gt_atTop 0] with y hy
        have := (digamma_le_log_and hy).2; linarith
    have h2 : Tendsto J atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).1
      · filter_upwards [eventually_gt_atTop 0] with y hy
        exact (integral_exp_mul_binetKernel_mem hy).2
    simpa using h1.add h2
  have hc : J 1 - Real.eulerMascheroniConstant = 0 := by
    refine tendsto_nhds_unique (tendsto_const_nhds.congr' ?_) hlim
    filter_upwards [eventually_gt_atTop 0] with y hy
    exact (hconst y hy).symm
  have := hconst x hx
  simp only [hJ] at this hc ⊢
  linarith

end DigammaIntegrals

open Set in
@[dlmf 5.9.E12]
theorem digamma_gauss {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0,
        Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)) := by
  have hJ1 : ∫ t in Ioi (0 : ℝ), Real.exp (-1 * t) * binetKernel t =
      Real.eulerMascheroniConstant := by
    have := digamma_eq_log_sub one_pos
    rw [Real.digamma_one, Real.log_one] at this
    linarith
  have hA : IntegrableOn (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)))
      (Ioi 0) := by
    have hi := ((integrableOn_exp_mul_binetKernel one_pos).sub
      (integrableOn_exp_mul_binetKernel hx)).add (integrableOn_exp_neg_sub_exp_neg_div hx)
    refine hi.congr_fun (fun t ht => ?_) measurableSet_Ioi
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [Pi.add_apply, Pi.sub_apply, binetKernel, neg_mul, one_mul]
    field_simp
    ring
  have heq : EqOn (fun t => Real.exp (-t) / t - Real.exp (-x * t) / (1 - Real.exp (-t)))
      (fun t => (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) -
        Real.exp (-1 * t) * binetKernel t) (Ioi 0) := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : 1 - Real.exp (-t) ≠ 0 := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    simp only [binetKernel, neg_mul, one_mul]
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq,
    integral_sub hA (integrableOn_exp_mul_binetKernel one_pos), ← digamma_add_euler_Ioi hx, hJ1]
  ring

open Set in
@[dlmf 5.9.E13]
theorem digamma_binet {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x +
        ∫ t : ℝ in Set.Ioi 0,
          (1 / t - 1 / (1 - Real.exp (-t))) * Real.exp (-t * x) := by
  rw [digamma_eq_log_sub hx, sub_eq_add_neg, ← MeasureTheory.integral_neg]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [binetKernel]
  ring_nf

@[dlmf 5.9.E14]
theorem digamma_frullani {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.exp (-t) - (1 + t) ^ (-x)) / t := by
  sorry

@[dlmf 5.9.E15]
theorem digamma_coth {x : ℝ} (hx : 0 < x) :
    Real.digamma x =
      Real.log x - 1 / (2 * x) -
        2 * ∫ t : ℝ in Set.Ioi 0,
          t / ((t ^ 2 + x ^ 2) * (Real.exp (2 * π * t) - 1)) := by
  sorry

@[dlmf 5.9.E16]
theorem digamma_add_euler {x : ℝ} (hx : 0 < x) :
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0,
        (Real.exp (-t) - Real.exp (-x * t)) / (1 - Real.exp (-t)) ∧
    Real.digamma x + Real.eulerMascheroniConstant =
      ∫ t : ℝ in (0 : ℝ)..1, (1 - t ^ (x - 1)) / (1 - t) := by
  refine ⟨digamma_add_euler_Ioi hx, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact digamma_add_euler_Ioo hx

@[dlmf 5.9.E18]
theorem eulerMascheroni_integrals :
    Real.eulerMascheroniConstant =
      -∫ t : ℝ in Set.Ioi 0, Real.exp (-t) * Real.log t ∧
    Real.eulerMascheroniConstant =
      ∫ t : ℝ in Set.Ioi 0, (1 / (1 + t) - Real.exp (-t)) / t := by
  sorry

@[dlmf 5.9.E19]
theorem iteratedDeriv_Gamma {n : ℕ} {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n Real.Gamma x =
      ∫ t : ℝ in Set.Ioi 0, (Real.log t) ^ n * Real.exp (-t) * t ^ (x - 1) := by
  sorry

@[dlmf 5.9.E20]
theorem integral_Gamma {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    ∫ t : ℝ in c..x, Real.Gamma t =
      ∫ t : ℝ in Set.Ioi 0,
        (t ^ (x - 1) - t ^ (c - 1)) / Real.log t * Real.exp (-t) := by
  sorry

end AAR.Gamma
