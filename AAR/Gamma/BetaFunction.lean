/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Beta function (DLMF §5.12)

The Euler integral and the identity `B(a,b) = Γ(a)Γ(b)/Γ(a+b)` are Mathlib
`betaIntegral` and `Gamma_mul_Gamma_eq_betaIntegral`, and are also
`selberg_integral_one` in `AAR.Selberg.Basic`. Contour formulae 5.12.9–5.12.12
are deferred.
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace AAR.Gamma

/-- Euler's Beta integral for real parameters, `∫₀¹ u^(a-1) (1-u)^(b-1) du = Γ(a)Γ(b)/Γ(a+b)`.
This is the real form of Mathlib's `Complex.Gamma_mul_Gamma_eq_betaIntegral`. -/
lemma real_betaIntegral {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ u : ℝ in (0 : ℝ)..1, u ^ (a - 1) * (1 - u) ^ (b - 1) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := (b : ℂ))
    (by simpa using ha) (by simpa using hb)
  have hne : Complex.Gamma ((a : ℂ) + b) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  push_cast
  rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, Complex.ofReal_add,
    eq_div_iff hne, hG, ← intervalIntegral.integral_ofReal, mul_comm, Complex.betaIntegral]
  congr 1
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [Set.uIcc_of_le zero_le_one] at hu
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hu.1, Complex.ofReal_cpow (by linarith [hu.2])]
  push_cast
  rfl

@[dlmf 5.12.E2]
theorem beta_sin_cos {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∫ θ : ℝ in (0 : ℝ)..(π / 2), Real.sin θ ^ (2 * a - 1) * Real.cos θ ^ (2 * b - 1) =
      (1 / 2) * (Real.Gamma a * Real.Gamma b / Real.Gamma (a + b)) := by
  -- The substitution `u = sin² θ` maps `(0, π/2)` onto `(0, 1)`.
  set f : ℝ → ℝ := fun θ => Real.sin θ ^ 2 with hf
  set f' : ℝ → ℝ := fun θ => 2 * Real.sin θ * Real.cos θ with hf'
  have hsin {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) (π / 2), HasDerivWithinAt f (f' θ) (Set.Ioo 0 (π / 2)) θ := by
    intro θ _
    refine HasDerivAt.hasDerivWithinAt ?_
    convert (Real.hasDerivAt_sin θ).pow 2 using 1
    simp only [hf']
    ring
  have hinj : Set.InjOn f (Set.Ioo 0 (π / 2)) := by
    intro x hx y hy hxy
    have h := (pow_left_inj₀ (hsin hx).le (hsin hy).le two_ne_zero).mp hxy
    exact Real.injOn_sin ⟨by linarith [hx.1, Real.pi_pos], hx.2.le⟩
      ⟨by linarith [hy.1, Real.pi_pos], hy.2.le⟩ h
  have himage : f '' Set.Ioo 0 (π / 2) = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hs := hsin hθ
      have hc := hcos hθ
      refine ⟨by positivity, ?_⟩
      have := Real.sin_sq_add_cos_sq θ
      simp only [hf]
      nlinarith
    · rintro ⟨h0, h1⟩
      have hs0 : 0 < Real.sqrt u := Real.sqrt_pos.mpr h0
      have hs1 : Real.sqrt u < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using h1
      refine ⟨Real.arcsin (Real.sqrt u), ⟨Real.arcsin_pos.mpr hs0, ?_⟩, ?_⟩
      · exact (Real.arcsin_lt_pi_div_two).mpr hs1
      · simp only [hf]
        rw [Real.sin_arcsin (by linarith) hs1.le, Real.sq_sqrt h0.le]
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun u : ℝ => u ^ (a - 1) * (1 - u) ^ (b - 1))
  rw [himage] at key
  rw [← real_betaIntegral ha hb, intervalIntegral.integral_of_le zero_le_one,
    integral_Ioc_eq_integral_Ioo, key, intervalIntegral.integral_of_le (by positivity),
    integral_Ioc_eq_integral_Ioo, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hs := hsin hθ
  have hc := hcos hθ
  have hpow {x : ℝ} (hx : 0 < x) (p : ℝ) : (x ^ 2) ^ (p - 1) = x ^ (2 * p - 1) / x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, eq_div_iff hx.ne',
      ← Real.rpow_add_one hx.ne']
    norm_num
    ring_nf
  simp only [hf, hf', smul_eq_mul]
  rw [abs_of_pos (by positivity), show 1 - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
    rw [Real.cos_sq']]
  rw [hpow hs, hpow hc]
  field_simp

@[dlmf 5.12.E3]
theorem beta_on_Ioi {a b : ℂ} (_ha : 0 < a.re) (_hb : 0 < b.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (a - 1) / (1 + (t : ℂ)) ^ (a + b) =
      betaIntegral a b := by
  -- The substitution `u = t / (1 + t)` maps `(0, ∞)` onto `(0, 1)`.
  set f : ℝ → ℝ := fun t => t / (1 + t) with hf
  set f' : ℝ → ℝ := fun t => 1 / (1 + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivWithinAt f (f' t) (Set.Ioi 0) t := by
    intro t ht
    have h1 : 1 + t ≠ 0 := ne_of_gt (by linarith [Set.mem_Ioi.mp ht])
    have hd : HasDerivAt f (f' t) t := by
      convert (hasDerivAt_id t).div ((hasDerivAt_id t).const_add 1) h1 using 1
      · rfl
      · simp only [hf', id]
        ring
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
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))
  rw [himage] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    key]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 < t := ht
  have ht1 : 0 < 1 + t := by linarith
  have hft : 0 < f t := by simp only [hf]; positivity
  have hcpow (x : ℝ) (hx : 0 < x) (s : ℂ) :
      (x : ℂ) ^ s = Complex.exp (Real.log x * s) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]
  have hlogf : Real.log (f t) = Real.log t - Real.log (1 + t) := by
    simp only [hf]
    exact Real.log_div ht0.ne' ht1.ne'
  have h1f : 1 - f t = (1 + t)⁻¹ := by
    simp only [hf]
    field_simp
    ring
  have habs : |f' t| = Real.exp (-2 * Real.log (1 + t)) := by
    rw [abs_of_pos (by simp only [hf']; positivity),
      show -2 * Real.log (1 + t) = -(Real.log (1 + t) + Real.log (1 + t)) by ring,
      Real.exp_neg, Real.exp_add, Real.exp_log ht1]
    simp only [hf']
    ring
  have e2 : (1 + (t : ℂ)) ^ (a + b) = Complex.exp (Real.log (1 + t) * (a + b)) := by
    rw [← hcpow _ ht1]
    push_cast
    rfl
  have e4 : (1 - ((f t : ℝ) : ℂ)) ^ (b - 1) = Complex.exp (-Real.log (1 + t) * (b - 1)) := by
    rw [show (1 - ((f t : ℝ) : ℂ)) = ((1 - f t : ℝ) : ℂ) by push_cast; rfl,
      hcpow _ (by rw [h1f]; positivity), h1f, Real.log_inv]
    push_cast
    rfl
  rw [hcpow _ ht0, e2, hcpow _ hft, e4, habs, Complex.real_smul, Complex.ofReal_exp, hlogf,
    ← Complex.exp_sub, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

section BetaShifted

open Filter
open scoped Topology

/-- Helper lemma for `beta_shifted`: the case of a positive real shift, by the substitution
`s = (1 + x) t / (x + t)`. -/
lemma beta_shifted_of_pos {a b : ℂ} {x : ℝ} (hx : 0 < x) :
    ∫ t : ℝ in Set.Ioo 0 1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + x) ^ (-(a + b)) =
      betaIntegral a b * (1 + (x : ℂ)) ^ (-a) * (x : ℂ) ^ (-b) := by
  set f : ℝ → ℝ := fun t => (1 + x) * t / (x + t) with hf
  set f' : ℝ → ℝ := fun t => x * (1 + x) / (x + t) ^ 2 with hf'
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivWithinAt f (f' t) (Set.Ioo 0 1) t := by
    intro t ht
    have h1 : x + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have hd : HasDerivAt f (f' t) t := by
      convert ((hasDerivAt_id t).const_mul (1 + x)).div ((hasDerivAt_id t).const_add x) h1
        using 1
      · rfl
      · simp only [hf', id]
        ring
    exact hd.hasDerivWithinAt
  have hinj : Set.InjOn f (Set.Ioo 0 1) := by
    intro t ht u hu htu
    have h1 : x + t ≠ 0 := ne_of_gt (by linarith [ht.1])
    have h2 : x + u ≠ 0 := ne_of_gt (by linarith [hu.1])
    simp only [hf] at htu
    field_simp at htu
    have h3 : x * (t - u) = 0 := by linear_combination htu
    linarith [(mul_eq_zero.mp h3).resolve_left hx.ne']
  have himage : f '' Set.Ioo 0 1 = Set.Ioo 0 1 := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      have ht0 : 0 < t := ht.1
      have ht1 : t < 1 := ht.2
      refine ⟨by simp only [hf]; positivity, ?_⟩
      rw [hf, div_lt_one (by linarith)]
      nlinarith
    · rintro ⟨h0, h1⟩
      have hd : 0 < 1 + x - u := by linarith
      refine ⟨u * x / (1 + x - u), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one hd]
        nlinarith
      · simp only [hf]
        field_simp
        ring
  have key := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj
    (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1))
  rw [himage] at key
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    key, mul_assoc, ← MeasureTheory.integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioo fun t ht => ?_
  have ht0 : 0 < t := ht.1
  have ht1 : 0 < 1 - t := by linarith [ht.2]
  have htx : 0 < t + x := by linarith
  have hx1 : 0 < 1 + x := by linarith
  have hcpow (y : ℝ) (hy : 0 < y) (w : ℂ) :
      (y : ℂ) ^ w = Complex.exp (Real.log y * w) := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hy.ne'), ofReal_log hy.le]
  have hft : 0 < f t := by simp only [hf]; positivity
  have h1f : 1 - f t = x * (1 - t) / (t + x) := by
    simp only [hf]
    field_simp
    ring
  have h1f0 : 0 < 1 - f t := by rw [h1f]; positivity
  have hlogf : Real.log (f t) = Real.log (1 + x) + Real.log t - Real.log (t + x) := by
    simp only [hf]
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul (by positivity) ht0.ne',
      add_comm x t]
  have hlog1f : Real.log (1 - f t) = Real.log x + Real.log (1 - t) - Real.log (t + x) := by
    rw [h1f, Real.log_div (by positivity) htx.ne', Real.log_mul hx.ne' ht1.ne']
  have habs : |f' t| =
      Real.exp (Real.log x + Real.log (1 + x) - 2 * Real.log (t + x)) := by
    rw [abs_of_pos (by simp only [hf']; positivity),
      show Real.log x + Real.log (1 + x) - 2 * Real.log (t + x) =
        Real.log x + Real.log (1 + x) - (Real.log (t + x) + Real.log (t + x)) by ring,
      Real.exp_sub, Real.exp_add, Real.exp_add, Real.exp_log hx, Real.exp_log hx1,
      Real.exp_log htx]
    simp only [hf']
    ring
  have e1 : (1 - (t : ℂ)) ^ (b - 1) = Complex.exp (Real.log (1 - t) * (b - 1)) := by
    rw [← hcpow _ ht1]
    push_cast
    rfl
  have e2 : ((t : ℂ) + x) ^ (-(a + b)) = Complex.exp (Real.log (t + x) * (-(a + b))) := by
    rw [← hcpow _ htx]
    push_cast
    rfl
  have e3 : (1 - ((f t : ℝ) : ℂ)) ^ (b - 1) = Complex.exp (Real.log (1 - f t) * (b - 1)) := by
    rw [← hcpow _ h1f0]
    push_cast
    rfl
  have e4 : (1 + (x : ℂ)) ^ (-a) = Complex.exp (Real.log (1 + x) * (-a)) := by
    rw [← hcpow _ hx1]
    push_cast
    rfl
  rw [hcpow t ht0, e1, e2, hcpow _ hft, e3, e4, hcpow x hx, habs, hlogf, hlog1f,
    Complex.real_smul, ofReal_exp]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[dlmf 5.12.E4]
theorem beta_shifted {a b z : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (hz : z ∈ slitPlane) :
    ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + z) ^ (a + b) =
      betaIntegral a b * (1 + z) ^ (-a) * z ^ (-b) := by
  have hform (w : ℂ) (t : ℝ) :
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) / ((t : ℂ) + w) ^ (a + b) =
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)) := by
    rw [cpow_neg, div_eq_mul_inv]
  simp_rw [hform]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  let I : ℂ → ℂ := fun w => ∫ t : ℝ in Set.Ioo 0 1,
    (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b))
  change I z = _
  have hAint : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1))
      (Set.Ioo 0 1) := by
    have := betaIntegral_convergent ha hb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    exact this.mono_set Set.Ioo_subset_Ioc_self
  have hslit_add (t : ℝ) (ht : 0 ≤ t) (w : ℂ) (hw : w ∈ slitPlane) :
      (t : ℂ) + w ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hw ⊢
    simp only [add_re, ofReal_re, add_im, ofReal_im, zero_add]
    rcases hw with h | h
    · left
      linarith
    · exact Or.inr h
  have hmeasF (w : ℂ) : AEStronglyMeasurable (fun t : ℝ =>
      (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)))
      (volume.restrict (Set.Ioo 0 1)) :=
    Measurable.aestronglyMeasurable (by fun_prop)
  have hdiff : DifferentiableOn ℂ I slitPlane := by
    intro w₀ hw₀
    set S := (fun t : ℝ => (t : ℂ) + w₀) '' Set.Icc 0 1 with hS
    have hSc : IsCompact S := isCompact_Icc.image (by fun_prop)
    have hSU : S ⊆ slitPlane := by
      rintro _ ⟨t, ht, rfl⟩
      exact hslit_add t ht.1 w₀ hw₀
    obtain ⟨δ, hδ, hδU⟩ := hSc.exists_cthickening_subset_open isOpen_slitPlane hSU
    have hKc : IsCompact (Metric.cthickening δ S) := hSc.cthickening
    have hmemK : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Metric.ball w₀ δ,
        (t : ℂ) + w ∈ Metric.cthickening δ S := by
      intro t ht w hw
      apply Metric.mem_cthickening_of_dist_le _ ((t : ℂ) + w₀) _ _
        (show (t : ℂ) + w₀ ∈ S from ⟨t, ht, rfl⟩)
      rw [dist_eq_norm, add_sub_add_left_eq_sub, ← dist_eq_norm]
      exact (Metric.mem_ball.mp hw).le
    have hcont (c : ℂ) : ContinuousOn (fun v : ℂ => v ^ c) (Metric.cthickening δ S) :=
      fun v hv => (continuousAt_cpow_const (hδU hv)).continuousWithinAt
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn (hcont (-(a + b) - 1))
    obtain ⟨M₀, hM₀⟩ := hKc.exists_bound_of_continuousOn (hcont (-(a + b)))
    have hball := Metric.ball_mem_nhds w₀ hδ
    have hint0 : Integrable (fun t : ℝ =>
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w₀) ^ (-(a + b)))
        (volume.restrict (Set.Ioo 0 1)) := by
      refine Integrable.mono' (hAint.norm.mul_const M₀) (hmeasF w₀) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      rw [norm_mul _ (((t : ℂ) + w₀) ^ (-(a + b)))]
      exact mul_le_mul_of_nonneg_left
        (hM₀ _ (hmemK t (Set.Ioo_subset_Icc_self ht) w₀ (Metric.mem_ball_self hδ)))
        (norm_nonneg _)
    have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume.restrict (Set.Ioo 0 1))
      (F := fun w (t : ℝ) =>
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) * ((t : ℂ) + w) ^ (-(a + b)))
      (F' := fun w (t : ℝ) => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) *
        (-(a + b) * ((t : ℂ) + w) ^ (-(a + b) - 1)))
      (bound := fun t : ℝ => ‖(t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)‖ * (‖a + b‖ * M))
      hball (Eventually.of_forall hmeasF) hint0
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_ (hAint.norm.mul_const _) ?_
    · exact h.2.differentiableAt.differentiableWithinAt
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w hw
      rw [norm_mul _ (-(a + b) * _), norm_mul (-(a + b)), norm_neg]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (hM _ (hmemK t (Set.Ioo_subset_Icc_self ht) w hw)) (norm_nonneg _)) (norm_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht w hw
      have hmem := hδU (hmemK t (Set.Ioo_subset_Icc_self ht) w hw)
      have := (((hasDerivAt_id w).const_add (t : ℂ)).cpow_const (c := -(a + b)) hmem).const_mul
        ((t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1))
      simp only [id, mul_one] at this
      exact this
  have hanI : AnalyticOnNhd ℂ I slitPlane := hdiff.analyticOnNhd isOpen_slitPlane
  have hanR : AnalyticOnNhd ℂ (fun w => betaIntegral a b * (1 + w) ^ (-a) * w ^ (-b))
      slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) isOpen_slitPlane
    have h1w : 1 + w ∈ slitPlane := by simpa using hslit_add 1 zero_le_one w hw
    exact (((differentiableAt_const _).mul (((differentiableAt_const 1).add
      differentiableAt_id).cpow (differentiableAt_const _) h1w)).mul
      (differentiableAt_id.cpow (differentiableAt_const _) hw)).differentiableWithinAt
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), I w = betaIntegral a b * (1 + w) ^ (-a) * w ^ (-b) := by
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
    exact beta_shifted_of_pos hr
  exact hanI.eqOn_of_preconnected_of_frequently_eq hanR
    (starConvex_one_slitPlane.isPathConnected one_mem_slitPlane).isConnected.isPreconnected
    one_mem_slitPlane hfreq hz

end BetaShifted

@[dlmf 5.12.E5]
theorem beta_cos_cos {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..(π / 2), Real.cos t ^ (a - 1) * Real.cos (b * t) =
      π / (2 : ℝ) ^ a /
        (a * (Real.Gamma ((a + b + 1) / 2) * Real.Gamma ((a - b + 1) / 2) /
          Real.Gamma (a + 1))) := by
  sorry

@[dlmf 5.12.E6]
theorem beta_sin_exp {a b : ℝ} (ha : 0 < a) (hba : |b| < a + 1) :
    ∫ t : ℝ in (0 : ℝ)..π, (Real.sin t : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * b * t) =
      (π : ℂ) / (2 : ℂ) ^ (a - 1 : ℂ) * Complex.exp (I * π * b / 2) /
        ((a : ℂ) * betaIntegral ((a + b + 1 : ℂ) / 2) ((a - b + 1 : ℂ) / 2)) := by
  sorry

/-- The real form of `beta_on_Ioi`, together with integrability of the integrand. -/
lemma real_beta_on_Ioi {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    IntegrableOn (fun u : ℝ => u ^ (p - 1) / (1 + u) ^ (p + q)) (Set.Ioi 0) ∧
      ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
        Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
  have hval : ∫ u : ℝ in Set.Ioi 0, u ^ (p - 1) / (1 + u) ^ (p + q) =
      Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by
    apply Complex.ofReal_injective
    have hG := Complex.Gamma_mul_Gamma_eq_betaIntegral (s := (p : ℂ)) (t := (q : ℂ))
      (by simpa using hp) (by simpa using hq)
    have hne : Complex.Gamma ((p : ℂ) + q) ≠ 0 :=
      Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
    push_cast
    rw [← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      Complex.ofReal_add, eq_div_iff hne, hG, ← integral_complex_ofReal, mul_comm,
      ← beta_on_Ioi (a := (p : ℂ)) (b := (q : ℂ)) (by simpa using hp) (by simpa using hq)]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Ioi (a := (0 : ℝ))) fun u hu => ?_
    have hu0 : (0 : ℝ) ≤ u := (Set.mem_Ioi.mp hu).le
    rw [Complex.ofReal_div, Complex.ofReal_cpow hu0, Complex.ofReal_cpow (by linarith)]
    push_cast
    rfl
  refine ⟨?_, hval⟩
  by_contra h
  rw [integral_undef h] at hval
  have := Real.Gamma_pos_of_pos hp
  have := Real.Gamma_pos_of_pos hq
  have := Real.Gamma_pos_of_pos (add_pos hp hq)
  have : 0 < Real.Gamma p * Real.Gamma q / Real.Gamma (p + q) := by positivity
  linarith

/-- `cosh t ^ (2a)` written with exponentials, for the substitution `u = exp (2t)`. -/
lemma cosh_rpow_eq_exp_mul (a t : ℝ) :
    Real.cosh t ^ (2 * a) =
      Real.exp (-(2 * a * t)) * (1 + Real.exp (2 * t)) ^ (2 * a) / (2 : ℝ) ^ (2 * a) := by
  have h : Real.cosh t = Real.exp (-t) * (1 + Real.exp (2 * t)) / 2 := by
    rw [Real.cosh_eq, mul_add, ← Real.exp_add]
    ring_nf
  rw [h, Real.div_rpow (by positivity) (by norm_num), Real.mul_rpow (by positivity)
    (by positivity), ← Real.exp_mul]
  ring_nf

/-- `∫ exp(2ct) / cosh(t)^(2a) dt` over `ℝ`, by the substitution `u = exp (2t)` in
`real_beta_on_Ioi`. -/
lemma integral_exp_div_cosh_rpow {a c : ℝ} (hc : |c| < a) :
    Integrable (fun t : ℝ => Real.exp (2 * c * t) / Real.cosh t ^ (2 * a)) ∧
      ∫ t : ℝ, Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
        (2 : ℝ) ^ (2 * a - 1) *
          (Real.Gamma (a + c) * Real.Gamma (a - c) / Real.Gamma (2 * a)) := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hc
  -- The substitution `u = exp (2 t)` maps `ℝ` onto `(0, ∞)`.
  set f : ℝ → ℝ := fun t => Real.exp (2 * t) with hf
  set f' : ℝ → ℝ := fun t => 2 * Real.exp (2 * t) with hf'
  have hderiv : ∀ t ∈ (Set.univ : Set ℝ), HasDerivWithinAt f (f' t) Set.univ t := by
    intro t _
    refine HasDerivAt.hasDerivWithinAt ?_
    have h := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
    simp only [id, mul_one] at h
    exact h.congr_deriv (mul_comm _ _)
  have hinj : Set.InjOn f Set.univ := fun x _ y _ hxy => by
    simpa using Real.exp_injective hxy
  have himage : f '' Set.univ = Set.Ioi 0 := by
    rw [Set.image_univ]
    ext u
    refine ⟨fun ⟨t, ht⟩ => ht ▸ Real.exp_pos _, fun hu => ⟨Real.log u / 2, ?_⟩⟩
    simp only [hf]
    rw [mul_div_cancel₀ _ two_ne_zero, Real.exp_log hu]
  set g : ℝ → ℝ := fun u => u ^ (a + c - 1) / (1 + u) ^ (a + c + (a - c))
  obtain ⟨hint, hval⟩ := real_beta_on_Ioi (p := a + c) (q := a - c) (by linarith) (by linarith)
  have key := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  have keyI := integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ hderiv hinj g
  rw [himage] at key keyI
  have hpt (t : ℝ) : Real.exp (2 * c * t) / Real.cosh t ^ (2 * a) =
      (2 : ℝ) ^ (2 * a - 1) * (|f' t| • g (f t)) := by
    simp only [hf, hf', g, smul_eq_mul]
    rw [abs_of_pos (by positivity), cosh_rpow_eq_exp_mul, ← Real.exp_mul,
      show a + c + (a - c) = 2 * a by ring, Real.rpow_sub (by norm_num), Real.rpow_one]
    field_simp
    rw [← Real.exp_add, ← Real.exp_add]
    ring_nf
  simp_rw [hpt]
  refine ⟨?_, ?_⟩
  · rw [← integrableOn_univ]
    exact (keyI.mp hint).const_mul _
  · rw [MeasureTheory.integral_const_mul, ← setIntegral_univ, ← key, hval, show a + c + (a - c) = 2 * a by ring]

@[dlmf 5.12.E7]
theorem beta_cosh {a b : ℝ} (ha : |b| < a) :
    ∫ t : ℝ in Set.Ioi 0, Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a) =
      (4 : ℝ) ^ (a - 1) *
        (Real.Gamma (a + b) * Real.Gamma (a - b) / Real.Gamma (2 * a)) := by
  obtain ⟨hI₁, hv₁⟩ := integral_exp_div_cosh_rpow ha
  obtain ⟨hI₂, hv₂⟩ := integral_exp_div_cosh_rpow (c := -b) (by rwa [abs_neg])
  have heven := integral_comp_abs (f := fun t => Real.cosh (2 * b * t) / Real.cosh t ^ (2 * a))
  have habs (t : ℝ) : Real.cosh (2 * b * |t|) / Real.cosh |t| ^ (2 * a) =
      (1 / 2) * (Real.exp (2 * b * t) / Real.cosh t ^ (2 * a)) +
        (1 / 2) * (Real.exp (2 * -b * t) / Real.cosh t ^ (2 * a)) := by
    rw [Real.cosh_abs]
    rcases abs_choice t with h | h <;> rw [h] <;>
      simp only [Real.cosh_eq] <;> ring_nf
  simp only [habs] at heven
  rw [integral_add (hI₁.const_mul _) (hI₂.const_mul _), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, hv₁, hv₂, sub_neg_eq_add,
    show a + -b = a - b by ring, mul_comm (Real.Gamma (a - b))] at heven
  have h4 : (4 : ℝ) ^ (a - 1) = (2 : ℝ) ^ (2 * a - 1) / 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num),
      show 2 * (a - 1) = 2 * a - 1 - 1 by ring, Real.rpow_sub_one two_ne_zero]
  rw [h4]
  linear_combination (-1 / 2 : ℝ) * heven

@[dlmf 5.12.E8]
theorem beta_vertical {a b : ℂ} {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re)
    (hab : 1 < (a + b).re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        1 / ((w + I * t) ^ a * (z - I * t) ^ b) =
      (w + z) ^ (1 - a - b) / ((a + b - 1) * betaIntegral a b) := by
  sorry

end AAR.Gamma
