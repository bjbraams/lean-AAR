/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues
public import AAR.IncompleteGamma.SeriesRecurrences
public import AAR.Confluent.Integrals
public import AAR.Bessel.Elementary

/-!
# Real, contour and Mellin–Barnes representations, DLMF §8.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- Termwise evaluation of `∫_{-π}^{π} e^{iaθ + z e^{iθ}} dθ`. -/
lemma hasSum_integral_exp_circle {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun n : ℕ => 2*sin (π*a)*((-z)^n/((n.factorial : ℂ)*(a+n))))
      (∫ θ : ℝ in (-π)..π, exp (a*I*θ+z*exp (I*θ))) := by
  set F : ℕ → ℝ → ℂ := fun n θ => exp (a*I*θ)*((z*exp (I*θ))^n/(n.factorial : ℂ))
  have hF : ∀ n, Continuous (F n) := fun n => by fun_prop
  have hnorm : ∀ n θ, ‖F n θ‖ = ‖exp (a*I*θ)‖*(‖z‖^n/(n.factorial : ℝ)) := by
    intro n θ
    simp only [F, norm_mul, norm_div, norm_pow, Complex.norm_natCast]
    rw [show I*(θ:ℂ) = (θ:ℂ)*I by ring, norm_exp_ofReal_mul_I, mul_one]
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := -π) (b := π) (F := F) (f := fun θ : ℝ => exp (a*I*θ+z*exp (I*θ)))
    (fun n θ => ‖exp (a*I*θ)‖*(‖z‖^n/(n.factorial : ℝ)))
    (fun n => (hF n).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun θ _ => (hnorm n θ).le)
    (Eventually.of_forall fun θ _ => (Real.summable_pow_div_factorial ‖z‖).mul_left _)
    (by
      have : (fun t : ℝ => ∑' n : ℕ, ‖exp (a*I*t)‖*(‖z‖^n/(n.factorial : ℝ))) =
          fun t : ℝ => ‖exp (a*I*(t:ℂ))‖*Real.exp ‖z‖ := by
        funext t
        rw [tsum_mul_left, Real.exp_eq_exp_ℝ, ← NormedSpace.expSeries_div_hasSum_exp ‖z‖ |>.tsum_eq]
      rw [this]
      exact (by fun_prop : Continuous fun t : ℝ => ‖exp (a*I*(t:ℂ))‖*Real.exp ‖z‖).intervalIntegrable _ _)
    (Eventually.of_forall fun θ _ => by
      have h : HasSum (fun n : ℕ => (z*exp (I*θ))^n/(n.factorial : ℂ)) (exp (z*exp (I*θ))) := by
        simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp (z*exp (I*θ))
      simpa only [F, Complex.exp_add] using h.mul_left (exp (a*I*θ)))
  refine hsum.congr_fun fun n => ?_
  have han : a + n ≠ 0 := fun h => ha n (by linear_combination h)
  have hc : I*(a+n) ≠ 0 := mul_ne_zero I_ne_zero han
  have hint : (∫ θ : ℝ in (-π)..π, F n θ) =
      z^n/(n.factorial : ℂ) * ∫ θ : ℝ in (-π)..π, exp (I*(a+n)*θ) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [F]
    rw [mul_pow, ← Complex.exp_nat_mul, show I*(a+n)*(θ:ℂ) = a*I*θ + n*(I*θ) by ring,
      Complex.exp_add]
    ring
  rw [hint, integral_exp_mul_complex hc]
  have hs : sin (π*(a+n)) = (-1)^n*sin (π*a) := by
    rw [mul_add, show (π:ℂ)*n = n*π by ring, Complex.sin_antiperiodic.add_nat_mul_eq n]
  have hsin : exp (I*(a+n)*π) - exp (I*(a+n)*(-π:ℝ)) = 2*I*sin (π*(a+n)) := by
    rw [Complex.sin, ofReal_neg]
    ring_nf
    rw [I_sq]
    ring_nf
  rw [hsin, hs, neg_pow]
  field_simp

/-- lowerIncGamma trigonometric integral. -/
@[dlmf 8.6.E1]
theorem lowerIncGamma_trigonometric_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) (z : ℂ) :
    lowerIncGamma a z=z^a/sin (π*a)*(∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) := by
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => ha (-n) (by push_cast; exact h)
  have hsin : sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact ha k (by
      have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk)
  set G : ℝ → ℂ := fun θ => exp (a*I*θ+z*exp (I*θ))
  have hGc : Continuous G := by fun_prop
  have heq : (∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) =
      (1/2) * ∫ θ : ℝ in (-π)..π, G θ := by
    have h1 : (∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) =
        ∫ t : ℝ in 0..π, (1/2)*(G t + G (-t)) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      have hp : exp (I*(t:ℂ)) = Real.cos t + Real.sin t * I := by
        rw [show I*(t:ℂ) = t*I by ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
      have hn : exp (I*((-t:ℝ):ℂ)) = Real.cos t - Real.sin t * I := by
        rw [show I*((-t:ℝ):ℂ) = ((-t:ℝ):ℂ)*I by ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
          Real.cos_neg, Real.sin_neg, ofReal_neg]
        ring
      have e1 : G t = exp (z*Real.cos t) * exp ((a*t+z*Real.sin t)*I) := by
        simp only [G, hp]; rw [← Complex.exp_add]; congr 1; ring
      have e2 : G (-t) = exp (z*Real.cos t) * exp (-((a*t+z*Real.sin t)*I)) := by
        simp only [G, hn]; rw [← Complex.exp_add]; congr 1; push_cast; ring
      rw [e1, e2, Complex.cos]
      ring
    have hGi : ∀ c d : ℝ, IntervalIntegrable G volume c d := fun c d => hGc.intervalIntegrable c d
    have hGn : IntervalIntegrable (fun x => G (-x)) volume 0 π :=
      (hGc.comp continuous_neg).intervalIntegrable 0 π
    rw [h1, intervalIntegral.integral_const_mul, intervalIntegral.integral_add (hGi 0 π) hGn,
      intervalIntegral.integral_comp_neg,
      neg_zero, add_comm, intervalIntegral.integral_add_adjacent_intervals (hGi _ _) (hGi _ _)]
  rw [heq, ← (hasSum_integral_exp_circle ha' z).tsum_eq, tsum_mul_left,
    lowerIncGamma_eq_regularized ha', regularizedConfluent_self_succ_neg,
    ← (scIncGamma_hasSum_alternating ha' z).tsum_eq]
  have hG := Gamma_ne_zero ha'
  have hT : (∑' k : ℕ, (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) =
      (∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k)))/Gamma a := by
    rw [← tsum_div_const]
    congr 1; funext k; field_simp
  rw [hT]
  set T := ∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k))
  field_simp

/-- lowerIncGamma besselJ integral. -/
@[dlmf 8.6.E2]
theorem lowerIncGamma_besselJ_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    lowerIncGamma a z=z^(a/2)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ))) := by
  sorry

/-- `(e^x)^w = e^{xw}` for real `x`. -/
lemma ofReal_exp_cpow_eq_exp_mul (x : ℝ) (w : ℂ) : ((Real.exp x : ℝ) : ℂ)^w = exp (x*w) := by
  rw [ofReal_exp, cpow_def_of_ne_zero (Complex.exp_ne_zero _), log_exp (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le])]

/-- lowerIncGamma logarithmic integral. -/
@[dlmf 8.6.E3]
theorem lowerIncGamma_logarithmic_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (-a*t-z*Real.exp (-t))) := by
  have ha' : ∀ k : ℕ, a ≠ -k := fun k hk => by
    have := congrArg Complex.re hk
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hk := regularizedConfluent_kummer_transform a (a+1) (-z)
  rw [show a+1-a=1 by ring, neg_neg] at hk
  have hsc : regularizedHGFun {a} {a+1} (-z) = scIncGamma a z := by
    rw [hk, scIncGamma]
  rw [lowerIncGamma_eq_regularized ha', hsc, scIncGamma_integral ha]
  have hG := Gamma_ne_zero ha'
  rw [show Gamma a * z^a * (1/Gamma a * ∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t)) =
    z^a * ∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t) by field_simp]
  congr 1
  set g : ℝ → ℂ := fun s => (s : ℂ)^(a-1)*exp (-z*s)
  have hneg := integral_comp_neg_Ioi 0 (fun x : ℝ => Real.exp x • g (Real.exp x))
  have himg := integral_image_eq_integral_abs_deriv_smul (s := Iio (0:ℝ)) (f := Real.exp)
    measurableSet_Iio (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Real.image_exp_Iio, Real.exp_zero] at himg
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo, himg,
    ← integral_Iic_eq_integral_Iio]
  simp_rw [abs_of_pos (Real.exp_pos _)]
  rw [neg_zero] at hneg
  rw [← hneg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [g, Complex.real_smul]
  rw [ofReal_exp_cpow_eq_exp_mul, ofReal_exp, ← Complex.exp_add]
  push_cast
  rw [← Complex.exp_add]
  congr 1
  ring

/-- upperIncGamma stieltjes integral. -/
@[dlmf 8.6.E4]
theorem upperIncGamma_stieltjes_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=z^a*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t)) := by
  -- Tricomi's Stieltjes representation 13.4.5 at `a = b = 1 - a`, where `U(0,b,t) = 1`.
  have h := kummerU_stieltjes (a := 1 - a) (b := 1 - a) hz (by simp) (by simp; linarith)
  rw [upperIncGamma, h, show 1 - (1 - a) = a by ring, show (1 : ℂ) + (1 - a) - (1 - a) = 1 by ring,
    show (1 - a) - (1 - a) = (0 : ℂ) by ring, show (1 - a) - 1 = -a by ring, Gamma_one, mul_one]
  have hi : (∫ t : ℝ in Ioi 0, kummerU 0 (1 - a) t * exp (-(t : ℂ)) * (t : ℂ) ^ (-a) /
      ((t : ℂ) + z)) = ∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [kummerU_zero, add_comm (t : ℂ) z]; ring
  rw [hi]; ring

/-- upperIncGamma laplace integral complex. -/
@[dlmf 8.6.E5]
theorem upperIncGamma_laplace_integral_complex (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*exp (-z)*(∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) := by
  have hz0 : z ≠ 0 := slitPlane_ne_zero (Or.inl hz)
  rw [upperIncGamma_eq_cpow_mul_kummerU a hz0, kummerU_laplace (by norm_num) hz, Gamma_one,
    div_one, one_mul]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [sub_self, cpow_zero, mul_one, show a+1-1-1 = a-1 by ring]

/-- upperIncGamma besselK integral. -/
@[dlmf 8.6.E6]
theorem upperIncGamma_besselK_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=2*z^(a/2)*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*AAR.Bessel.besselK a (2*(z*t)^(1/2 : ℂ))) := by
  -- DLMF 13.4.7 at `a = b = 1 - a`, with `K_{-a} = K_a`.
  have h := kummerU_eq_integral_besselK (a := 1 - a) (b := 1 - a) hz (by simp) (by simp; linarith)
  rw [show (1 - (1 - a)) / 2 = a / 2 by ring, show 1 - a - (1 - a) + 1 = (1 : ℂ) by ring,
    show 1 - a - (1 - a) / 2 - 1 / 2 = -a / 2 by ring, show 1 - a - 1 = -a by ring,
    Gamma_one, mul_one] at h
  have hi : (∫ t : ℝ in Ioi 0, exp (-(t : ℂ)) * (t : ℂ) ^ (-a / 2) *
      AAR.Bessel.besselK (-a) (2 * (z * t) ^ (1 / 2 : ℂ))) =
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*AAR.Bessel.besselK a (2*(z*t)^(1/2 : ℂ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [AAR.Bessel.besselK_neg a (two_mul_cpow_half_mem_slitPlane hz ht)]
  rw [upperIncGamma, h, hi]
  ring

/-- upperIncGamma logarithmic integral. -/
@[dlmf 8.6.E7]
theorem upperIncGamma_logarithmic_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (a*t-z*Real.exp t)) := by
  rw [upperIncGamma_laplace_integral_complex a hz, mul_assoc]
  congr 1
  have hshift := setIntegral_Ioi_comp_add_right
    (fun s : ℝ => exp (-z*(s-1))*(s:ℂ)^(a-1)) 0 1
  simp only [zero_add] at hshift
  have h1 : (∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) =
      ∫ s : ℝ in Ioi 1, exp (-z*((s:ℂ)-1))*(s:ℂ)^(a-1) := by
    rw [← hshift]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; ring_nf
  have h2 := integral_comp_exp_Ioi (fun s : ℝ => exp (-z*((s:ℂ)-1))*(s:ℂ)^(a-1)) 0
  rw [Real.exp_zero] at h2
  rw [h1, ← h2, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  simp only [Complex.real_smul]
  rw [ofReal_exp_cpow_eq_exp_mul, ofReal_exp, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

/-- lowerIncGamma circle integral. -/
@[dlmf 8.6.E8]
theorem lowerIncGamma_circle_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z = -I*z^a/(2*sin (π*a))*(∫ θ : ℝ in (-π)..π, I*exp (a*I*θ+z*exp (I*θ))) := by
  have ha' : ∀ n : ℕ, a ≠ -n := fun n h => ha (-n) (by push_cast; exact h)
  have hsin : sin (π*a) ≠ 0 := by
    rw [Complex.sin_ne_zero_iff]
    intro k hk
    exact ha k (by
      have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
      field_simp at hk
      linear_combination hk)
  rw [intervalIntegral.integral_const_mul, ← (hasSum_integral_exp_circle ha' z).tsum_eq,
    tsum_mul_left, lowerIncGamma_eq_regularized ha', regularizedConfluent_self_succ_neg,
    ← (scIncGamma_hasSum_alternating ha' z).tsum_eq]
  have hG := Gamma_ne_zero ha'
  have hT : (∑' k : ℕ, (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) =
      (∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k)))/Gamma a := by
    rw [← tsum_div_const]
    congr 1; funext k; field_simp
  rw [hT]
  set T := ∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(a+k))
  field_simp
  ring_nf
  rw [I_sq]
  ring

/-- Symmetric principal value underlying the indented contour of 8.6.9. -/
def upperGammaIndentPV (a z : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => (∫ t : ℝ in 0..(1-ε), (t : ℂ)^a*exp (-z*t)/(t-1)) + improperAtTop (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) (1+ε))

/-- upperGammaIndentPV converges. -/
@[dlmf 8.6.E9]
theorem upperGammaIndentPV_converges {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) :
    HasPrincipalValueIoi (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) 0 1 (upperGammaIndentPV a z) := by
  sorry

/-- upperIncGamma indented integral. -/
@[dlmf 8.6.E9]
theorem upperIncGamma_indented_integral {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog (-a) (log z+ε*π*I)=exp z*exp (-ε*π*I*a)/Gamma (1+a)*(upperGammaIndentPV a z-ε*π*I*exp (-z)) := by
  sorry

/-- The separating contour expressed by a vertical line and its crossed-pole residue. -/
@[dlmf 8.6.E10]
theorem lowerIncGamma_mellinBarnes {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : c ≠ a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma s/(a-s)*z^(a-s)) (2*π*(lowerIncGamma a z-(if a.re < c then Gamma a else 0))) := by
  sorry

/-- The Mellin–Barnes integrand `Γ(s+a) z^{-s}/s`, `s = c+iy`, of DLMF 8.6.11. -/
noncomputable def upperIncGammaMBIntegrand (a z : ℂ) (c y : ℝ) : ℂ :=
  Gamma ((c+y*I)+a)*z^(-((c:ℂ)+y*I))/((c:ℂ)+y*I)

/-- The Mellin–Barnes integrand is continuous in `y`. -/
lemma continuous_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : z ≠ 0) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Continuous (upperIncGammaMBIntegrand a z c) := by
  refine continuous_iff_continuousAt.mpr fun y => ?_
  unfold upperIncGammaMBIntegrand
  refine ContinuousAt.div (ContinuousAt.mul ?_ ?_) (by fun_prop) ?_
  · exact (AAR.Gamma.continuousAt_Gamma_of_re_pos (by simp; linarith)).comp (by fun_prop)
  · exact (Continuous.const_cpow (f := fun y : ℝ => -((c:ℂ)+y*I)) (by fun_prop) (Or.inl hz)).continuousAt
  · intro h; have := congrArg re h; simp at this; linarith

/-- Uniform bound for the Mellin–Barnes integrand on `‖z‖ ≥ ρ`, `|arg z| ≤ θ`. -/
lemma norm_upperIncGammaMBIntegrand_le (a : ℂ) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
    ∃ C : ℝ, ∃ K : ℕ, ∀ {ρ θ : ℝ}, 0 < ρ → ∀ z : ℂ, ρ ≤ ‖z‖ → |arg z| ≤ θ → ∀ y : ℝ,
      ‖upperIncGammaMBIntegrand a z c y‖ ≤
        C * ρ ^ (-c) / c * ((1 + |y|) ^ K * Real.exp (-((π/2-θ) * |y|))) := by
  obtain ⟨C, K, hC⟩ := AAR.Gamma.exists_norm_Gamma_shift_le hca a.im
  refine ⟨C, K, fun {ρ θ} hρ z hzρ hθ y => ?_⟩
  have hz : z ≠ 0 := norm_pos_iff.mp (hρ.trans_le hzρ)
  have e : ((c:ℂ)+y*I)+a = ((c + a.re : ℝ) : ℂ) + I * ((a.im : ℂ) + (y : ℂ)) := by
    apply Complex.ext <;> simp; ring
  have h1 := hC y; rw [← e] at h1
  have h2 : ‖z^(-((c:ℂ)+y*I))‖ ≤ ρ ^ (-c) * Real.exp (θ * |y|) := by
    rw [norm_cpow_of_ne_zero hz]
    simp only [neg_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_im, add_im, mul_im, zero_add]
    rw [div_eq_mul_inv, ← Real.exp_neg]
    refine mul_le_mul (Real.rpow_le_rpow_of_nonpos hρ hzρ (by linarith)) (Real.exp_le_exp.mpr ?_)
      (by positivity) (by positivity)
    calc -(arg z * -y) = arg z * y := by ring
      _ ≤ |arg z * y| := le_abs_self _
      _ = |arg z| * |y| := abs_mul _ _
      _ ≤ θ * |y| := by gcongr
  have h3 : ‖((c:ℂ)+y*I)‖⁻¹ ≤ 1/c := by
    rw [one_div]
    refine inv_anti₀ hc ?_
    have := Complex.abs_re_le_norm ((c:ℂ)+y*I)
    simp at this
    rwa [abs_of_pos hc] at this
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (by simpa using hC 0)
  unfold upperIncGammaMBIntegrand
  rw [div_eq_mul_inv, norm_mul, norm_mul, norm_inv]
  calc _ ≤ (C * (1 + |y|) ^ K * Real.exp (-(π * |y|) / 2)) * (ρ ^ (-c) * Real.exp (θ * |y|)) *
        (1/c) := by gcongr
    _ = _ := by
      have : Real.exp (-(π * |y|) / 2) * Real.exp (θ * |y|) = Real.exp (-((π/2-θ) * |y|)) := by
        rw [← Real.exp_add]; ring_nf
      rw [← this]; ring

/-- The Mellin–Barnes integrand is integrable for `Re z > 0`. -/
lemma integrable_upperIncGammaMBIntegrand (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) : Integrable (upperIncGammaMBIntegrand a z c) := by
  obtain ⟨C, K, hCK⟩ := norm_upperIncGammaMBIntegrand_le a hc hca
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hθ : |arg z| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  refine ((AAR.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-|arg z|) (by linarith)
    K).const_mul (C * ‖z‖ ^ (-c) / c)).mono'
    (continuous_upperIncGammaMBIntegrand a hz0 hc hca).aestronglyMeasurable
    (Eventually.of_forall fun y => hCK (norm_pos_iff.mpr hz0) z le_rfl le_rfl y)

/-- The Mellin–Barnes integral is holomorphic in `z` on the right half-plane. -/
lemma differentiableOn_integral_upperIncGammaMBIntegrand (a : ℂ) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) :
    DifferentiableOn ℂ (fun z => ∫ y, upperIncGammaMBIntegrand a z c y) {z : ℂ | 0 < z.re} := by
  obtain ⟨C, K, hCK⟩ := norm_upperIncGammaMBIntegrand_le a hc hca
  have hU : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  refine Complex.differentiableOn_integral_of_locally_dominated hU (fun z hz => ?_) ?_ ?_
  · exact (continuous_upperIncGammaMBIntegrand a (fun h => by
      rw [h] at hz; simp at hz) hc hca).aestronglyMeasurable
  · refine Eventually.of_forall fun y z hz => ?_
    have hz' : z ∈ slitPlane := Or.inl hz
    unfold upperIncGammaMBIntegrand
    refine (DifferentiableAt.div_const (DifferentiableAt.const_mul ?_ _) _).differentiableWithinAt
    exact differentiableAt_id.cpow (differentiableAt_const _) hz'
  · intro z0 hz0
    have hz00 : z0 ≠ 0 := fun h => by rw [h] at hz0; simp at hz0
    have hθ : |arg z0| < π/2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz0)
    obtain ⟨θ, hθ1, hθ2⟩ : ∃ θ : ℝ, |arg z0| < θ ∧ θ < π/2 := ⟨(|arg z0| + π/2)/2, by linarith, by linarith⟩
    have hρ : 0 < ‖z0‖/2 := by have := norm_pos_iff.mpr hz00; linarith
    have harg : ∀ᶠ z in 𝓝 z0, |arg z| < θ :=
      ((continuousAt_arg (Or.inl hz0)).abs).eventually_lt continuousAt_const hθ1
    have hnorm : ∀ᶠ z in 𝓝 z0, ‖z0‖/2 < ‖z‖ :=
      continuousAt_const.eventually_lt continuous_norm.continuousAt (by linarith)
    refine ⟨_, harg.and hnorm, fun y => C * (‖z0‖/2) ^ (-c) / c *
      ((1 + |y|) ^ K * Real.exp (-((π/2-θ) * |y|))), ?_, Eventually.of_forall fun y z hz =>
        hCK hρ z hz.2.le hz.1.le y⟩
    exact (AAR.Gamma.integrable_one_add_abs_pow_mul_exp_neg (c := π/2-θ) (by linarith)
      K).const_mul _

/-- DLMF 8.6.11 for real `x > 0`, from the Barnes integral for `U` (DLMF 13.4.18). -/
lemma integral_upperIncGammaMBIntegrand_ofReal (a : ℂ) {x : ℝ} (hx : 0 < x) {c : ℝ} (hc : 0 < c)
    (hca : 0 < c+a.re) :
    ∫ y, upperIncGammaMBIntegrand a x c y = 2*π*upperIncGamma a x := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have hB := kummerU_barnes_exp (a := 1-a) (b := 1-a) (σ := c+a.re) hx
    (by simp; linarith) hca
  set σ : ℝ := c+a.re with hσ
  set H : ℝ → ℂ := fun t => Gamma (σ + I*t) / (-a + σ + I*t) * (x:ℂ)^(-(σ + I*t)) with hH
  have hG : ∀ t : ℝ, Gamma (1 - a - 1 + σ + I * t) * Gamma (σ + I * t) /
      Gamma (1 - a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I = H t * I := by
    intro t
    have hw : -a + σ + I*t ≠ 0 := fun h => by
      have := congrArg re h; simp [hσ] at this; linarith
    have hw' : Gamma (-a + σ + I*t) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [hσ]; linarith)
    rw [show 1 - a - 1 + σ + I * t = -a + σ + I*t by ring,
      show 1 - a + σ + I * t = (-a + σ + I*t) + 1 by ring, Gamma_add_one _ hw, hH]
    field_simp
  rw [integral_congr_ae (ae_of_all _ hG), integral_mul_const] at hB
  have hshift : ∫ y, upperIncGammaMBIntegrand a x c y = ∫ y, (x:ℂ)^a * H (y + a.im) := by
    refine integral_congr_ae (ae_of_all _ fun y => ?_)
    have e1 : (σ:ℂ) + I*((y + a.im : ℝ) : ℂ) = ((c:ℂ)+y*I)+a := by
      apply Complex.ext <;> simp [hσ]
    have e2 : -a + (σ:ℂ) + I*((y + a.im : ℝ) : ℂ) = (c:ℂ)+y*I := by
      rw [add_assoc, e1]; ring
    simp only [hH, upperIncGammaMBIntegrand]
    rw [e2, e1, show -(((c:ℂ)+y*I)+a) = -((c:ℂ)+y*I) + -a by ring,
      cpow_add _ _ hx0, cpow_neg (x:ℂ) a]
    have hxa : (x:ℂ)^a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hx0)
    field_simp
  rw [hshift, integral_const_mul, integral_add_right_eq_self (fun t => H t) a.im, upperIncGamma, hB]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have he : exp (-(x:ℂ)) * exp x = 1 := by rw [← exp_add]; simp
  rw [show (1:ℂ) - (1 - a) = a by ring]
  field_simp
  linear_combination -((x:ℂ)^a * (∫ t, H t)) * he

/-- upperIncGamma mellinBarnes. -/
@[dlmf 8.6.E11]
theorem upperIncGamma_mellinBarnes (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) (2*π*upperIncGamma a z) := by
  set U : Set ℂ := {z : ℂ | 0 < z.re}
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hF := (differentiableOn_integral_upperIncGammaMBIntegrand a hc hca).analyticOnNhd hUo
  have hG : AnalyticOnNhd ℂ (fun z => 2*π*upperIncGamma a z) U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUo
    unfold upperIncGamma
    exact ((differentiableAt_neg_iff.mpr differentiableAt_id |>.cexp).mul
      (differentiableAt_kummerU _ _ (Or.inl hz))).const_mul _ |>.differentiableWithinAt
  have h1 : (1:ℂ) ∈ U := by simp [U]
  have hfreq : ∃ᶠ w in 𝓝[≠] (1:ℂ), (∫ y, upperIncGammaMBIntegrand a w c y) = 2*π*upperIncGamma a w := by
    have hmap : Tendsto (fun x : ℝ => (x:ℂ)) (𝓝[≠] (1:ℝ)) (𝓝[≠] (1:ℂ)) := by
      have := continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin (s := {(1:ℝ)}ᶜ)
        (t := {(1:ℂ)}ᶜ) (x := 1) (fun x hx h => hx (by simp at h ⊢; exact_mod_cast h))
      simpa using this
    have hev : ∀ᶠ x : ℝ in 𝓝[≠] (1:ℝ), (∫ y, upperIncGammaMBIntegrand a (x:ℂ) c y) =
        2*π*upperIncGamma a x := by
      filter_upwards [nhdsWithin_le_nhds (lt_mem_nhds (show (0:ℝ) < 1 by norm_num))] with x hx
      exact integral_upperIncGammaMBIntegrand_ofReal a hx hc hca
    exact hmap.frequently hev.frequently
  have heq := hF.eqOn_of_preconnected_of_frequently_eq hG
    (convex_halfSpace_re_gt (0:ℝ)).isPreconnected h1 hfreq hz
  have hint := integrable_upperIncGammaMBIntegrand a hz hc hca
  have hfun : (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) =
      upperIncGammaMBIntegrand a z c := rfl
  rw [hfun]
  refine ⟨_, _, intervalIntegral_tendsto_integral_Iic 0 hint.integrableOn tendsto_id,
    intervalIntegral_tendsto_integral_Ioi 0 hint.integrableOn tendsto_id, ?_⟩
  rw [intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  exact heq

/-- Finitely many residues recording indentation past right-hand Gamma poles. -/
def gammaBarnesResidueSum (a w : ℂ) (c : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/sin (π*s)*exp (-s*w))

/-- Logarithmic-plane formula with explicit separating-contour residues. -/
@[dlmf 8.6.E12]
theorem upperIncGamma_mellinBarnes_continued {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) (hw : |w.im| < 3*π/2) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0) (hca : ∀ n : ℕ, a.re-1-n ≠ c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) (2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-gammaBarnesResidueSum a w c)) := by
  sorry

end AAR.Confluent
