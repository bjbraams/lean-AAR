/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Properties
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Struve integrals and Laplace transforms

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel

/-- struveH trig integral. -/
@[dlmf 11.5.E1]
theorem struveH_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sin (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveH_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sin (z*t))]

/-- struveL trig integral. -/
@[dlmf 11.5.E6]
theorem struveL_trig_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ θ : ℝ in 0..π/2, sinh (z*Real.cos θ)*(Real.sin θ : ℂ)^(2*ν) := by
  rw [struveL_eq_poisson hν (slitPlane_ne_zero hz),
    integral_poissonWeight_eq_trig ν (fun t => sinh (z*t))]

/-- struveH integral. -/
@[dlmf 11.5.E1]
theorem struveH_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH ν z = 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, (1-t^2:ℂ)^(ν-1/2)*sin (z*t) := by
  exact struveH_eq_poisson hν (slitPlane_ne_zero hz)

/-- Laplace representation retaining the reciprocal-gamma prefactor at exceptional orders. -/
@[dlmf 11.5.E2]
theorem struveK_laplace (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => 2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2))*exp (-z*t)*(1+t^2:ℂ)^(ν-1/2)) 0 (struveK ν z) := by
  sorry

/-- struveK zero laplace. -/
@[dlmf 11.5.E3]
theorem struveK_zero_laplace {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => 2/π*exp (-z*Real.sinh t)) 0 (struveK 0 z) := by
  sorry

/-- struveM integral. -/
@[dlmf 11.5.E4]
theorem struveM_integral {ν : ℂ} (hν : -1/2 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveM ν z = -2*(z/2)^ν/(Real.sqrt π*Gamma (ν+1/2)) * ∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^(ν-1/2) := by
  exact struveM_eq_poisson hν hz

/-- Two continuous functions on `ℂ` that agree on the slit plane agree everywhere. -/
theorem eq_of_continuous_of_eqOn_slitPlane {f g : ℂ → ℂ} (hf : Continuous f)
    (hg : Continuous g) (h : ∀ z ∈ slitPlane, f z = g z) (z : ℂ) : f z = g z := by
  have hd : Dense slitPlane := by
    intro z
    by_cases hz : z ∈ slitPlane
    · exact subset_closure hz
    · have ht : Tendsto (fun n : ℕ => z + I*((1:ℂ)/(n+1))) atTop (𝓝 z) := by
        have : Tendsto (fun n : ℕ => (1:ℂ)/(n+1)) atTop (𝓝 0) := by
          simpa using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℂ)
        simpa using (this.const_mul I).const_add z
      refine mem_closure_of_tendsto ht (Eventually.of_forall fun n => ?_)
      have hzim : z.im = 0 := by
        by_contra hne; exact hz (Or.inr hne)
      apply Or.inr
      have : ((1:ℂ)/(n+1)) = ((1/(n+1:ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      simp only [add_im, mul_im, I_re, I_im, ofReal_re, ofReal_im, hzim]
      positivity
  exact congrFun (hf.ext_on hd hg h) z

/-- `I₀` is entire. -/
theorem continuous_besselI_zero : Continuous (besselI 0) := by
  have he : besselI 0 = fun z => regularizedHGFun (∅ : Multiset ℂ) {0+1} (z^2/4) := by
    funext z; rw [besselI, cpow_zero, one_mul]
  rw [he]
  have hF : Differentiable ℂ (regularizedHGFun (∅ : Multiset ℂ) {(0:ℂ)+1}) :=
    fun w => (analyticAt_regularizedHGFun_of_card_le (by simp) w).differentiableAt
  exact (hF.comp (by fun_prop)).continuous

/-- struveM zero integral. -/
@[dlmf 11.5.E5]
theorem struveM_zero_integral (z : ℂ) :
    struveM 0 z = -2/π * ∫ θ : ℝ in 0..π/2, exp (-z*Real.cos θ) := by
  refine eq_of_continuous_of_eqOn_slitPlane (f := struveM 0)
    (g := fun z => -2/π * ∫ θ : ℝ in 0..π/2, exp (-z*Real.cos θ)) ?_ ?_ (fun z hz => ?_) z
  · have h1 : Continuous (struveL 0) := by
      simpa using (struveL_nat_entire 0).continuous
    exact h1.sub continuous_besselI_zero
  · refine continuous_const.mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (by fun_prop) _ _
  · rw [struveM_eq_poisson (by norm_num) hz]
    have := integral_poissonWeight_eq_trig 0 (fun t => exp (-z*t))
    rw [show (∫ t : ℝ in 0..1, exp (-z*t)*(1-t^2:ℂ)^((0:ℂ)-1/2)) =
      ∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^((0:ℂ)-1/2) * exp (-z*t) from
      intervalIntegral.integral_congr fun t _ => by ring, this]
    simp only [mul_zero, cpow_zero, mul_one, zero_add]
    rw [Complex.Gamma_one_half_eq]
    have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
    have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
      rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [hs, hp]

/-- struveL fourier. -/
@[dlmf 11.5.E7]
theorem struveL_fourier {ν : ℂ} (hν : ν.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => 2*(x/2:ℂ)^ν/(Real.sqrt π*Gamma (ν+1/2))*(1+t^2:ℂ)^(ν-1/2)*Real.sin (x*t)) 0 (besselI (-ν) x-struveL ν x) := by
  sorry

/-- struveH barnes. -/
@[dlmf 11.5.E8]
theorem struveH_barnes {ν : ℂ} (hν : -1 < ν.re) {x c : ℝ} (hx : 0 < x) (hc : -1 < c) (hc0 : c < 0) (hv : -1 < ν.re+2*c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(x^2/4:ℂ)^s) (-2*π*(x/2:ℂ)^(-ν-1)*struveH ν x) := by
  sorry

/-- Separating loop from positive infinity above the poles to positive infinity below them. -/
def positiveBarnesLoop (f : ℂ → ℂ) (c h R : ℝ) : ℂ :=
  segmentIntegral f (R+h*I) (c+h*I) + segmentIntegral f (c+h*I) (c-h*I) + segmentIntegral f (c-h*I) (R-h*I)

/-- struveL barnes loop. -/
@[dlmf 11.5.E9]
theorem struveL_barnes_loop (ν : ℂ) {z : ℂ} (hz : z ≠ 0) {c h : ℝ} (hc : -1 < c) (hc0 : c < 0) (hh : 0 < h) :
    Tendsto (fun R => positiveBarnesLoop (fun s : ℂ => π/sin (π*s)/(Gamma (3/2+s)*Gamma (3/2+ν+s))*(-z^2/4)^s) c h R) atTop (𝓝 (2*π*I*(z/2)^(-ν-1)*struveL ν z)) := by
  sorry

/-- struveHPrimitive. -/
@[dlmf 11.7.E5]
def struveHPrimitive (ν z : ℂ) : ℂ :=
  primitive (fun t => t^ν*struveH ν t) z

/-- A positive real multiple of a slit-plane point lies in the slit plane. -/
theorem ofReal_mul_mem_slitPlane {s : ℝ} (hs : 0 < s) {z : ℂ} (hz : z ∈ slitPlane) :
    (s:ℂ)*z ∈ slitPlane := by
  rw [mem_slitPlane_iff] at hz ⊢
  rcases hz with h | h
  · left; simp; positivity
  · right; simp; exact ⟨hs.ne', h⟩

/-- Derivative of the antiderivative used in the primitive recurrence. -/
theorem hasDerivAt_struveHPrimitive_aux {ν : ℂ} (hν1 : ν + 1 ≠ 0) {w : ℂ} (hw : w ∈ slitPlane) :
    HasDerivAt (fun w : ℂ => -(w^(ν+1)*struveH ν w) +
        w^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)))
      (w^(ν+1)*struveH (ν+1) w - (2*ν+1)*(w^ν*struveH ν w)) w := by
  have hw0 := slitPlane_ne_zero hw
  have h28 := struveH_weighted_deriv_28 ν hw
  have hp := (hasStrictDerivAt_cpow_const (c := 2*ν+1) hw).hasDerivAt
  have hprod := hp.mul h28
  have heq : (fun u : ℂ => u^(2*ν+1) * (u^(-1*ν) * struveH ν u)) =ᶠ[𝓝 w]
      fun u => u^(ν+1)*struveH ν u := by
    filter_upwards [isOpen_slitPlane.mem_nhds hw] with u hu
    rw [← mul_assoc, ← cpow_add _ _ (slitPlane_ne_zero hu)]; ring_nf
  have hA := hprod.congr_of_eventuallyEq heq.symm
  have hB := (hasStrictDerivAt_cpow_const (c := 2*ν+2) hw).hasDerivAt.div_const
    (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2))
  refine (hA.neg.add hB).congr_deriv ?_
  have e1 : w^(2*ν+1-1) * w^(-1*ν) = w^ν := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e2 : w^(2*ν+1) * w^(-ν) = w^(ν+1) := by
    rw [← cpow_add _ _ hw0]; ring_nf
  have e3 : w^(2*ν+2-1) = w^(2*ν+1) := by ring_nf
  have key : (2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) := by
    rw [cpow_neg, cpow_add _ _ two_ne_zero, cpow_one]
    have h2 : (2:ℂ)^ν ≠ 0 := cpow_ne_zero_iff.2 (Or.inl two_ne_zero)
    by_cases hg : (Real.sqrt π:ℂ)*Gamma (ν+3/2) = 0
    · rw [hg, div_zero, show (2:ℂ)^ν*2*(ν+1)*Real.sqrt π*Gamma (ν+3/2) =
        2^ν*2*(ν+1)*((Real.sqrt π)*Gamma (ν+3/2)) by ring, hg, mul_zero, div_zero]
    · field_simp
  rw [e3]
  have : (2*ν+2) * w^(2*ν+1) / (2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      w^(2*ν+1) * (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2))) := by
    rw [← key]; ring
  rw [this]
  linear_combination (-(2*ν+1)*struveH ν w) * e1 + struveH (ν+1) w * e2

/-- The power of z squared carries twice the argument of z, and is expressed using the inherited logarithm. -/
@[dlmf 11.7.E6]
theorem struveHPrimitive_recurrence {ν : ℂ} (hν : -1 < ν.re) {z : ℂ} (hz : z ∈ slitPlane) :
    struveHPrimitive (ν+1) z = (2*ν+1)*struveHPrimitive ν z-z^(ν+1)*struveH ν z+exp ((ν+1)*(2*log z-log 2))/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
  have hν1 : ν+1 ≠ 0 := fun h => by have := congrArg re h; simp at this; linarith
  have hν2 : 2*ν+2 ≠ 0 := fun h => hν1 (by linear_combination h/2)
  have hz0 := slitPlane_ne_zero hz
  set D : ℂ := 2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2) with hD
  set G : ℂ → ℂ := fun w => -(w^(ν+1)*struveH ν w) + w^(2*ν+2)/D with hG
  have hcore : ∀ μ : ℂ, Continuous (struveHCore μ) := fun μ => (entire_struveHCore μ).continuous
  have hf : ∀ μ : ℂ, ∀ s : ℝ, 0 < s → ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z) =
      (s:ℂ)^(2*μ+1) * (z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z)) := by
    intro μ s hs
    rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, AAR.Confluent.ofReal_mul_cpow' hs hz0,
      AAR.Confluent.ofReal_mul_cpow' hs (div_ne_zero hz0 two_ne_zero)]
    have : (s:ℂ)^(2*μ+1) = (s:ℂ)^μ * (s:ℂ)^(μ+1) := by
      rw [← cpow_add _ _ (ofReal_ne_zero.2 hs.ne')]; ring_nf
    rw [this]; ring
  have hint : ∀ μ : ℂ, -1 < μ.re →
      IntervalIntegrable (fun s : ℝ => ((s:ℂ)*z)^μ * struveH μ ((s:ℂ)*z)) volume 0 1 := by
    intro μ hμ
    have h1 : IntervalIntegrable (fun s : ℝ => (s:ℂ)^(2*μ+1)) volume 0 1 :=
      intervalIntegral.intervalIntegrable_cpow' (by simp; linarith)
    have hc : Continuous fun s : ℝ => z^μ*(z/2)^(μ+1)*struveHCore μ ((s:ℂ)*z) :=
      continuous_const.mul ((hcore μ).comp (by fun_prop))
    have h2 := h1.mul_continuousOn hc.continuousOn
    refine h2.congr fun s hs => ?_
    rw [uIoc_of_le zero_le_one] at hs
    exact (hf μ s hs.1).symm
  set ψ : ℝ → ℂ := fun s => -(z^(ν+1)*(z/2)^(ν+1)*struveHCore ν ((s:ℂ)*z)) + z^(2*ν+2)/D
  have hφ : ∀ s : ℝ, 0 ≤ s → G ((s:ℂ)*z) = (s:ℂ)^(2*ν+2) * ψ s := by
    intro s hs
    rcases hs.eq_or_lt with h0 | hpos
    · subst h0
      simp only [G, ψ, ofReal_zero, zero_mul, zero_cpow hν1, zero_cpow hν2]
      ring
    · simp only [G, ψ]
      rw [struveH, show (s:ℂ)*z/2 = (s:ℂ)*(z/2) by ring, AAR.Confluent.ofReal_mul_cpow' hpos hz0,
        AAR.Confluent.ofReal_mul_cpow' hpos (div_ne_zero hz0 two_ne_zero),
        AAR.Confluent.ofReal_mul_cpow' hpos hz0]
      have : (s:ℂ)^(2*ν+2) = (s:ℂ)^(ν+1) * (s:ℂ)^(ν+1) := by
        rw [← cpow_add _ _ (ofReal_ne_zero.2 hpos.ne')]; ring_nf
      rw [this]; ring
  have hcontφ : ContinuousOn (fun s : ℝ => G ((s:ℂ)*z)) (Icc 0 1) := by
    have hψ : Continuous ψ :=
      (continuous_const.mul ((hcore ν).comp (by fun_prop))).neg.add continuous_const
    have : ContinuousOn (fun s : ℝ => (s:ℂ)^(2*ν+2) * ψ s) (Icc 0 1) := fun s _ =>
      ((continuousAt_ofReal_cpow_const s _ (Or.inl (by simp; linarith))).mul
        hψ.continuousAt).continuousWithinAt
    exact this.congr fun s hs => hφ s hs.1
  have hderiv : ∀ s ∈ Ioo (0:ℝ) 1, HasDerivAt (fun s : ℝ => G ((s:ℂ)*z))
      (z * (((s:ℂ)*z)^(ν+1)*struveH (ν+1) ((s:ℂ)*z) -
        (2*ν+1)*(((s:ℂ)*z)^ν*struveH ν ((s:ℂ)*z)))) s := by
    intro s hs
    have h1 := hasDerivAt_struveHPrimitive_aux hν1 (ofReal_mul_mem_slitPlane hs.1 hz)
    have h2 : HasDerivAt (fun s : ℝ => (s:ℂ)*z) z s :=
      ((hasDerivAt_id s).ofReal_comp.mul_const z).congr_deriv (by simp)
    refine (h1.comp s h2).congr_deriv ?_
    ring
  have hII := ((hint (ν+1) (by simp; linarith)).sub ((hint ν hν).const_mul (2*ν+1))).const_mul z
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hcontφ hderiv hII
  have hP : ∀ μ, struveHPrimitive μ z =
      z * ∫ s : ℝ in 0..1, ((s:ℂ)*z)^μ*struveH μ ((s:ℂ)*z) := by
    intro μ; simp [struveHPrimitive, primitive, segmentIntegral]
  have hG0 : G (((0:ℝ):ℂ)*z) = 0 := by
    rw [hφ 0 le_rfl, ofReal_zero, zero_cpow hν2, zero_mul]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub (hint (ν+1)
    (by simp; linarith)) ((hint ν hν).const_mul (2*ν+1)), intervalIntegral.integral_const_mul,
    hG0, ofReal_one, one_mul] at hFTC
  rw [hP, hP]
  have hexp : exp ((ν+1)*(2*log z-log 2)) = z^(2*ν+2)/2^(ν+1) := by
    rw [cpow_def_of_ne_zero hz0, cpow_def_of_ne_zero two_ne_zero, ← Complex.exp_sub]; ring_nf
  rw [hexp]
  simp only [G, hD] at hFTC
  have hsplit : z^(2*ν+2)/(2^(ν+1)*(ν+1)*Real.sqrt π*Gamma (ν+3/2)) =
      z^(2*ν+2)/2^(ν+1)/((ν+1)*Real.sqrt π*Gamma (ν+3/2)) := by
    rw [div_div, ← mul_assoc, ← mul_assoc]
  rw [hsplit] at hFTC
  linear_combination hFTC

/-- `sin²` maps `(0, π/2)` onto `(0, 1)`. -/
theorem sin_sq_image_Ioo : (fun θ : ℝ => Real.sin θ^2) '' Ioo 0 (π/2) = Ioo 0 1 := by
  ext x; constructor
  · rintro ⟨θ, ⟨h0, h1⟩, rfl⟩
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 (by linarith [Real.pi_pos])
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith, h1⟩
    have := Real.sin_sq_add_cos_sq θ
    exact ⟨by positivity, by nlinarith⟩
  · rintro ⟨h0, h1⟩
    refine ⟨Real.arcsin (Real.sqrt x), ⟨Real.arcsin_pos.2 (Real.sqrt_pos.2 h0), ?_⟩, ?_⟩
    · rw [Real.arcsin_lt_pi_div_two, Real.sqrt_lt' one_pos]; simpa using h1
    · show Real.sin (Real.arcsin (Real.sqrt x))^2 = x
      rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg x]) (by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt h1.le), Real.sq_sqrt h0.le]

/-- `sin²` is injective on `(0, π/2)`. -/
theorem sin_sq_injOn : InjOn (fun θ : ℝ => Real.sin θ^2) (Ioo 0 (π/2)) := by
  intro a ha b hb hab
  have hsa : 0 < Real.sin a := Real.sin_pos_of_pos_of_lt_pi ha.1 (by linarith [ha.2, Real.pi_pos])
  have hsb : 0 < Real.sin b := Real.sin_pos_of_pos_of_lt_pi hb.1 (by linarith [hb.2, Real.pi_pos])
  have : Real.sin a = Real.sin b := by
    simp only at hab; nlinarith [sq_nonneg (Real.sin a - Real.sin b)]
  exact Real.injOn_sin ⟨by linarith [ha.1, Real.pi_pos], ha.2.le⟩
    ⟨by linarith [hb.1, Real.pi_pos], hb.2.le⟩ this

/-- Derivative of `sin²`. -/
theorem hasDerivWithinAt_sin_sq (θ : ℝ) :
    HasDerivWithinAt (fun θ : ℝ => Real.sin θ^2) (2*Real.sin θ*Real.cos θ) (Ioo 0 (π/2)) θ := by
  have := ((Real.hasDerivAt_sin θ).pow 2).hasDerivWithinAt (s := Ioo 0 (π/2))
  convert this using 1; push_cast; ring

/-- The weight `sin^(2a-1) θ cos^(2b-1) θ` after the substitution `x = sin² θ`. -/
theorem trigBeta_integrand_eq {a b : ℂ} {θ : ℝ} (hθ : θ ∈ Ioo 0 (π/2)) :
    |2*Real.sin θ*Real.cos θ| • (((Real.sin θ^2:ℝ):ℂ)^(a-1)*(1-((Real.sin θ^2:ℝ):ℂ))^(b-1)) =
      2*((Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) := by
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have h1 : 1-((Real.sin θ^2:ℝ):ℂ) = ((Real.cos θ^2:ℝ):ℂ) := by
    have := Real.sin_sq_add_cos_sq θ
    rw [show Real.cos θ^2 = 1 - Real.sin θ^2 by linarith]; push_cast; ring
  rw [abs_of_pos (by positivity), h1, Complex.real_smul]
  have e1 := ofReal_mul_sq_cpow' hs (a-1)
  have e2 := ofReal_mul_sq_cpow' hc (b-1)
  rw [show 2*(a-1)+1 = 2*a-1 by ring] at e1
  rw [show 2*(b-1)+1 = 2*b-1 by ring] at e2
  rw [← e1, ← e2]; push_cast; ring

/-- **Trigonometric Beta integral**, with integrability. -/
theorem trigBeta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntervalIntegrable (fun θ : ℝ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) volume 0 (π/2) ∧
    (∫ θ : ℝ in 0..π/2, (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)) =
      Gamma a * Gamma b / (2*Gamma (a+b)) := by
  set g : ℝ → ℂ := fun x => (x:ℂ)^(a-1)*(1-(x:ℂ))^(b-1)
  have hconv := Complex.betaIntegral_convergent ha hb
  have hg : IntegrableOn g (Ioo 0 1) := by
    have := hconv.1
    exact (integrableOn_Ioc_iff_integrableOn_Ioo'
      (by simp)).1 this
  set W : ℝ → ℂ := fun θ => (Real.sin θ:ℂ)^(2*a-1)*(Real.cos θ:ℂ)^(2*b-1)
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  have heq := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
    (fun θ _ => hasDerivWithinAt_sin_sq θ) sin_sq_injOn g
  rw [sin_sq_image_Ioo] at hiff heq
  have hcongr : EqOn (fun θ => |2*Real.sin θ*Real.cos θ| • g (Real.sin θ^2))
      (fun θ => 2 * W θ) (Ioo 0 (π/2)) := fun θ hθ => by
    simp only [g, W]; exact trigBeta_integrand_eq hθ
  have hW2 : IntegrableOn (fun θ => 2 * W θ) (Ioo 0 (π/2)) :=
    (hiff.1 hg).congr_fun hcongr measurableSet_Ioo
  have hW : IntegrableOn W (Ioo 0 (π/2)) := by
    exact IntegrableOn.congr_fun (hW2.const_mul (1/2:ℂ)) (fun θ _ => by ring) measurableSet_Ioo
  have hWi : IntervalIntegrable W volume 0 (π/2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by positivity)]
    exact hW
  refine ⟨hWi, ?_⟩
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha hb
  have hG : Gamma (a+b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [hB, mul_comm (2:ℂ), ← div_div, mul_div_cancel_left₀ _ hG, Complex.betaIntegral,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  change _ = (∫ t in Ioo 0 1, g t)/2
  rw [heq, setIntegral_congr_fun measurableSet_Ioo hcongr, integral_const_mul,
    intervalIntegral.integral_of_le (by positivity), integral_Ioc_eq_integral_Ioo]
  ring

/-- struveH sonine. -/
@[dlmf 11.7.E7]
theorem struveH_sonine {ν : ℂ} (hν0 : -3/2 < ν.re) (hν1 : ν.re < 1/2) {z : ℂ} (hz : z ∈ slitPlane) :
    (∫ θ : ℝ in 0..π/2, struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) = 2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)*(1-cos z) := by
  have hz0 := slitPlane_ne_zero hz
  have hz2 : z/2 ≠ 0 := div_ne_zero hz0 two_ne_zero
  have hb : 0 < (1/2-ν).re := by simp; linarith
  have ha : ∀ k : ℕ, 0 < ((k:ℂ)+ν+3/2).re := fun k => by
    simp; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  set W : ℕ → ℝ → ℂ := fun k θ =>
    (Real.sin θ:ℂ)^(2*((k:ℂ)+ν+3/2)-1)*(Real.cos θ:ℂ)^(2*(1/2-ν)-1)
  have hTB := fun k => trigBeta (ha k) hb
  set c : ℕ → ℂ := fun k => (z/2)^(ν+1)*((-1)^k*(z/2)^(2*k)*struveCoeff ν k)
  have hc : Summable fun k => ‖c k‖ := by
    rw [summable_norm_iff]
    exact ((hasSum_struveHCore ν z).mul_left _).summable
  have hWk : ∀ k : ℕ, ∀ θ ∈ Ioo (0:ℝ) (π/2), W k θ = (Real.sin θ:ℂ)^(2*k) * W 0 θ := by
    intro k θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    simp only [W]
    rw [← cpow_natCast, ← mul_assoc, ← cpow_add _ _ hs0]
    push_cast; ring_nf
  have hpt : ∀ θ ∈ Ioo (0:ℝ) (π/2), HasSum (fun k => c k * W k θ)
      (struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν)) := by
    intro θ hθ
    have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hs0 : (Real.sin θ:ℂ) ≠ 0 := ofReal_ne_zero.2 hs.ne'
    have hzs : z*Real.sin θ/2 = (Real.sin θ:ℂ)*(z/2) := by ring
    rw [struveH, hzs, AAR.Confluent.ofReal_mul_cpow' hs hz2]
    have hser := (hasSum_struveHCore ν ((Real.sin θ:ℂ)*z)).mul_left
      ((Real.sin θ:ℂ)^(ν+1)*(z/2)^(ν+1)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    rw [show (Real.sin θ:ℂ)*z = z*Real.sin θ by ring] at hser
    convert hser using 1
    · funext k
      simp only [c, W]
      rw [show 2*((k:ℂ)+ν+3/2)-1 = (2*k:ℕ) + ((ν+1)+(ν+1)) by push_cast; ring,
        cpow_add _ _ hs0, cpow_add _ _ hs0, cpow_natCast,
        show 2*(1/2-ν)-1 = -(2*ν) by ring, cpow_neg]
      rw [show z*(Real.sin θ:ℂ)/2 = (Real.sin θ:ℂ)*(z/2) by ring, mul_pow]
      field_simp
    · ring
  have hne : ∀ᵐ t ∂(volume:Measure ℝ), t ≠ π/2 := by
    rw [ae_iff]; simp
  have hIoo : ∀ᵐ t ∂(volume:Measure ℝ), t ∈ uIoc (0:ℝ) (π/2) → t ∈ Ioo (0:ℝ) (π/2) := by
    filter_upwards [hne] with t ht h
    rw [uIoc_of_le (by positivity)] at h
    exact ⟨h.1, lt_of_le_of_ne h.2 ht⟩
  have hS := intervalIntegral.hasSum_integral_of_dominated_convergence
    (F := fun k θ => c k * W k θ) (μ := volume) (a := 0) (b := π/2)
    (f := fun θ => struveH ν (z*Real.sin θ)*(Real.sin θ:ℂ)^(ν+1)/(Real.cos θ:ℂ)^(2*ν))
    (fun k θ => ‖c k‖ * ‖W 0 θ‖)
    (fun k => (((hTB k).1.const_mul (c k)).def').aestronglyMeasurable)
    (fun k => by
      filter_upwards [hIoo] with θ hθ h
      have h' := hθ h
      show ‖c k * W k θ‖ ≤ ‖c k‖ * ‖W 0 θ‖
      rw [norm_mul (c k), hWk k θ h', norm_mul ((Real.sin θ:ℂ)^(2*k)), norm_pow,
        Complex.norm_real]
      have h1 : ‖Real.sin θ‖^(2*k) ≤ 1 := pow_le_one₀ (norm_nonneg _)
        (by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one θ)
      have := mul_le_mul_of_nonneg_right h1 (norm_nonneg (W 0 θ))
      rw [one_mul] at this
      exact mul_le_mul_of_nonneg_left this (norm_nonneg _))
    (Eventually.of_forall fun θ _ => hc.mul_right _)
    (by simp_rw [tsum_mul_right]; exact (hTB 0).1.norm.const_mul _)
    (by filter_upwards [hIoo] with θ hθ h; exact hpt θ (hθ h))
  simp only [intervalIntegral.integral_const_mul] at hS
  refine hS.unique ?_
  -- the cosine series
  have hcos := Complex.hasSum_cos z
  rw [← hasSum_nat_add_iff' 1] at hcos
  simp only [Finset.range_one, Finset.sum_singleton, mul_zero, pow_zero, Nat.factorial_zero,
    Nat.cast_one, div_one] at hcos
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 : (2:ℂ)^(-ν) * 2^(ν+1) = 2 := by
    rw [← cpow_add _ _ two_ne_zero, show -ν+(ν+1) = 1 by ring, cpow_one]
  have hzp : z^(ν-1) * z^2 = 2^(ν+1) * (z/2)^(ν+1) := by
    rw [← cpow_natCast, ← cpow_add _ _ hz0, show ν-1+((2:ℕ):ℂ) = ν+1 by push_cast; ring]
    conv_lhs => rw [show z = ((2:ℝ):ℂ)*(z/2) by push_cast; ring]
    rw [AAR.Confluent.ofReal_mul_cpow' (by norm_num : (0:ℝ) < 2) hz2]
    push_cast; ring
  have hTQ : (2:ℂ)^(-ν) * z^(ν-1) * z^2 = 2 * (z/2)^(ν+1) := by
    rw [mul_assoc, hzp, ← mul_assoc, h2]
  convert hcos.neg.mul_left (2^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1)) using 1
  · funext k
    simp only [W]
    rw [(hTB k).2]
    rw [show (2:ℂ)^(-ν)/Real.sqrt π*Gamma (1/2-ν)*z^(ν-1) *
        -((-1)^(k+1)*z^(2*(k+1))/(((2*(k+1))! : ℕ) : ℂ)) =
        ((2:ℂ)^(-ν) * z^(ν-1) * z^2) * (Gamma (1/2-ν)*(-1)^k*z^(2*k)/
          (Real.sqrt π*(((2*(k+1))! : ℕ) : ℂ))) by ring, hTQ]
    have hf : (((2*(k+1))! : ℕ):ℂ) = oddProduct k * 2^(k+1) * (((k+1)! : ℕ) : ℂ) := by
      rw [show 2*(k+1) = (2*k+1)+1 by ring, Nat.factorial_succ, Nat.cast_mul,
        factorial_odd_eq_oddProduct, Nat.factorial_succ]
      push_cast; ring
    have ho : oddProduct k ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro j _
      have : (0:ℝ) < 2*j+1 := by positivity
      exact_mod_cast this.ne'
    have hG : Gamma ((k:ℂ)+ν+3/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (ha k)
    have hk : (((k+1)! : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    rw [hf, show (k:ℂ)+ν+3/2+(1/2-ν) = ((k+1:ℕ):ℂ)+1 by push_cast; ring,
      Complex.Gamma_nat_eq_factorial]
    simp only [c, struveCoeff, Gamma_oddProduct]
    rw [show (k:ℂ)+ν+3/2 = (k:ℂ)+ν+3/2 from rfl, div_pow z 2 (2*k)]
    generalize (z/2)^(ν+1) = P
    generalize Gamma ((k:ℂ)+ν+3/2) = G at hG ⊢
    field_simp
    ring
  · ring

/-- struveH integral zero div. -/
@[dlmf 11.7.E8]
theorem struveH_integral_zero_div  :
    HasIntegralAtTop (fun t : ℝ => struveH 0 t/t) 0 (π/2) := by
  sorry

/-- struveH integral one div sq. -/
@[dlmf 11.7.E8]
theorem struveH_integral_one_div_sq  :
    HasIntegralAtTop (fun t : ℝ => struveH 1 t/t^2) 0 (π/4) := by
  sorry

/-- struveH integral plain. -/
@[dlmf 11.7.E9]
theorem struveH_integral_plain {ν : ℂ} (h0 : -2 < ν.re) (h1 : ν.re < 0) :
    HasIntegralAtTop (fun t : ℝ => struveH ν t) 0 (-cos (π*ν/2)/sin (π*ν/2)) := by
  sorry

/-- struveH integral mellin zero. -/
@[dlmf 11.7.E10]
theorem struveH_integral_mellin_zero {ν : ℂ} (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-ν-1)*struveH ν t) 0 (π/(2^(ν+1)*Gamma (ν+1))) := by
  sorry

/-- struveH integral mellin. -/
@[dlmf 11.7.E11]
theorem struveH_integral_mellin {μ ν : ℂ} (hμ : |μ.re| < 1) (hν : μ.re-3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(μ-ν-1)*struveH ν t) 0 (if μ=0 then π/(2^(ν+1)*Gamma (ν+1)) else Gamma (μ/2)*2^(μ-ν-1)*sin (π*μ/2)/(cos (π*μ/2)*Gamma (ν-μ/2+1))) := by
  sorry

/-- struveH integral product. DLMF 11.7.12 states only `Re(μ+ν) > 0`; the integral then
diverges, e.g. at `μ = 3`, `ν = -2` the integrand grows like `t^(1/2) cos(...)`. The cross terms
`t^(-ν-3/2)` and `t^(-μ-3/2)` of the large-`t` expansion require `Re μ, Re ν > -3/2`
(hypotheses added 2026-10-20). -/
@[dlmf 11.7.E12]
theorem struveH_integral_product {μ ν : ℂ} (h : 0 < (μ+ν).re) (hμ : -3/2 < μ.re)
    (hν : -3/2 < ν.re) :
    HasIntegralAtTop (fun t : ℝ => (t:ℂ)^(-μ-ν)*struveH μ t*struveH ν t) 0 (Real.sqrt π*Gamma (μ+ν)/(2^(μ+ν)*Gamma (μ+ν+1/2)*Gamma (μ+1/2)*Gamma (ν+1/2))) := by
  sorry

/-- Fubini for the Laplace transform of a Poisson-weighted integral. -/
theorem laplace_poissonWeight {a : ℂ} {β : ℝ} (hβ : β < a.re) {k : ℝ → ℝ → ℂ}
    (hk : Continuous (Function.uncurry k))
    (hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖k t s‖ ≤ Real.exp (β*t)) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s)
      (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * k t s) =
      ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ∫ t : ℝ in Ioi 0, exp (-a*t) * k t s := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntegrableOn w (Ioc 0 1) := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
    convert this using 3; norm_num
  set F : ℝ × ℝ → ℂ := fun p => exp (-a*p.1) * (w p.2 * k p.1 p.2)
  have hwm : Measurable w := by
    simp only [w]; fun_prop
  have hFm : AEStronglyMeasurable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    apply Measurable.aestronglyMeasurable
    simp only [F]
    have hk' : Measurable (fun p : ℝ × ℝ => k p.1 p.2) := hk.measurable
    have : Measurable (fun p : ℝ × ℝ => w p.2) := hwm.comp measurable_snd
    fun_prop
  have hG : Integrable (fun p : ℝ × ℝ => Real.exp ((β - a.re)*p.1) * ‖w p.2‖)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) :=
    (integrableOn_exp_mul_Ioi (by linarith) 0).mul_prod hw.norm
  have hF : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    refine hG.mono' hFm ?_
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioc)] with p hp
    obtain ⟨ht, hs⟩ := hp
    simp only [F, norm_mul, Complex.norm_exp]
    have h1 := hkb p.1 p.2 ht hs
    have : (-a*(p.1:ℂ)).re = -a.re*p.1 := by simp
    rw [this]
    calc Real.exp (-a.re*p.1) * (‖w p.2‖ * ‖k p.1 p.2‖)
        ≤ Real.exp (-a.re*p.1) * (‖w p.2‖ * Real.exp (β*p.1)) := by gcongr
      _ = Real.exp ((β - a.re)*p.1) * ‖w p.2‖ := by
        rw [show (β - a.re)*p.1 = -a.re*p.1 + β*p.1 by ring, Real.exp_add]; ring
  have hswap := integral_integral_swap (f := fun t s => F (t, s)) hF
  have hint := hF.integral_prod_left
  constructor
  · refine (hint.congr (Eventually.of_forall fun t => ?_))
    simp only [F]
    rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
  · rw [intervalIntegral.integral_of_le zero_le_one]
    convert hswap using 1
    · refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      simp only [F]
      rw [integral_const_mul, intervalIntegral.integral_of_le zero_le_one]
    · refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only [F]
      rw [← integral_const_mul]
      congr 1; funext t; ring

/-- `∫₀^∞ e^{-at} e^{ct} dt = 1/(a-c)` for `Re c < Re a`. -/
theorem integral_exp_neg_mul_exp_Ioi {a c : ℂ} (h : c.re < a.re) :
    IntegrableOn (fun t : ℝ => exp (-a*t) * exp (c*t)) (Ioi 0) ∧
    (∫ t : ℝ in Ioi 0, exp (-a*t) * exp (c*t)) = 1/(a-c) := by
  have he : (fun t : ℝ => exp (-a*t) * exp (c*t)) = fun t : ℝ => exp ((c-a)*t) := by
    funext t; rw [← Complex.exp_add]; ring_nf
  have hre : (c-a).re < 0 := by simp; linarith
  have hne : a - c ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  rw [he]
  refine ⟨integrableOn_exp_mul_complex_Ioi hre 0, ?_⟩
  rw [integral_exp_mul_complex_Ioi hre 0]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  have hne' : c - a ≠ 0 := fun h0 => hne (by linear_combination -h0)
  field_simp
  ring

/-- Laplace transform of `sin(st)`. -/
theorem laplace_sin_mul {a : ℂ} (ha : 0 < a.re) (s : ℝ) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) = s/(a^2+s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := I*s) (by simpa using ha)
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -I*s) (by simpa using ha)
  have hsin : ∀ t : ℝ, exp (-a*t) * sin ((t:ℂ)*s) =
      (exp (-a*t) * exp (I*s*t) - exp (-a*t) * exp (-I*s*t)) / (2*I) := by
    intro t
    have h2I : (2:ℂ)*I ≠ 0 := by simp
    rw [eq_div_iff h2I, Complex.sin]
    ring_nf; rw [I_sq]; ring_nf
  simp_rw [hsin]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hm : a - -I*s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith
  have hprod : (a - I*s)*(a - -I*s) = a^2+s^2 := by ring_nf; rw [I_sq]; ring
  have key : 1/(a - I*s) - 1/(a - -I*s) = (2*I) * (s/(a^2+s^2)) := by
    rw [div_sub_div _ _ hp hm, hprod]; ring
  rw [key, mul_div_cancel_left₀ _ (by simp : (2:ℂ)*I ≠ 0)]

/-- Laplace transform of `sinh(st)`. -/
theorem laplace_sinh_mul {a : ℂ} (ha : 1 < a.re) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) :
    (∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) = s/(a^2-s^2) := by
  have h1 := integral_exp_neg_mul_exp_Ioi (a := a) (c := (s:ℂ)) (by simp; linarith [hs.2])
  have h2 := integral_exp_neg_mul_exp_Ioi (a := a) (c := -(s:ℂ)) (by simp; linarith [hs.1])
  have hsinh : ∀ t : ℝ, exp (-a*t) * sinh ((t:ℂ)*s) =
      (exp (-a*t) * exp (s*t) - exp (-a*t) * exp (-s*t)) / 2 := by
    intro t
    rw [Complex.sinh]
    ring_nf
  simp_rw [hsinh]
  rw [integral_div, integral_sub h1.1 h2.1, h1.2, h2.2]
  have hp : a - s ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.2]
  have hm : a - -(s:ℂ) ≠ 0 := fun h0 => by
    have := congrArg Complex.re h0; simp at this; linarith [hs.1]
  have key : 1/(a - s) - 1/(a - -(s:ℂ)) = 2 * (s/(a^2-s^2)) := by
    rw [div_sub_div _ _ hp hm, show (a - s)*(a - -(s:ℂ)) = a^2-s^2 by ring]; ring
  rw [key, mul_div_cancel_left₀ _ (by norm_num : (2:ℂ) ≠ 0)]

/-- Principal square roots of slit-plane numbers lie in the open right half-plane. -/
theorem re_cpow_half_pos {x : ℂ} (hx : x ∈ slitPlane) : 0 < (x^(1/2:ℂ)).re := by
  rw [show (1/2:ℂ) = ((1/2:ℝ):ℂ) by push_cast; ring, cpow_ofReal_re]
  have hx0 := slitPlane_ne_zero hx
  have harg := (mem_slitPlane_iff_arg.1 hx).1
  have h1 : -π < arg x := neg_pi_lt_arg x
  have h2 : arg x < π := lt_of_le_of_ne (arg_le_pi x) harg
  apply mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hx0) _)
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [Real.pi_pos]

theorem cpow_half_sq (x : ℂ) : (x^(1/2:ℂ))^2 = x := by
  have := cpow_nat_inv_pow x (n := 2) two_ne_zero
  rwa [show ((2:ℕ):ℂ)⁻¹ = 1/2 by norm_num] at this

theorem eq_of_sq_eq_of_re_pos {r a : ℂ} (hr : 0 < r.re) (ha : 0 < a.re) (h : r^2 = a^2) :
    r = a := by
  have h0 : (r - a)*(r + a) = 0 := by linear_combination h
  rcases mul_eq_zero.1 h0 with h1 | h1
  · linear_combination h1
  · exfalso; have := congrArg Complex.re h1; simp at this; linarith

theorem div_mem_slitPlane_of_re_pos {p r : ℂ} (hp : 0 < p.re) (hr : 0 < r.re) :
    p / r ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hr0 : r ≠ 0 := fun h => by rw [h] at hr; simp at hr
  have hpe : p = (p/r)*r := by field_simp
  have : p.re = (p/r).re * r.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

theorem sq_add_mem_slitPlane {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 + u).re = a.re^2 - a.im^2 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero ha.ne') him

/-- `∫₀¹ du/(b²-u²) = log((1+b)/a)/b` with `b = (1+a²)^{1/2}`, `Re a > 0`. -/
theorem integral_inv_one_add_sq_sub_sq {a : ℂ} (ha : 0 < a.re) :
    (∫ u : ℝ in 0..1, 1/((1+a^2) - (u:ℂ)^2)) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  set b : ℂ := (1+a^2)^(1/2:ℂ) with hbdef
  have hslit : ∀ u : ℝ, u ∈ uIcc (0:ℝ) 1 → a^2 + ((1-u^2:ℝ):ℂ) ∈ slitPlane := by
    intro u hu
    rw [uIcc_of_le zero_le_one] at hu
    exact sq_add_mem_slitPlane ha (by nlinarith [hu.1, hu.2])
  have hb1 : a^2 + ((1-(0:ℝ)^2:ℝ):ℂ) = 1+a^2 := by push_cast; ring
  have hbre : 0 < b.re := by
    have := re_cpow_half_pos (hslit 0 (by simp))
    rwa [hb1] at this
  have hb2 : b^2 = 1+a^2 := cpow_half_sq _
  set r : ℝ → ℂ := fun u => (a^2 + ((1-u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u ∈ uIcc (0:ℝ) 1, 0 < (r u).re := fun u hu => re_cpow_half_pos (hslit u hu)
  have hr2 : ∀ u : ℝ, (r u)^2 = b^2 - (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hb2]; push_cast; ring
  have hr0 : r 0 = b := by simp only [r]; rw [hb1]
  have hr1 : r 1 = a := by
    apply eq_of_sq_eq_of_re_pos (hrre 1 (by simp)) ha
    rw [hr2, hb2]; push_cast; ring
  set Φ : ℝ → ℂ := fun u => log ((b+u)/r u) / b
  have hbne : b ≠ 0 := fun h => by rw [h] at hbre; simp at hbre
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Φ (1/((1+a^2) - (u:ℂ)^2)) u := by
    intro u hu
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    have hpre : 0 < (b + u).re := by
      rw [uIcc_of_le zero_le_one] at hu; simp; linarith [hu.1]
    have hpne : b + (u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 + ((1-u^2:ℝ):ℂ)) (-(2*(u:ℂ))) u := by
      have := ((hasDerivAt_pow 2 u).const_sub 1).ofReal_comp.const_add (a^2)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r (-(u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u hu)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 + ((1-u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u hu)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp
      rw [this]; field_simp
    have hp : HasDerivAt (fun u : ℝ => b + (u:ℂ)) 1 u := by
      simpa using (hasDerivAt_id (u:ℝ)).ofReal_comp.const_add b
    have hdiv := hp.div hr hrne
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u hu))
    have := hlog.div_const b
    convert this using 1
    have hr2u := hr2 u
    rw [← hb2]
    have hden : b^2 - (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 hrne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (b*(u:ℂ) + (u:ℂ)^2) * hr2u
  have hcont : ContinuousOn (fun u : ℝ => 1/((1+a^2) - (u:ℂ)^2)) (uIcc 0 1) := by
    refine continuousOn_const.div (by fun_prop) fun u hu => ?_
    have hrne : r u ≠ 0 := fun h => by have := hrre u hu; rw [h] at this; simp at this
    rw [← hb2, ← hr2]; exact pow_ne_zero 2 hrne
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Φ, hr0, hr1]
  push_cast
  rw [add_zero, div_self hbne, log_one, zero_div, sub_zero, add_comm]

theorem one_add_sq_sub_sq_ne_zero {a : ℂ} (ha : 0 < a.re) {u : ℝ} (hu : u ∈ uIcc (0:ℝ) 1) :
    (1+a^2) - (u:ℂ)^2 ≠ 0 := by
  rw [uIcc_of_le zero_le_one] at hu
  have := slitPlane_ne_zero (sq_add_mem_slitPlane ha (u := 1-u^2) (by nlinarith [hu.1, hu.2]))
  convert this using 1; push_cast; ring

/-- `∫₀¹ (1-s²)^{-1/2} s/(a²+s²) ds = log((1+b)/a)/b`. -/
theorem integral_poissonWeight_mul_div_sq_add {a : ℂ} (ha : 0 < a.re) :
    (∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * ((s:ℂ)/(a^2+(s:ℂ)^2))) =
      log ((1+(1+a^2)^(1/2:ℂ))/a) / (1+a^2)^(1/2:ℂ) := by
  have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2+(s:ℂ)^2))
  rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
  rw [h, ← integral_inv_one_add_sq_sub_sq ha]
  simp only [mul_zero, cpow_zero, mul_one]
  set g : ℝ → ℂ := fun u => 1/((1+a^2) - (u:ℂ)^2)
  have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
    (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
    (by
      refine ContinuousOn.mono (s := uIcc 0 1) ?_ ?_
      · exact continuousOn_const.div (by fun_prop) fun u hu => one_add_sq_sub_sq_ne_zero ha hu
      · rintro _ ⟨x, hx, rfl⟩
        rw [uIcc_of_le (by positivity)] at hx
        rw [uIcc_of_le zero_le_one]
        exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, Real.pi_pos]),
          Real.sin_le_one x⟩)
  rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun θ hθ => ?_
  simp only [g, Function.comp, real_smul]
  have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
    rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
  rw [hc]; ring

/-- `H₀` is bounded on the positive real axis. -/
theorem exists_bound_struveH_zero : ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveH 0 t‖ ≤ C := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  refine ⟨2/π * ∫ s : ℝ in 0..1, ‖w s‖, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg zero_le_one fun _ _ =>
      norm_nonneg _)
  rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 hpos.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp, mul_one, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  refine intervalIntegral.integral_mono_on zero_le_one ?_ hw.norm fun s _ => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have : ‖sin ((t:ℂ)*s)‖ ≤ 1 := by
      rw [← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
    calc ‖w s‖ * ‖sin ((t:ℂ)*s)‖ ≤ ‖w s‖ * 1 := by gcongr
      _ = ‖w s‖ := mul_one _

theorem sq_sub_one_add_mem_slitPlane {a : ℂ} (ha : 1 < a.re) {u : ℝ} (hu : 0 ≤ u) :
    a^2 - 1 + u ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have : (a^2 - 1 + u).re = a.re^2 - a.im^2 - 1 + u := by simp [sq, mul_re]
    rw [this, him]; nlinarith
  · right
    have : (a^2 - 1 + u).im = 2*a.re*a.im := by simp [sq, mul_im]; ring
    rw [this]
    exact mul_ne_zero (mul_ne_zero two_ne_zero (by linarith)) him

theorem one_sub_inv_sq_mem_slitPlane {a : ℂ} (ha : 1 < a.re) : 1 - 1/a^2 ∈ slitPlane := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  rw [mem_slitPlane_iff]
  by_cases him : a.im = 0
  · left
    have hae : a = (a.re:ℂ) := Complex.ext (by simp) (by simp [him])
    rw [hae, ← ofReal_pow, ← ofReal_one, ← ofReal_div, ← ofReal_sub, ofReal_re]
    have h1 : 1 < a.re^2 := by nlinarith
    have : 1/a.re^2 < 1 := by rw [div_lt_one (by positivity)]; exact h1
    linarith
  · right
    have h2 : (a^2).im ≠ 0 := by
      rw [sq, mul_im]; intro h; apply him; nlinarith [h]
    rw [sub_im, one_im, one_div, inv_im, zero_sub, neg_ne_zero, neg_div, neg_ne_zero]
    exact div_ne_zero h2 (normSq_pos.2 (pow_ne_zero 2 ha0)).ne'

/-- `√(a²-1) = a √(1-a⁻²)` for `Re a > 1`. -/
theorem cpow_half_sq_sub_one {a : ℂ} (ha : 1 < a.re) :
    (a^2-1)^(1/2:ℂ) = a * (1-1/a^2)^(1/2:ℂ) := by
  set S : Set ℂ := {z | 1 < z.re}
  have hS : IsPreconnected S := (convex_halfSpace_re_gt 1).isPreconnected
  have hslit1 : ∀ z ∈ S, z^2 - 1 ∈ slitPlane := fun z hz => by
    simpa using sq_sub_one_add_mem_slitPlane (u := 0) hz le_rfl
  have hf : ContinuousOn (fun z : ℂ => (z^2-1)^(1/2:ℂ)) S := fun z hz =>
    ((by fun_prop : ContinuousAt (fun z : ℂ => z^2-1) z).cpow continuousAt_const
      (hslit1 z hz)).continuousWithinAt
  have hz0 : ∀ z ∈ S, z ≠ 0 := fun z hz h => by
    simp only [S, mem_ofPred_eq] at hz; rw [h] at hz; simp at hz; linarith
  have hg : ContinuousOn (fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ)) S := fun z hz => by
    have h1 : ContinuousAt (fun z : ℂ => 1 - 1/z^2) z :=
      continuousAt_const.sub (continuousAt_const.div (by fun_prop) (pow_ne_zero 2 (hz0 z hz)))
    exact (continuousAt_id.mul (h1.cpow continuousAt_const
      (one_sub_inv_sq_mem_slitPlane hz))).continuousWithinAt
  have hsq : EqOn ((fun z : ℂ => (z^2-1)^(1/2:ℂ))^2) ((fun z : ℂ => z * (1-1/z^2)^(1/2:ℂ))^2) S := by
    intro z hz
    simp only [Pi.pow_apply, mul_pow, cpow_half_sq]
    field_simp [hz0 z hz]
  have hne : ∀ {z : ℂ}, z ∈ S → z * (1-1/z^2)^(1/2:ℂ) ≠ 0 := by
    intro z hz
    refine mul_ne_zero (hz0 z hz) fun h => ?_
    have := re_cpow_half_pos (one_sub_inv_sq_mem_slitPlane hz)
    rw [h] at this; simp at this
  have h2 : (2:ℂ) ∈ S := by simp [S]
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg hsq hne with h | h
  · exact h ha
  · exfalso
    have h1 := h h2
    have hp1 := re_cpow_half_pos (hslit1 2 h2)
    have hp2 := re_cpow_half_pos (one_sub_inv_sq_mem_slitPlane (a := 2) (by simp))
    simp only [Pi.neg_apply] at h1
    rw [h1] at hp1
    simp only [neg_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero] at hp1
    linarith

/-- For `Re q > 0` and `Re p = Re q`, the quotient `p/q` lies in the slit plane. -/
theorem div_mem_slitPlane_of_re_eq {p q : ℂ} (hq : 0 < q.re) (h : p.re = q.re) :
    p / q ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra hc
  push Not at hc
  have hq0 : q ≠ 0 := fun h0 => by rw [h0] at hq; simp at hq
  have hpe : p = (p/q)*q := by field_simp
  have : p.re = (p/q).re * q.re := by
    conv_lhs => rw [hpe]
    simp [mul_re, hc.2]
  nlinarith [hc.1]

theorem sq_sub_one_add_sq_ne_zero {a : ℂ} (ha : 1 < a.re) (u : ℝ) :
    (a^2-1) + (u:ℂ)^2 ≠ 0 := by
  have := slitPlane_ne_zero (sq_sub_one_add_mem_slitPlane ha (u := u^2) (sq_nonneg u))
  convert this using 1; push_cast; ring

/-- Logarithmic form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_inv_sq_sub_one_add_sq_log {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      -I*log (I/a+(1-1/a^2)^(1/2:ℂ)) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
  have hslit : ∀ u : ℝ, a^2 - 1 + ((u^2:ℝ):ℂ) ∈ slitPlane :=
    fun u => sq_sub_one_add_mem_slitPlane ha (sq_nonneg u)
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (hslit 0)
    rwa [show a^2-1+(((0:ℝ)^2:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set r : ℝ → ℂ := fun u => (a^2 - 1 + ((u^2:ℝ):ℂ))^(1/2:ℂ) with hrdef
  have hrre : ∀ u, 0 < (r u).re := fun u => re_cpow_half_pos (hslit u)
  have hrne : ∀ u, r u ≠ 0 := fun u h => by have := hrre u; rw [h] at this; simp at this
  have hr2 : ∀ u : ℝ, (r u)^2 = c^2 + (u:ℂ)^2 := by
    intro u; simp only [r]; rw [cpow_half_sq, hc2]; push_cast; ring
  have hr0 : r 0 = c := by simp [r, c]
  have hr1 : r 1 = a := by
    have ha' : 0 < a.re := by linarith
    apply eq_of_sq_eq_of_re_pos (hrre 1) ha'
    rw [hr2, hc2]; push_cast; ring
  set Ψ : ℝ → ℂ := fun u => -I*log ((c+I*u)/r u) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Ψ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hpre : 0 < (c + I*u).re := by simp; exact hcre
    have hpne : c + I*(u:ℂ) ≠ 0 := fun h => by rw [h] at hpre; simp at hpre
    have hq : HasDerivAt (fun u : ℝ => a^2 - 1 + ((u^2:ℝ):ℂ)) (2*(u:ℂ)) u := by
      have := (hasDerivAt_pow 2 u).ofReal_comp.const_add (a^2-1)
      convert this using 1; push_cast; ring
    have hr : HasDerivAt r ((u:ℂ) / r u) u := by
      have := (hasStrictDerivAt_cpow_const (c := 1/2) (hslit u)).hasDerivAt.comp u hq
      refine this.congr_deriv ?_
      set Q : ℂ := a^2 - 1 + ((u^2:ℝ):ℂ) with hQdef
      have hQne : Q ≠ 0 := slitPlane_ne_zero (hslit u)
      have hru : r u = Q^(1/2:ℂ) := rfl
      have hQ : Q = (r u)^2 := (cpow_half_sq Q).symm
      have : Q^((1/2:ℂ)-1) = (r u)⁻¹ := by
        rw [cpow_sub _ _ hQne, cpow_one, ← hru]
        conv_lhs => rw [hQ]
        field_simp [hrne u]
      rw [this]; field_simp [hrne u]
    have hp : HasDerivAt (fun u : ℝ => c + I*(u:ℂ)) I u := by
      simpa using ((hasDerivAt_id (u:ℝ)).ofReal_comp.const_mul I).const_add c
    have hdiv := hp.div hr (hrne u)
    have hlog := hdiv.clog_real (div_mem_slitPlane_of_re_pos hpre (hrre u))
    have := (hlog.const_mul (-I)).div_const c
    convert this using 1
    have hr2u := hr2 u
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [← hr2u]; exact pow_ne_zero 2 (hrne u)
    have hrn := hrne u
    have hpne' : c + (u:ℂ)*I ≠ 0 := by rw [mul_comm]; exact hpne
    simp only [Pi.div_apply]
    field_simp
    linear_combination (c*(u:ℂ)*I - (u:ℂ)^2) * hr2u +
      (c^2*(r u)^2 - c^2*(u:ℂ)^2 + (r u)^2*(u:ℂ)^2 - (u:ℂ)^4) * I_sq
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Ψ, hr0, hr1]
  push_cast
  rw [mul_zero, add_zero, div_self hcne, log_one, mul_zero, zero_div, sub_zero, mul_one]
  congr 3
  rw [hcdef, cpow_half_sq_sub_one ha]
  field_simp
  ring

/-- Arctangent form of `∫₀¹ du/(c²+u²)`, `c = (a²-1)^{1/2}`. -/
theorem integral_inv_sq_sub_one_add_sq_arctan {a : ℂ} (ha : 1 < a.re) :
    (∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) =
      arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ) := by
  set c : ℂ := (a^2-1)^(1/2:ℂ) with hcdef
  have hcre : 0 < c.re := by
    have := re_cpow_half_pos (sq_sub_one_add_mem_slitPlane ha (u := 0) le_rfl)
    rwa [show a^2-1+((0:ℝ):ℂ) = a^2-1 by push_cast; ring] at this
  have hc2 : c^2 = a^2-1 := cpow_half_sq _
  have hcne : c ≠ 0 := fun h => by rw [h] at hcre; simp at hcre
  set Λ : ℝ → ℂ := fun u => -I/2 * log ((1+(u/c)*I)/(1-(u/c)*I)) / c
  have hderiv : ∀ u ∈ uIcc (0:ℝ) 1, HasDerivAt Λ (1/((a^2-1) + (u:ℂ)^2)) u := by
    intro u _
    have hD : 1-((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c - (u:ℂ)*I = c * (1-((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hN : 1+((u:ℂ)/c)*I ≠ 0 := by
      intro h
      have : c + (u:ℂ)*I = c * (1+((u:ℂ)/c)*I) := by field_simp
      rw [h, mul_zero] at this
      have := congrArg Complex.re this; simp at this; linarith
    have hslit : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) ∈ slitPlane := by
      have : (1+((u:ℂ)/c)*I)/(1-((u:ℂ)/c)*I) = (c + (u:ℂ)*I)/(c - (u:ℂ)*I) := by
        field_simp
      rw [this]
      exact div_mem_slitPlane_of_re_eq (by simpa using hcre) (by simp)
    have hNd : HasDerivAt (fun u : ℝ => 1+((u:ℂ)/c)*I) (I/c) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_add 1
      exact this.congr_deriv (by norm_num; ring)
    have hDd : HasDerivAt (fun u : ℝ => 1-((u:ℂ)/c)*I) (-(I/c)) u := by
      have := (((hasDerivAt_id (u:ℝ)).ofReal_comp.div_const c).mul_const I).const_sub 1
      exact this.congr_deriv (by norm_num; ring)
    have hlog := (hNd.div hDd hD).clog_real hslit
    have := (hlog.const_mul (-I/2)).div_const c
    convert this using 1
    rw [← hc2]
    have hden : c^2 + (u:ℂ)^2 ≠ 0 := by rw [hc2]; exact sq_sub_one_add_sq_ne_zero ha u
    have hden' : c^2 - (u:ℂ)^2*I^2 ≠ 0 := by rw [I_sq]; convert hden using 1; ring
    simp only [Pi.div_apply]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
    linear_combination (-2*c) * mul_inv_cancel₀ hden
  have hcont : ContinuousOn (fun u : ℝ => 1/((a^2-1) + (u:ℂ)^2)) (uIcc 0 1) :=
    continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp only [Λ, Complex.arctan]
  push_cast
  simp

/-- Poisson form of `L₀` on the positive axis. -/
theorem struveL_zero_eq_poisson {t : ℝ} (ht : 0 < t) :
    struveL 0 t = 2/π * ∫ s : ℝ in 0..1, (1-(s:ℂ)^2)^(-1/2:ℂ) * sinh ((t:ℂ)*s) := by
  rw [struveL_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
  rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
  have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  rw [hs, hp]; ring

theorem norm_sinh_mul_le {t s : ℝ} (ht : 0 < t) (hs : s ∈ Ioc (0:ℝ) 1) :
    ‖sinh ((t:ℂ)*s)‖ ≤ Real.exp (1*t) := by
  rw [← ofReal_mul, ← ofReal_sinh, norm_real, Real.norm_eq_abs, one_mul,
    abs_of_nonneg (Real.sinh_nonneg_iff.2 (by nlinarith [hs.1])), Real.sinh_eq]
  have h1 : Real.exp (t*s) ≤ Real.exp t := Real.exp_le_exp.2 (by nlinarith [hs.2])
  have h2 : 0 < Real.exp (-(t*s)) := Real.exp_pos _
  have h3 : 0 < Real.exp t := Real.exp_pos _
  linarith

/-- `L₀` grows at most like `e^t` on the positive axis. -/
theorem exists_bound_struveL_zero :
    ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖struveL 0 t‖ ≤ C * Real.exp t := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hw : IntervalIntegrable w volume 0 1 := by
    have := intervalIntegrable_poissonWeight (ν := 0) (by norm_num)
    convert this using 3; norm_num
  set C : ℝ := 2/π * ∫ s : ℝ in 0..1, ‖w s‖
  have hC : 0 ≤ C := mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg zero_le_one fun _ _ => norm_nonneg _)
  refine ⟨C, fun t ht => ?_⟩
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul, norm_zero]
    positivity
  rw [struveL_zero_eq_poisson hpos, norm_mul]
  have h2 : ‖(2:ℂ)/π‖ = 2/π := by
    rw [norm_div, Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  rw [h2, show C * Real.exp t = 2/π * ((∫ s : ℝ in 0..1, ‖w s‖) * Real.exp t) by ring]
  gcongr
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans ?_
  rw [← intervalIntegral.integral_mul_const]
  refine intervalIntegral.integral_mono_on_of_le_Ioo zero_le_one ?_ (hw.norm.mul_const _)
    fun s hs => ?_
  · exact (hw.mul_continuousOn (by fun_prop)).norm
  · rw [norm_mul]
    have := norm_sinh_mul_le hpos ⟨hs.1, hs.2.le⟩
    rw [one_mul] at this
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)

/-- Laplace transform of `L₀` in terms of `∫₀¹ du/((a²-1)+u²)`. -/
theorem struveL_zero_laplace_aux {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0
      (2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hk : Continuous (Function.uncurry fun t s : ℝ => sinh ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 1) ha hk
    (fun t s ht hs => norm_sinh_mul_le ht hs)
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveL 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sinh ((t:ℂ)*s)) := by
    intro t ht; rw [struveL_zero_eq_poisson ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveL 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveL 0 t) =
      2/π * ∫ u : ℝ in 0..1, 1/((a^2-1) + (u:ℂ)^2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    congr 1
    have h1 : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sinh ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2-(s:ℂ)^2)) := by
      refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs => ?_)
      rw [uIoc_of_le zero_le_one] at hs
      rw [laplace_sinh_mul ha hs]
    rw [h1]
    have h := integral_poissonWeight_eq_trig 0 (fun s : ℝ => (s:ℂ)/(a^2-(s:ℂ)^2))
    rw [show (0:ℂ)-1/2 = -1/2 by ring] at h
    rw [h]
    simp only [mul_zero, cpow_zero, mul_one]
    set g : ℝ → ℂ := fun u => 1/((a^2-1) + (u:ℂ)^2)
    have hsub := intervalIntegral.integral_deriv_smul_comp' (a := 0) (b := π/2) (f := Real.sin)
      (f' := Real.cos) (g := g) (fun x _ => Real.hasDerivAt_sin x) Real.continuous_cos.continuousOn
      (continuousOn_const.div (by fun_prop) fun u _ => sq_sub_one_add_sq_ne_zero ha u)
    rw [Real.sin_zero, Real.sin_pi_div_two] at hsub
    rw [← hsub]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [g, Function.comp, real_smul]
    have hc : (Real.cos θ : ℂ)^2 = 1 - (Real.sin θ : ℂ)^2 := by
      rw [← ofReal_pow, ← ofReal_pow, Real.cos_sq']; push_cast; ring
    rw [hc]; ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- struve laplace 13. -/
@[dlmf 11.7.E13]
theorem struve_laplace_13 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 0 t) 0 (2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set w : ℝ → ℂ := fun s => (1-(s:ℂ)^2)^(-1/2:ℂ)
  have hH : ∀ t : ℝ, 0 < t → struveH 0 t = 2/π * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s) := by
    intro t ht
    rw [struveH_eq_poisson (by norm_num) (ofReal_ne_zero.2 ht.ne')]
    rw [cpow_zero, zero_add, Complex.Gamma_one_half_eq, show (0:ℂ)-1/2 = -1/2 by ring]
    have hs : (π:ℂ)^(1/2:ℂ) = (Real.sqrt π : ℂ) := by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
    have hp : (Real.sqrt π : ℂ) * (Real.sqrt π : ℂ) = π := by
      rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    rw [hs, hp]; ring
  have hk : Continuous (Function.uncurry fun t s : ℝ => sin ((t:ℂ)*s)) := by
    simp only [Function.uncurry_def]; fun_prop
  have hkb : ∀ t s : ℝ, 0 < t → s ∈ Ioc (0:ℝ) 1 → ‖sin ((t:ℂ)*s)‖ ≤ Real.exp (0*t) := by
    intro t s _ _
    rw [zero_mul, Real.exp_zero, ← ofReal_mul, ← ofReal_sin, norm_real, Real.norm_eq_abs]
    exact Real.abs_sin_le_one _
  obtain ⟨hI, hV⟩ := laplace_poissonWeight (a := a) (β := 0) ha hk hkb
  have hae : ∀ t ∈ Ioi (0:ℝ), exp (-a*t) * struveH 0 t =
      2/π * (exp (-a*t) * ∫ s : ℝ in 0..1, w s * sin ((t:ℂ)*s)) := by
    intro t ht; rw [hH t ht]; ring
  have hI' : IntegrableOn (fun t : ℝ => exp (-a*t)*struveH 0 t) (Ioi 0) :=
    IntegrableOn.congr_fun (Integrable.const_mul hI (2/π:ℂ)) (fun t ht => (hae t ht).symm)
      measurableSet_Ioi
  have hval : (∫ t : ℝ in Ioi 0, exp (-a*t)*struveH 0 t) =
      2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hae, integral_const_mul, hV]
    have : (∫ s : ℝ in 0..1, w s * ∫ t : ℝ in Ioi 0, exp (-a*t) * sin ((t:ℂ)*s)) =
        ∫ s : ℝ in 0..1, w s * ((s:ℂ)/(a^2+(s:ℂ)^2)) :=
      intervalIntegral.integral_congr fun s _ => by rw [laplace_sin_mul ha]
    rw [this, integral_poissonWeight_mul_div_sq_add ha]
    ring
  have := intervalIntegral_tendsto_integral_Ioi 0 hI' tendsto_id
  rw [hval] at this
  exact this

/-- struve laplace 14. -/
@[dlmf 11.7.E14]
theorem struve_laplace_14 {a : ℂ} (ha : 0 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveH 1 t) 0 (2/(π*a)-2*a/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)) := by
  set L : ℂ := 2/(π*((1+a^2)^(1/2:ℂ)))*log ((1+((1+a^2)^(1/2:ℂ)))/a)
  have h13 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) atTop (𝓝 L) :=
    struve_laplace_13 ha
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveH_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveH 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => ‖exp (-a*R)‖) atTop (𝓝 0) := by
      have : (fun R : ℝ => ‖exp (-a*R)‖) = fun R => Real.exp ((-a).re * R) := by
        funext R; rw [Complex.norm_exp]; simp
      rw [this]
      exact Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hre)
    have hEC : Tendsto (fun R : ℝ => ‖exp (-a*R)‖ * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hC R hR) (norm_nonneg _)
  have hH0 : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have hH1 : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have hc0 : Continuous fun t : ℝ => struveH 0 t := hH0.continuous.comp continuous_ofReal
  have hc1 : Continuous fun t : ℝ => struveH 1 t := hH1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveH 0 t)
        (2/π - struveH 1 x) x := fun x _ => (struveH_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.sub hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) =
        (∫ t in (0:ℝ)..R, 2/π * exp (-a*t)) -
          ∫ t in (0:ℝ)..R, exp (-a*t) * (2/π - struveH 1 t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.sub hc1)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveH 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveH, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveH 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  have : (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 1 t) = fun R =>
      2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) - (exp (-a*R) * struveH 0 R +
        a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveH 0 t) := funext hval
  unfold HasIntegralAtTop
  rw [this]
  have hlim := (hexp.const_mul (2/π:ℂ)).sub (hbd.add (h13.const_mul a))
  convert hlim using 2
  simp only [L, zero_add]
  ring

/-- struve laplace 15. -/
@[dlmf 11.7.E15]
theorem struve_laplace_15 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 0 t) 0 (2/(π*((a^2-1)^(1/2:ℂ)))*(-I*log (I/a+(1-1/a^2)^(1/2:ℂ)))) := by
  have h := struveL_zero_laplace_aux ha
  rw [integral_inv_sq_sub_one_add_sq_log ha] at h
  convert h using 1
  ring

/-- struve laplace 16. -/
@[dlmf 11.7.E16]
theorem struve_laplace_16 {a : ℂ} (ha : 1 < a.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-a*t)*struveL 1 t) 0 (2*a/(π*((a^2-1)^(1/2:ℂ)))*arctan (1/((a^2-1)^(1/2:ℂ)))-2/(π*a)) := by
  set L : ℂ := 2/π * (arctan (1/((a^2-1)^(1/2:ℂ))) / (a^2-1)^(1/2:ℂ))
  have h15 : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) atTop (𝓝 L) := by
    have h := struveL_zero_laplace_aux ha
    rwa [integral_inv_sq_sub_one_add_sq_arctan ha] at h
  have ha0' : 0 < a.re := by linarith
  have hre : (-a).re < 0 := by simp; linarith
  have hexp : Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R, exp (-a*t)) atTop (𝓝 (1/a)) := by
    have := intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_exp_mul_complex_Ioi hre 0)
      tendsto_id
    rw [integral_exp_mul_complex_Ioi hre 0] at this
    have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha; linarith
    convert this using 2
    · rfl
    · rw [ofReal_zero, mul_zero, Complex.exp_zero]
      field_simp
  obtain ⟨C, hC⟩ := exists_bound_struveL_zero
  have hbd : Tendsto (fun R : ℝ => exp (-a*R) * struveL 0 R) atTop (𝓝 0) := by
    have hE : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg (by linarith))
    have hEC : Tendsto (fun R : ℝ => Real.exp ((1 - a.re) * R) * C) atTop (𝓝 0) := by
      have := hE.mul_const C; rwa [zero_mul] at this
    refine squeeze_zero_norm' ?_ hEC
    filter_upwards [eventually_ge_atTop 0] with R hR
    rw [norm_mul, Complex.norm_exp]
    have : (-a*(R:ℂ)).re = -a.re*R := by simp
    rw [this]
    calc Real.exp (-a.re*R) * ‖struveL 0 R‖ ≤ Real.exp (-a.re*R) * (C * Real.exp R) :=
          mul_le_mul_of_nonneg_left (hC R hR) (Real.exp_pos _).le
      _ = Real.exp ((1 - a.re) * R) * C := by
          rw [show (1 - a.re) * R = -a.re*R + R by ring, Real.exp_add]; ring
  have hL0 : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hL1 : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have hc1 : Continuous fun t : ℝ => struveL 1 t := hL1.continuous.comp continuous_ofReal
  have hval : ∀ R : ℝ, (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
      (exp (-a*R) * struveL 0 R + a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t) -
        2/π * (∫ t in (0:ℝ)..R, exp (-a*t)) := by
    intro R
    have hu : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => exp (-a*t)) (-a * exp (-a*x)) x := by
      intro x _
      have := ((hasDerivAt_id (x:ℝ)).ofReal_comp.const_mul (-a)).cexp
      exact this.congr_deriv (by simp only [id, ofReal_one, mul_one]; ring)
    have hv : ∀ x ∈ uIcc (0:ℝ) R, HasDerivAt (fun t : ℝ => struveL 0 t)
        (2/π + struveL 1 x) x := fun x _ => (struveL_zero_deriv x).comp_ofReal
    have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv
      ((by fun_prop : Continuous fun x : ℝ => -a * exp (-a*x)).intervalIntegrable _ _)
      ((continuous_const.add hc1).intervalIntegrable _ _)
    have hsplit : (∫ t in (0:ℝ)..R, exp (-a*t)*struveL 1 t) =
        (∫ t in (0:ℝ)..R, exp (-a*t) * (2/π + struveL 1 t)) -
          ∫ t in (0:ℝ)..R, 2/π * exp (-a*t) := by
      rw [← intervalIntegral.integral_sub]
      · congr 1; funext t; ring
      · exact ((by fun_prop : Continuous fun t : ℝ => exp (-a*t)).mul
          (continuous_const.add hc1)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun t : ℝ => 2/π * exp (-a*t)).intervalIntegrable _ _
    rw [hsplit, hibp, intervalIntegral.integral_const_mul]
    have hz : struveL 0 ((0:ℝ):ℂ) = 0 := by
      simp only [ofReal_zero, struveL, zero_div, zero_add, cpow_one, zero_mul]
    have hneg : (∫ x in (0:ℝ)..R, -a * exp (-a*x) * struveL 0 x) =
        -a * ∫ t in (0:ℝ)..R, exp (-a*t)*struveL 0 t := by
      rw [← intervalIntegral.integral_const_mul]; congr 1; funext t; ring
    rw [hneg, hz]
    ring
  unfold HasIntegralAtTop
  rw [funext hval]
  have hlim := (hbd.add (h15.const_mul a)).sub (hexp.const_mul (2/π:ℂ))
  convert hlim using 2
  simp only [L, zero_add]
  ring

end AAR.Struve
