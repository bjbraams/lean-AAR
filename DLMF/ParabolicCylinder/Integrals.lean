/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ParabolicCylinder.Relations
public import DLMF.ParabolicCylinder.IntegralTools
public import DLMF.ParabolicCylinder.ContourTools

/-!
# Cylinder real and contour integrals

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- pcfU integral 2. -/
@[dlmf 12.5.E2]
theorem pcfU_integral_2 {a z : ℂ} (ha : -1/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => z*exp (-z^2/4)/Gamma (a/2+1/4)*((t:ℂ)^(a/2-3/4)*exp (-t)*(z^2+2*t)^(-a/2-3/4))) 0 (pcfU a z) := by
  have hα : 0 < (a/2+1/4).re := by simp; linarith
  have hv : pcfU a z = z * exp (-z^2/4) / Gamma (a/2+1/4) * pcfInt_F (a/2+1/4) (-a/2-3/4) (z^2) := by
    refine pcfInt_eq_of_real (f := pcfU a)
      (g := fun z => z * exp (-z^2/4) / Gamma (a/2+1/4) * pcfInt_F (a/2+1/4) (-a/2-3/4) (z^2))
      (pcfU_entire a).differentiableOn ?_ (fun x hx => pcfInt_U_real_2 ha hx) hz
    exact ((differentiableOn_id.mul (differentiableOn_id.pow 2 |>.neg.div_const 4 |>.cexp)).div_const _).mul
      (pcfInt_differentiableOn_comp hα _)
  have hI := pcfInt_integrableOn hα (-a/2-3/4) (pcfInt_sq_mem_slitPlane hz)
  rw [show a/2+1/4-1 = a/2-3/4 by ring] at hI
  have T := intervalIntegral_tendsto_integral_Ioi 0 (hI.const_mul (z*exp (-z^2/4)/Gamma (a/2+1/4))) tendsto_id
  rw [integral_const_mul] at T
  unfold HasIntegralAtTop
  rw [hv]
  unfold pcfInt_F
  rw [show a/2+1/4-1 = a/2-3/4 by ring]
  exact T

/-- pcfU integral 3. -/
@[dlmf 12.5.E3]
theorem pcfU_integral_3 {a z : ℂ} (ha : -3/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-z^2/4)/Gamma (a/2+3/4)*((t:ℂ)^(a/2-1/4)*exp (-t)*(z^2+2*t)^(-a/2-1/4))) 0 (pcfU a z) := by
  have hα : 0 < (a/2+3/4).re := by simp; linarith
  have hv : pcfU a z = exp (-z^2/4) / Gamma (a/2+3/4) * pcfInt_F (a/2+3/4) (-a/2-1/4) (z^2) := by
    refine pcfInt_eq_of_real (f := pcfU a)
      (g := fun z => exp (-z^2/4) / Gamma (a/2+3/4) * pcfInt_F (a/2+3/4) (-a/2-1/4) (z^2))
      (pcfU_entire a).differentiableOn ?_ (fun x hx => pcfInt_U_real_3 ha hx) hz
    exact ((differentiableOn_id.pow 2 |>.neg.div_const 4 |>.cexp).div_const _).mul
      (pcfInt_differentiableOn_comp hα _)
  have hI := pcfInt_integrableOn hα (-a/2-1/4) (pcfInt_sq_mem_slitPlane hz)
  rw [show a/2+3/4-1 = a/2-1/4 by ring] at hI
  have T := intervalIntegral_tendsto_integral_Ioi 0 (hI.const_mul (exp (-z^2/4)/Gamma (a/2+3/4))) tendsto_id
  rw [integral_const_mul] at T
  unfold HasIntegralAtTop
  rw [hv]
  unfold pcfInt_F
  rw [show a/2+3/4-1 = a/2-1/4 by ring]
  exact T

/-- pcfU integral 4. -/
@[dlmf 12.5.E4]
theorem pcfU_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => (Real.sqrt (2/π):ℂ)*exp (z^2/4)*((t:ℂ)^(-a-1/2)*exp (-t^2/2)*cos (z*t+(a/2+1/4)*π))) 0 (pcfU a z) := by
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have ha' : -1/2 < (-a).re := by simp; linarith
  have han : ∀ n : ℕ, a ≠ n+1/2 := fun n h => by
    have := congrArg Complex.re h; simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero fun n h => han n (by linear_combination -h)
  set θ : ℂ := (a/2+1/4)*π with hθ
  set K : ℂ := (Real.sqrt (2/π):ℂ)*exp (z^2/4)/2 with hK
  set gp := fun t : ℝ => (t : ℂ) ^ (-a-1/2) * exp (-(t : ℂ) ^ 2 / 2 - (-I*z) * t)
  set gm := fun t : ℝ => (t : ℂ) ^ (-a-1/2) * exp (-(t : ℂ) ^ 2 / 2 - (I*z) * t)
  have ip : IntegrableOn gp (Ioi 0) := integrableOn_pcfIntegrand hc (-I*z)
  have im : IntegrableOn gm (Ioi 0) := integrableOn_pcfIntegrand hc (I*z)
  have hf : (fun t : ℝ => (Real.sqrt (2/π):ℂ)*exp (z^2/4)*((t:ℂ)^(-a-1/2)*exp (-t^2/2)*cos (z*t+(a/2+1/4)*π))) =
      fun t => K * (exp (I*θ) * gp t + exp (-I*θ) * gm t) := by
    funext t
    simp only [K, gp, gm, θ, Complex.cos]
    have e1 : exp (I*((a/2+1/4)*π)) * exp (-(t:ℂ)^2/2 - -I*z*t) = exp (-(t:ℂ)^2/2) * exp ((z*t+(a/2+1/4)*π)*I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    have e2 : exp (-I*((a/2+1/4)*π)) * exp (-(t:ℂ)^2/2 - I*z*t) = exp (-(t:ℂ)^2/2) * exp (-(z*t+(a/2+1/4)*π)*I) := by
      rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; ring
    linear_combination (-(Real.sqrt (2/π):ℂ)*exp (z^2/4)/2 * (t:ℂ)^(-a-1/2)) * (e1 + e2)
  have hp := pcfU_eq_integral ha' (-I*z)
  have hm := pcfU_eq_integral ha' (I*z)
  rw [show (1/2:ℂ) + -a = 1/2 - a by ring, show (-a) - 1/2 = -a-1/2 by ring] at hp hm
  have hsq : (-I*z)^2 = -z^2 := by rw [mul_pow, neg_pow, I_sq]; ring
  have hsq' : (I*z)^2 = -z^2 := by rw [mul_pow, I_sq]; ring
  rw [hsq] at hp; rw [hsq'] at hm
  have hconn := pcfU_rotated_connection_pos han z
  unfold HasIntegralAtTop
  rw [hf]
  have H : IntegrableOn (fun t => K*(exp (I*θ)*gp t + exp (-I*θ)*gm t)) (Ioi 0) :=
    ((ip.const_mul (exp (I*θ))).add (im.const_mul (exp (-I*θ)))).const_mul K
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  suffices hv : ∫ t in Ioi (0:ℝ), K*(exp (I*θ)*gp t + exp (-I*θ)*gm t) = pcfU a z by
    rw [← hv]; exact T
  rw [integral_const_mul, integral_add (ip.const_mul _) (im.const_mul _), integral_const_mul, integral_const_mul]
  have hs : (Real.sqrt (2/π):ℂ) * Real.sqrt (2*π) = 2 := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity), show 2/π*(2*π) = 2^2 by field_simp,
      Real.sqrt_sq (by norm_num)]; norm_num
  have he : exp (-(-z^2)/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have he2 : exp (z^2/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hIp : ∫ t in Ioi (0:ℝ), gp t = Gamma (1/2-a) * exp (-z^2/4) * pcfU (-a) (-I*z) := by
    rw [hp, show ∀ X : ℂ, Gamma (1/2-a) * exp (-z^2/4) * (exp (- -z^2/4) / Gamma (1/2-a) * X) =
      (exp (- -z^2/4) * exp (-z^2/4)) * X from fun X => by rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hΓ]; ring, he, one_mul]
  have hIm : ∫ t in Ioi (0:ℝ), gm t = Gamma (1/2-a) * exp (-z^2/4) * pcfU (-a) (I*z) := by
    rw [hm, show ∀ X : ℂ, Gamma (1/2-a) * exp (-z^2/4) * (exp (- -z^2/4) / Gamma (1/2-a) * X) =
      (exp (- -z^2/4) * exp (-z^2/4)) * X from fun X => by rw [div_mul_eq_mul_div, mul_div_assoc', div_eq_iff hΓ]; ring, he, one_mul]
  rw [hIp, hIm, hK]
  have q1 : exp (-I*θ) = exp (-1*I*π*(a/2+1/4)) := by rw [hθ]; congr 1; ring
  have q2 : exp (I*θ) = exp (1*I*π*(a/2+1/4)) := by rw [hθ]; congr 1; ring
  rw [q1, q2, show (1:ℂ)*I*z = I*z by ring, show (-1:ℂ)*I*z = -I*z by ring] at *
  linear_combination (Real.sqrt (2/π):ℂ)/2 * (Gamma (1/2-a) * (exp (1*I*π*(a/2+1/4)) * pcfU (-a) (-I*z) + exp (-1*I*π*(a/2+1/4)) * pcfU (-a) (I*z))) * he2 - (Real.sqrt (2/π):ℂ)/2 * hconn + pcfU a z / 2 * hs

/-- pcfU vertical integral. -/
@[dlmf 12.5.E6]
theorem pcfU_vertical_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; exp (z^2/4)/Real.sqrt (2*π)*exp (-z*t+t^2/2)*t^(-a-1/2)) (pcfU a z) := by
  set K : ℂ := exp (z^2/4)/Real.sqrt (2*π)
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; exp (z^2/4)/Real.sqrt (2*π)*exp (-z*t+t^2/2)*t^(-a-1/2)) =
      fun y : ℝ => K * (exp (-z*((c:ℂ)+y*I) + ((c:ℂ)+y*I)^2/2) * ((c:ℂ)+y*I)^(-a-1/2)) := by
    funext y; simp only [K]; ring
  have h := pcfInt_hasIntegralWholeLine ((pcfCt_vert_integrable z (-a-1/2) hc).const_mul K)
  have hs : (Real.sqrt (2*π) : ℂ) ≠ 0 :=
    ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
  have he : exp (z^2/4) * exp (-z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  rw [integral_const_mul, pcfCt_vertical a z hc] at h
  rw [hfun]
  convert h using 1
  rw [show K * ((Real.sqrt (2*π) : ℂ) * exp (-z^2/4) * pcfU a z) =
      (exp (z^2/4) * exp (-z^2/4)) * pcfU a z * ((Real.sqrt (2*π) : ℂ) / Real.sqrt (2*π)) by
    simp only [K]; ring, he, div_self hs]
  ring

/-- pcfV horizontal integral. -/
@[dlmf 12.5.E7]
theorem pcfV_horizontal_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ u v : ℂ, HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) u ∧ HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) v ∧ u+v=pcfV a z := by
  set K : ℂ := exp (-z^2/4)/(2*π)
  obtain ⟨hiu, hvu⟩ := pcfCt_horizontal_upper a z hc
  obtain ⟨hil, hvl⟩ := pcfCt_horizontal_lower a z hc
  have fl : (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) =
      fun x : ℝ => K * (exp (z*((x:ℂ)-c*I) - ((x:ℂ)-c*I)^2/2) * ((x:ℂ)-c*I)^(a-1/2)) := by
    funext x; simp only [K]; ring
  have fu : (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) =
      fun x : ℝ => K * (exp (z*((x:ℂ)+c*I) - ((x:ℂ)+c*I)^2/2) * ((x:ℂ)+c*I)^(a-1/2)) := by
    funext x; simp only [K]; ring
  refine ⟨_, _, fl ▸ pcfInt_hasIntegralWholeLine (hil.const_mul K),
    fu ▸ pcfInt_hasIntegralWholeLine (hiu.const_mul K), ?_⟩
  rw [fl, fu, integral_const_mul, integral_const_mul, hvl, hvu]
  have hV1 := pcfV_eq_mul_I a z
  have hV2 := pcfV_eq_mul_neg_I a z
  have hsum : 2 * pcfV a z = (Real.sqrt (2/π):ℂ) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) := by
    linear_combination hV1 + hV2
  have hs : (Real.sqrt (2*π) : ℂ) * (Real.sqrt (2/π) : ℂ) = 2 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show 2*π*(2/π) = 2^2 by field_simp,
      Real.sqrt_sq (by norm_num)]; norm_num
  have he : exp (-z^2/4) * exp (z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hsq : (Real.sqrt (2*π) : ℂ)^2 = 2*π := by
    rw [← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hc' : (Real.sqrt (2*π) : ℂ)/(2*π) = (Real.sqrt (2/π) : ℂ)/2 := by
    rw [div_eq_div_iff (by simp) two_ne_zero]
    linear_combination (-(Real.sqrt (2*π) : ℂ)) * hs + (Real.sqrt (2/π) : ℂ) * hsq
  rw [show K * (exp (-I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (I*z))) +
      K * (exp (I*π*(a/2-1/4)) * ((Real.sqrt (2*π) : ℂ) * exp (z^2/4) * pcfU (-a) (-I*z))) =
      (exp (-z^2/4) * exp (z^2/4)) * ((Real.sqrt (2*π) : ℂ)/(2*π)) *
        (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) + exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) by
    simp only [K]; ring, he, one_mul, hc']
  linear_combination (-1/2:ℂ) * hsum

/-- Hankel loop from negative infinity below the cut around zero to negative infinity above. -/
def pcfNegativeLoop (a z : ℂ) (r R : ℝ) : ℂ :=
  (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I))) + (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) - (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I)))

/-- pcfU hankel integral. -/
@[dlmf 12.5.E5]
theorem pcfU_hankel_integral {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R => Gamma (1/2-a)/(2*π*I)*exp (-z^2/4)*pcfNegativeLoop a z r R) atTop (𝓝 (pcfU a z)) := by
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero fun n h => ha n (by linear_combination -h)
  have hT := ((intervalIntegral_tendsto_integral_Ioi r (pcfCt_g_integrableOn a z hr)
    tendsto_id).const_mul (pcfCt_kappa a)).add_const (pcfCt_C a z r)
  rw [pcfCt_loop_value a z hr] at hT
  have hev : (fun R => pcfCt_kappa a * (∫ t in r..id R, pcfCt_g a z t) + pcfCt_C a z r) =ᶠ[atTop]
      (fun R => pcfNegativeLoop a z r R) := by
    filter_upwards [eventually_gt_atTop 0] with R hR
    exact (pcfCt_loop_eq a z hr hR).symm
  have hT' := (hT.congr' hev).const_mul (Gamma (1/2-a)/(2*π*I)*exp (-z^2/4))
  have hv : Gamma (1/2-a)/(2*π*I)*exp (-z^2/4) * (2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) =
      pcfU a z := by
    have he : exp (-z^2/4) * exp (z^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
    have hπ : (2*π*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    rw [show Gamma (1/2-a)/(2*π*I)*exp (-z^2/4) * (2*π*I * exp (z^2/4) * pcfU a z * (Gamma (1/2-a))⁻¹) =
      (Gamma (1/2-a) * (Gamma (1/2-a))⁻¹) * ((2*π*I)/(2*π*I)) * (exp (-z^2/4) * exp (z^2/4)) * pcfU a z by
        ring, mul_inv_cancel₀ hΓ, div_self hπ, he]
    ring
  rw [hv] at hT'
  simpa only [mul_assoc] using hT'

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E8]
theorem pcfU_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, 1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) (2*π*Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z) := by
  have _ := ha
  have hca' : 2*c < 1/2 + a.re := by simpa using hca
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) =
      pcfInt_B a z c := rfl
  rw [hfun, ← pcfInt_B_integral a hz0 hz hc hca']
  exact pcfInt_hasIntegralWholeLine (pcfInt_B_integrable a hz0 hz hc hca')

/-- `arg (±i z) = arg z ± π/2` for `|arg z| < π/2`. -/
lemma pcfInt_arg_I_mul {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) :
    arg (I*z) = arg z + π/2 ∧ arg (-I*z) = arg z - π/2 := by
  obtain ⟨h1, h2⟩ := abs_lt.mp hz
  constructor
  · rw [arg_mul I_ne_zero hz0 (by rw [arg_I]; constructor <;> linarith), arg_I]; ring
  · rw [arg_mul (neg_ne_zero.mpr I_ne_zero) hz0 (by rw [arg_neg_I]; constructor <;> linarith),
      arg_neg_I]; ring

/-- `(±i z)^w = z^w e^{±iπw/2}` for `|arg z| < π/2`. -/
lemma pcfInt_I_mul_cpow {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (w : ℂ) :
    (I*z)^w = z^w * exp (π/2*I*w) ∧ (-I*z)^w = z^w * exp (-(π/2)*I*w) := by
  obtain ⟨ha1, ha2⟩ := pcfInt_arg_I_mul hz0 hz
  have hl1 : log (I*z) = log z + π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha1, add_im, log_im]; simp
  have hl2 : log (-I*z) = log z - π/2*I := by
    apply Complex.ext
    · simp [log_re]
    · rw [log_im, ha2, sub_im, log_im]; simp
  constructor
  · rw [cpow_def_of_ne_zero (mul_ne_zero I_ne_zero hz0), cpow_def_of_ne_zero hz0, hl1,
      ← Complex.exp_add]; congr 1; ring
  · rw [cpow_def_of_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0),
      cpow_def_of_ne_zero hz0, hl2, ← Complex.exp_add]; congr 1; ring

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E9]
theorem pcfV_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, -1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+-1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) (2*π*Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z) := by
  have _ := ha
  have hca' : 2*c < 1/2 + (-a).re := by simpa using hca
  have hz2 : |arg z| < π/2 := by linarith [Real.pi_pos]
  obtain ⟨ha1, ha2⟩ := pcfInt_arg_I_mul hz0 hz2
  have hp0 : I*z ≠ 0 := mul_ne_zero I_ne_zero hz0
  have hm0 : -I*z ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hz0
  have hpa : |arg (I*z)| < 3*π/4 := by
    rw [ha1]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hma : |arg (-I*z)| < 3*π/4 := by
    rw [ha2]; obtain ⟨h1, h2⟩ := abs_lt.mp hz; rw [abs_lt]; constructor <;> linarith
  have hfun : (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) =
      fun y => (pcfInt_B (-a) (I*z) c y + pcfInt_B (-a) (-I*z) c y)/2 := by
    funext y
    simp only [pcfInt_B]
    obtain ⟨e1, e2⟩ := pcfInt_I_mul_cpow hz0 hz2 (2*((c:ℂ)+y*I))
    rw [e1, e2, show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring, Complex.cos]
    have q1 : exp (π/2*I*(2*((c:ℂ)+y*I))) = exp (π*((c:ℂ)+y*I)*I) := by congr 1; ring
    have q2 : exp (-(π/2)*I*(2*((c:ℂ)+y*I))) = exp (-(π*((c:ℂ)+y*I))*I) := by congr 1; ring
    rw [q1, q2]; ring
  have i1 := pcfInt_B_integrable (-a) hp0 hpa hc hca'
  have i2 := pcfInt_B_integrable (-a) hm0 hma hc hca'
  rw [hfun]
  suffices hI : ∫ y, (pcfInt_B (-a) (I*z) c y + pcfInt_B (-a) (-I*z) c y)/2 =
      2*π*Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z by
    rw [← hI]; exact pcfInt_hasIntegralWholeLine ((i1.add i2).div_const 2)
  rw [integral_div, integral_add i1 i2, pcfInt_B_integral (-a) hp0 hpa hc hca',
    pcfInt_B_integral (-a) hm0 hma hc hca']
  have hV1 := pcfV_eq_mul_I a z
  have hV2 := pcfV_eq_mul_neg_I a z
  obtain ⟨f1, f2⟩ := pcfInt_I_mul_cpow hz0 hz2 (-a+1/2)
  rw [f1, f2, show (I*z)^2 = -z^2 by rw [mul_pow, I_sq]; ring,
    show (-I*z)^2 = -z^2 by rw [mul_pow, neg_sq, I_sq]; ring, show (1/2:ℂ)+1*(-a) = 1/2+-1*a by ring]
  have hs : (Real.sqrt (π/2):ℂ) * (Real.sqrt (2/π):ℂ) = 1 := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by positivity), show π/2*(2/π) = 1 by field_simp]; simp
  have hq1 : exp (π/2*I*(-a+1/2)) = exp (-I*π*(a/2-1/4)) := by congr 1; ring
  have hq2 : exp (-(π/2)*I*(-a+1/2)) = exp (I*π*(a/2-1/4)) := by congr 1; ring
  rw [hq1, hq2]
  have hsum : 2 * pcfV a z = (Real.sqrt (2/π):ℂ) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z)) := by
    linear_combination hV1 + hV2
  linear_combination (-(π * Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (Real.sqrt (π/2):ℂ))) * hsum -
    (π * Gamma (1/2+-1*a) * exp (-z^2/4) * z^(-a+1/2) * (exp (-I*π*(a/2-1/4)) * pcfU (-a) (I*z) +
      exp (I*π*(a/2-1/4)) * pcfU (-a) (-I*z))) * hs

/-- pcf integral 1. -/
@[dlmf 12.12.E1]
theorem pcf_integral_1 {μ : ℂ} (hμ : 0 < μ.re) (a : ℂ) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(μ-1)*pcfU a t) 0 (Real.sqrt π*2^(-(μ+a+1/2)/2)*Gamma μ/Gamma ((μ+a+3/2)/2)) := by
  obtain ⟨hI, hV⟩ := laplace_kummerU_gauss (a := a/2+1/4) (b := μ/2) (c := 1/2) (z := 1)
    (by simp; linarith) (by simp; linarith) (by simp)
  obtain ⟨hI2, hV2⟩ := pcfInt_sq_half_subst hI
  set C : ℂ := (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1)
  have heq : EqOn (fun t : ℝ => C * ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 1 (t^2/2)))
      (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(μ-1)*pcfU a t) (Ioi 0) :=
    fun t ht => (pcfInt_integrand_1 μ a ht).symm
  have H := IntegrableOn.congr_fun (hI2.const_mul C) heq measurableSet_Ioi
  unfold HasIntegralAtTop
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hV2, hV, sub_self,
    pcfInt_regularizedGaussHG_zero] at T
  have hd := Complex.Gamma_mul_Gamma_add_half (μ/2)
  rw [show 2*(μ/2) = μ by ring] at hd
  have h2 : C * (2:ℂ)^(1-μ) = (2:ℂ)^(-(μ+a+1/2)/2) := by
    simp only [C]
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero]; ring_nf
  have hval : C * (Gamma (μ / 2) * Gamma (μ / 2 + 1 / 2) * (Gamma (a / 2 + 1 / 4 + μ / 2 - 1 / 2 + 1))⁻¹) =
      Real.sqrt π*2^(-(μ+a+1/2)/2)*Gamma μ/Gamma ((μ+a+3/2)/2) := by
    rw [hd, show a/2+1/4 + μ/2 - 1/2 + 1 = (μ+a+3/2)/2 by ring]
    generalize Gamma ((μ+a+3/2)/2) = G
    linear_combination (Real.sqrt π * Gamma μ / G) * h2
  rw [show μ/2 - 1/2 + 1 = μ/2 + 1/2 by ring] at T
  rw [hval] at T
  exact T

/-- pcf integral 2. -/
@[dlmf 12.12.E2]
theorem pcf_integral_2 {a : ℂ} (ha : a.re < -1/2) :
    HasIntegralAtTop (fun t : ℝ => exp (-3*t^2/4)*(t:ℂ)^(-a-3/2)*pcfU a t) 0 (2^(1/4+a/2)*Gamma (-a-1/2)*cos ((a/4+1/8)*π)) := by
  set μ : ℂ := -a-1/2 with hμ
  have hb : 0 < (μ/2).re := by simp [hμ]; linarith
  have hab : a/2+1/4 = -(μ/2) := by rw [hμ]; ring
  have hI := (laplace_kummerU_gauss (a := a/2+1/4) (b := μ/2) (c := 1/2) (z := 2) hb
    (by simp [hμ]; linarith) (by simp)).1
  obtain ⟨hI2, hV2⟩ := pcfInt_sq_half_subst hI
  set C : ℂ := (2:ℂ)^(-(1/4)-a/2) * (2:ℂ)^(μ/2-1)
  have heq : EqOn (fun t : ℝ => C * ((t:ℂ) * tricomiLaplaceKernel (a/2+1/4) (μ/2) (1/2) 2 (t^2/2)))
      (fun t : ℝ => exp (-3*t^2/4)*(t:ℂ)^(-a-3/2)*pcfU a t) (Ioi 0) := fun t ht => by
    rw [show -a-3/2 = μ - 1 by rw [hμ]; ring]
    exact (pcfInt_integrand_2 μ a ht).symm
  have H := IntegrableOn.congr_fun (hI2.const_mul C) heq measurableSet_Ioi
  unfold HasIntegralAtTop
  have T := intervalIntegral_tendsto_integral_Ioi 0 H tendsto_id
  rw [← setIntegral_congr_fun measurableSet_Ioi heq, integral_const_mul, hV2, hab,
    pcfInt_laplace_two hb] at T
  have hd := Complex.Gamma_mul_Gamma_add_half (μ/2)
  rw [show 2*(μ/2) = μ by ring] at hd
  have h2 : C * (2:ℂ)^(1-μ) * (2:ℂ)^(-(μ/2)) = (2:ℂ)^(1/4+a/2) := by
    simp only [C]
    rw [← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, ← cpow_add _ _ two_ne_zero, hμ]
    ring_nf
  have hc : cos (μ/2*π/2) = cos ((a/4+1/8)*π) := by
    rw [← Complex.cos_neg, hμ]; ring_nf
  have hs : (Real.sqrt π : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr Real.pi_pos)
  have hval : C * (Gamma (μ/2) * Gamma (μ/2 + 1/2) * (2:ℂ)^(-(μ/2)) * cos (μ/2*π/2) / Real.sqrt π) =
      2^(1/4+a/2)*Gamma (-a-1/2)*cos ((a/4+1/8)*π) := by
    rw [hd, hc, ← hμ]
    calc C * (Gamma μ * (2:ℂ)^(1-μ) * Real.sqrt π * (2:ℂ)^(-(μ/2)) * cos ((a/4+1/8)*π) / Real.sqrt π)
        = (C * (2:ℂ)^(1-μ) * (2:ℂ)^(-(μ/2))) * Gamma μ * cos ((a/4+1/8)*π) *
            ((Real.sqrt π : ℂ) / Real.sqrt π) := by ring
      _ = _ := by rw [h2, div_self hs]; ring
  rw [hval] at T
  exact T

/-- `‖cos w‖ ≤ e^{|Im w|}`. -/
lemma pcfCt_norm_cos_le (w : ℂ) : ‖cos w‖ ≤ Real.exp |w.im| := by
  rw [Complex.cos]
  have h1 : ‖exp (w*I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith [neg_abs_le w.im]
  have h2 : ‖exp (-w*I)‖ ≤ Real.exp |w.im| := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr; simp; linarith [le_abs_self w.im]
  rw [norm_div, show ‖(2:ℂ)‖ = 2 by simp]
  have := norm_add_le (exp (w*I)) (exp (-w*I))
  linarith

/-- DLMF 12.5.4 as a Lebesgue integral: `e^{-t²/4} U(a,t) = √(2/π) ∫₀^∞ s^{-a-1/2} e^{-s²/2}
cos(ts + (a/2+1/4)π) ds` for `re a < 1/2`, real `t`. -/
lemma pcfCt_U_cos {a : ℂ} (ha : a.re < 1/2) (t : ℝ) :
    IntegrableOn (fun s : ℝ => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π)) (Ioi 0) ∧
    exp (-(t:ℂ)^2/4) * pcfU a t =
      (Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π) := by
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have hI : IntegrableOn (fun s : ℝ => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) * cos (t*s + (a/2+1/4)*π)) (Ioi 0) := by
    refine Integrable.mono' (((integrableOn_pcfIntegrand hc 0).norm).mul_const
      (Real.exp |((a/2+1/4)*π).im|)) ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun s hs => ?_) measurableSet_Ioi
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul (ContinuousAt.mul ?_ (by fun_prop)) (by fun_prop)
      exact (continuous_ofReal.continuousAt).cpow continuousAt_const (ofReal_mem_slitPlane.mpr hs)
    · refine Eventually.of_forall fun s => ?_
      have e : (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - 0*s) = (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) := by
        simp
      rw [e, norm_mul]
      refine mul_le_mul_of_nonneg_left ((pcfCt_norm_cos_le _).trans (le_of_eq ?_)) (norm_nonneg _)
      congr 2; simp
  refine ⟨hI, ?_⟩
  have h4 := pcfU_integral_4 ha (t:ℂ)
  have hT := intervalIntegral_tendsto_integral_Ioi 0
    (hI.const_mul ((Real.sqrt (2/π):ℂ)*exp ((t:ℂ)^2/4))) tendsto_id
  unfold HasIntegralAtTop at h4
  have hU := tendsto_nhds_unique h4 (hT.congr fun R => by
    refine intervalIntegral.integral_congr fun s _ => ?_
    rfl)
  rw [hU, integral_const_mul]
  have he : exp (-(t:ℂ)^2/4) * exp ((t:ℂ)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  linear_combination ((Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2) *
    cos (t*s + (a/2+1/4)*π)) * he


/-- DLMF 12.12.3 on the strip `-1/2 < re a < 1/2`, as a Lebesgue integral (Fubini against
12.5.4 and the kernel `pcfCt_kernel`). -/
lemma pcfCt_integral_3_strip {a : ℂ} (ha1 : -1/2 < a.re) (ha2 : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x := by
  set μ : ℂ := 1/2 - a with hμ
  have hm0 : 0 < μ.re := by simp [hμ]; linarith
  have hm2 : μ.re < 2 := by simp [hμ]; linarith
  have hμ1 : μ - 1 = -a-1/2 := by rw [hμ]; ring
  set θ : ℂ := (a/2+1/4)*π with hθ
  have hθμ : θ = π/2 - π*μ/2 := by rw [hθ, hμ]; ring
  -- the two factors
  set G1 : ℝ → ℂ := fun t => (t:ℂ)^(-a-1/2) / ((x:ℂ)^2 + (t:ℂ)^2)
  set G2 : ℝ → ℂ := fun s => (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2)
  have hG1 : IntegrableOn G1 (Ioi 0) := by
    have h := (integrable_comp_exp (pcfCt_gs μ x 0)).mp
      ((funext (pcfCt_Phi_real μ x 0)) ▸ pcfCt_Phi_real_integrable hm0 hm2 hx 0)
    refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp [pcfCt_gs, G1, hμ1]
  have hc : -1 < (-a-1/2).re := by simp; linarith
  have hG2 : IntegrableOn G2 (Ioi 0) := by
    refine (integrableOn_pcfIntegrand hc 0).congr_fun (fun s _ => ?_) measurableSet_Ioi
    simp [G2]
  set F : ℝ × ℝ → ℂ := fun q => G1 q.1 * (G2 q.2 * cos (q.1*q.2 + θ)) with hF
  have hprod : Integrable F ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
    refine ((hG1.norm.mul_prod hG2.norm).mul_const (Real.exp |θ.im|)).mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      simp only [hF, G1, G2]
      fun_prop
    · refine Eventually.of_forall fun q => ?_
      simp only [hF, norm_mul]
      have hcos : ‖cos ((q.1:ℂ)*q.2 + θ)‖ ≤ Real.exp |θ.im| :=
        (pcfCt_norm_cos_le _).trans (le_of_eq (by simp))
      calc ‖G1 q.1‖ * (‖G2 q.2‖ * ‖cos ((q.1:ℂ)*q.2 + θ)‖)
          ≤ ‖G1 q.1‖ * (‖G2 q.2‖ * Real.exp |θ.im|) := by gcongr
        _ = _ := by ring
  have hfeq : ∀ t : ℝ, exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (2/π):ℂ) * ∫ s in Ioi (0:ℝ), F (t, s) := by
    intro t
    have h := (pcfCt_U_cos ha2 t).2
    rw [show exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      G1 t * (exp (-(t:ℂ)^2/4) * pcfU a t) by simp only [G1]; ring, h, ← integral_const_mul,
      ← integral_const_mul, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hF, G2, hθ]; ring
  have hint : IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) := by
    rw [funext hfeq]; exact hprod.integral_prod_left.const_mul _
  refine ⟨hint, ?_⟩
  rw [integral_congr_ae (Eventually.of_forall hfeq), integral_const_mul]
  rw [show (∫ t in Ioi (0:ℝ), ∫ s in Ioi (0:ℝ), F (t, s)) = ∫ s in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), F (t, s)
    from integral_integral_swap hprod]
  have hin : ∀ s ∈ Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), F (t, s) =
      π/2 * (x:ℂ)^(-a-3/2) * ((s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - x*s)) := by
    intro s hs
    have hk := (pcfCt_kernel hm0 hm2 hx (le_of_lt hs)).2
    rw [hμ1, ← hθμ, show μ - 2 = -a-3/2 by rw [hμ]; ring] at hk
    rw [show (fun t : ℝ => F (t, s)) = fun t : ℝ => G2 s * ((t:ℂ)^(-a-1/2) * cos (t*s + θ) /
      ((x:ℂ)^2 + (t:ℂ)^2)) from funext fun t => by simp only [hF, G1]; ring, integral_const_mul, hk]
    simp only [G2]
    rw [show -(s:ℂ)^2/2 - x*s = -(s:ℂ)^2/2 + -(x*s) by ring, Complex.exp_add]; ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_const_mul]
  have hU := pcfU_eq_integral (a := -a) (by simp; linarith) (x:ℂ)
  rw [show (-a) - 1/2 = -a-1/2 by ring, show (1/2:ℂ) + -a = 1/2 - a by ring] at hU
  have hΓ : Gamma (1/2 - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simp; linarith)
  have he : exp ((x:ℂ)^2/4) * exp (-(x:ℂ)^2/4) = 1 := by rw [← Complex.exp_add]; ring_nf; simp
  have hs : (Real.sqrt (2/π):ℂ) * (π/2) = Real.sqrt (π/2) := by
    have : Real.sqrt (π/2) = Real.sqrt (2/π) * (π/2) := by
      rw [show π/2 = 2/π * (π/2)^2 by field_simp, Real.sqrt_mul (by positivity),
        Real.sqrt_sq (by positivity)]
      field_simp
    rw [this]; push_cast; ring
  rw [hU]
  generalize (∫ s in Ioi (0:ℝ), (s:ℂ)^(-a-1/2) * exp (-(s:ℂ)^2/2 - x*s)) = J
  generalize Gamma (1/2 - a) = G at hΓ ⊢
  rw [← hs]
  have hG' : G * G⁻¹ = 1 := mul_inv_cancel₀ hΓ
  set K : ℂ := (Real.sqrt (2/π):ℂ) * (π/2) * (x:ℂ)^(-a-3/2) * J
  linear_combination (-K) * he + (-K * exp ((x:ℂ)^2/4) * exp (-(x:ℂ)^2/4)) * hG'


/-- Elementary: `t^r ≤ t^{q₁} + t^{q₂}` for `t > 0` and `q₁ ≤ r ≤ q₂`. -/
lemma pcfCt_rpow_le_add {t q1 q2 r : ℝ} (ht : 0 < t) (h1 : q1 ≤ r) (h2 : r ≤ q2) :
    t ^ r ≤ t ^ q1 + t ^ q2 := by
  rcases le_total t 1 with h | h
  · have := Real.rpow_le_rpow_of_exponent_ge ht h h1
    have := Real.rpow_nonneg ht.le q2
    linarith
  · have := Real.rpow_le_rpow_of_exponent_le h h2
    have := Real.rpow_nonneg ht.le q1
    linarith

/-- Local domination for the integrand of 12.12.3 in the parameter `a`. -/
lemma pcfCt_integral_3_dom {a0 : ℂ} (ha0 : a0.re < 1/2) {x : ℝ} (hx : 0 < x) :
    ∃ V ∈ 𝓝 a0, ∃ g : ℝ → ℝ, IntegrableOn g (Ioi 0) ∧ ∀ t ∈ Ioi (0:ℝ), ∀ a ∈ V,
      ‖exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t‖ ≤ g t := by
  set δ := (1/2 - a0.re)/2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨M, hM⟩ := pcfCt_U_decay (‖a0‖ + δ + 1/2)
  set q1 := -a0.re - 1/2 - δ
  set q2 := -a0.re - 1/2 + δ
  refine ⟨Metric.ball a0 δ, Metric.ball_mem_nhds _ hδ0,
    fun t => M / x^2 * ((Real.exp (-t) * t ^ (q1+1-1)) + (Real.exp (-t) * t ^ (q2+1-1))), ?_, ?_⟩
  · refine Integrable.const_mul (Integrable.add ?_ ?_) _
    · exact Real.GammaIntegral_convergent (by simp only [q1, hδ]; linarith)
    · exact Real.GammaIntegral_convergent (by simp only [q2, hδ]; linarith)
  · intro t ht a ha
    have ht : 0 < t := ht
    have hda : ‖a - a0‖ < δ := by simpa [dist_eq_norm] using ha
    have hre : |a.re - a0.re| < δ := by
      have := abs_re_le_norm (a - a0); simp at this; linarith
    have hP : ‖-a-1/2‖ ≤ ‖a0‖ + δ + 1/2 := by
      calc ‖-a-1/2‖ ≤ ‖a‖ + 1/2 := by
            have := norm_add_le (-a) (-(1/2:ℂ)); simp [sub_eq_add_neg] at this ⊢
            norm_num at this ⊢; linarith
        _ ≤ ‖a0‖ + δ + 1/2 := by
            have := norm_le_norm_add_norm_sub' a a0; linarith
    have hU := hM a hP t
    have hc : ‖(t:ℂ)^(-a-1/2)‖ = t ^ (-a.re - 1/2) := by
      rw [norm_cpow_eq_rpow_re_of_pos ht]; simp
    have hden : x^2 ≤ ‖((x:ℂ)^2+(t:ℂ)^2)‖ := by
      rw [show ((x:ℂ)^2+(t:ℂ)^2) = ((x^2+t^2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity)]
      nlinarith
    have hrp := pcfCt_rpow_le_add (r := -a.re - 1/2) ht (q1 := q1) (q2 := q2)
      (by simp only [q1]; linarith [(abs_lt.mp hre).2]) (by simp only [q2]; linarith [(abs_lt.mp hre).1])
    have hx2 : 0 < x^2 := by positivity
    simp only [add_sub_cancel_right]
    calc ‖exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t‖
        = ‖(t:ℂ)^(-a-1/2)‖ / ‖((x:ℂ)^2+(t:ℂ)^2)‖ * ‖exp (-(t:ℂ)^2/4) * pcfU a t‖ := by
          rw [norm_mul, norm_div, norm_mul, norm_mul]; ring
      _ ≤ (t ^ q1 + t ^ q2) / x^2 * (M * Real.exp (-t)) := by
          rw [hc]
          apply mul_le_mul _ hU (norm_nonneg _) (by positivity)
          exact div_le_div₀ (by positivity) hrp hx2 hden
      _ = _ := by ring
/-- DLMF 12.12.3 as a Lebesgue integral on `(0,∞)`, for all `Re a < 1/2`. -/
lemma pcfCt_integral_3_all {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t =
      (Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x := by
  set Ω : Set ℂ := {a | a.re < 1/2} with hΩ
  have hΩo : IsOpen Ω := isOpen_lt Complex.continuous_re continuous_const
  have hint : ∀ b ∈ Ω, IntegrableOn
      (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-b-1/2)/(x^2+t^2:ℂ)*pcfU b t) (Ioi 0) := by
    intro b hb
    obtain ⟨V, hV, g, hg, hle⟩ := pcfCt_integral_3_dom (a0 := b) hb hx
    refine Integrable.mono' hg ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
      intro t ht
      have ht : (0:ℝ) < t := ht
      refine ContinuousAt.continuousWithinAt ?_
      have hden : ((x:ℂ)^2 + (t:ℂ)^2) ≠ 0 := by
        rw [show ((x:ℂ)^2+(t:ℂ)^2) = ((x^2+t^2 : ℝ) : ℂ) by push_cast; ring]
        exact_mod_cast (by positivity : (0:ℝ) < x^2+t^2).ne'
      have hcp : ContinuousAt (fun s : ℝ => (s:ℂ)^(-b-1/2)) t :=
        Complex.continuous_ofReal.continuousAt.cpow continuousAt_const
          (Complex.ofReal_mem_slitPlane.mpr ht)
      have hU : ContinuousAt (fun s : ℝ => pcfU b s) t :=
        ((pcfU_entire b).continuous.comp Complex.continuous_ofReal).continuousAt
      exact (((by fun_prop : Continuous fun s : ℝ => exp (-(s:ℂ)^2/4)).continuousAt.mul hcp).div
        (by fun_prop) hden).mul hU
    · exact (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht => hle t ht b (mem_of_mem_nhds hV))
  refine ⟨hint a ha, ?_⟩
  set Λ : ℂ → ℂ := fun b => ∫ t in Ioi (0:ℝ),
    exp (-t^2/4)*(t:ℂ)^(-b-1/2)/(x^2+t^2:ℂ)*pcfU b t
  set R : ℂ → ℂ := fun b =>
    (Real.sqrt (π/2):ℂ)*Gamma (1/2-b)*(x:ℂ)^(-b-3/2)*exp (x^2/4)*pcfU (-b) x
  have hΛ : DifferentiableOn ℂ Λ Ω := by
    refine differentiableOn_integral_of_locally_dominated hΩo
      (fun b hb => (hint b hb).aestronglyMeasurable) ?_ ?_
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
      have ht : (0:ℝ) < t := ht
      have htc : (t:ℂ) ≠ 0 := by exact_mod_cast ht.ne'
      refine Differentiable.differentiableOn ?_
      exact (((differentiable_const _).mul
        ((by fun_prop : Differentiable ℂ fun b : ℂ => -b-1/2).const_cpow (Or.inl htc))).div_const
        _).mul (pcfU_entire_order (t:ℂ))
    · intro b hb
      obtain ⟨V, hV, g, hg, hle⟩ := pcfCt_integral_3_dom (a0 := b) hb hx
      exact ⟨V, hV, g, hg, (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun t ht c hc => hle t ht c hc)⟩
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hR : DifferentiableOn ℂ R Ω := by
    intro b hb
    have hb : b.re < 1/2 := hb
    have hG : DifferentiableAt ℂ (fun c : ℂ => Gamma (1/2-c)) b := by
      refine (Complex.differentiableAt_Gamma _ ?_).comp b (by fun_prop)
      intro m hm
      have := congrArg Complex.re hm
      simp at this
      have : (0:ℝ) ≤ m := m.cast_nonneg
      linarith
    refine DifferentiableAt.differentiableWithinAt ?_
    exact ((((differentiableAt_const _).mul hG).mul
      ((by fun_prop : Differentiable ℂ fun c : ℂ => -c-3/2).const_cpow (Or.inl hxc) b)).mul
      (differentiableAt_const _)).mul
      ((pcfU_entire_order (x:ℂ)).comp (by fun_prop : Differentiable ℂ fun c : ℂ => -c) b)
  have h0 : (0:ℂ) ∈ Ω := by simp [hΩ]
  have hev : Λ =ᶠ[𝓝 (0:ℂ)] R := by
    filter_upwards [Metric.ball_mem_nhds (0:ℂ) (by norm_num : (0:ℝ) < 1/2)] with b hb
    have hb' : ‖b‖ < 1/2 := by simpa using hb
    have := abs_re_le_norm b
    exact (pcfCt_integral_3_strip (by linarith [neg_abs_le b.re]) (by linarith [le_abs_self b.re])
      hx).2
  exact (hΛ.analyticOnNhd hΩo).eqOn_of_preconnected_of_eventuallyEq (hR.analyticOnNhd hΩo)
    (convex_halfSpace_re_lt (1/2)).isPreconnected h0 hev ha

/-- pcf integral 3. -/
@[dlmf 12.12.E3]
theorem pcf_integral_3 {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) 0 ((Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x) := by
  obtain ⟨hI, hv⟩ := pcfCt_integral_3_all ha hx
  unfold HasIntegralAtTop
  rw [← hv]
  exact intervalIntegral_tendsto_integral_Ioi 0 hI tendsto_id

/-- pcf integral 4. -/
@[dlmf 12.12.E4]
theorem pcf_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => 2^(3/2:ℂ)/π*Gamma (1/2-a)*exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) 0 ((pcfU a z)^2+(pcfUBar a z)^2) := by
  sorry

end DLMF.Confluent
