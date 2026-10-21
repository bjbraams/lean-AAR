/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Relations
public import AAR.ParabolicCylinder.IntegralTools

/-!
# Cylinder real and contour integrals

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

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
  sorry

/-- pcfV horizontal integral. -/
@[dlmf 12.5.E7]
theorem pcfV_horizontal_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ u v : ℂ, HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) u ∧ HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) v ∧ u+v=pcfV a z := by
  sorry

/-- Hankel loop from negative infinity below the cut around zero to negative infinity above. -/
def pcfNegativeLoop (a z : ℂ) (r R : ℝ) : ℂ :=
  (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I))) + (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) - (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I)))

/-- pcfU hankel integral. -/
@[dlmf 12.5.E5]
theorem pcfU_hankel_integral {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R => Gamma (1/2-a)/(2*π*I)*exp (-z^2/4)*pcfNegativeLoop a z r R) atTop (𝓝 (pcfU a z)) := by
  sorry

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

/-- pcf integral 3. -/
@[dlmf 12.12.E3]
theorem pcf_integral_3 {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) 0 ((Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x) := by
  sorry

/-- pcf integral 4. -/
@[dlmf 12.12.E4]
theorem pcf_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => 2^(3/2:ℂ)/π*Gamma (1/2-a)*exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) 0 ((pcfU a z)^2+(pcfUBar a z)^2) := by
  sorry

end AAR.Confluent
