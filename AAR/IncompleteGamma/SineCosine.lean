/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.ExponentialIntegral
public import AAR.IncompleteGamma.SeriesRecurrences
public import AAR.IncompleteGamma.ExpIntegralAsymptotics

/-!
# Generalized sine and cosine integrals, DLMF §8.21

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Generalized lower sine integral on the logarithmic plane away from its parameter poles. -/
def genSinIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k+1 : ℂ)*w)/((2*k+a+1)*(2*k+1).factorial)

/-- Generalized lower cosine integral on the logarithmic plane away from its parameter poles. -/
def genCosIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k : ℂ)*w)/((2*k+a)*(2*k).factorial)

/-- Generalized upper sine integral, entire in a. -/
def genSinIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)-exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/(2*I)

/-- Generalized upper cosine integral, entire in a. -/
def genCosIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)+exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/2

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinInt (a z : ℂ) : ℂ :=
  genSinIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosInt (a z : ℂ) : ℂ :=
  genCosIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinIntTail (a z : ℂ) : ℂ :=
  genSinIntTailOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosIntTail (a z : ℂ) : ℂ :=
  genCosIntTailOnLog a (log z)

/-- genUpperTrig gamma. -/
@[dlmf 8.21.E1]
theorem genUpperTrig_gamma (a w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntTailOnLog a w+ε*I*genSinIntTailOnLog a w=exp (ε*π*I*a/2)*upperIncGammaOnLog a (w-ε*π*I/2) := by
  rcases hε with rfl | rfl <;>
    simp only [genCosIntTailOnLog,genSinIntTailOnLog,Complex.ofReal_one,Complex.ofReal_neg,
      neg_mul,one_mul,sub_neg_eq_add,neg_neg]
  all_goals field_simp; ring_nf

/-- genSinIntTail parameter entire. -/
theorem genSinIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genSinIntTailOnLog a w) := by
  have h1 := upperIncGammaOnLog_parameter_entire (w-π*I/2)
  have h2 := upperIncGammaOnLog_parameter_entire (w+π*I/2)
  exact (((by fun_prop : Differentiable ℂ fun a : ℂ => exp (π*I*a/2)).mul h1).sub
    ((by fun_prop : Differentiable ℂ fun a : ℂ => exp (-π*I*a/2)).mul h2)).div_const (2*I)

/-- genCosIntTail parameter entire. -/
theorem genCosIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genCosIntTailOnLog a w) := by
  have h1 := upperIncGammaOnLog_parameter_entire (w-π*I/2)
  have h2 := upperIncGammaOnLog_parameter_entire (w+π*I/2)
  exact (((by fun_prop : Differentiable ℂ fun a : ℂ => exp (π*I*a/2)).mul h1).add
    ((by fun_prop : Differentiable ℂ fun a : ℂ => exp (-π*I*a/2)).mul h2)).div_const 2

/-- genSinInt parameter analytic. -/
theorem genSinInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genSinIntOnLog b w) a := by
  sorry

/-- genCosInt parameter analytic. -/
theorem genCosInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genCosIntOnLog b w) a := by
  sorry

/-- genSinInt parameter residue. -/
theorem genSinInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+(2*n+1))*genSinIntOnLog a w) (𝓝[≠] (-(2*n+1 : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n+1).factorial)) := by
  sorry

/-- genCosInt parameter residue. -/
theorem genCosInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+2*n)*genCosIntOnLog a w) (𝓝[≠] (-(2*n : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n).factorial)) := by
  sorry

/-- `Γ(a, ε i (z+t)) → 0` along horizontal rays when `re a < 1`. -/
theorem tendsto_upperIncGamma_mul_I_add_ofReal {a : ℂ} (ha : a.re < 1) (z : ℂ) {ε : ℝ}
    (hε : ε=1 ∨ ε = -1) :
    Tendsto (fun t : ℝ => upperIncGamma a (ε*I*(z+t))) atTop (𝓝 0) := by
  have hβ : |-ε*(π/4)| < π/2 := by
    rcases hε with rfl | rfl <;> simp [abs_of_pos (by positivity : (0:ℝ) < π/4)] <;> linarith [Real.pi_pos]
  have hr := tendsto_mul_I_add_ofReal_rotSectorAtTop z hε
  have hU := (tendsto_kummerU_rotSectorAtTop (a := 1-a) (1-a) (by simp; linarith) (by norm_num) hβ).comp hr
  have hU' := hU.norm.mul_const (Real.exp (ε*z.im))
  rw [norm_zero, zero_mul] at hU'
  refine squeeze_zero_norm' (Eventually.of_forall fun t => ?_) hU'
  rw [upperIncGamma, norm_mul, Complex.norm_exp, Function.comp_apply, mul_comm]
  apply le_of_eq
  congr 2
  rcases hε with rfl | rfl <;> simp

/-- A quarter turn down on the logarithmic plane. -/
lemma exp_sub_pi_I_half (w : ℂ) : exp (w-π*I/2) = -I*exp w := by
  rw [Complex.exp_sub, show (π:ℂ)*I/2 = (π/2:ℂ)*I by ring, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  field_simp

/-- A quarter turn up on the logarithmic plane. -/
lemma exp_add_pi_I_half (w : ℂ) : exp (w+π*I/2) = I*exp w := by
  rw [Complex.exp_add, show (π:ℂ)*I/2 = (π/2:ℂ)*I by ring, Complex.exp_mul_I]
  simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
  ring

/-- Derivatives of the generalized sine and cosine tails on the logarithmic plane. -/
theorem hasDerivAt_genTrigTailOnLog (a w : ℂ) :
    HasDerivAt (genSinIntTailOnLog a) (-exp (a*w)*sin (exp w)) w ∧
    HasDerivAt (genCosIntTailOnLog a) (-exp (a*w)*cos (exp w)) w := by
  have h1 := ((hasDerivAt_upperIncGammaOnLog a (w-π*I/2)).comp w ((hasDerivAt_id w).sub_const _)).const_mul
    (exp (π*I*a/2))
  have h2 := ((hasDerivAt_upperIncGammaOnLog a (w+π*I/2)).comp w ((hasDerivAt_id w).add_const _)).const_mul
    (exp (-π*I*a/2))
  have e1 : exp (π*I*a/2)*exp (a*(w-π*I/2)-exp (w-π*I/2)) = exp (a*w)*exp (I*exp w) := by
    rw [exp_sub_pi_I_half, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have e2 : exp (-π*I*a/2)*exp (a*(w+π*I/2)-exp (w+π*I/2)) = exp (a*w)*exp (-(I*exp w)) := by
    rw [exp_add_pi_I_half, ← Complex.exp_add, ← Complex.exp_add]; ring_nf
  have hs : sin (exp w) = (exp (-(exp w)*I)-exp (exp w*I))*I/2 := rfl
  have hc : cos (exp w) = (exp (exp w*I)+exp (-(exp w)*I))/2 := rfl
  constructor
  · refine ((h1.sub h2).div_const (2*I)).congr_deriv ?_
    simp only [id, Function.comp_apply, mul_one]
    rw [hs, mul_neg, mul_neg, e1, e2]
    field_simp
    ring_nf; rw [I_sq]; ring
  · refine ((h1.add h2).div_const 2).congr_deriv ?_
    simp only [id, Function.comp_apply, mul_one]
    rw [hc, mul_neg, mul_neg, e1, e2]
    ring_nf

/-- Derivatives of the principal generalized sine and cosine tails on the slit plane. -/
theorem hasDerivAt_genTrigTail (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (genSinIntTail a) (-z^(a-1)*sin z) z ∧
    HasDerivAt (genCosIntTail a) (-z^(a-1)*cos z) z := by
  have hz0 := slitPlane_ne_zero hz
  have hl := Complex.hasDerivAt_log hz
  have hp : exp (a*log z)*z⁻¹ = z^(a-1) := by
    rw [cpow_sub _ _ hz0, cpow_one, cpow_def_of_ne_zero hz0, mul_comm a, div_eq_mul_inv]
  obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTailOnLog a (log z)
  constructor
  · refine (hS.comp z hl).congr_deriv ?_
    rw [Complex.exp_log hz0, ← hp]; ring
  · refine (hC.comp z hl).congr_deriv ?_
    rw [Complex.exp_log hz0, ← hp]; ring

/-- Away from the cut the generalized tails are combinations of principal upper Gamma values. -/
theorem genTrigTail_eq_upperIncGamma (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genSinIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z)-exp (-π*I*a/2)*upperIncGamma a (I*z))/(2*I) ∧
    genCosIntTail a z = (exp (π*I*a/2)*upperIncGamma a (-I*z)+exp (-π*I*a/2)*upperIncGamma a (I*z))/2 := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have ha := abs_lt.mp (Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz))
  have hm : upperIncGammaOnLog a (log z-π*I/2) = upperIncGamma a (-I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma, exp_sub_pi_I_half, Complex.exp_log hz0]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
  have hp : upperIncGammaOnLog a (log z+π*I/2) = upperIncGamma a (I*z) := by
    rw [upperIncGammaOnLog_eq_upperIncGamma, exp_add_pi_I_half, Complex.exp_log hz0]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
    · simp [Complex.log_im]; linarith [Real.pi_pos]
  simp only [genSinIntTail, genCosIntTail, genSinIntTailOnLog, genCosIntTailOnLog, hm, hp]
  exact ⟨trivial, trivial⟩

/-- Both generalized tails tend to zero along horizontal rays when `re a < 1`. -/
theorem tendsto_genTrigTail_add_ofReal {a : ℂ} (ha : a.re < 1) (z : ℂ) :
    Tendsto (fun t : ℝ => genSinIntTail a (z+t)) atTop (𝓝 0) ∧
    Tendsto (fun t : ℝ => genCosIntTail a (z+t)) atTop (𝓝 0) := by
  have hm := (tendsto_upperIncGamma_mul_I_add_ofReal ha z (ε := -1) (Or.inr rfl)).const_mul (exp (π*I*a/2))
  have hp := (tendsto_upperIncGamma_mul_I_add_ofReal ha z (ε := 1) (Or.inl rfl)).const_mul (exp (-π*I*a/2))
  rw [mul_zero] at hm hp
  constructor
  · have h := (hm.sub hp).div_const (2*I)
    rw [sub_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_re_add_ofReal_pos z] with t ht
    rw [(genTrigTail_eq_upperIncGamma a ht).1]; push_cast; ring_nf
  · have h := (hm.add hp).div_const 2
    rw [add_zero, zero_div] at h
    refine h.congr' ?_
    filter_upwards [eventually_re_add_ofReal_pos z] with t ht
    rw [(genTrigTail_eq_upperIncGamma a ht).2]; push_cast; ring_nf

/-- gamma rotated oscillatory integral. -/
@[dlmf 8.21.E3]
theorem gamma_rotated_oscillatory_integral {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a) := by
  sorry

/-- genSinIntTail horizontal integral. -/
@[dlmf 8.21.E4]
theorem genSinIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*sin (z+t)) 0 (genSinIntTail a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genSinIntTail a (z+t)) ((z+t)^(a-1)*sin (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genSinIntTail a w)
      (hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)).1.neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => (z+t)^(a-1)*sin (z+t)) (Ici 0) := by
    refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
    exact ((continuousAt_const.add continuous_ofReal.continuousAt).cpow continuousAt_const
      (add_ofReal_mem_slitPlane hz ht)).continuousWithinAt
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_genTrigTail_add_ofReal ha z).1.neg
  simpa using h

/-- genCosIntTail horizontal integral. -/
@[dlmf 8.21.E5]
theorem genCosIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*cos (z+t)) 0 (genCosIntTail a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -genCosIntTail a (z+t)) ((z+t)^(a-1)*cos (z+t)) t := by
    intro t ht
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -genCosIntTail a w)
      (hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)).2.neg).congr_deriv ?_
    ring
  have hc : ContinuousOn (fun t : ℝ => (z+t)^(a-1)*cos (z+t)) (Ici 0) := by
    refine ContinuousOn.mul (fun t ht => ?_) (by fun_prop)
    exact ((continuousAt_const.add continuous_ofReal.continuousAt).cpow continuousAt_const
      (add_ofReal_mem_slitPlane hz ht)).continuousWithinAt
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc (tendsto_genTrigTail_add_ofReal ha z).2.neg
  simpa using h

/-- Γ(a)sin(πa/2), with removable even-integer singularities filled by limits. -/
def gammaSinHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*sin (π*b/2))

/-- Γ(a)cos(πa/2), with removable odd-integer singularities filled by limits. -/
def gammaCosHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*cos (π*b/2))

/-- genSinInt complement. -/
@[dlmf 8.21.E8]
theorem genSinInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z=gammaSinHalfPiContinued a-genSinIntTail a z := by
  sorry

/-- genCosInt complement. -/
@[dlmf 8.21.E9]
theorem genCosInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z=gammaCosHalfPiContinued a-genCosIntTail a z := by
  sorry

/-- Ein at the negative rotated argument, by the parities of Cin and Si. -/
lemma expIntEin_neg_mul_I_eq (z : ℂ) : expIntEin (-I*z)=cosIntCin z-I*sinInt z := by
  have h := expIntEin_mul_I (-z)
  rw [show I*(-z)=-I*z by ring, cosIntCin_even, sinInt_odd] at h
  rw [h]; ring

/-- genTrig order zero. -/
@[dlmf 8.21.E10]
theorem genTrig_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinIntTail 0 z = -sinIntTail z ∧ genCosIntTail 0 z = -cosInt z := by
  have h1 : exp (log z-π*I/2)=-I*z := by
    rw [Complex.exp_sub, Complex.exp_log hz, show (π:ℂ)*I/2=(π/2:ℂ)*I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    field_simp
  have h2 : exp (log z+π*I/2)=I*z := by
    rw [Complex.exp_add, Complex.exp_log hz, show (π:ℂ)*I/2=(π/2:ℂ)*I by ring,
      Complex.exp_mul_I]
    simp [Complex.cos_pi_div_two, Complex.sin_pi_div_two]
    ring
  simp only [genSinIntTail, genCosIntTail, genSinIntTailOnLog, genCosIntTailOnLog, mul_zero,
    zero_div, Complex.exp_zero, one_mul, upperIncGammaOnLog_zero, h1, h2, expIntEin_mul_I,
    expIntEin_neg_mul_I_eq, sinIntTail, cosInt]
  constructor
  · field_simp; ring_nf
  · ring

/-- genSinInt order zero. -/
@[dlmf 8.21.E11]
theorem genSinInt_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinInt 0 z=sinInt z := by
  simp only [genSinInt,genSinIntOnLog,zero_mul,Complex.exp_zero,one_mul,add_zero]
  unfold sinInt
  apply tsum_congr
  intro k
  rw [show (2*k+1:ℂ)*log z=((2*k+1:ℕ):ℂ)*log z by push_cast; ring,Complex.exp_nat_mul,Complex.exp_log hz]
  ring

/-- Ordinary infinity limits need Re a<1; other values are interpreted by parameter continuation. -/
@[dlmf 8.21.E12]
theorem genSinInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genSinInt a x) atTop (𝓝 (gammaSinHalfPiContinued a)) := by
  sorry

/-- genCosInt value at infinity. -/
@[dlmf 8.21.E13]
theorem genCosInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genCosInt a x) atTop (𝓝 (gammaCosHalfPiContinued a)) := by
  sorry

/-- Factorial decay controls the generalized trigonometric coefficients for every parameter;
totalized exceptional terms affect only finitely many coefficients. -/
theorem summable_genTrig_coeff (a z : ℂ) (ε : ℕ) :
    Summable (fun n : ℕ => (-1:ℂ)^n*z^(2*n+ε)/((2*n+ε).factorial*((2*n+ε:ℕ)+a))) := by
  have hd : Function.Injective (fun n : ℕ => 2*n+ε) := by intro n m h; dsimp only at h; omega
  apply Summable.of_norm_bounded_eventually_nat
    ((Real.summable_pow_div_factorial ‖z‖).comp_injective hd)
  obtain ⟨N,hN⟩ := exists_nat_gt (1+|a.re|)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnr : (N:ℝ)≤n := by exact_mod_cast hn
  have he0 : (0:ℝ)≤ε := by positivity
  have hb : 1≤‖((2*n+ε:ℕ):ℂ)+a‖ := by
    calc
      1 ≤ (((2*n+ε:ℕ):ℂ)+a).re := by
        rw [add_re,Complex.natCast_re]
        push_cast
        linarith [le_abs_self (-a.re),abs_neg a.re]
      _ ≤ ‖((2*n+ε:ℕ):ℂ)+a‖ := Complex.re_le_norm _
  rw [norm_div,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_pow,Complex.norm_natCast]
  calc
    ‖z‖^(2*n+ε)/((2*n+ε).factorial*‖((2*n+ε:ℕ):ℂ)+a‖)
      ≤ ‖z‖^(2*n+ε)/((2*n+ε).factorial*1) := by gcongr
    _ = _ := by simp only [Function.comp_apply,mul_one]

/-- The logarithmic cosine series is absolutely convergent at every logarithmic argument. -/
theorem genCosIntOnLog_hasSum (a w : ℂ) :
    HasSum (fun k : ℕ=>exp (a*w)*(-1:ℂ)^k*(exp w)^(2*k)/
      ((2*k+a)*(2*k).factorial)) (genCosIntOnLog a w) := by
  have hs := (summable_genTrig_coeff a (exp w) 0).hasSum.mul_left (exp (a*w))
  have he (k : ℕ) : exp ((2*k:ℂ)*w)=(exp w)^(2*k) := by
    rw [show (2*k:ℂ)=((2*k:ℕ):ℂ) by push_cast; ring,exp_nat_mul]
  unfold genCosIntOnLog
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- The logarithmic sine series is absolutely convergent at every logarithmic argument. -/
theorem genSinIntOnLog_hasSum (a w : ℂ) :
    HasSum (fun k : ℕ=>exp (a*w)*(-1:ℂ)^k*(exp w)^(2*k+1)/
      ((2*k+a+1)*(2*k+1).factorial)) (genSinIntOnLog a w) := by
  have hs := (summable_genTrig_coeff a (exp w) 1).hasSum.mul_left (exp (a*w))
  have he (k : ℕ) : exp ((2*k+1:ℂ)*w)=(exp w)^(2*k+1) := by
    rw [show (2*k+1:ℂ)=((2*k+1:ℕ):ℂ) by push_cast; ring,exp_nat_mul]
  unfold genSinIntOnLog
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- genLowerTrig gamma. -/
@[dlmf 8.21.E2]
theorem genLowerTrig_gamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntOnLog a w+ε*I*genSinIntOnLog a w=exp (ε*π*I*a/2)*lowerIncGammaOnLog a (w-ε*π*I/2) := by
  have ht : ((ε:ℂ)*I)^2= -1 := by
    rcases hε with rfl | rfl <;> norm_num [Complex.I_sq]
  have he : -exp (w-ε*π*I/2)=((ε:ℂ)*I)*exp w := by
    rw [sub_eq_add_neg,exp_add]
    rcases hε with rfl | rfl
    · simp only [ofReal_one,one_mul]
      rw [show -(π*I/2)= -π/2*I by ring,exp_neg_pi_div_two_mul_I]
      ring
    · simp only [ofReal_neg,ofReal_one,neg_mul,one_mul,neg_neg]
      rw [show -(-(π*I)/2)=π/2*I by ring,exp_pi_div_two_mul_I]
      ring
  let f : ℕ→ℂ := fun k=>exp (a*w)*((ε:ℂ)*I)^k*(exp w)^k/
    ((a+k)*(k.factorial:ℂ))
  have hce : HasSum (fun k=>f (2*k)) (genCosIntOnLog a w) := by
    refine (genCosIntOnLog_hasSum a w).congr_fun fun k=>?_
    dsimp [f]
    rw [pow_mul,ht]
    push_cast
    ring
  have hso : HasSum (fun k=>f (2*k+1)) (ε*I*genSinIntOnLog a w) := by
    refine ((genSinIntOnLog_hasSum a w).mul_left (ε*I)).congr_fun fun k=>?_
    dsimp [f]
    rw [pow_succ,pow_mul,ht]
    push_cast
    ring
  have hs := (scIncGamma_hasSum_alternating ha (exp (w-ε*π*I/2))).mul_left
    (Gamma a*exp (a*w))
  have hfull : HasSum f (Gamma a*exp (a*w)*AAR.Statistical.scIncGamma a (exp (w-ε*π*I/2))) := by
    refine hs.congr_fun fun k=>?_
    dsimp [f]
    rw [he,mul_pow]
    field_simp [Gamma_ne_zero ha]
    simp only [mul_pow]
  have hsum := (hce.even_add_odd hso).unique hfull
  rw [hsum,lowerIncGammaOnLog]
  have hp : exp (a*w)=exp (ε*π*I*a/2)*exp (a*(w-ε*π*I/2)) := by
    rw [←exp_add]
    congr 1
    ring
  rw [hp]
  ring

/-- genSinInt hasSum. -/
@[dlmf 8.21.E14]
theorem genSinInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k+1)/((2*k+a+1)*(2*k+1).factorial)) (genSinInt a z) := by
  have hs := (summable_genTrig_coeff a z 1).hasSum.mul_left (z^a)
  have he (k : ℕ) : exp ((2*k+1:ℂ)*log z)=z^(2*k+1) := by
    rw [show (2*k+1:ℂ)*log z=((2*k+1:ℕ):ℂ)*log z by push_cast; ring,
      Complex.exp_nat_mul,Complex.exp_log hz]
  rw [genSinInt,genSinIntOnLog]
  rw [show exp (a*log z)=z^a by rw [cpow_def_of_ne_zero hz]; congr 1; ring]
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- genCosInt hasSum. -/
@[dlmf 8.21.E15]
theorem genCosInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k)/((2*k+a)*(2*k).factorial)) (genCosInt a z) := by
  have hs := (summable_genTrig_coeff a z 0).hasSum.mul_left (z^a)
  have he (k : ℕ) : exp ((2*k+0:ℂ)*log z)=z^(2*k+0) := by
    rw [show (2*k+0:ℂ)*log z=((2*k+0:ℕ):ℂ)*log z by push_cast; ring,
      Complex.exp_nat_mul,Complex.exp_log hz]
  rw [genCosInt,genCosIntOnLog]
  rw [show exp (a*log z)=z^a by rw [cpow_def_of_ne_zero hz]; congr 1; ring]
  simp only [Nat.add_zero] at hs he
  simp only [add_zero] at he
  simp_rw [he]
  convert hs using 1
  · funext k
    push_cast
    ring
  · congr 1
    apply tsum_congr
    intro k
    push_cast
    ring

/-- Termwise integration of `∑ t^{s+2k} c_k` over `[0,1]`. -/
lemma hasSum_integral_cpow_two_mul {s : ℂ} (hs : -1 < s.re) {c : ℕ → ℂ}
    (hc : Summable fun k => ‖c k‖) :
    HasSum (fun k : ℕ => c k/(s+2*k+1))
      (∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(s+2*k)*c k) := by
  have hb : ∀ k : ℕ, ∀ t : ℝ, t ∈ Set.uIoc (0:ℝ) 1 → ‖(t:ℂ)^(s+2*k)*c k‖ ≤ t^s.re*‖c k‖ := by
    intro k t ht
    rw [Set.uIoc_of_le zero_le_one] at ht
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos ht.1]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 ?_
    simp
  have hsum := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume)
    (a := 0) (b := 1) (F := fun (k : ℕ) (t:ℝ) => (t:ℂ)^(s+2*k)*c k)
    (f := fun t : ℝ => ∑' k : ℕ, (t:ℂ)^(s+2*k)*c k)
    (fun (k : ℕ) (t : ℝ) => t^s.re*‖c k‖)
    (fun k => ((Complex.measurable_ofReal.pow_const _).mul_const _).aestronglyMeasurable)
    (fun k => Eventually.of_forall fun t ht => hb k t ht)
    (Eventually.of_forall fun t _ => hc.mul_left _)
    (by
      simp_rw [tsum_mul_left]
      exact (intervalIntegral.intervalIntegrable_rpow' hs).mul_const _)
    (Eventually.of_forall fun t ht => (Summable.of_norm_bounded (hc.mul_left (t^s.re))
      (fun k => hb k t ht)).hasSum)
  refine hsum.congr_fun fun k => ?_
  have hre : -1 < (s+2*k).re := by simp; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne : s+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  rw [intervalIntegral.integral_mul_const, integral_cpow (Or.inl hre)]
  simp only [ofReal_one, one_cpow, ofReal_zero, zero_cpow hne]
  field_simp
  ring

/-- genSinInt segment integral. -/
@[dlmf 8.21.E6]
theorem genSinInt_segment_integral {a : ℂ} (ha : -1 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genSinInt a z=primitive (fun t => t^(a-1)*sin t) z := by
  have hz0 := slitPlane_ne_zero hz
  set c : ℕ → ℂ := fun k => z^(a-1)*((-1:ℂ)^k*z^(2*k+1)/((2*k+1).factorial : ℂ))
  have hc : Summable fun k => ‖c k‖ := by
    have h := ((Real.summable_pow_div_factorial ‖z‖).comp_injective
      (strictMono_nat_of_lt_succ (f := fun k : ℕ => 2*k+1) (fun k => by omega)).injective).mul_left
      ‖z^(a-1)‖
    refine h.congr fun k => ?_
    simp [c]
  have hI := hasSum_integral_cpow_two_mul ha hc
  have hint : (∫ t : ℝ in (0:ℝ)..1, (0+(t:ℂ)*(z-0))^(a-1)*sin (0+(t:ℂ)*(z-0))) =
      ∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(a+2*k)*c k := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    rw [zero_add, sub_zero, ofReal_mul_cpow_of_pos ht.1 hz0, ← (Complex.hasSum_sin _).tsum_eq,
      ← tsum_mul_left]
    congr 1; funext k
    simp only [c]
    rw [mul_pow, show a+2*(k:ℂ) = (a-1) + ((2*k+1 : ℕ) : ℂ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_natCast]
    ring
  rw [primitive, segmentIntegral, hint, ← hI.tsum_eq, sub_zero, ← tsum_mul_left,
    ← (genSinInt_hasSum (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz0).tsum_eq]
  congr 1; funext k
  have hza : z ^ a = z * z ^ (a-1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  simp only [c]
  rw [hza]
  have hne : a+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne' : 2*k+a+1 ≠ 0 := by rw [show 2*(k:ℂ)+a+1 = a+2*k+1 by ring]; exact hne
  have hf : ((2*k+1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  ring

/-- genCosInt segment integral. -/
@[dlmf 8.21.E7]
theorem genCosInt_segment_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genCosInt a z=primitive (fun t => t^(a-1)*cos t) z := by
  have hz0 := slitPlane_ne_zero hz
  set c : ℕ → ℂ := fun k => z^(a-1)*((-1:ℂ)^k*z^(2*k)/((2*k).factorial : ℂ))
  have hc : Summable fun k => ‖c k‖ := by
    have h := ((Real.summable_pow_div_factorial ‖z‖).comp_injective
      (strictMono_nat_of_lt_succ (f := fun k : ℕ => 2*k) (fun k => by omega)).injective).mul_left
      ‖z^(a-1)‖
    refine h.congr fun k => ?_
    simp [c]
  have hI := hasSum_integral_cpow_two_mul (s := a-1) (by simp; linarith) hc
  have hint : (∫ t : ℝ in (0:ℝ)..1, (0+(t:ℂ)*(z-0))^(a-1)*cos (0+(t:ℂ)*(z-0))) =
      ∫ t : ℝ in (0:ℝ)..1, ∑' k : ℕ, (t:ℂ)^(a-1+2*k)*c k := by
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
    rw [Set.uIoc_of_le zero_le_one] at ht
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
    rw [zero_add, sub_zero, ofReal_mul_cpow_of_pos ht.1 hz0, ← (Complex.hasSum_cos _).tsum_eq,
      ← tsum_mul_left]
    congr 1; funext k
    simp only [c]
    rw [mul_pow, show a-1+2*(k:ℂ) = (a-1) + ((2*k : ℕ) : ℂ) by push_cast; ring, cpow_add _ _ ht0,
      cpow_natCast]
    ring
  rw [primitive, segmentIntegral, hint, ← hI.tsum_eq, sub_zero, ← tsum_mul_left,
    ← (genCosInt_hasSum (fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]) hz0).tsum_eq]
  congr 1; funext k
  have hza : z ^ a = z * z ^ (a-1) := by
    conv_lhs => rw [show a = 1 + (a - 1) by ring]
    rw [Complex.cpow_add _ _ hz0, Complex.cpow_one]
  simp only [c]
  rw [hza]
  have hne : a-1+2*k+1 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hne' : 2*k+a ≠ 0 := by rw [show 2*(k:ℂ)+a = a-1+2*k+1 by ring]; exact hne
  have hf : ((2*k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp
  ring

/-- genSinInt spherical series. -/
@[dlmf 8.21.E16]
theorem genSinInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1)*sphericalJ (2*k+1) z) (genSinInt a z) := by
  sorry

/-- genCosInt spherical series. -/
@[dlmf 8.21.E17]
theorem genCosInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1)*sphericalJ (2*k) z) (genCosInt a z) := by
  sorry

/-- Generalized auxiliary f. -/
@[dlmf 8.21.E18]
def genTrigAuxF (a z : ℂ) : ℂ :=
  genSinIntTail a z*cos z-genCosIntTail a z*sin z

/-- Generalized auxiliary g. -/
@[dlmf 8.21.E19]
def genTrigAuxG (a z : ℂ) : ℂ :=
  genSinIntTail a z*sin z+genCosIntTail a z*cos z

/-- genSinIntTail aux. -/
@[dlmf 8.21.E20]
theorem genSinIntTail_aux (a z : ℂ) :
    genSinIntTail a z=genTrigAuxF a z*cos z+genTrigAuxG a z*sin z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genSinIntTail a z*h

/-- genCosIntTail aux. -/
@[dlmf 8.21.E21]
theorem genCosIntTail_aux (a z : ℂ) :
    genCosIntTail a z = -genTrigAuxF a z*sin z+genTrigAuxG a z*cos z := by
  unfold genTrigAuxF genTrigAuxG
  have h := Complex.sin_sq_add_cos_sq z
  linear_combination -genCosIntTail a z*h

/-- genTrigAuxF oscillatory integral. -/
@[dlmf 8.21.E22]
theorem genTrigAuxF_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin t*(t+z)^(a-1)) 0 (genTrigAuxF a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t))
      (sin t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -cos z*genSinIntTail a w+sin z*genCosIntTail a w)
      ((hS.const_mul _).add (hC.const_mul _))).congr_deriv ?_
    have hs : sin (t:ℂ) = sin (z+t)*cos z-cos (z+t)*sin z := by rw [← Complex.sin_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => sin t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -cos z*genSinIntTail a (z+t)+sin z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-cos z)).add (h2.const_mul (sin z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxF]; ring

/-- genTrigAuxG oscillatory integral. -/
@[dlmf 8.21.E23]
theorem genTrigAuxG_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos t*(t+z)^(a-1)) 0 (genTrigAuxG a z) := by
  have hd : ∀ t : ℝ, 0 ≤ t → HasDerivAt (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t))
      (cos t*(t+z)^(a-1)) t := by
    intro t ht
    obtain ⟨hS, hC⟩ := hasDerivAt_genTrigTail a (add_ofReal_mem_slitPlane hz ht)
    refine (hasDerivAt_comp_add_ofReal (g := fun w => -sin z*genSinIntTail a w-cos z*genCosIntTail a w)
      ((hS.const_mul _).sub (hC.const_mul _))).congr_deriv ?_
    have hs : cos (t:ℂ) = cos (z+t)*cos z+sin (z+t)*sin z := by rw [← Complex.cos_sub]; ring_nf
    rw [hs, add_comm (t:ℂ) z]
    ring
  have hc : ContinuousOn (fun t : ℝ => cos t*(t+z)^(a-1)) (Ici 0) := by
    refine ContinuousOn.mul (by fun_prop) (fun t ht => ?_)
    have := add_ofReal_mem_slitPlane hz ht
    rw [add_comm] at this
    exact ((continuous_ofReal.continuousAt.add continuousAt_const).cpow continuousAt_const
      this).continuousWithinAt
  have hl : Tendsto (fun t : ℝ => -sin z*genSinIntTail a (z+t)-cos z*genCosIntTail a (z+t)) atTop (𝓝 0) := by
    obtain ⟨h1, h2⟩ := tendsto_genTrigTail_add_ofReal ha z
    simpa using (h1.const_mul (-sin z)).sub (h2.const_mul (cos z))
  have h := hasIntegralAtTop_of_hasDerivAt_of_tendsto hd hc hl
  convert h using 1
  simp [genTrigAuxG]; ring

/-- genTrigAuxF laplace integral. -/
@[dlmf 8.21.E24]
theorem genTrigAuxF_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) := by
  sorry

/-- genTrigAuxG laplace integral. -/
@[dlmf 8.21.E25]
theorem genTrigAuxG_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) := by
  sorry

/-- `e^{e^w} Γ(a, e^w) ~ ∑ (-1)^k (1-a)_k e^{(a-1-k) w}` on the logarithmic sector
`|im w| ≤ 3π/2 - δ` (DLMF 8.11.2 continued to the logarithmic plane). -/
theorem upperIncGammaOnLog_logSector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun (k : ℕ) w => exp ((a-1-k)*w))
      (fun k => (-1 : ℂ)^k*poch (1-a) k) (fun w => exp (exp w) * upperIncGammaOnLog a w) := by
  have h := (genExpIntE_log_sector_asymptotic (1-a) hδ hδ1).mul_left (fun w => exp (a*w + exp w))
  have hφ : (fun (k : ℕ) (w : ℂ) => exp (a*w + exp w) * exp (-exp w-(k+1 : ℂ)*w)) =
      fun (k : ℕ) w => exp ((a-1-k)*w) := by
    funext k w; rw [← Complex.exp_add]; congr 1; ring
  have hf : (fun w => exp (a*w + exp w) • genExpIntEOnLog (1-a) w) =
      fun w => exp (exp w) * upperIncGammaOnLog a w := by
    funext w
    rw [smul_eq_mul, genExpIntEOnLog, show (1:ℂ) - (1 - a) = a by ring, ← mul_assoc,
      ← Complex.exp_add]
    congr 2; ring
  rw [hφ, hf] at h
  exact h

/-- `z ↦ log z + iπ s/2` (`s = ±1`) maps `|arg z| ≤ π - δ` into the logarithmic sector
`|im w| ≤ 3π/2 - δ`, uniformly towards infinity. -/
lemma tendsto_log_add_sector {s : ℝ} (hs : |s| ≤ 1) {δ : ℝ} :
    Tendsto (fun z : ℂ => log z + s*π*I/2) (sector (π-δ)) (logSector (3*π/2-δ)) := by
  unfold sector logSector
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · refine (tendsto_comap.mono_left inf_le_left).congr' ?_
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, -⟩ := hz
    simp only [Function.comp, add_re, log_re]
    simp [Real.exp_log (norm_pos_iff.mpr hz0)]
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨-, hza⟩ := hz
    show |(log z + s*π*I/2).im| ≤ 3*π/2-δ
    have him : (log z + s*π*I/2).im = arg z + s*π/2 := by simp [log_im]
    rw [him]
    have h1 := abs_le.mp hza
    have h2 := abs_le.mp hs
    rw [abs_le]; constructor <;> nlinarith [Real.pi_pos]

/-- `exp(s π i/2) = s i` for `s = ±1`. -/
lemma exp_sign_mul_pi_div_two_mul_I {s : ℝ} (hs : s = 1 ∨ s = -1) :
    exp ((s : ℂ) * π * I / 2) = s * I := by
  rcases hs with rfl | rfl
  · push_cast; rw [show (1:ℂ) * π * I / 2 = π / 2 * I by ring, exp_pi_div_two_mul_I]; ring
  · push_cast; rw [show (-1:ℂ) * π * I / 2 = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]; ring

/-- One exponential piece of the generalized auxiliary functions:
`e^{-sπia/2} e^{siz} Γ(a, z e^{sπi/2}) ~ ∑ e^{-s(k+1)πi/2} (-1)^k (1-a)_k z^{a-1-k}` (`s = ±1`)
in the sector `|arg z| ≤ π - δ`. -/
theorem upperIncGamma_rotated_piece_asymptotic (a : ℂ) {s : ℝ} (hs : s = 1 ∨ s = -1) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun (k : ℕ) z => z^(a-1-k))
      (fun k => exp (-((s : ℂ)*(k+1)*π*I/2)) * ((-1 : ℂ)^k*poch (1-a) k))
      (fun z => exp (-((s : ℂ)*π*I*a/2)) * (exp ((s : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + s*π*I/2))) := by
  have hs1 : |s| ≤ 1 := by rcases hs with rfl | rfl <;> norm_num
  have hnz : ∀ᶠ z in sector (π-δ), z ≠ 0 := by
    filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    exact hz.1
  have h1 := (upperIncGammaOnLog_logSector_asymptotic a hδ (by linarith)).comp_tendsto
    (tendsto_log_add_sector hs1 (δ := δ))
  have h2 := h1.smul_scale (ψ := fun (k : ℕ) (z : ℂ) => z^(a-1-k))
    (κ := fun (k : ℕ) => exp ((a-1-k)*((s : ℂ)*π*I/2))) (fun k => by
      filter_upwards [hnz] with z hz0
      rw [cpow_def_of_ne_zero hz0, ← Complex.exp_add]; congr 1; ring)
  have h3 := h2.const_smul (exp (-((s : ℂ)*π*I*a/2)))
  refine (h3.congr' ?_).congr_coeff ?_
  · filter_upwards [hnz] with z hz0
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp]
    rw [Complex.exp_add, Complex.exp_log hz0, exp_sign_mul_pi_div_two_mul_I hs]
    congr 2; ring_nf
  · funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2; ring

/-- `exp(-s(k+1)πi/2) = (-s i)^{k+1}` for `s = ±1`. -/
lemma exp_neg_sign_mul_pi_div_two_mul_I_pow {s : ℝ} (hs : s = 1 ∨ s = -1) (k : ℕ) :
    exp (-((s : ℂ)*(k+1)*π*I/2)) = (-(s : ℂ) * I)^(k+1) := by
  have h := exp_sign_mul_pi_div_two_mul_I (s := -s) (by rcases hs with rfl | rfl <;> norm_num)
  rw [show -((s : ℂ)*(k+1)*π*I/2) = ((k+1 : ℕ) : ℂ) * (((-s : ℝ) : ℂ)*π*I/2) by push_cast; ring,
    Complex.exp_nat_mul, h]
  push_cast; ring

/-- The auxiliary functions in terms of the two exponential pieces. -/
lemma genTrigAux_eq_pieces (a z : ℂ) :
    genTrigAuxF a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) -
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / (2*I) ∧
    genTrigAuxG a z = (exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2)) +
      exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))) / 2 := by
  have e1 : log z + ((-1:ℝ) : ℂ)*π*I/2 = log z - π*I/2 := by push_cast; ring
  have e2 : log z + ((1:ℝ) : ℂ)*π*I/2 = log z + π*I/2 := by push_cast; ring
  have e3 : exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) = exp (π*I*a/2) := by congr 1; push_cast; ring
  have e4 : exp (-(((1:ℝ) : ℂ)*π*I*a/2)) = exp (-π*I*a/2) := by congr 1; push_cast; ring
  have e5 : exp (((-1:ℝ) : ℂ)*I*z) = exp (-z*I) := by congr 1; push_cast; ring
  have e6 : exp (((1:ℝ) : ℂ)*I*z) = exp (z*I) := by congr 1; push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  simp only [genTrigAuxF, genTrigAuxG, genSinIntTail, genCosIntTail, genSinIntTailOnLog,
    genCosIntTailOnLog, Complex.cos, Complex.sin]
  set X := upperIncGammaOnLog a (log z - π*I/2)
  set Y := upperIncGammaOnLog a (log z + π*I/2)
  set α := exp (π*I*a/2)
  set β := exp (-π*I*a/2)
  set u := exp (z*I)
  set v := exp (-z*I)
  constructor
  · field_simp
    ring_nf
    rw [I_sq]
    ring
  · field_simp
    ring_nf

/-- genTrigAuxF sector asymptotic. -/
@[dlmf 8.21.E26]
theorem genTrigAuxF_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-0)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+0)) (genTrigAuxF a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.sub hp).const_smul (1 / (2 * I))
  have hf : ((1 / (2 * I)) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) -
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxF a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).1]
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have he := h.even (fun n => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, pow_mul]
    simp)
  refine (he.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2, pow_mul (-1:ℂ) 2 n]
    field_simp
    ring

/-- genTrigAuxG sector asymptotic. -/
@[dlmf 8.21.E27]
theorem genTrigAuxG_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-1)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+1)) (genTrigAuxG a) := by
  have hm := upperIncGamma_rotated_piece_asymptotic a (s := -1) (Or.inr rfl) hδ hδ1
  have hp := upperIncGamma_rotated_piece_asymptotic a (s := 1) (Or.inl rfl) hδ hδ1
  have h := (hm.add hp).const_smul (1 / 2 : ℂ)
  have hf : ((1 / 2 : ℂ) • ((fun z => exp (-(((-1:ℝ) : ℂ)*π*I*a/2)) * (exp (((-1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((-1:ℝ) : ℂ)*π*I/2))) +
      (fun z => exp (-(((1:ℝ) : ℂ)*π*I*a/2)) * (exp (((1:ℝ) : ℂ)*I*z) *
        upperIncGammaOnLog a (log z + ((1:ℝ) : ℂ)*π*I/2))))) = genTrigAuxG a := by
    funext z
    rw [(genTrigAux_eq_pieces a z).2]
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    ring
  rw [hf] at h
  have ho := h.odd (fun n => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2]
    ring)
  refine (ho.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    rw [exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inr rfl),
      exp_neg_sign_mul_pi_div_two_mul_I_pow (Or.inl rfl)]
    push_cast
    have h1 : (-(-1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    have h2 : (-(1:ℂ) * I)^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    rw [h1, h2, pow_succ (-1:ℂ) (2*n), pow_mul (-1:ℂ) 2 n, pow_succ (-1:ℂ) n]
    ring

end AAR.Confluent
