/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Integrals

/-!
# The oscillatory parabolic cylinder function W

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat ComplexConjugate
namespace AAR.Confluent

open AAR.Bessel

/-- pcfWZero. -/
@[dlmf 12.14.E1]
def pcfWZero (a : ℝ) : ℝ :=
  2^(-3/4:ℝ)*Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖

/-- pcfWDerivZero. -/
@[dlmf 12.14.E2]
def pcfWDerivZero (a : ℝ) : ℝ :=
  -2^(-1/4:ℝ)*Real.sqrt ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖

/-- pcfWEven. -/
@[dlmf 12.14.E15]
def pcfWEven (a z : ℂ) : ℂ :=
  pcfEven (-I*a) (exp (π*I/4)*z)

/-- pcfWOdd. -/
@[dlmf 12.14.E16]
def pcfWOdd (a z : ℂ) : ℂ :=
  exp (-π*I/4)*pcfOdd (-I*a) (exp (π*I/4)*z)

/-- pcfW. -/
@[dlmf 12.14.E8]
def pcfW (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a*pcfWEven a z+pcfWDerivZero a*pcfWOdd a z

/-- pcfW initial. -/
@[dlmf 12.14.E1, dlmf 12.14.E2]
theorem pcfW_initial (a : ℝ) :
    pcfW a 0=pcfWZero a ∧ HasDerivAt (pcfW a) (pcfWDerivZero a) 0 := by
  constructor
  · simp [pcfW, pcfWEven, pcfWOdd, pcfEven, pcfOdd]
  · have he : HasDerivAt (pcfWEven (a:ℂ)) 0 0 := by
      have h := (hasDerivAt_pcfEven (-I*a) (exp (π*I/4)*0)).comp 0
        ((hasDerivAt_id (0:ℂ)).const_mul (exp (π*I/4)))
      have h' : HasDerivAt (pcfWEven (a:ℂ)) _ 0 :=
        h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
      simpa [pcfEvenDeriv] using h'
    have ho : HasDerivAt (pcfWOdd (a:ℂ)) 1 0 := by
      have h := ((hasDerivAt_pcfOdd (-I*a) (exp (π*I/4)*0)).comp 0
        ((hasDerivAt_id (0:ℂ)).const_mul (exp (π*I/4)))).const_mul (exp (-π*I/4))
      have h' : HasDerivAt (pcfWOdd (a:ℂ)) _ 0 :=
        h.congr_of_eventuallyEq (Eventually.of_forall fun w => rfl)
      simpa [pcfOddDeriv, ← Complex.exp_add, neg_div] using h'
    have h : HasDerivAt (pcfW a) _ 0 :=
      ((he.const_mul (pcfWZero a:ℂ)).add (ho.const_mul (pcfWDerivZero a:ℂ))).congr_of_eventuallyEq
        (Eventually.of_forall fun w => rfl)
    simpa only [mul_zero, mul_one, zero_add] using h

/-- `(e^{iπ/4})² = i`. -/
lemma exp_pi_I_quarter_sq : exp (π*I/4)^2 = I := by
  rw [← Complex.exp_nat_mul, show ((2:ℕ):ℂ)*(π*I/4) = (π/2:ℝ)*I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
    Real.sin_pi_div_two]
  simp

/-- `e^{-iπ/4} e^{iπ/4} = 1`. -/
lemma exp_neg_pi_I_quarter_mul : exp (-π*I/4) * exp (π*I/4) = 1 := by
  rw [← Complex.exp_add]; ring_nf; simp

/-- pcfWEven kummer. -/
@[dlmf 12.14.E15]
theorem pcfWEven_kummer (a z : ℂ) :
    pcfWEven a z = exp (-I*z^2/4)*kummerM (1/4-I*a/2) (1/2) (I*z^2/2) ∧ pcfWEven a z = exp (I*z^2/4)*kummerM (1/4+I*a/2) (1/2) (-I*z^2/2) := by
  constructor
  · rw [pcfWEven, pcfEven, mul_pow, exp_pi_I_quarter_sq, show -I*a/2 + 1/4 = 1/4-I*a/2 by ring,
      show -(I*z^2)/4 = -I*z^2/4 by ring]
  · rw [pcfWEven, pcfEven_kummer_alternative, mul_pow, exp_pi_I_quarter_sq,
      show -(-I*a)/2 + 1/4 = 1/4+I*a/2 by ring, show -(I*z^2)/2 = -I*z^2/2 by ring]

/-- pcfWOdd kummer. -/
@[dlmf 12.14.E16]
theorem pcfWOdd_kummer (a z : ℂ) :
    pcfWOdd a z = z*exp (-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2) ∧ pcfWOdd a z = z*exp (I*z^2/4)*kummerM (3/4+I*a/2) (3/2) (-I*z^2/2) := by
  have h1 := exp_neg_pi_I_quarter_mul
  constructor
  · rw [pcfWOdd, pcfOdd, mul_pow, exp_pi_I_quarter_sq, show -I*a/2 + 3/4 = 3/4-I*a/2 by ring,
      show -(I*z^2)/4 = -I*z^2/4 by ring]
    linear_combination (z * exp (-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2)) * h1
  · rw [pcfWOdd, pcfOdd_kummer_alternative, mul_pow, exp_pi_I_quarter_sq,
      show -(-I*a)/2 + 3/4 = 3/4+I*a/2 by ring, show -(I*z^2)/2 = -I*z^2/2 by ring]
    linear_combination (z * exp (I*z^2/4)*kummerM (3/4+I*a/2) (3/2) (-I*z^2/2)) * h1

/-- Derivative of `W(a,z)`. -/
def pcfWDeriv (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a * (exp (π*I/4) * pcfEvenDeriv (-I*a) (exp (π*I/4)*z)) +
    pcfWDerivZero a * pcfOddDeriv (-I*a) (exp (π*I/4)*z)

/-- A rotated solution of Weber's equation. -/
lemma IsWeberSol.hasDerivAt_rot {b : ℂ} {f f' : ℂ → ℂ} (hf : IsWeberSol b f f') (c z : ℂ) :
    HasDerivAt (fun w => f (c*w)) (c * f' (c*z)) z ∧
      HasDerivAt (fun w => c * f' (c*w)) (c^2*((c*z)^2/4+b) * f (c*z)) z := by
  have hl : ∀ w : ℂ, HasDerivAt (fun w : ℂ => c*w) c w := fun w =>
    ((hasDerivAt_id w).const_mul c).congr_deriv (mul_one c)
  constructor
  · exact ((hf (c*z)).1.comp z (hl z)).congr_deriv (mul_comm _ _)
  · exact (((hf (c*z)).2.comp z (hl z)).const_mul c).congr_deriv (by ring)

/-- `W` has derivative `pcfWDeriv`. -/
theorem hasDerivAt_pcfW (a : ℝ) (z : ℂ) : HasDerivAt (pcfW a) (pcfWDeriv a z) z := by
  have he := ((isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).1
  have ho := ((isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).1
  have h := (he.const_mul (pcfWZero a : ℂ)).add ((ho.const_mul (exp (-π*I/4))).const_mul (pcfWDerivZero a : ℂ))
  convert h using 1
  · funext w; simp [pcfW, pcfWEven, pcfWOdd]
  · rw [pcfWDeriv, ← mul_assoc (exp (-π*I/4)), exp_neg_pi_I_quarter_mul, one_mul]

/-- Weber's oscillatory equation `W'' = (a - z²/4) W`. -/
theorem hasDerivAt_pcfWDeriv (a : ℝ) (z : ℂ) :
    HasDerivAt (pcfWDeriv a) ((a - z^2/4) * pcfW a z) z := by
  have he := ((isWeberSol_pcfEven (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).2
  have ho := ((isWeberSol_pcfOdd (-I*a)).hasDerivAt_rot (exp (π*I/4)) z).2
  have h := (he.const_mul (pcfWZero a : ℂ)).add ((ho.const_mul (exp (-π*I/4))).const_mul (pcfWDerivZero a : ℂ))
  have h1 := exp_neg_pi_I_quarter_mul
  have h2 := exp_pi_I_quarter_sq
  convert h using 1
  · funext w; simp only [Pi.add_apply, pcfWDeriv]
    linear_combination (-(pcfWDerivZero a : ℂ) * pcfOddDeriv (-I*a) (exp (π*I/4)*w)) * h1
  · rw [pcfW, pcfWEven, pcfWOdd, mul_pow, h2]
    linear_combination ((a:ℂ) - z^2/4) * ((pcfWZero a : ℂ) * pcfEven (-I*a) (exp (π*I/4)*z) +
      (pcfWDerivZero a : ℂ) * (exp (-π*I/4) * pcfOdd (-I*a) (exp (π*I/4)*z))) * I_sq

/-- The derivative of `W`. -/
theorem deriv_pcfW (a : ℝ) : deriv (pcfW a) = pcfWDeriv a :=
  funext fun z => (hasDerivAt_pcfW a z).deriv

/-- pcfW ode. -/
@[dlmf 12.2.E3]
theorem pcfW_ode (a : ℝ) :
    IsOscillatoryCylinderSolution a (pcfW a) := by
  intro z
  rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, deriv_pcfW,
    (hasDerivAt_pcfWDeriv a z).deriv]
  ring

/-- `W(a, z̄) = conj W(a, z)`. -/
lemma conj_pcfW_conj (a : ℝ) (z : ℂ) : conj (pcfW a (conj z)) = pcfW a z := by
  have hE : conj (pcfWEven a (conj z)) = pcfWEven a z := by
    rw [(pcfWEven_kummer _ _).1, (pcfWEven_kummer _ _).2]
    simp [conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]
    ring_nf
  have hO : conj (pcfWOdd a (conj z)) = pcfWOdd a z := by
    rw [(pcfWOdd_kummer _ _).1, (pcfWOdd_kummer _ _).2]
    simp [conj_kummerM, ← Complex.exp_conj, map_div₀, map_ofNat]
    left; ring_nf
  simp only [pcfW, map_add, map_mul, Complex.conj_ofReal, hE, hO]

/-- W is real on the real axis. -/
theorem pcfW_real (a x : ℝ) :
    (pcfW a x).im=0 := by
  rw [← Complex.conj_eq_iff_im]
  simpa using conj_pcfW_conj a x

/-- `W'(a,x)` is real for real `x`. -/
lemma conj_pcfWDeriv_ofReal (a x : ℝ) : conj (pcfWDeriv a x) = pcfWDeriv a x := by
  have h := (hasDerivAt_pcfW a (conj (x:ℂ))).conj_conj
  have he : (conj ∘ pcfW a ∘ conj) = pcfW a := funext fun z => conj_pcfW_conj a z
  rw [he, Complex.conj_conj, Complex.conj_ofReal] at h
  exact h.unique (hasDerivAt_pcfW a x)

/-- The Wronskian of `W(a,z)` and `W(a,-z)`. -/
lemma pcfW_wronskian_aux (a : ℝ) (z : ℂ) :
    pcfW a z*(-pcfWDeriv a (-z))-pcfW a (-z)*pcfWDeriv a z = -2 * pcfWZero a * pcfWDerivZero a := by
  have hn : ∀ w : ℂ, HasDerivAt (fun w => pcfW a (-w)) (-pcfWDeriv a (-w)) w := fun w => by
    exact ((hasDerivAt_pcfW a (-w)).comp w (hasDerivAt_neg w)).congr_deriv (by ring)
  have hn' : ∀ w : ℂ, HasDerivAt (fun w => -pcfWDeriv a (-w)) ((a - (-w)^2/4) * pcfW a (-w)) w := fun w => by
    exact ((hasDerivAt_pcfWDeriv a (-w)).comp w (hasDerivAt_neg w)).neg.congr_deriv (by ring)
  have hd : ∀ w, HasDerivAt (fun w => pcfW a w*(-pcfWDeriv a (-w))-pcfW a (-w)*pcfWDeriv a w) 0 w :=
    fun w => (((hasDerivAt_pcfW a w).mul (hn' w)).sub ((hn w).mul (hasDerivAt_pcfWDeriv a w))).congr_deriv
      (by ring)
  have := is_const_of_deriv_eq_zero (fun w => (hd w).differentiableAt) (fun w => (hd w).deriv) z 0
  rw [this, neg_zero]
  have h0 : pcfW a 0 = pcfWZero a := by simp [pcfW, pcfWEven, pcfWOdd, pcfEven, pcfOdd]
  have h1 : pcfWDeriv a 0 = pcfWDerivZero a := by
    simp [pcfWDeriv, pcfEvenDeriv_zero, pcfOddDeriv_zero]
  rw [h0, h1]; ring

/-- `W(a,0) W'(a,0) = -1/2`. -/
lemma pcfWZero_mul_pcfWDerivZero (a : ℝ) : pcfWZero a * pcfWDerivZero a = -1/2 := by
  have hpos : 0 < ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖ := by
    refine norm_pos_iff.mpr (div_ne_zero ?_ ?_) <;> apply Complex.Gamma_ne_zero_of_re_pos <;> simp
  have hinv : ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖ = ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖⁻¹ := by
    rw [← norm_inv, inv_div]
  rw [pcfWZero, pcfWDerivZero, hinv]
  have hs : Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖ * Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖⁻¹ = 1 := by
    rw [← Real.sqrt_mul hpos.le, mul_inv_cancel₀ hpos.ne', Real.sqrt_one]
  have h2 : (2:ℝ)^(-3/4:ℝ) * 2^(-1/4:ℝ) = 1/2 := by
    rw [← Real.rpow_add (by norm_num)]; norm_num
  linear_combination (-(2:ℝ)^(-3/4:ℝ) * 2^(-1/4:ℝ)) * hs - h2

/-- pcfW wronskian. -/
@[dlmf 12.14.E3]
theorem pcfW_wronskian (a : ℝ) (z : ℂ) :
    pcfW a z*(-deriv (pcfW a) (-z))-pcfW a (-z)*deriv (pcfW a) z=1 := by
  rw [deriv_pcfW, pcfW_wronskian_aux]
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  linear_combination (-2) * this

/-- pcfWK. -/
@[dlmf 12.14.E5]
def pcfWK (a : ℝ) : ℝ :=
  Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a)

/-- pcfWK inv. -/
@[dlmf 12.14.E5]
theorem pcfWK_inv (a : ℝ) :
    0 < pcfWK a ∧ (pcfWK a)⁻¹=Real.sqrt (1+Real.exp (2*π*a))+Real.exp (π*a) := by
  unfold pcfWK
  have hE : Real.exp (2*π*a)=(Real.exp (π*a))^2 := by
    rw [show 2*π*a=π*a+π*a by ring, Real.exp_add, pow_two]
  have hs:=Real.sq_sqrt (by positivity : 0 ≤ 1+Real.exp (2*π*a))
  have hp : 0 < Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a) := by
    nlinarith [hE, Real.sqrt_nonneg (1+Real.exp (2*π*a)),Real.exp_pos (π*a)]
  refine ⟨hp, ?_⟩
  apply (mul_eq_one_iff_inv_eq₀ hp.ne').mp
  nlinarith [hE]

/-- Continuous argument of Gamma along the vertical line, normalized to zero at a=0. -/
@[dlmf 12.14.E7]
def pcfGammaPhase (a : ℝ) : ℝ :=
  ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).re

/-- The digamma function is continuous on the line `Re s = 1/2`. -/
theorem continuous_digamma_half_line : Continuous fun t : ℝ => Complex.digamma (1/2+I*t) := by
  have hU : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hG : DifferentiableOn ℂ Gamma {s : ℂ | 0 < s.re} := fun s hs =>
    (Complex.differentiableAt_Gamma s (fun m h => by
      have : (s).re = -(m:ℝ) := by rw [h]; simp
      have hs : (0:ℝ) < s.re := hs
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).differentiableWithinAt
  have hdG : ContinuousOn (deriv Gamma) {s : ℂ | 0 < s.re} := (hG.deriv hU).continuousOn
  have hψ : ContinuousOn Complex.digamma {s : ℂ | 0 < s.re} := by
    have : ContinuousOn (fun s => deriv Gamma s / Gamma s) {s : ℂ | 0 < s.re} :=
      hdG.div hG.continuousOn (fun s hs => Complex.Gamma_ne_zero_of_re_pos hs)
    exact this.congr fun s _ => rfl
  refine hψ.comp_continuous (by fun_prop) fun t => ?_
  show (0:ℝ) < (1/2+I*t).re
  simp

/-- pcfGammaPhase spec. -/
@[dlmf 12.14.E7]
theorem pcfGammaPhase_spec (a : ℝ) :
    Gamma (1/2+I*a) = ‖Gamma (1/2+I*a)‖*exp (I*pcfGammaPhase a) := by
  have hψc := continuous_digamma_half_line
  set Ph : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).re with hPh
  set Th : ℝ → ℝ := fun a => ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).im with hTh
  have hPhd (x : ℝ) : HasDerivAt Ph (Complex.digamma (1/2+I*x)).re x :=
    ((Complex.continuous_re.comp hψc).integral_hasStrictDerivAt 0 x).hasDerivAt
  have hThd (x : ℝ) : HasDerivAt Th (Complex.digamma (1/2+I*x)).im x :=
    ((Complex.continuous_im.comp hψc).integral_hasStrictDerivAt 0 x).hasDerivAt
  set h : ℝ → ℂ := fun x => Gamma (1/2+I*x)*exp (-I*Ph x)*exp (Th x) with hh
  have hre (x : ℝ) : 0 < (1/2+I*(x:ℂ)).re := by simp
  have hGd (x : ℝ) : HasDerivAt (fun x : ℝ => Gamma (1/2+I*x))
      (deriv Gamma (1/2+I*x)*I) x := by
    have hd := (Complex.differentiableAt_Gamma (1/2+I*x) (fun m hm => by
      have := congrArg Complex.re hm; simp at this
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])).hasDerivAt
    have hl : HasDerivAt (fun x : ℝ => (1/2:ℂ)+I*x) I x := by
      simpa using ((hasDerivAt_id (x:ℂ)).const_mul I).const_add (1/2:ℂ) |>.comp_ofReal
    exact hd.comp x hl
  have hhd (x : ℝ) : HasDerivAt h 0 x := by
    have h1 := hGd x
    have h2 : HasDerivAt (fun x : ℝ => exp (-I*Ph x)) (exp (-I*Ph x)*(-I*(Complex.digamma (1/2+I*x)).re)) x := by
      have := ((hPhd x).ofReal_comp.const_mul (-I)).cexp
      simpa using this
    have h3 : HasDerivAt (fun x : ℝ => exp ((Th x : ℂ))) (exp (Th x)*(Complex.digamma (1/2+I*x)).im) x := by
      have := ((hThd x).ofReal_comp).cexp
      simpa using this
    have hd := (h1.mul h2).mul h3
    refine hd.congr_deriv ?_
    have hG0 : Gamma (1/2+I*x) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (hre x)
    have hψ : deriv Gamma (1/2+I*x) = Gamma (1/2+I*x)*
        (((Complex.digamma (1/2+I*x)).re:ℂ) + ((Complex.digamma (1/2+I*x)).im:ℂ)*I) := by
      rw [Complex.re_add_im, Complex.digamma_def, logDeriv_apply, mul_div_assoc', eq_div_iff hG0]
      ring
    simp only [Pi.mul_apply]
    rw [hψ]
    ring_nf
    rw [I_sq]
    ring
  have hdiff : Differentiable ℝ h := fun x => (hhd x).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun x => (hhd x).deriv) a 0
  have h0 : h 0 = Real.sqrt π := by
    simp [hh, hPh, hTh]
    rw [← one_div, Gamma_one_half_eq_sqrt]
  rw [h0] at hconst
  simp only [hh] at hconst
  have e1 : exp (I*Ph a)*exp (-I*Ph a) = 1 := by rw [← Complex.exp_add]; simp
  have e2 : exp (-((Th a:ℝ):ℂ))*exp ((Th a:ℝ):ℂ) = 1 := by rw [← Complex.exp_add]; simp
  have hE : Gamma (1/2+I*a) = (Real.sqrt π:ℂ)*exp (-((Th a:ℝ):ℂ))*exp (I*Ph a) := by
    linear_combination (exp (I*Ph a)*exp (-((Th a:ℝ):ℂ)))*hconst +
      (-(Gamma (1/2+I*a))*(exp (-((Th a:ℝ):ℂ))*exp ((Th a:ℝ):ℂ)))*e1 + (-(Gamma (1/2+I*a)))*e2
  have hn : ‖Gamma (1/2+I*a)‖ = Real.sqrt π*Real.exp (-Th a) := by
    rw [hE, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_exp, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos)]
    simp
  rw [hn]
  conv_lhs => rw [hE]
  rw [show pcfGammaPhase a = Ph a from rfl]
  push_cast
  ring

/-- pcfWRho. -/
@[dlmf 12.14.E6]
def pcfWRho (a : ℝ) : ℝ :=
  π/8+pcfGammaPhase a/2

/-- pcfW connection. -/
@[dlmf 12.14.E4]
theorem pcfW_connection (a : ℝ) (z : ℂ) :
    pcfW a z=(Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))+exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  sorry

/-- Unnumbered companion connection formula in DLMF 12.14(iv). -/
theorem pcfW_connection_neg (a : ℝ) (z : ℂ) :
    pcfW a (-z)=-I/Real.sqrt (2*pcfWK a)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))-exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  sorry

/-- Maclaurin recurrence for the pcfWAlpha coefficients. -/
def pcfWAlpha (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWAlpha a (n+1)-1/2*(n+1)*(2*n+1)*pcfWAlpha a n

/-- Maclaurin recurrence for the pcfWBeta coefficients. -/
def pcfWBeta (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWBeta a (n+1)-1/2*(n+1)*(2*n+3)*pcfWBeta a n

/-- pcfWEven series. -/
@[dlmf 12.14.E9, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWEven_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWAlpha a n*z^(2*n)/((2*n).factorial:ℂ)) (pcfWEven a z) := by
  sorry

/-- pcfWOdd series. -/
@[dlmf 12.14.E10, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWOdd_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWBeta a n*z^(2*n+1)/((2*n+1).factorial:ℂ)) (pcfWOdd a z) := by
  sorry

/-- `Γ(1/4) Γ(3/4) = π √2`. -/
lemma real_Gamma_quarter_mul : Real.Gamma (1/4) * Real.Gamma (3/4) = π * Real.sqrt 2 := by
  have h := Real.Gamma_mul_Gamma_one_sub (1/4)
  rw [show (1:ℝ) - 1/4 = 3/4 by norm_num, show π * (1/4) = π/4 by ring, Real.sin_pi_div_four] at h
  rw [h]
  have hs : Real.sqrt 2 ≠ 0 := by positivity
  field_simp
  rw [Real.sq_sqrt (by norm_num)]

/-- `W(0,0) = 2^{-3/4} √(Γ(1/4)/Γ(3/4))`. -/
lemma pcfWZero_zero : pcfWZero 0 = 2^(-3/4:ℝ) * Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)) := by
  rw [pcfWZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

/-- `W'(0,0) = -2^{-1/4} √(Γ(3/4)/Γ(1/4))`. -/
lemma pcfWDerivZero_zero : pcfWDerivZero 0 = -2^(-1/4:ℝ) * Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)) := by
  rw [pcfWDerivZero]
  congr 2
  simp only [Complex.ofReal_zero, mul_zero, zero_div, add_zero]
  rw [show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring, show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring,
    Complex.Gamma_ofReal, Complex.Gamma_ofReal, ← Complex.ofReal_div, Complex.norm_real,
    Real.norm_of_nonneg (div_nonneg (Real.Gamma_pos_of_pos (by norm_num)).le (Real.Gamma_pos_of_pos (by norm_num)).le)]

lemma rpow_quarter_pow_four {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y^(r/4))^4 = y^r := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; norm_num

/-- Equality of positive reals from equality of fourth powers. -/
lemma eq_of_pow_four_eq {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (h : u^4 = v^4) : u = v :=
  (pow_left_inj₀ hu hv (by norm_num : (4:ℕ) ≠ 0)).mp h

/-- The real coefficient of `J_{-1/4}` in `W(0,x)`. -/
lemma pcfW_zero_coeffA {x : ℝ} (hx : 0 < x) :
    pcfWZero 0 * Real.Gamma (3/4) * (x^2/8)^(1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  rw [pcfWZero_zero]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, show (-3/4:ℝ) = -3/4 by ring, show (1/4:ℝ) = 1/4 by ring,
    show (-3/4:ℝ) = (-3)/4 by ring, rpow_quarter_pow_four (by norm_num), show (1/4:ℝ) = 1/4 from rfl,
    rpow_quarter_pow_four (by positivity) 1, show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (1/4) / Real.Gamma (3/4)))^4 = (Real.Gamma (1/4) / Real.Gamma (3/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num)]
  field_simp
  linear_combination 32*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 32*π^2 * hs

/-- The real coefficient of `J_{1/4}` in `W(0,x)`. -/
lemma pcfW_zero_coeffB {x : ℝ} (hx : 0 < x) :
    -pcfWDerivZero 0 * x * Real.Gamma (5/4) * (x^2/8)^(-1/4:ℝ) = 2^(-5/4:ℝ) * (π*x)^(1/2:ℝ) := by
  have g1 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 1/4)
  have g3 := Real.Gamma_pos_of_pos (by norm_num : (0:ℝ) < 3/4)
  have g5 : Real.Gamma (5/4) = Real.Gamma (1/4) / 4 := by
    rw [show (5/4:ℝ) = 1/4 + 1 by norm_num, Real.Gamma_add_one (by norm_num)]; ring
  rw [pcfWDerivZero_zero, g5]
  simp only [neg_mul, neg_neg]
  apply eq_of_pow_four_eq (by positivity) (by positivity)
  rw [mul_pow, mul_pow, mul_pow, mul_pow, mul_pow,
    show (-1/4:ℝ) = (-1)/4 by ring, rpow_quarter_pow_four (by norm_num),
    rpow_quarter_pow_four (by positivity) (-1), show (-5/4:ℝ) = (-5)/4 by ring, rpow_quarter_pow_four (by norm_num),
    show (1/2:ℝ) = 2/4 by norm_num, rpow_quarter_pow_four (by positivity),
    show (Real.sqrt (Real.Gamma (3/4) / Real.Gamma (1/4)))^4 = (Real.Gamma (3/4) / Real.Gamma (1/4))^2 by
      rw [show 4 = 2*2 by rfl, pow_mul, Real.sq_sqrt (by positivity)]]
  have hq := real_Gamma_quarter_mul
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  simp only [Real.rpow_one, Real.rpow_two, Real.rpow_neg (show (0:ℝ) ≤ 2 by norm_num),
    Real.rpow_neg (show (0:ℝ) ≤ x^2/8 by positivity)]
  field_simp
  linear_combination 256*(Real.Gamma (1/4) * Real.Gamma (3/4) + π*Real.sqrt 2) * hq + 256*π^2 * hs

/-- Real `cpow` of a nonnegative real is real. -/
lemma ofReal_cpow_real {y : ℝ} (hy : 0 ≤ y) (r : ℝ) : (y:ℂ)^(r:ℂ) = ((y^r : ℝ) : ℂ) :=
  (Complex.ofReal_cpow hy r).symm

/-- `W`'s even solution at `a = 0` through `J_{-1/4}`. -/
lemma pcfWEven_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWEven 0 t = Gamma (3/4) * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * besselJ (-1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(-1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWEven_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (-1/4:ℂ) = ((-1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (3/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((-1/4:ℝ):ℂ) + 1 = 3/4 by push_cast; ring, show ((-1/4:ℝ):ℂ) + 1/2 = 1/4 by push_cast; ring,
    show 2*((-1/4:ℝ):ℂ) + 1 = 1/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2))) * hm'
    - ((((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (1/4) (1/2) (I*(t:ℂ)^2/2)) * hg

/-- `W`'s odd solution at `a = 0` through `J_{1/4}`. -/
lemma pcfWOdd_zero_besselJ {t : ℝ} (ht : 0 < t) :
    pcfWOdd 0 t = t * Gamma (5/4) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) * besselJ (1/4) ((t:ℂ)^2/4) := by
  have hν : ∀ k : ℕ, (1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have h2ν : ∀ k : ℕ, 2*(1/4:ℂ) + 1 ≠ -k := fun k h => by
    have := congrArg Complex.re h; simp at this; norm_num at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hy : (0:ℝ) < t^2/8 := by positivity
  rw [besselJ_eq_kummerM hν h2ν, (pcfWOdd_kummer _ _).1,
    show (t:ℂ)^2/4/2 = ((t^2/8 : ℝ) : ℂ) by push_cast; ring, show (1/4:ℂ) = ((1/4:ℝ):ℂ) by push_cast; ring,
    ofReal_cpow_real hy.le]
  have hG : Gamma (5/4:ℂ) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
  have hm : ((t^2/8)^(1/4:ℝ) : ℝ) * (t^2/8)^(-1/4:ℝ) = 1 := by
    rw [← Real.rpow_add hy]; norm_num
  have hm' : (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 1 := by exact_mod_cast hm
  rw [show ((1/4:ℝ):ℂ) + 1 = 5/4 by push_cast; ring, show ((1/4:ℝ):ℂ) + 1/2 = 3/4 by push_cast; ring,
    show 2*((1/4:ℝ):ℂ) + 1 = 3/2 by push_cast; ring, show 2*I*((t:ℂ)^2/4) = I*(t:ℂ)^2/2 by ring,
    show -I*((t:ℂ)^2/4) = -I*(t:ℂ)^2/4 by ring]
  simp only [mul_zero, zero_div, sub_zero]
  have hg := mul_inv_cancel₀ hG
  linear_combination (-(t * exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2))) * hm'
    - (t * (((t^2/8)^(1/4:ℝ) : ℝ) : ℂ) * (((t^2/8)^(-1/4:ℝ) : ℝ) : ℂ) *
      exp (-I*(t:ℂ)^2/4) * kummerM (3/4) (3/2) (I*(t:ℂ)^2/2)) * hg

/-- `pcfWEven` is even. -/
lemma pcfWEven_neg (a z : ℂ) : pcfWEven a (-z) = pcfWEven a z := by
  simp [pcfWEven, pcfEven, mul_neg]

/-- `pcfWOdd` is odd. -/
lemma pcfWOdd_neg (a z : ℂ) : pcfWOdd a (-z) = -pcfWOdd a z := by
  simp [pcfWOdd, pcfOdd, mul_neg]

/-- Complex form of the `J_{-1/4}` coefficient. -/
lemma pcfW_zero_coeffA' {x : ℝ} (hx : 0 < x) :
    (pcfWZero 0 : ℂ) * Gamma (3/4) * (((x^2/8)^(1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffA hx)
  simp only [Complex.ofReal_mul] at h
  rw [show (3/4:ℂ) = ((3/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Complex form of the `J_{1/4}` coefficient. -/
lemma pcfW_zero_coeffB' {x : ℝ} (hx : 0 < x) :
    -(pcfWDerivZero 0 : ℂ) * x * Gamma (5/4) * (((x^2/8)^(-1/4:ℝ) : ℝ) : ℂ) = 2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ) := by
  have h := congrArg (fun r : ℝ => (r:ℂ)) (pcfW_zero_coeffB hx)
  simp only [Complex.ofReal_mul, Complex.ofReal_neg] at h
  rw [show (5/4:ℂ) = ((5/4:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal, h,
    Complex.ofReal_cpow (by norm_num), Complex.ofReal_cpow (by positivity)]
  push_cast; ring_nf

/-- Derivative of the complex Bessel form of `W(0, ±w)`. -/
lemma pcfW_zero_bessel_hasDerivAt_aux (ε : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun w : ℂ => 2^(-5/4:ℂ)*(π*w)^(1/2:ℂ)*(besselJ (-1/4) (w^2/4)-ε*besselJ (1/4) (w^2/4)))
      (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+ε*besselJ (-3/4) (x^2/4))) (x:ℂ) := by
  have hz : ((x:ℂ)^2/4) ∈ slitPlane := by
    rw [show (x:ℂ)^2/4 = ((x^2/4:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hp : (π*(x:ℂ)) ∈ slitPlane := by
    rw [show (π:ℂ)*(x:ℂ) = ((π*x:ℝ):ℂ) by push_cast; ring]
    exact ofReal_mem_slitPlane.2 (by positivity)
  have hsq : HasDerivAt (fun w : ℂ => w^2/4) ((x:ℂ)/2) x := by
    exact ((hasDerivAt_pow 2 (x:ℂ)).div_const 4).congr_deriv (by simp; ring)
  have h1 := (hasDerivAt_besselJ (ν := -1/4) hz).comp (x:ℂ) hsq
  have h2 := (hasDerivAt_besselJ' (ν := 1/4) hz).comp (x:ℂ) hsq
  have hc := ((hasDerivAt_id (x:ℂ)).const_mul (π:ℂ)).cpow_const (c := 1/2) (by simpa using hp)
  have := (hc.const_mul (2^(-5/4:ℂ))).mul (h1.sub (h2.const_mul ε))
  convert this using 1
  · ext w; simp
  simp only [id, Function.comp, Pi.sub_apply]
  have hx0 : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hpx : (π:ℂ)*x ≠ 0 := mul_ne_zero hπ hx0
  rw [Complex.cpow_sub _ _ hpx, Complex.cpow_one, show (-9/4:ℂ) = -5/4 - 1 by norm_num,
    Complex.cpow_sub _ _ two_ne_zero, Complex.cpow_one,
    show (-1/4:ℂ) + 1 = 3/4 by norm_num, show (1/4:ℂ) - 1 = -3/4 by norm_num]
  field_simp
  ring

/-- pcfW zero bessel 1. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_1 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [one_mul, pcfW, Complex.ofReal_zero, pcfWEven_zero_besselJ hx, pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    - besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- pcfW zero bessel deriv 1. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux 1 hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_1 ht

/-- pcfW zero bessel 2. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_2 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (-1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(-1:ℂ)*besselJ (1/4) (x^2/4)) := by
  rw [neg_one_mul, pcfW, Complex.ofReal_zero, pcfWEven_neg, pcfWOdd_neg, pcfWEven_zero_besselJ hx,
    pcfWOdd_zero_besselJ hx]
  linear_combination besselJ (-1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffA' hx
    + besselJ (1/4) ((x:ℂ)^2/4) * pcfW_zero_coeffB' hx

/-- pcfW zero bessel deriv 2. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_2 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (-1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(-1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  refine (pcfW_zero_bessel_hasDerivAt_aux (-1) hx).comp_ofReal.congr_of_eventuallyEq ?_
  filter_upwards [lt_mem_nhds hx] with t ht
  exact pcfW_zero_bessel_2 ht

/-- pcfWOmega. -/
@[dlmf 12.14.E19]
def pcfWOmega (a x : ℝ) : ℝ :=
  x^2/4-a*Real.log x+π/4+pcfGammaPhase a/2

/-- `W(a,x)` is real. -/
lemma pcfW_ofReal_im (a x : ℝ) : (pcfW a x).im = 0 := by
  rw [← Complex.conj_eq_iff_im]; simpa using conj_pcfW_conj a x

/-- `W(a,z)` and `W(a,-z)` do not vanish together. -/
lemma pcfW_one_ne (a : ℝ) (z : ℂ) (h1 : pcfW a z = 0) (h2 : pcfW a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- `W'(a,z)` and `W'(a,-z)` do not vanish together. -/
lemma pcfWDeriv_one_ne (a : ℝ) (z : ℂ) (h1 : pcfWDeriv a z = 0) (h2 : pcfWDeriv a (-z) = 0) : False := by
  have hw := pcfW_wronskian_aux a z
  have := pcfWZero_mul_pcfWDerivZero a
  have : (pcfWZero a : ℂ) * pcfWDerivZero a = -1/2 := by exact_mod_cast this
  rw [h1, h2] at hw
  have : (0:ℂ) = 1 := by linear_combination hw - 2 * this
  exact zero_ne_one this

/-- Combined exact amplitude s1+i s2, recovered from the two real W solutions. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
def pcfWS (a x : ℝ) : ℂ :=
  exp (-I*pcfWOmega a x)*(Real.sqrt (x/(2*pcfWK a))*pcfW a x+I*Real.sqrt (pcfWK a*x/2)*pcfW a (-x))

/-- pcfW amplitude. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
theorem pcfW_amplitude (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfW a x=Real.sqrt (2*pcfWK a/x)*((pcfWS a x).re*Real.cos (pcfWOmega a x)-(pcfWS a x).im*Real.sin (pcfWOmega a x)) ∧ pcfW a (-x)=Real.sqrt (2/(pcfWK a*x))*((pcfWS a x).re*Real.sin (pcfWOmega a x)+(pcfWS a x).im*Real.cos (pcfWOmega a x)) := by
  have h1r := pcfW_ofReal_im a x
  have h2r := pcfW_ofReal_im a (-x)
  push_cast at h2r
  have hk := (pcfWK_inv a).1
  set ω := pcfWOmega a x
  set k := pcfWK a
  set p := Real.sqrt (x/(2*k))
  set q := Real.sqrt (k*x/2)
  have hT : exp (I*ω) * pcfWS a x = p * pcfW a x + I * (q * pcfW a (-x)) := by
    rw [pcfWS, ← mul_assoc, ← Complex.exp_add, show I*ω + -I*ω = 0 by ring, Complex.exp_zero, one_mul]
    ring
  have hre := congrArg Complex.re hT
  have him := congrArg Complex.im hT
  simp [Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    h1r, h2r, mul_comm I] at hre him
  have hp : Real.sqrt (2*k/x) * p = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have hq : Real.sqrt (2/(k*x)) * q = 1 := by
    rw [← Real.sqrt_mul (by positivity)]; field_simp; simp
  have e1 : pcfW a x = ((pcfW a x).re : ℂ) := (Complex.ext (by simp) (by simp [h1r]))
  have e2 : pcfW a (-x) = ((pcfW a (-x)).re : ℂ) := (Complex.ext (by simp) (by simp [h2r]))
  constructor
  · rw [e1]
    have : (pcfW a x).re = Real.sqrt (2*k/x) * ((pcfWS a x).re * Real.cos ω - (pcfWS a x).im * Real.sin ω) := by
      linear_combination (-Real.sqrt (2*k/x)) * hre - (pcfW a x).re * hp
    rw [this]; push_cast; ring
  · rw [e2]
    have : (pcfW a (-x)).re = Real.sqrt (2/(k*x)) * ((pcfWS a x).re * Real.sin ω + (pcfWS a x).im * Real.cos ω) := by
      linear_combination (-Real.sqrt (2/(k*x))) * him - (pcfW a (-x)).re * hq
    rw [this]; push_cast; ring

/-- pcfWCoeff. -/
@[dlmf 12.14.E22]
def pcfWCoeff (a : ℝ) (r : ℕ) : ℂ :=
  poch (1/2+I*a) (2*r)

/- DLMF 12.14.22 is Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`,
with z=1/2+i*a and n=2*r. The real part of z is positive, so its regularity
hypothesis holds. `pcfWCoeff` uses the equivalent Pochhammer definition.
This upstream gamma-ratio identity is not reproved here. -/

/-- pcfWS asymptotic. -/
@[dlmf 12.14.E20, dlmf 12.14.E21, dlmf 12.14.E23]
theorem pcfWS_asymptotic (a : ℝ) (N : ℕ) :
    (fun x : ℝ => pcfWS a x-∑ r ∈ Finset.range N, (-I)^r*pcfWCoeff a r/(2^r*(r.factorial:ℂ)*(x:ℂ)^(2*r))) =O[atTop] (fun x : ℝ => (x:ℂ)^(-(2*N:ℤ))) := by
  sorry

/-- pcfWF. -/
@[dlmf 12.14.E37]
def pcfWF (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)‖

/-- pcfWTheta. -/
@[dlmf 12.14.E37]
def pcfWTheta (a x : ℝ) : ℝ :=
  arg ((1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)))

/-- pcfWF phase. -/
@[dlmf 12.14.E37]
theorem pcfWF_phase (a x : ℝ) :
    0 < pcfWF a x ∧ 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)=(pcfWF a x*exp (I*pcfWTheta a x)) := by
  have hk := (pcfWK_inv a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x) ≠ 0 := by
    rw [mul_assoc I]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, Complex.conj_eq_iff_im.mpr (pcfW_ofReal_im a x)]; simp
    · have := pcfW_ofReal_im a (-x); push_cast at this
      rw [map_mul, Complex.conj_eq_iff_im.mpr this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfW_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I] at h
  exact h.symm

/-- pcfWG. -/
@[dlmf 12.14.E38]
def pcfWG (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)‖

/-- pcfWPsi. -/
@[dlmf 12.14.E38]
def pcfWPsi (a x : ℝ) : ℝ :=
  arg (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))

/-- pcfWG phase. -/
@[dlmf 12.14.E38]
theorem pcfWG_phase (a x : ℝ) :
    0 < pcfWG a x ∧ 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)=-(pcfWG a x*exp (I*pcfWPsi a x)) := by
  have hk := (pcfWK_inv a).1
  have hs : (Real.sqrt (pcfWK a) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hk).ne'
  have hne : 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x) ≠ 0 := by
    rw [mul_assoc I, deriv_pcfW]
    refine add_I_mul_ne_zero_of_real ?_ ?_ ?_
    · rw [map_mul, conj_pcfWDeriv_ofReal]; simp
    · have := conj_pcfWDeriv_ofReal a (-x); push_cast at this
      rw [map_mul, this, Complex.conj_ofReal]
    · rintro ⟨h1, h2⟩
      exact pcfWDeriv_one_ne a x (by simpa [hs] using h1) (by simpa [hs] using h2)
  refine ⟨norm_pos_iff.mpr hne, ?_⟩
  have h := norm_mul_exp_arg_mul_I (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))
  rw [mul_comm ((arg _ : ℝ) : ℂ) I, norm_neg] at h
  rw [pcfWG, pcfWPsi, h, neg_neg]

end AAR.Confluent
