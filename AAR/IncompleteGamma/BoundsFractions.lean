/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues

/-!
# Continued fractions and inequalities, DLMF §§8.9–8.10

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- scIncGamma continuedFraction. -/
@[dlmf 8.9.E1]
theorem scIncGamma_continuedFraction {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(n+1)) (z : ℂ) :
    HasContinuedFraction (fun k => if k=0 then 1 else if Odd k then -(if k=1 then 1 else ((k-1 : ℕ)/2 : ℂ)+a)*z else ((k : ℕ)/2 : ℂ)*z) (fun k => if k=0 then 1 else a+k) (Gamma (a+1)*exp z*scIncGamma a z) := by
  sorry

/-- upperIncGamma continuedFraction complex. -/
@[dlmf 8.9.E2]
theorem upperIncGamma_continuedFraction_complex (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then z⁻¹ else (if Odd k then ((k+1)/2 : ℕ)-a else ((k/2 : ℕ) : ℂ))/z) (fun _ => 1) (z^(-a)*exp z*upperIncGamma a z) := by
  sorry

/-- upperIncGamma bound le one. -/
@[dlmf 8.10.E1]
theorem upperIncGamma_bound_le_one {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    x^(1-a)*Real.exp x*(upperIncGamma a x).re ≤ 1 := by
  sorry

/-- lowerIncGamma bound ge. -/
@[dlmf 8.10.E2]
theorem lowerIncGamma_bound_ge {a x : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hx : 0 < x) :
    (lowerIncGamma a x).re ≥ x^(a-1)/a*(1-Real.exp (-x)) := by
  sorry

/-- upperIncGamma bound ge one. -/
@[dlmf 8.10.E1]
theorem upperIncGamma_bound_ge_one {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    1 ≤ x^(1-a)*Real.exp x*(upperIncGamma a x).re := by
  sorry

/-- lowerIncGamma bound le. -/
@[dlmf 8.10.E2]
theorem lowerIncGamma_bound_le {a x : ℝ} (ha : 1 ≤ a) (hx : 0 < x) :
    (lowerIncGamma a x).re ≤ x^(a-1)/a*(1-Real.exp (-x)) := by
  sorry

/-- The first-order real incomplete-Gamma remainder ratio. -/
@[dlmf 8.10.E3]
def Real.upperGammaTheta (a x : ℝ) : ℝ :=
  if a=1 then 1 else (x^(1-a)*Real.exp x*(upperIncGamma a x).re-1)*x/(a-1)

/-- Real.upperGammaTheta identity. -/
@[dlmf 8.10.E3]
theorem Real.upperGammaTheta_identity {a x : ℝ} (hx : 0 < x) :
    x^(1-a)*Real.exp x*(upperIncGamma a x).re=1+(a-1)/x*Real.upperGammaTheta a x := by
  rw [Real.upperGammaTheta]
  split_ifs with h
  · subst h
    rw [ofReal_one, upperIncGamma_one, ← ofReal_neg, ← ofReal_exp, ofReal_re, sub_self,
      Real.rpow_zero, one_mul, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
    ring
  · have h1 : a - 1 ≠ 0 := sub_ne_zero.mpr h
    field_simp
    ring

/-- The remainder ratio tends to one in DLMF §8.10. -/
theorem Real.upperGammaTheta_limit (a : ℝ) :
    Tendsto (Real.upperGammaTheta a) atTop (𝓝 1) := by
  by_cases ha : a = 1
  · subst ha
    exact tendsto_const_nhds.congr fun x => by simp [Real.upperGammaTheta]
  have ha1 : (a:ℝ) - 1 ≠ 0 := sub_ne_zero.mpr ha
  have h := hasAsymptoticExpansion_upperIncGamma (a:ℂ) 2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
    smul_eq_mul] at h
  set D : ℝ → ℂ := fun x => upperIncGamma a x - (exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((0:ℕ):ℂ)) *
    poch (1-a) 0 + exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((1:ℕ):ℂ)) * ((-1)^1*poch (1-a) 1))
  have hf := (isBigO_refl (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)) atTop).mul h
  -- the comparison function tends to zero
  have hg : Tendsto (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))))
      atTop (𝓝 0) := by
    have he : (fun x : ℝ => (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))))
        =ᶠ[atTop] fun x : ℝ => ((x⁻¹ : ℝ) : ℂ) := by
      filter_upwards [eventually_gt_atTop 0] with x hx
      have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
      have hee : exp (x:ℂ) * exp (-(x:ℂ)) = 1 := by rw [← Complex.exp_add]; simp
      rw [show (x:ℂ)^(2-(a:ℂ))*exp (x:ℂ)*(exp (-(x:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))) =
        (exp (x:ℂ) * exp (-(x:ℂ))) * ((x:ℂ)^(2-(a:ℂ))*(x:ℂ)^((a:ℂ)-1-((2:ℕ):ℂ))) by ring,
        hee, one_mul, ← cpow_add _ _ hx0, show 2-(a:ℂ)+((a:ℂ)-1-((2:ℕ):ℂ)) = -1 by push_cast; ring,
        cpow_neg_one, ofReal_inv]
    refine Tendsto.congr' he.symm ?_
    have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
    simpa [Function.comp_def] using this
  have hf0 := hf.trans_tendsto hg
  -- relate to θ
  refine (((Complex.continuous_re.tendsto _).comp hf0).div_const (a-1) |>.const_add 1).congr' ?_ |>.mono_right ?_
  · filter_upwards [eventually_gt_atTop 0] with x hx
    simp only [Function.comp_apply, D]
    have hc : (x:ℂ)^(2-(a:ℂ))*cexp x = ((x^(2-a)*Real.exp x : ℝ):ℂ) := by
      rw [ofReal_mul, ofReal_cpow hx.le, ofReal_exp]; push_cast; ring
    have hsum : exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((0:ℕ):ℂ)) * poch (1-a) 0 +
        exp (-(x:ℂ)) * (x:ℂ)^((a:ℂ)-1-((1:ℕ):ℂ)) * ((-1)^1*poch (1-a) 1) =
        ((Real.exp (-x) * x^(a-1) - Real.exp (-x) * x^(a-2) * (1-a) : ℝ) : ℂ) := by
      push_cast
      rw [ofReal_cpow hx.le, ofReal_cpow hx.le]
      simp [poch]
      ring_nf
    rw [hc, hsum, re_ofReal_mul, sub_re, ofReal_re, Real.upperGammaTheta]
    simp only [ha, ↓reduceIte]
    set u := x^(1-a) with hu
    have hu0 : 0 < u := Real.rpow_pos_of_pos hx _
    have e1 : x^(2-a) = x*u := by
      rw [hu, show 2-a = 1 + (1-a) by ring, Real.rpow_add hx, Real.rpow_one]
    have e2 : x^(a-1) = u⁻¹ := by
      rw [hu, ← Real.rpow_neg hx.le]; ring_nf
    have e3 : x^(a-2) = u⁻¹*x⁻¹ := by
      rw [hu, ← Real.rpow_neg hx.le, ← Real.rpow_neg_one, ← Real.rpow_add hx]; ring_nf
    have hee : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    rw [e1, e2, e3]
    field_simp
    linear_combination (-(x-(1-a))) * hee
  · simp

/-- Real.upperGammaTheta bounds. -/
@[dlmf 8.10.E4]
theorem Real.upperGammaTheta_bounds {a x : ℝ} (ha : a ≤ 2) (hx : 0 < x) :
    0 < Real.upperGammaTheta a x ∧ Real.upperGammaTheta a x ≤ 1 := by
  sorry

/-- Finite Legendre convergents giving A_n and B_n. -/
def Real.upperGammaPade (upper : Bool) (n : ℕ) (a x : ℝ) : ℝ :=
  (cfTail (fun k => if k=0 then x else if Odd k then ((k+1)/2 : ℕ)-a else ((k/2 : ℕ) : ℝ)) (fun k => if Even k then (x : ℂ) else 1) 0 (2*n+if upper then 1 else 0)).re

/-- Real.upperGammaPade bounds. -/
@[dlmf 8.10.E5]
theorem Real.upperGammaPade_bounds {a x : ℝ} (ha : a < 1) (hx : 0 < x) {n : ℕ} (hn : 1 ≤ n) :
    Real.upperGammaPade false n a x < x^(1-a)*Real.exp x*(upperIncGamma a x).re ∧ x^(1-a)*Real.exp x*(upperIncGamma a x).re < Real.upperGammaPade true n a x := by
  sorry

/-- Real.upperGammaPade first. -/
@[dlmf 8.10.E6]
theorem Real.upperGammaPade_first {a x : ℝ} (ha : a < 1) (hx : 0 < x) :
    Real.upperGammaPade false 1 a x=x/(x+1-a) ∧ Real.upperGammaPade true 1 a x=(x+1)/(x+2-a) ∧ Real.upperGammaPade false 2 a x=x*(x+3-a)/(x^2+2*(2-a)*x+(1-a)*(2-a)) ∧ Real.upperGammaPade true 2 a x=(x^2+(5-a)*x+2)/(x^2+2*(3-a)*x+(2-a)*(3-a)) := by
  have h1 : (1:ℂ) - (a:ℂ) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub, ofReal_ne_zero]; linarith
  have h2 : (2:ℂ) - (a:ℂ) ≠ 0 := by
    rw [← ofReal_ofNat, ← ofReal_sub, ofReal_ne_zero]; linarith
  have hc : ∀ r : ℝ, 0 < r → (r:ℂ) ≠ 0 := fun r hr => ofReal_ne_zero.mpr hr.ne'
  have d1 := hc (x+1-a) (by linarith)
  have d2 := hc (x+2-a) (by linarith)
  have d3 := hc (x^2+2*(2-a)*x+(1-a)*(2-a)) (by nlinarith)
  have d4 := hc (x^2+2*(3-a)*x+(2-a)*(3-a)) (by nlinarith)
  have hx0 := hc x hx
  push_cast at d1 d2 d3 d4
  simp only [Real.upperGammaPade, cfTail]
  simp [cfContinuants.eq_def, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen, h1, h2,
    show ¬ Odd 2 by decide, show Odd 3 by decide, show ¬ Odd 4 by decide, show Odd 1 by decide,
    show Even 2 by decide, show ¬ Even 3 by decide, show Even 4 by decide, show ¬ Even 1 by decide]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← Complex.ofReal_re (x/(x+1-a))]; congr 1; push_cast; ring_nf
  · rw [← Complex.ofReal_re ((x+1)/(x+2-a))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x+(1-a))+x = x*(x+2-a) by ring]; exact mul_ne_zero hx0 d2) d2]
    ring
  · rw [← Complex.ofReal_re (x*(x+3-a)/(x^2+2*(2-a)*x+(1-a)*(2-a)))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x+(1-a))+x+(2-a)*(x+(1-a)) = x^2+2*(2-a)*x+(1-a)*(2-a) by ring]; exact d3) d3]
    ring
  · rw [← Complex.ofReal_re ((x^2+(5-a)*x+2)/(x^2+2*(3-a)*x+(2-a)*(3-a)))]; congr 1; push_cast
    rw [div_eq_div_iff (by rw [show (x:ℂ)*(x*(x+(1-a))+x+(2-a)*(x+(1-a)))+2*(x*(x+(1-a))+x) = x*(x^2+2*(3-a)*x+(2-a)*(3-a)) by ring]; exact mul_ne_zero hx0 d4) d4]
    ring

/-- incompleteGamma positive exponential integral. -/
@[dlmf 8.10.E7]
theorem incompleteGamma_positive_exponential_integral {a : ℂ} (ha : 0 < a.re) {x : ℝ} (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, (t : ℂ)^(a-1)*exp t)=Gamma a*(x : ℂ)^a*scIncGamma a (-x) := by
  have hG : Gamma a ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha
  rw [scIncGamma_integral ha, ← mul_assoc, mul_assoc (Gamma a), mul_comm ((x:ℂ)^a), ← mul_assoc,
    mul_one_div_cancel hG, one_mul]
  have hsub := intervalIntegral.integral_comp_mul_left (a := 0) (b := 1)
    (fun t : ℝ => (t : ℂ)^(a-1)*exp t) hx.ne'
  simp only [mul_zero, mul_one] at hsub
  have hJ : (∫ s in (0:ℝ)..1, ((x * s : ℝ) : ℂ)^(a-1)*exp ((x * s : ℝ) : ℂ)) =
      (x:ℂ)^(a-1) * ∫ t in (0:ℝ)..1, (t : ℂ)^(a-1)*exp (- -(x:ℂ)*t) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by
      rw [Set.uIcc_of_le zero_le_one] at hs; exact hs.1
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le hs0, neg_neg]; ring
  rw [hJ] at hsub
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have ha1 : (x:ℂ)^a = (x:ℂ) * (x:ℂ)^(a-1) := by
    conv_lhs => rw [show a = 1 + (a-1) by ring, cpow_add _ _ hx0, cpow_one]
  rw [ha1, mul_assoc, hsub, Complex.real_smul, ← mul_assoc, ofReal_inv, mul_inv_cancel₀ hx0, one_mul]

/-- The integral needs a>0; the a=0 boundary is acquired separately as a limit. -/
@[dlmf 8.10.E8]
theorem incompleteGamma_positive_exponential_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (a+1)*(a+2)-x < ((a+1)*(a+2+x))*(a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t)) ∧ a*x^(-a)*Real.exp (-x)*(∫ t in (0 : ℝ)..x, t^(a-1)*Real.exp t) < (a+1)/(a+1+x) := by
  sorry

/-- incompleteGamma positive exponential limit. -/
@[dlmf 8.10.E8]
theorem incompleteGamma_positive_exponential_limit {x : ℝ} (hx : 0 < x) :
    Tendsto (fun a : ℝ => (exp (-x : ℂ)*Gamma (a+1)*scIncGamma a (-x)).re) (𝓝[>] 0) (𝓝 (Real.exp (-x))) := by
  have h0 : scIncGamma 0 (-x) = 1 := by
    have := scIncGamma_neg_nat 0 (-(x:ℂ)); simpa using this
  have hG : ContinuousAt (fun a : ℝ => Gamma (a+1)) 0 := by
    have hd : DifferentiableAt ℂ Gamma ((0:ℝ)+1) := by
      refine Complex.differentiableAt_Gamma _ fun m => ?_
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    exact hd.continuousAt.comp (f := fun a : ℝ => (a:ℂ)+1) (by fun_prop)
  have hc : ContinuousAt (fun a : ℝ => (exp (-x : ℂ)*Gamma (a+1)*scIncGamma a (-x)).re) 0 := by
    refine Complex.continuous_re.continuousAt.comp ?_
    exact (continuousAt_const.mul hG).mul
      ((continuous_scIncGamma_param _).comp continuous_ofReal).continuousAt
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  convert this using 2
  simp only [ofReal_zero, zero_add, Complex.Gamma_one, h0, mul_one]
  rw [← ofReal_neg, ← ofReal_exp, ofReal_re]

/-- Constant c_a. -/
@[dlmf 8.10.E9]
def Real.upperGammaCa (a : ℝ) : ℝ :=
  Real.Gamma (1+a)^(1/(a-1))

/-- Constant d_a. -/
@[dlmf 8.10.E9]
def Real.upperGammaDa (a : ℝ) : ℝ :=
  Real.Gamma (1+a)^(-1/a)

/-- At x=0 the displayed scaled formula uses its zero limit. -/
@[dlmf 8.10.E10]
theorem upperIncGamma_power_bounds {a x : ℝ} (ha : 0 < a) (ha1 : a < 1) (hx : 0 < x) :
    x/(2*a)*((1+2/x)^a-1) < x^(1-a)*Real.exp x*(upperIncGamma a x).re ∧ x^(1-a)*Real.exp x*(upperIncGamma a x).re ≤ x/(a*Real.upperGammaCa a)*((1+Real.upperGammaCa a/x)^a-1) := by
  sorry

/-- upperIncGamma power bounds zero limit. -/
@[dlmf 8.10.E10]
theorem upperIncGamma_power_bounds_zero_limit {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : ℝ => x^(1-a)*Real.exp x*(upperIncGamma a x).re) (𝓝[>] 0) (𝓝 0) := by
  have hnp : ∀ k : ℕ, (a:ℂ) ≠ -k := by
    intro k h
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  have hc : ContinuousAt (fun x : ℝ => x^(1-a)*Real.exp x*(Real.Gamma a - TauCeti.lowerIncompleteGamma a x)) 0 := by
    have h1 : ContinuousAt (fun x : ℝ => x^(1-a)) 0 :=
      Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
    exact (h1.mul Real.continuous_exp.continuousAt).mul
      (continuousAt_const.sub (TauCeti.continuous_lowerIncompleteGamma a).continuousAt)
  have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  rw [Real.zero_rpow (by linarith), zero_mul, zero_mul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  have h := lowerIncGamma_add_upperIncGamma hnp hx'
  rw [lowerIncGamma_ofReal ha hx] at h
  have hu : upperIncGamma a x = ((Real.Gamma a - TauCeti.lowerIncompleteGamma a x : ℝ) : ℂ) := by
    rw [ofReal_sub, ← Complex.Gamma_ofReal]; linear_combination h
  rw [hu, ofReal_re]

/-- Lower bounding constant α_a, with its continuous value at a=1. -/
@[dlmf 8.10.E12]
def Real.gammaPAlpha (a : ℝ) : ℝ :=
  if a < 1 then 1 else Real.upperGammaDa a

/-- Upper bounding constant β_a. -/
@[dlmf 8.10.E12]
def Real.gammaPBeta (a : ℝ) : ℝ :=
  if a < 1 then Real.upperGammaDa a else 1

/-- normIncGammaP exponential bounds. -/
@[dlmf 8.10.E11]
theorem normIncGammaP_exponential_bounds {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (1-Real.exp (-Real.gammaPAlpha a*x))^a ≤ (normIncGammaPContinued a x).re ∧ (normIncGammaPContinued a x).re ≤ (1-Real.exp (-Real.gammaPBeta a*x))^a := by
  sorry

/-- The source equality condition excludes the automatic equality at x=0. -/
@[dlmf 8.10.E11]
theorem normIncGammaP_exponential_bounds_strict {a x : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hx : 0 < x) :
    (1-Real.exp (-Real.gammaPAlpha a*x))^a < (normIncGammaPContinued a x).re ∧ (normIncGammaPContinued a x).re < (1-Real.exp (-Real.gammaPBeta a*x))^a := by
  sorry

/-- normIncGammaQ diagonal bounds. -/
@[dlmf 8.10.E13]
theorem normIncGammaQ_diagonal_bounds {n : ℕ} (hn : 1 ≤ n) :
    (normIncGammaQContinued n n).re < 1/2 ∧ 1/2 < (normIncGammaQContinued n (n-1 : ℕ)).re := by
  sorry

end AAR.Confluent
