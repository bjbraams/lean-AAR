/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations
public import ToMathlib.Analysis.Asymptotics.WatsonRotated
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# Inequalities, continued fractions and asymptotic remainders, DLMF §§7.8–7.9 and 7.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat Interval
namespace AAR.Confluent

/-- Mills ratio in DLMF normalization. -/
@[dlmf 7.8.E1]
def Real.millsRatio (x : ℝ) : ℝ :=
  Real.sqrt π/2*Real.exp (x^2)*(erfc x).re

/-- Real.millsRatio integral. -/
@[dlmf 7.8.E1]
theorem Real.millsRatio_integral (x : ℝ) :
    Real.millsRatio x=Real.exp (x^2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2)) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  have hd (t : ℝ) : HasDerivAt (fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t)) (Real.exp (-t^2)) t := by
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    convert ((TauCeti.Real.hasDerivAt_erfc t).const_mul (Real.sqrt π/2)).neg using 1
    field_simp
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t))
    (m := 0) (a := x) (hd x).continuousAt.continuousWithinAt (fun t _ => hd t)
    (by simpa using (integrable_exp_neg_mul_sq one_pos).integrableOn)
    (by simpa using (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π/2)).neg)
  rw [Real.millsRatio, hre, hi]
  ring

/-- Real.millsRatio bound 2. -/
@[dlmf 7.8.E2]
theorem Real.millsRatio_bound_2 {x : ℝ} (hx : 0 ≤ x) :
    1/(x+Real.sqrt (x^2+2)) < Real.millsRatio x ∧ Real.millsRatio x ≤ 1/(x+Real.sqrt (x^2+4/π)) := by
  sorry

/-- Real.millsRatio bound 3. -/
@[dlmf 7.8.E3]
theorem Real.millsRatio_bound_3 {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π/(2*Real.sqrt π*x+2) ≤ Real.millsRatio x ∧ Real.millsRatio x < 1/(x+1) := by
  sorry

/-- Real.millsRatio bound four. -/
@[dlmf 7.8.E4]
theorem Real.millsRatio_bound_four {x : ℝ} (hx : -Real.sqrt 2/2 < x) :
    Real.millsRatio x < 2/(3*x+Real.sqrt (x^2+4)) := by
  sorry

/-- Real.millsRatio rational bounds. -/
@[dlmf 7.8.E5]
theorem Real.millsRatio_rational_bounds {x : ℝ} (hx : 0 ≤ x) :
    x^2/(2*x^2+1) ≤ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ∧ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ≤ x*Real.millsRatio x ∧ x*Real.millsRatio x < (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) ∧ (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) < (x^2+1)/(2*x^2+3) := by
  sorry

/-- Real.exp sq integral bound. -/
@[dlmf 7.8.E6]
theorem Real.exp_sq_integral_bound {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.exp (a*t^2)) < (2*Real.exp (a*x^2)+a*x^2-2)/(3*a*x) := by
  sorry

/-- Real.dawsonF integral bounds. -/
@[dlmf 7.8.E7]
theorem Real.dawsonF_integral_bounds {x : ℝ} (hx : 0 < x) :
    Real.sinh (x^2)/x < Real.exp (x^2)*Real.dawsonF x ∧ Real.exp (x^2)*Real.dawsonF x < (Real.exp (x^2)-1)/x := by
  sorry

/-- Real.erf exponential bound. -/
@[dlmf 7.8.E8]
theorem Real.erf_exponential_bound {x : ℝ} (hx : 0 < x) :
    (erf x).re < Real.sqrt (1-Real.exp (-4*x^2/π)) := by
  sorry

/-- Monotonicity theorem stated in the prose of DLMF §7.8. -/
theorem Real.dawsonF_normalized_strictAnti  :
    StrictAntiOn (fun x : ℝ => Real.dawsonF x/Real.sqrt (1-Real.exp (-2*x^2))) (Ioi 0) := by
  sorry

/-- erfc continuedFraction one. -/
@[dlmf 7.9.E1]
theorem erfc_continuedFraction_one {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then z else (k : ℂ)/2) (fun k => if Even k then z^2 else 1) (Real.sqrt π*exp (z^2)*erfc z) := by
  sorry

/-- erfc continuedFraction two. -/
@[dlmf 7.9.E2]
theorem erfc_continuedFraction_two {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then 2*z else -(2*k-1 : ℂ)*(2*k)) (fun k => 2*z^2+4*k+1) (Real.sqrt π*exp (z^2)*erfc z) := by
  sorry

/-- faddeevaW continuedFraction. -/
@[dlmf 7.9.E3]
theorem faddeevaW_continuedFraction {z : ℂ} (hz : 0 < z.im) :
    HasContinuedFraction (fun k => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) (fun _ => z) (faddeevaW z) := by
  sorry

/-- The Gaussian kernel along a ray. -/
lemma norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq (r y : ℝ) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 2 / 4))‖ = Real.exp (-(r ^ 2 * Real.cos (2 * y)) / 4) := by
  rw [Complex.norm_exp, ofReal_mul_exp_ofReal_mul_I_sq]
  congr 1
  rw [neg_re, div_ofNat_re, re_ofReal_mul, exp_ofReal_mul_I_re]
  ring

/-- The Gaussian kernel is bounded by `1` in the sector `|arg t| ≤ π/4`. -/
lemma norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one (r : ℝ) {y : ℝ} (hy : |y| ≤ π / 4) :
    ‖cexp (-(((r : ℂ) * exp (y * I)) ^ 2 / 4))‖ ≤ 1 := by
  rw [norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq, Real.exp_le_one_iff]
  have : 0 ≤ Real.cos (2 * y) := by
    rw [← Real.cos_abs, abs_mul, abs_two]
    exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg y, Real.pi_pos], by linarith⟩
  have := mul_nonneg (sq_nonneg r) this
  linarith

/-- Integrability of the Gaussian kernel along a ray `|arg t| < π/4`. -/
lemma integrableOn_gauss_rotate (c : ℝ) {θ : ℝ} (hθ : |θ| < π / 4) :
    IntegrableOn (fun r : ℝ => Real.exp (-c * r) • cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))
      (Ioi 0) := by
  have hb : 0 < (exp (((2 * θ : ℝ) : ℂ) * I) / 4).re := by
    rw [div_ofNat_re, exp_ofReal_mul_I_re]
    have : 0 < Real.cos (2 * θ) := by
      rw [← Real.cos_abs, abs_mul, abs_two]
      exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg θ, Real.pi_pos], by linarith⟩
    positivity
  refine (integrable_cexp_quadratic hb (-c : ℂ) 0).integrableOn.congr_fun (fun r _ => ?_)
    measurableSet_Ioi
  rw [Complex.real_smul, ofReal_exp, ← Complex.exp_add, ofReal_mul_exp_ofReal_mul_I_sq]
  push_cast
  ring_nf

/-- The Laplace transform of the Gaussian kernel along a ray `|arg t| < π/4` is entire. -/
lemma differentiable_laplace_gauss_rotate {θ : ℝ} (hθ : |θ| < π / 4) :
    Differentiable ℂ (fun w : ℂ => ∫ r in Ioi (0 : ℝ), cexp (-(w * r)) •
      cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := fun w =>
  (differentiableOn_integral_cexp_neg_mul_smul (integrableOn_gauss_rotate (w.re - 1) hθ)).differentiableAt
    ((isOpen_lt continuous_const continuous_re).mem_nhds (by simp))

/-- The real Laplace representation `erfc x = π^{-1/2} e^{-x²} ∫₀^∞ e^{-xt} e^{-t²/4} dt`. -/
lemma erfc_ofReal_eq_laplace_gauss (x : ℝ) :
    erfc x = 1 / Real.sqrt π * cexp (-(x : ℂ) ^ 2) *
      ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) * cexp (-((t : ℂ) ^ 2 / 4)) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  have herfc : erfc (x : ℂ) = (TauCeti.Real.erfc x : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  have hm := Real.millsRatio_integral x
  rw [Real.millsRatio, hre] at hm
  have hI : ∫ t in Ioi (x : ℝ), Real.exp (-t ^ 2) = Real.sqrt π / 2 * TauCeti.Real.erfc x := by
    have := Real.exp_pos (x ^ 2)
    field_simp at hm ⊢
    nlinarith [hm]
  -- substitution `t = 2s` and the shift `u = x + s`
  have h2 := integral_comp_mul_left_Ioi
    (fun t : ℝ => cexp (-((x : ℂ) * t)) * cexp (-((t : ℂ) ^ 2 / 4))) 0 (two_pos : (0 : ℝ) < 2)
  rw [mul_zero] at h2
  have hsh := setIntegral_Ioi_comp_add_right (fun u : ℝ => cexp (-((u : ℂ) ^ 2))) 0 x
  rw [zero_add] at hsh
  have hcomp : ∫ s in Ioi (0 : ℝ), cexp (-(x : ℂ) ^ 2) *
      (cexp (-((x : ℂ) * ((2 * s : ℝ) : ℂ))) * cexp (-((((2 * s : ℝ) : ℂ)) ^ 2 / 4))) =
      ∫ s in Ioi (0 : ℝ), cexp (-(((s + x : ℝ) : ℂ) ^ 2)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun s _ => ?_
    rw [← Complex.exp_add, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [integral_const_mul, h2, hsh] at hcomp
  have hreal : ∫ u in Ioi x, cexp (-((u : ℂ) ^ 2)) = ((∫ u in Ioi x, Real.exp (-u ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    push_cast; rfl
  rw [hreal, hI] at hcomp
  rw [herfc]
  have hcomp' : cexp (-(x : ℂ) ^ 2) * ∫ t in Ioi (0 : ℝ), cexp (-((x : ℂ) * t)) *
      cexp (-((t : ℂ) ^ 2 / 4)) = 2 * ((Real.sqrt π / 2 * TauCeti.Real.erfc x : ℝ) : ℂ) := by
    rw [← hcomp, Complex.real_smul]
    push_cast
    field_simp
  rw [mul_assoc, hcomp']
  have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  push_cast
  field_simp


/-- **Rotated Laplace representation of `erfc`**: for `|θ| < π/4` and every complex `z`,
`erfc z = π^{-1/2} e^{-z²} e^{iθ} ∫₀^∞ e^{-z e^{iθ} r} e^{-(r e^{iθ})²/4} dr`. -/
theorem erfc_eq_integral_rotate {θ : ℝ} (hθ : |θ| < π / 4) (z : ℂ) :
    erfc z = 1 / Real.sqrt π * cexp (-z ^ 2) * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z * exp (θ * I) * r)) * cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
  have hL := differentiable_laplace_gauss_rotate hθ
  simp only [smul_eq_mul] at hL
  have hd1 : Differentiable ℂ erfc := by
    unfold erfc; exact differentiable_const _ |>.sub differentiable_erf_complex
  have hd2 : Differentiable ℂ (fun z : ℂ => 1 / Real.sqrt π * cexp (-z ^ 2) * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)))) := by
    have := hL.comp (differentiable_id.mul_const (exp (θ * I)))
    exact ((differentiable_const _).mul (by fun_prop)).mul ((differentiable_const _).mul this)
  have hreal : ∀ x : ℝ, 0 < x → erfc x = 1 / Real.sqrt π * cexp (-(x : ℂ) ^ 2) *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-((x : ℂ) * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
    intro x hx
    rw [erfc_ofReal_eq_laplace_gauss x]
    congr 1
    have hy : ∀ y ∈ [[0, θ]], |y| ≤ π / 4 := fun y hy =>
      (abs_le_abs_of_mem_uIcc_zero hy).trans hθ.le
    refine integral_cexp_neg_mul_mul_eq_rotate (F := fun t => cexp (-(t ^ 2 / 4))) (σ := 1)
      (C := 1) (k := 0) one_pos (fun r _ y _ => by fun_prop) (fun r _ _ y hy' => ?_)
      (fun r _ y hy' => ?_) (fun y hy' => ?_)
    · rw [sub_self, Real.rpow_zero, mul_one]
      exact norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
    · rw [Real.rpow_zero, mul_one]
      exact norm_cexp_neg_ofReal_mul_exp_ofReal_mul_I_sq_le_one r (hy y hy')
    · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
      have := hy y hy'
      exact mul_pos hx (Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le y, Real.pi_pos],
        by linarith [le_abs_self y, Real.pi_pos]⟩)
  have hfreq : ∃ᶠ w in 𝓝[≠] (1 : ℂ), erfc w = 1 / Real.sqrt π * cexp (-w ^ 2) *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w * exp (θ * I) * r)) *
        cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4))) := by
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
    exact hreal r hr
  exact (hd1.differentiableOn.analyticOnNhd isOpen_univ).eqOn_of_preconnected_of_frequently_eq
    (hd2.differentiableOn.analyticOnNhd isOpen_univ) isPreconnected_univ (mem_univ _) hfreq
    (mem_univ z)

/-- Coefficients of `e^{-t²/4} = ∑ aₙ tⁿ`. -/
noncomputable def gaussQuarterCoeff (n : ℕ) : ℂ :=
  if Even n then (-1 / 4 : ℂ) ^ (n / 2) / ((n / 2).factorial : ℂ) else 0

/-- Partial sums of `∑ aₙ tⁿ` are partial sums of the exponential series of `-t²/4`. -/
lemma sum_gaussQuarterCoeff (t : ℂ) (M : ℕ) :
    (∑ n ∈ Finset.range (2 * M), t ^ n * gaussQuarterCoeff n =
      ∑ k ∈ Finset.range M, (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ)) ∧
    (∑ n ∈ Finset.range (2 * M + 1), t ^ n * gaussQuarterCoeff n =
      ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ)) := by
  induction M with
  | zero => simp [gaussQuarterCoeff]
  | succ M ih =>
    have h1 : ∑ n ∈ Finset.range (2 * (M + 1)), t ^ n * gaussQuarterCoeff n =
        ∑ k ∈ Finset.range (M + 1), (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ) := by
      rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, ih.2]
      have : ¬ Even (2 * M + 1) := by simp
      simp [gaussQuarterCoeff]
    refine ⟨h1, ?_⟩
    rw [Finset.sum_range_succ, h1, Finset.sum_range_succ (n := M + 1)]
    congr 1
    have he : Even (2 * (M + 1)) := even_two_mul _
    have hd : 2 * (M + 1) / 2 = M + 1 := by omega
    simp only [gaussQuarterCoeff, he, ite_true, hd]
    rw [neg_pow, div_pow, div_pow, ← pow_mul]
    ring

/-- Taylor remainders of `e^{-t²/4}` along a ray, in the form required by Watson's lemma. -/
lemma gauss_sub_sum_isBigO (θ : ℝ) (N : ℕ) :
    (fun r : ℝ => cexp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)) - ∑ n ∈ Finset.range N,
      (((r : ℂ) * exp (θ * I)) ^ ((n : ℂ) + 1 - 1)) • gaussQuarterCoeff n)
      =O[𝓝[>] 0] fun r => r ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ, N ≤ 2 * M ∧
      ∀ t : ℂ, ∑ n ∈ Finset.range N, t ^ n * gaussQuarterCoeff n =
        ∑ k ∈ Finset.range M, (-(t ^ 2 / 4)) ^ k / (k.factorial : ℂ) := by
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · exact ⟨M, le_rfl, fun t => (sum_gaussQuarterCoeff t M).1⟩
    · exact ⟨M + 1, by omega, fun t => (sum_gaussQuarterCoeff t M).2⟩
  refine IsBigO.of_bound 3 ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (zero_lt_one' ℝ))]
    with r hr hr1
  have hr : (0 : ℝ) < r := hr
  have hr1 : r < 1 := hr1
  simp only [one_re, add_sub_cancel_right, cpow_natCast, smul_eq_mul]
  rw [hM.2]
  have hb := Complex.norm_exp_sub_sum_le_norm_mul_exp (-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)) M
  have hn : ‖-(((r : ℂ) * exp (θ * I)) ^ 2 / 4)‖ = r ^ 2 / 4 := by
    rw [norm_neg, norm_div, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.le,
      norm_exp_ofReal_mul_I, mul_one]
    simp
  rw [hn] at hb
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hr.le _), Real.rpow_natCast]
  refine hb.trans ?_
  have h1 : (r ^ 2 / 4) ^ M ≤ r ^ N := by
    calc (r ^ 2 / 4) ^ M ≤ (r ^ 2) ^ M := by
          gcongr; linarith [sq_nonneg r]
      _ = r ^ (2 * M) := by rw [← pow_mul]
      _ ≤ r ^ N := pow_le_pow_of_le_one hr.le hr1.le hM.1
  have h2 : Real.exp (r ^ 2 / 4) ≤ 3 := by
    have : r ^ 2 / 4 ≤ 1 / 4 := by nlinarith
    calc Real.exp (r ^ 2 / 4) ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr this
      _ ≤ 3 := by
        have := Real.exp_one_lt_d9
        have h := Real.exp_le_exp.mpr (show (1 : ℝ) / 4 ≤ 1 by norm_num)
        linarith
  calc (r ^ 2 / 4) ^ M * Real.exp (r ^ 2 / 4) ≤ r ^ N * 3 := by
        gcongr
    _ = 3 * r ^ N := by ring


/-- `(1/2)ₙ 4ⁿ n! = (2n)!`. -/
lemma poch_half_mul_four_pow_mul_factorial (n : ℕ) :
    poch (1 / 2) n * (4 ^ n * (n.factorial : ℂ)) = ((2 * n).factorial : ℂ) := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    rw [poch_succ, show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1),
      Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    push_cast
    rw [← ih]
    ring

/-- `erfc z ~ π^{-1/2} e^{-z²} ∑ (-1)ⁿ (1/2)ₙ z^{-2n-1}` in a rotated sector. -/
theorem erfc_rotSector_asymptotic {θ δ : ℝ} (hθ : |θ| < π / 4) (hδ : 0 < δ) :
    HasAsymptoticExpansion (comap (fun z : ℂ => z * exp (θ * I)) (sectorAtTop δ))
      (fun n z => exp (-z ^ 2) * z ^ (-(2 * (n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n * poch (1 / 2) n / Real.sqrt π) erfc := by
  have hθ' : |θ| < π / 2 := by linarith [Real.pi_pos]
  have hW := hasAsymptoticExpansion_integral_cexp_smul_rotate_comap
    (F := fun t => cexp (-(t ^ 2 / 4))) (a := gaussQuarterCoeff) (μ := 1) (c := 0) hθ'
    (by norm_num) hδ (integrableOn_gauss_rotate 0 hθ) (gauss_sub_sum_isBigO θ)
  have hE := hW.even (fun n => by
    have : ¬ Even (2 * n + 1) := by simp
    simp [gaussQuarterCoeff, this])
  have h3 := (hE.const_smul (1 / Real.sqrt π : ℂ)).mul_left (fun z : ℂ => cexp (-z ^ 2))
  refine ((h3.congr' (Eventually.of_forall fun z => ?_)).congr_scale fun n =>
    Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only [Pi.smul_apply, smul_eq_mul]
    rw [erfc_eq_integral_rotate hθ z]
    ring
  · simp only
    push_cast
    ring_nf
  · funext n
    have hπ : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hp := poch_half_mul_four_pow_mul_factorial n
    simp only [Pi.smul_apply, smul_eq_mul, gaussQuarterCoeff, even_two_mul, ite_true,
      show 2 * n / 2 = n by omega]
    rw [show ((2 * n : ℕ) : ℂ) + 1 = ((2 * n : ℕ) : ℂ) + 1 from rfl,
      Complex.Gamma_nat_eq_factorial, ← hp]
    field_simp
    rw [mul_assoc, ← mul_pow]
    norm_num


/-- erfc sector asymptotic. -/
@[dlmf 7.12.E1]
theorem erfc_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) erfc ∧ HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => -(-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => erfc (-z)-2) := by
  set d := min δ (π / 4) with hd
  have hd0 : 0 < d := lt_min hδ (by positivity)
  have hdδ : d ≤ δ := min_le_left _ _
  have hdπ : d ≤ π / 4 := min_le_right _ _
  have hcov := le_sup_comap_rotate (α := 3 * π / 4 - δ) (β := π / 4 - d / 2) (γ := π / 2 - d / 2)
    (by linarith) (by linarith) (by linarith) (by linarith)
  have hcos : 0 < Real.cos (π / 2 - d / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩
  have hβ : |π / 4 - d / 2| < π / 4 := by
    rw [abs_lt]; constructor <;> linarith
  have h1 := erfc_rotSector_asymptotic (θ := -(π / 4 - d / 2)) (by rwa [abs_neg]) hcos
  have h2 := erfc_rotSector_asymptotic (θ := π / 4 - d / 2) hβ hcos
  have hA : HasAsymptoticExpansion (sector (3 * π / 4 - δ))
      (fun n z => exp (-z ^ 2) * z ^ (-(2 * (n : ℂ) + 1)))
      (fun n => (-1 : ℂ) ^ n * poch (1 / 2) n / Real.sqrt π) erfc :=
    (h1.sup h2).mono hcov
  refine ⟨hA, ?_⟩
  refine (hA.neg.congr' (Eventually.of_forall fun z => ?_)).congr_coeff ?_
  · simp only [Pi.neg_apply]
    rw [erfc_negative]
    ring
  · funext n
    simp only [Pi.neg_apply]
    ring


/-- Unnormalized erfc remainder. -/
def erfcAsymptoticRemainder (N : ℕ) (z : ℂ) : ℂ :=
  erfc z-exp (-z^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/z^(2*n+1)

/-- `(1/2)_n = Γ(n+1/2)/√π`, as a real number. -/
theorem poch_half_eq_Gamma (n : ℕ) :
    poch (1/2) n = ((Real.Gamma (n+1/2)/Real.sqrt π : ℝ) : ℂ) := by
  induction n with
  | zero =>
    rw [poch_zero]; simp only [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq]
    rw [div_self (Real.sqrt_pos.mpr Real.pi_pos).ne']; simp
  | succ n ih =>
    rw [poch_succ, ih]
    have : ((n+1:ℕ):ℝ)+1/2 = ((n:ℝ)+1/2)+1 := by push_cast; ring
    rw [this, Real.Gamma_add_one (by positivity)]
    push_cast; ring

/-- `r e^{iy}` lies in the slit plane for `r > 0` and `|y| < π`. -/
lemma ofReal_mul_exp_mem_slitPlane {r y : ℝ} (hr : 0 < r) (hy : |y| < π) :
    (r : ℂ) * exp (y * I) ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_cases hs : Real.sin y = 0
  · left
    have hy0 : y = 0 := (Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le y])
      (by linarith [le_abs_self y])).mp hs
    subst hy0; simp [hr]
  · right
    rw [im_ofReal_mul, exp_ofReal_mul_I_im]
    exact mul_ne_zero hr.ne' hs

/-- Bound for the kernel `t^{-1/2}/(1+t)` of the Laplace form of `erfc` along rays. -/
lemma norm_erfcKernel_le {θ c : ℝ} (hc0 : 0 < c)
    (hc : ∀ s : ℝ, 0 ≤ s → ∀ u : ℝ, |u| ≤ |θ| → c ≤ ‖1 + (s : ℂ) * exp (u * I)‖)
    (hθ : |θ| < π) {r y : ℝ} (hr : 0 < r) (hy : |y| ≤ |θ|) :
    ‖((r : ℂ) * exp (y * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (y * I))⁻¹‖ ≤
      1 / c * r ^ (-1/2 : ℝ) := by
  have hy' : |y| < π := lt_of_le_of_lt hy hθ
  rw [abs_lt] at hy'
  rw [norm_mul, norm_inv, ofReal_mul_exp_cpow hr hy'.1 hy'.2.le, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hr,
    show (y : ℂ) * I * (-1/2 : ℂ) = ((-y/2 : ℝ) : ℂ) * I by push_cast; ring,
    norm_exp_ofReal_mul_I, mul_one]
  have h1 := hc r hr.le y hy
  have hre : ((-1/2 : ℂ)).re = -1/2 := by norm_num
  rw [hre]
  have hp : 0 < r ^ (-1/2 : ℝ) := Real.rpow_pos_of_pos hr _
  calc r ^ (-1/2 : ℝ) * ‖1 + (r : ℂ) * exp (y * I)‖⁻¹ ≤ r ^ (-1/2 : ℝ) * (1 / c) := by
        gcongr; rw [one_div]; exact inv_anti₀ hc0 h1
    _ = _ := by ring

/-- If `re z > 0` and `re (z e^{iθ}) > 0` with `|θ| < π`, then `re (z e^{iy}) > 0` for every
`y` between `0` and `θ`. -/
lemma re_mul_exp_pos_of_mem_uIcc_of_lt_pi {z : ℂ} {θ y : ℝ} (hθ : |θ| < π) (hz : 0 < z.re)
    (hzθ : 0 < (z * exp (θ * I)).re) (hy : y ∈ [[0, θ]]) : 0 < (z * exp (y * I)).re := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  have h0 : |arg z| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hz)
  have h1 : |arg z + θ| < π / 2 := by
    rw [re_mul_exp_ofReal_mul_I] at hzθ
    have hc : 0 < Real.cos (arg z + θ) := by
      by_contra hc; push Not at hc; nlinarith [norm_nonneg z]
    rw [abs_lt] at h0 hθ
    exact abs_lt_pi_div_two_of_cos_pos' (by linarith) (by linarith) hc
  have h2 : |arg z + y| < π / 2 := by
    rcases le_total 0 θ with h | h
    · rw [uIcc_of_le h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
    · rw [uIcc_of_ge h] at hy
      rw [abs_lt] at h0 h1 ⊢; constructor <;> linarith [hy.1, hy.2]
  rw [re_mul_exp_ofReal_mul_I]
  refine mul_pos (norm_pos_iff.mpr hz0) ?_
  rw [← Real.cos_abs]
  exact Real.cos_pos_of_mem_Ioo ⟨by linarith [abs_nonneg (arg z + y), Real.pi_pos], h2⟩

/-- **Rotated Laplace form of `erfc`** (DLMF 7.7.2 continued): for `|θ| < π` and `z` in the
quarter-plane sector `|im (z e^{iθ/2})| < re (z e^{iθ/2})`,
`erfc z = e^{-z²}/π · e^{iθ} ∫₀^∞ e^{-z² e^{iθ} r} (r e^{iθ})^{-1/2}/(1 + r e^{iθ}) dr`. -/
theorem erfc_eq_integral_rotate_laplace {θ : ℝ} (hθ : |θ| < π) {z : ℂ}
    (hz : |(z * exp (((θ / 2 : ℝ) : ℂ) * I)).im| < (z * exp (((θ / 2 : ℝ) : ℂ) * I)).re) :
    erfc z = exp (-z ^ 2) / π * (exp (θ * I) * ∫ r in Ioi (0 : ℝ),
      cexp (-(z ^ 2 * exp (θ * I) * r)) *
        (((r : ℂ) * exp (θ * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (θ * I))⁻¹)) := by
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp hθ
  set ω := exp (((θ / 2 : ℝ) : ℂ) * I) with hω
  set U : Set ℂ := {z : ℂ | |(z * ω).im| < (z * ω).re} with hU
  have hUo : IsOpen U := isOpen_lt (by fun_prop) (by fun_prop)
  have hUc : Convex ℝ U := by
    intro x hx y hy a b ha hb hab
    have hx : |(x * ω).im| < (x * ω).re := hx
    have hy : |(y * ω).im| < (y * ω).re := hy
    show |((a • x + b • y) * ω).im| < ((a • x + b • y) * ω).re
    have hre : ((a • x + b • y) * ω).re = a * (x * ω).re + b * (y * ω).re := by
      simp only [add_mul, add_re, Complex.real_smul, mul_assoc, re_ofReal_mul]
    have him : ((a • x + b • y) * ω).im = a * (x * ω).im + b * (y * ω).im := by
      simp only [add_mul, add_im, Complex.real_smul, mul_assoc, im_ofReal_mul]
    rw [hre, him]
    rw [abs_lt] at hx hy ⊢
    rcases ha.lt_or_eq with ha | ha
    · constructor
      · nlinarith [mul_nonneg hb (by linarith [hy.1] : 0 ≤ (y * ω).re + (y * ω).im)]
      · nlinarith [mul_nonneg hb (by linarith [hy.2] : 0 ≤ (y * ω).re - (y * ω).im)]
    · subst ha; rw [zero_add] at hab; subst hab
      constructor <;> linarith [hy.1, hy.2]
  have hsq : ∀ z : ℂ, z ^ 2 * exp (θ * I) = (z * ω) ^ 2 := by
    intro z; rw [mul_pow, hω, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hUre : ∀ z ∈ U, 0 < (z ^ 2 * exp (θ * I)).re := by
    intro z hz
    have hz : |(z * ω).im| < (z * ω).re := hz
    rw [hsq, sq, mul_re]
    have h := abs_lt.mp hz
    nlinarith [abs_nonneg (z * ω).im]
  set K : ℂ → ℂ := fun t => t ^ (-1/2 : ℂ) * (1 + t)⁻¹ with hK
  have hKd : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      DifferentiableAt ℂ K ((r : ℂ) * exp (y * I)) := by
    intro r hr y hy
    have hm := ofReal_mul_exp_mem_slitPlane hr (lt_of_le_of_lt hy hθ)
    have hne : 1 + (r : ℂ) * exp (y * I) ≠ 0 := fun h0 => by
      have := hc r hr.le y hy; rw [h0, norm_zero] at this; linarith
    exact (differentiableAt_id.cpow (differentiableAt_const _) hm).mul
      (((differentiableAt_const _).add differentiableAt_id).inv hne)
  set G : ℝ → ℂ := fun r => K ((r : ℂ) * exp (θ * I)) with hG
  have hGc : ContinuousOn G (Ioi 0) := fun r hr =>
    ((hKd r hr θ le_rfl).continuousAt.comp (x := r)
      (f := fun r : ℝ => (r : ℂ) * exp (θ * I)) (by fun_prop)).continuousWithinAt
  have hLd := differentiableOn_integral_cexp_neg_mul_smul_of_le_rpow (G := G) (C := 1 / c)
    (D := 0) (k := -1/2) (by norm_num) hGc (fun r hr => by
      rw [add_zero]; exact norm_erfcKernel_le hc0 hc hθ hr le_rfl)
  simp only [smul_eq_mul] at hLd
  have hR : DifferentiableOn ℂ (fun z : ℂ => exp (-z ^ 2) / π * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z ^ 2 * exp (θ * I) * r)) * G r)) U := by
    refine (DifferentiableOn.div_const (by fun_prop) _).mul ((differentiableOn_const _).mul ?_)
    exact hLd.comp (by fun_prop : DifferentiableOn ℂ (fun z : ℂ => z ^ 2 * exp (θ * I)) U)
      (fun z hz => hUre z hz)
  have hd1 : Differentiable ℂ erfc := by
    unfold erfc; exact differentiable_const _ |>.sub differentiable_erf_complex
  -- agreement near `z₀ = e^{-iθ/4}`
  have hagree : ∀ w : ℂ, |w.im| < w.re → w ∈ U → erfc w = exp (-w ^ 2) / π *
      (exp (θ * I) * ∫ r in Ioi (0 : ℝ), cexp (-(w ^ 2 * exp (θ * I) * r)) * G r) := by
    intro w hw hwU
    have hw1 : 0 < w.re := lt_of_le_of_lt (abs_nonneg _) hw
    have hw2 : 0 < (w ^ 2).re := by
      rw [sq, mul_re]; have h := abs_lt.mp hw; nlinarith [abs_nonneg w.im]
    rw [erfc_eq_laplace hw1 hw2]
    congr 1
    have hlap : (∫ t : ℝ in Ioi 0, exp (-w ^ 2 * t) * (t : ℂ) ^ (-1/2 : ℂ) * (1 + (t : ℂ)) ^ (-1 : ℂ)) =
        ∫ t : ℝ in Ioi 0, cexp (-(w ^ 2 * t)) * K t :=
      setIntegral_congr_fun measurableSet_Ioi fun t _ => by
        rw [hK]; simp only [cpow_neg_one]; ring_nf
    rw [hlap]
    refine integral_cexp_neg_mul_mul_eq_rotate (F := K) (σ := 1/2) (C := 1 / c) (k := -1/2)
      (by norm_num) (fun r hr y hy => hKd r hr y (abs_le_abs_of_mem_uIcc_zero hy))
      (fun r hr _ y hy => ?_) (fun r hr y hy => ?_)
      (fun y hy => re_mul_exp_pos_of_mem_uIcc_of_lt_pi hθ hw2 (hUre w hwU) hy)
    · rw [show (1/2 : ℝ) - 1 = -1/2 by norm_num]
      exact norm_erfcKernel_le hc0 hc hθ hr (abs_le_abs_of_mem_uIcc_zero hy)
    · exact norm_erfcKernel_le hc0 hc hθ (by linarith) (abs_le_abs_of_mem_uIcc_zero hy)
  set z₀ : ℂ := exp (((-(θ / 4)) : ℝ) * I) with hz₀
  have hθ4 : |θ / 4| < π / 4 := by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 4)]; linarith
  have hsec : ∀ u : ℝ, |u| < π / 4 → |(exp (u * I)).im| < (exp (u * I)).re := by
    intro u hu
    rw [exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
    have hu' := abs_lt.mp hu
    rcases le_total 0 u with h | h
    · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith))]
      rw [← Real.cos_pi_div_two_sub]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two h (by linarith) (by linarith : u < π/2 - u)
      linarith
    · rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)),
        ← Real.sin_neg, ← Real.cos_neg u, ← Real.cos_pi_div_two_sub]
      have := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith)
        (by linarith : -u < π/2 - -u)
      linarith
  have hz₀a : |z₀.im| < z₀.re := hsec _ (by rwa [abs_neg])
  have hz₀U : z₀ ∈ U := by
    show |(z₀ * ω).im| < (z₀ * ω).re
    rw [hz₀, hω, ← Complex.exp_add, show ((-(θ / 4) : ℝ) : ℂ) * I + ((θ / 2 : ℝ) : ℂ) * I =
      ((θ / 4 : ℝ) : ℂ) * I by push_cast; ring]
    exact hsec _ hθ4
  have hev : erfc =ᶠ[𝓝 z₀] (fun z : ℂ => exp (-z ^ 2) / π * (exp (θ * I) *
      ∫ r in Ioi (0 : ℝ), cexp (-(z ^ 2 * exp (θ * I) * r)) * G r)) := by
    have hV : IsOpen {w : ℂ | |w.im| < w.re} := isOpen_lt (by fun_prop) continuous_re
    filter_upwards [hV.mem_nhds hz₀a, hUo.mem_nhds hz₀U] with w hw hwU
    exact hagree w hw hwU
  exact (hd1.differentiableOn.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hR.analyticOnNhd hUo) hUc.isPreconnected hz₀U hev hz

/-- Sector-dependent next-term bounds from DLMF §7.12(i). -/
theorem erfc_remainder_bound {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (N : ℕ) :
    ‖erfcAsymptoticRemainder N z‖ ≤ (if |arg z| ≤ π/4 then 1 else 1/Real.sin (2*|arg z|))*‖exp (-z^2)/Real.sqrt π*poch (1/2) N/z^(2*N+1)‖ := by
  set α := arg z with hα
  set θ : ℝ := -2 * α with hθdef
  have hθ : |θ| < π := by
    rw [hθdef, abs_mul, abs_neg, abs_two]; linarith
  have hθ2 : θ / 2 = -α := by rw [hθdef]; ring
  set ω := exp (((θ / 2 : ℝ) : ℂ) * I) with hω
  set e := exp (θ * I) with he
  set s : ℝ := ‖z‖ with hs
  have hs0 : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hz0
  have hzω : z * ω = (s : ℂ) := by
    conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
    rw [hω, hθ2, mul_assoc, ← Complex.exp_add]
    push_cast
    simp [hs, hα]
  have hωne : ω ≠ 0 := Complex.exp_ne_zero _
  have hωn : ‖ω‖ = 1 := by rw [hω]; exact norm_exp_ofReal_mul_I _
  have heω : e = ω ^ 2 := by
    rw [he, hω, ← Complex.exp_nat_mul]; push_cast; ring_nf
  have hen : ‖e‖ = 1 := by rw [he]; exact norm_exp_ofReal_mul_I _
  have hz' : |(z * ω).im| < (z * ω).re := by
    rw [hzω, ofReal_im, ofReal_re, abs_zero]; exact hs0
  have hrep := erfc_eq_integral_rotate_laplace hθ hz'
  have hz2e : z ^ 2 * e = ((s ^ 2 : ℝ) : ℂ) := by
    rw [heω, ← mul_pow, hzω]; push_cast; ring
  -- the sector constant
  set L : ℝ := if |arg z| ≤ π/4 then 1 else Real.sin (2*|arg z|) with hL
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      exact Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hLden : ∀ r : ℝ, 0 ≤ r → L ≤ ‖1 + (r : ℂ) * e‖ := by
    intro r hr
    rw [hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp hr ?_
      rw [← Real.cos_abs, hθdef, abs_mul, abs_neg, abs_two]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg α, Real.pi_pos],
        by linarith⟩
    · have hsin2 : |Real.sin θ| = Real.sin (2 * |arg z|) := by
        have hpos : 0 ≤ Real.sin (2 * |arg z|) :=
          Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
        have key : |Real.sin (-2 * α)| = |Real.sin (2 * |α|)| := by
          rcases le_total 0 α with h0 | h0
          · rw [abs_of_nonneg h0, neg_mul, Real.sin_neg, abs_neg]
          · rw [abs_of_nonpos h0]; ring_nf
        rw [hθdef, key, abs_of_nonneg hpos]
      rw [← hsin2]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  have hden0 : ∀ r : ℝ, 0 ≤ r → 1 + (r : ℂ) * e ≠ 0 := fun r hr h0 => by
    have := hLden r hr; rw [h0, norm_zero] at this; linarith
  -- real moments
  set g : ℕ → ℝ → ℝ := fun n r => r ^ ((n : ℝ) - 1/2) * Real.exp (-(s ^ 2 * r)) with hg
  have hmom (n : ℕ) : (∫ r in Ioi (0:ℝ), g n r) = Real.Gamma (n+1/2) / s^(2*n+1) := by
    have hr0 : 0 < s ^ 2 := by positivity
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1/2) (by positivity) hr0
    rw [show (n:ℝ)+1/2-1 = (n:ℝ)-1/2 by ring] at this
    simp only [hg]
    rw [this, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, ← Real.rpow_two,
      ← Real.rpow_mul hs0.le, show 2*((n:ℝ)+1/2) = ((2*n+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  have hint (n : ℕ) : IntegrableOn (g n) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)-1/2) (b := s ^ 2)
      (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos (by positivity)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [hg, Real.rpow_one, neg_mul]
  -- pointwise decomposition
  set R : ℝ → ℂ := fun r => ω⁻¹ * (((r ^ (-1/2 : ℝ) * Real.exp (-(s ^ 2 * r)) : ℝ) : ℂ) *
    ((-((r : ℂ) * e)) ^ N * (1 + (r : ℂ) * e)⁻¹)) with hR
  have hpt : ∀ r ∈ Ioi (0 : ℝ), cexp (-(z ^ 2 * e * r)) *
      (((r : ℂ) * e) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * e)⁻¹) =
      ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ) + R r := by
    intro r hr
    have hr : (0 : ℝ) < r := hr
    have hd := hden0 r hr.le
    have hgeom : (1 + (r : ℂ) * e)⁻¹ =
        ∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n + (-((r : ℂ) * e))^N * (1 + (r : ℂ) * e)⁻¹ := by
      have hgs := geom_sum_mul (-((r : ℂ) * e)) N
      have hS : (∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n) * (1 + (r : ℂ) * e) =
          1 - (-((r : ℂ) * e))^N := by linear_combination (-1 : ℂ) * hgs
      have hS' : ∑ n ∈ Finset.range N, (-((r : ℂ) * e))^n =
          (1 - (-((r : ℂ) * e))^N) * (1 + (r : ℂ) * e)⁻¹ := by
        rw [← hS, mul_assoc, mul_inv_cancel₀ hd, mul_one]
      rw [hS']; ring
    have hcp : ((r : ℂ) * e) ^ (-1/2 : ℂ) = ((r ^ (-1/2 : ℝ) : ℝ) : ℂ) * ω⁻¹ := by
      rw [he, ofReal_mul_exp_cpow hr (by linarith [(abs_lt.mp hθ).1]) (abs_lt.mp hθ).2.le,
        Complex.ofReal_cpow hr.le, hω, ← Complex.exp_neg]
      push_cast
      ring_nf
    have hpow (n : ℕ) : r ^ ((n:ℝ) - 1/2) = r ^ (-1/2 : ℝ) * r ^ n := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]; ring_nf
    have hex : cexp (-(z ^ 2 * e * r)) = ((Real.exp (-(s ^ 2 * r)) : ℝ) : ℂ) := by
      rw [hz2e, Complex.ofReal_exp]; push_cast; ring_nf
    rw [hcp, hex, hgeom, hR]
    simp only [hg, hpow]
    push_cast
    rw [mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun n _ => ?_
      rw [neg_pow ((r : ℂ) * e), mul_pow, neg_pow e]; ring
    · ring
  have hTi : ∀ n, IntegrableOn (fun r : ℝ => ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ)) (Ioi 0) :=
    fun n => ((hint n).ofReal).const_mul _
  have hTint : ∀ n, ∫ r in Ioi (0:ℝ), ω⁻¹ * (-e) ^ n * ((g n r : ℝ) : ℂ) =
      ω⁻¹ * (-e) ^ n * ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ) := by
    intro n; rw [integral_const_mul, integral_complex_ofReal, hmom]
  have hRb : ∀ r ∈ Ioi (0:ℝ), ‖R r‖ ≤ 1 / L * g N r := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    rw [hR]; simp only
    rw [norm_mul, norm_inv, hωn, inv_one, one_mul, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), norm_mul, norm_pow, norm_neg, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg hr.le, hen, mul_one, norm_inv]
    have h1 := hLden r hr.le
    have h2 : ‖1 + (r : ℂ) * e‖⁻¹ ≤ 1 / L := by rw [one_div]; exact inv_anti₀ hL0 h1
    have hpow : r ^ ((N:ℝ) - 1/2) = r ^ (-1/2 : ℝ) * r ^ N := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hr]; ring_nf
    simp only [hg, hpow]
    have h0 : 0 ≤ r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N := by positivity
    calc r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * (r ^ N * ‖1 + (r:ℂ) * e‖⁻¹)
        = (r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N) * ‖1 + (r:ℂ) * e‖⁻¹ := by ring
      _ ≤ (r ^ (-1/2:ℝ) * Real.exp (-(s^2*r)) * r ^ N) * (1 / L) := by gcongr
      _ = _ := by ring
  have hbi : IntegrableOn (fun r => 1 / L * g N r) (Ioi 0) := (hint N).const_mul _
  have hRc : ContinuousOn R (Ioi 0) := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    have hd := hden0 r hr.le
    refine ContinuousAt.continuousWithinAt ?_
    rw [hR]
    refine continuousAt_const.mul (ContinuousAt.mul ?_ ?_)
    · exact Complex.continuous_ofReal.continuousAt.comp
        ((Real.continuousAt_rpow_const _ _ (Or.inl hr.ne')).mul (by fun_prop))
    · exact (by fun_prop : Continuous fun r : ℝ => (-((r:ℂ) * e)) ^ N).continuousAt.mul
        (ContinuousAt.inv₀ (by fun_prop) hd)
  have hRi : IntegrableOn R (Ioi 0) :=
    Integrable.mono' hbi (hRc.aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  have hint2 : ∫ r in Ioi (0:ℝ), cexp (-(z ^ 2 * e * r)) *
      (((r : ℂ) * e) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * e)⁻¹) =
      ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n * ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ) +
        ∫ r in Ioi (0:ℝ), R r := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add
      (integrable_finsetSum _ fun n _ => hTi n) hRi, integral_finsetSum _ fun n _ => hTi n]
    simp only [hTint]
  have hRn := norm_integral_le_of_norm_le hbi
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hRb))
  have hgN : ∫ r in Ioi (0:ℝ), 1 / L * g N r = 1 / L * (Real.Gamma (N+1/2) / s^(2*N+1)) := by
    rw [integral_const_mul, hmom]
  rw [hgN] at hRn
  -- assemble
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) * (Real.sqrt π : ℂ) = π := by
    exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
  have hsq0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hzpow : ∀ n : ℕ, z ^ (2*n+1) = (s : ℂ) ^ (2*n+1) / ω ^ (2*n+1) := by
    intro n; rw [← hzω, mul_pow]; field_simp
  have hterm : ∀ n ∈ Finset.range N, exp (-z^2) / π * (e * (ω⁻¹ * (-e) ^ n *
      ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ))) =
      exp (-z^2) / Real.sqrt π * ((-1 : ℂ)^n * poch (1/2) n / z^(2*n+1)) := by
    intro n _
    rw [poch_half_eq_Gamma, hzpow, heω, neg_pow (ω^2)]
    have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs0.ne'
    push_cast
    rw [← hsqrt]
    field_simp
    ring
  have hsum : exp (-z^2) / π * (e * ∑ n ∈ Finset.range N, ω⁻¹ * (-e) ^ n *
      ((Real.Gamma (n+1/2) / s^(2*n+1) : ℝ) : ℂ)) =
      exp (-z^2) / Real.sqrt π * ∑ n ∈ Finset.range N, (-1 : ℂ)^n * poch (1/2) n / z^(2*n+1) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl hterm
  have hmain : erfcAsymptoticRemainder N z = exp (-z^2) / π * (e * ∫ r in Ioi (0:ℝ), R r) := by
    rw [erfcAsymptoticRemainder, hrep, ← he, hint2, mul_add, mul_add, hsum]
    ring
  rw [hmain, norm_mul, norm_mul, hen, one_mul, norm_div, Complex.norm_real,
    Real.norm_of_nonneg Real.pi_pos.le]
  have hG0 : 0 < Real.Gamma (N+1/2) := Real.Gamma_pos_of_pos (by positivity)
  have hrhs : ‖exp (-z^2)/Real.sqrt π*poch (1/2) N/z^(2*N+1)‖ =
      ‖exp (-z^2)‖ / π * (Real.Gamma (N+1/2) / s^(2*N+1)) := by
    rw [poch_half_eq_Gamma, norm_div, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      norm_pow, ← hs, Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (by positivity : 0 ≤ Real.Gamma (N+1/2) / Real.sqrt π)]
    have h := Real.mul_self_sqrt Real.pi_pos.le
    have h0 : 0 < Real.sqrt π := Real.sqrt_pos.mpr Real.pi_pos
    field_simp
    rw [Real.sq_sqrt Real.pi_pos.le]
  rw [hrhs]
  have hc : (if |arg z| ≤ π/4 then (1:ℝ) else 1/Real.sin (2*|arg z|)) = 1 / L := by
    rw [hL]; split_ifs <;> simp
  rw [hc]
  calc ‖exp (-z^2)‖ / π * ‖∫ r in Ioi (0:ℝ), R r‖
      ≤ ‖exp (-z^2)‖ / π * (1 / L * (Real.Gamma (N+1/2) / s^(2*N+1))) := by gcongr
    _ = _ := by ring

/-- Real Laplace form of `erfc x` for `x > 0`. -/
theorem erfc_ofReal_eq_laplace {x : ℝ} (hx : 0 < x) :
    TauCeti.Real.erfc x = Real.exp (-x^2)/π *
      ∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) := by
  have h := erfc_eq_laplace (z := (x:ℂ)) (by simpa using hx) (by rw [← ofReal_pow, ofReal_re]; positivity)
  have hk : (∫ t : ℝ in Ioi 0, exp (-(x:ℂ)^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)) =
      ((∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    push_cast
    rw [ofReal_cpow ht.le, ofReal_cpow (by linarith)]
    push_cast; ring_nf
  have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  rw [hk, herfc] at h
  have := congrArg re h
  rw [ofReal_re] at this
  rw [this, show -(x:ℂ)^2 = ((-x^2:ℝ):ℂ) by push_cast; ring, ← ofReal_exp,
    show ((Real.exp (-x^2):ℂ)/(π:ℂ)) = ((Real.exp (-x^2)/π:ℝ):ℂ) by push_cast; ring,
    ← ofReal_mul, ofReal_re]

/-- Signed real remainder from DLMF §7.12(i). -/
theorem erfc_remainder_sign {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(erfcAsymptoticRemainder N x).re := by
  set r := x^2 with hr
  have hr0 : 0 < r := by positivity
  -- moments
  have hmom (n : ℕ) : (∫ u in Ioi (0:ℝ), u^((n:ℝ)-1/2) * Real.exp (-(r*u))) =
      Real.Gamma (n+1/2) / x^(2*n+1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1/2) (by positivity) hr0
    rw [show (n:ℝ)+1/2-1 = (n:ℝ)-1/2 by ring] at this
    rw [this, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, hr, ← Real.rpow_two,
      ← Real.rpow_mul hx.le, show 2*((n:ℝ)+1/2) = ((2*n+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  have hint (n : ℕ) : IntegrableOn (fun u : ℝ => u^((n:ℝ)-1/2) * Real.exp (-(r*u))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)-1/2) (b := r)
      (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hr0
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  set g : ℝ → ℝ := fun u => u^((N:ℝ)-1/2) * Real.exp (-(r*u)) * (1+u)⁻¹ with hg
  have hgint : IntegrableOn g (Ioi 0) := by
    refine (hint N).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hu : (0:ℝ) < u := hu
      refine ContinuousAt.continuousWithinAt ?_
      have : 1 + u ≠ 0 := by linarith
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu.ne')).mul (by fun_prop)).mul
        ((continuousAt_const.add continuousAt_id).inv₀ this)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      have hu : (0:ℝ) < u := hu
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1+u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have : 0 ≤ u^((N:ℝ)-1/2) * Real.exp (-(r*u)) := by positivity
      simp only [hg]
      nlinarith
  have hgnn : 0 ≤ ∫ u in Ioi (0:ℝ), g u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu : (0:ℝ) < u := hu; positivity
  -- the kernel decomposition
  have hdec : (∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ)) =
      ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) +
        (-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u := by
    have hpt : ∀ u ∈ Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) =
        ∑ n ∈ Finset.range N, (-1:ℝ)^n * (u^((n:ℝ)-1/2) * Real.exp (-(r*u))) + (-1:ℝ)^N * g u := by
      intro u hu
      have hu : (0:ℝ) < u := hu
      have hgeom : (1+u)⁻¹ = ∑ n ∈ Finset.range N, (-u)^n + (-u)^N * (1+u)⁻¹ := by
        have h := geom_sum_mul (-u) N
        have h1 : 1 + u ≠ 0 := by linarith
        have hS : (∑ n ∈ Finset.range N, (-u)^n) = (1 - (-u)^N) * (1+u)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq₀ h1]; linear_combination (-1)*h
        rw [hS]; ring
      have hpow (n : ℕ) : u^((n:ℝ)-1/2) = u^(-1/2:ℝ) * u^n := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hu]; ring_nf
      rw [Real.rpow_neg_one, hgeom, mul_add, Finset.mul_sum]
      simp only [hg, hpow, hr]
      congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_; rw [neg_pow]; ring
      · rw [neg_pow]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add, integral_finsetSum]
    · congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_const_mul, hmom]
      · rw [integral_const_mul]
    · exact fun n _ => (hint n).const_mul _
    · exact integrable_finsetSum _ fun n _ => (hint n).const_mul _
    · exact hgint.const_mul _
  -- the remainder
  have hR : (erfcAsymptoticRemainder N x).re = Real.exp (-x^2)/π * ((-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u) := by
    have hsum : (exp (-(x:ℂ)^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/(x:ℂ)^(2*n+1)) =
        ((Real.exp (-x^2)/π * ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) : ℝ) : ℂ) := by
      simp only [poch_half_eq_Gamma]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hp : (Real.sqrt π:ℂ)*Real.sqrt π = π := by exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
      have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
      rw [← hp]; field_simp
    have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
      rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
    rw [erfcAsymptoticRemainder, hsum, herfc, ← ofReal_sub, ofReal_re, erfc_ofReal_eq_laplace hx, hdec]
    ring
  rw [hR, ← mul_assoc, mul_comm ((-1:ℝ)^N), mul_assoc, ← mul_assoc ((-1:ℝ)^N), ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have : 0 ≤ Real.exp (-x^2)/π := by positivity
  exact mul_nonneg this hgnn

/-- The n-th auxiliary Fresnel asymptotic term. -/
def fresnelAsymptoticTerm (aux : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^n*poch (1/2) (2*n+if aux then 1 else 0)/(π*z*(π*z^2/2)^(2*n+if aux then 1 else 0))

/-- Finite Fresnel auxiliary remainder. -/
@[dlmf 7.12.E4, dlmf 7.12.E5]
def fresnelAsymptoticRemainder (aux : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z)-∑ n ∈ Finset.range N, fresnelAsymptoticTerm aux n z

/-- `e^{ζ²} erfc ζ ~ π^{-1/2} ∑ (-1)^m (1/2)_m ζ^{-2m-1}` in the sector `|arg ζ| ≤ 3π/4 - δ`. -/
lemma exp_sq_mul_erfc_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)))
      (fun n => (-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => exp (z^2) * erfc z) := by
  have h := (erfc_sector_asymptotic hδ hδ1).1.mul_left (fun z => exp (z^2))
  have hφ : (fun (n : ℕ) (z : ℂ) => exp (z^2) * (exp (-z^2) * z^(-(2*(n : ℂ)+1)))) =
      fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)) := by
    funext n z; rw [← mul_assoc, ← Complex.exp_add]; simp
  rw [hφ] at h
  simp only [smul_eq_mul] at h
  exact h

/-- `arg (z e^{iθ}) = arg z + θ` when `arg z + θ ∈ (-π, π]`. -/
lemma arg_mul_exp_ofReal_mul_I {z : ℂ} (hz : z ≠ 0) {θ : ℝ} (h1 : -π < arg z + θ)
    (h2 : arg z + θ ≤ π) : arg (z * exp (θ * I)) = arg z + θ := by
  have hlog : log (z * exp (θ * I)) = log z + θ * I := by
    have : z * exp (θ * I) = exp (log z + θ * I) := by rw [exp_add, exp_log hz]
    rw [this, log_exp] <;> simp [log_im] <;> linarith
  rw [← log_im, hlog]; simp [log_im]

/-- `1 - εi = √2 e^{-iεπ/4}` for `ε = ±1`. -/
lemma one_sub_mul_I_eq {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    (1 - ε * I : ℂ) = ((Real.sqrt 2 : ℝ) : ℂ) * exp (((-ε * π / 4 : ℝ) : ℂ) * I) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  apply Complex.ext
  · rw [re_ofReal_mul, exp_ofReal_mul_I_re]
    rcases hε with rfl | rfl
    · simp only [sub_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, Real.cos_neg, Real.cos_pi_div_four]
      nlinarith
    · simp only [sub_re, one_re, mul_re, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, Real.cos_pi_div_four]
      nlinarith
  · rw [im_ofReal_mul, exp_ofReal_mul_I_im]
    rcases hε with rfl | rfl
    · simp only [sub_im, one_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, Real.sin_neg, Real.sin_pi_div_four]
      nlinarith
    · simp only [sub_im, one_im, mul_im, ofReal_re, I_re, ofReal_im, I_im]
      rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, Real.sin_pi_div_four]
      nlinarith

/-- `ζ_ε(z) = (√π/2)(1 - εi) z` maps the sector `|arg z| ≤ π/2 - δ` into `|arg ζ| ≤ 3π/4 - δ`,
uniformly towards infinity. -/
lemma tendsto_fresnelZetaComplex_sector {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < π/2) :
    Tendsto (fresnelZetaComplex ε) (sector (π/2-δ)) (sector (3*π/4-δ)) := by
  set ρ : ℝ := Real.sqrt π / 2 * Real.sqrt 2 with hρ
  have hρ0 : 0 < ρ := by positivity
  set θ : ℝ := -ε * π / 4 with hθ
  have hζ : ∀ z, fresnelZetaComplex ε z = (ρ : ℂ) * (z * exp (θ * I)) := by
    intro z
    rw [fresnelZetaComplex, one_sub_mul_I_eq hε, hρ, hθ]; push_cast; ring
  have hθa : |θ| = π / 4 := by
    rw [hθ]; rcases hε with rfl | rfl
    · rw [show -(1:ℝ) * π / 4 = -(π / 4) by ring, abs_neg, abs_of_pos (by positivity)]
    · rw [show -(-1:ℝ) * π / 4 = π / 4 by ring, abs_of_pos (by positivity)]
  unfold sector
  refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr ?_⟩
  · have hn : (norm ∘ fresnelZetaComplex ε) = fun z => ρ * ‖z‖ := by
      funext z
      simp only [Function.comp, hζ, norm_mul, Complex.norm_real, Real.norm_of_nonneg hρ0.le,
        norm_exp_ofReal_mul_I, mul_one]
    rw [hn]
    exact (tendsto_comap.mono_left inf_le_left).const_mul_atTop hρ0
  · filter_upwards [mem_inf_of_right (mem_principal_self _)] with z hz
    obtain ⟨hz0, hza⟩ := hz
    have hza' := abs_le.mp hza
    have hθ' := abs_eq_abs.mp (hθa.trans (abs_of_pos (by positivity : (0:ℝ) < π / 4)).symm)
    have hb : |arg z + θ| ≤ 3 * π / 4 - δ := by
      rw [abs_le]; rcases hθ' with h | h <;> rw [h] <;> constructor <;> linarith
    have hb' := abs_le.mp hb
    refine ⟨?_, ?_⟩
    · rw [hζ]
      exact mul_ne_zero (ofReal_ne_zero.mpr hρ0.ne') (mul_ne_zero hz0 (exp_ne_zero _))
    · rw [hζ, arg_real_mul _ hρ0, arg_mul_exp_ofReal_mul_I hz0 (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])]
      exact hb

/-- Coefficient algebra for the Fresnel expansions: with `w² = -1` and `c = (√π/2)(1-w)`,
`(1+w)/2 · c^{-2m-1} · (-1)^m (1/2)_m/√π = (-1)^m (1/2)_m w^{m+1} (2/π)^m/π`. -/
lemma fresnel_coeff_algebra {w : ℂ} (hw : w ^ 2 = -1) (p : ℂ) (m : ℕ) :
    (1 + w) / 2 * ((((Real.sqrt π : ℂ) / 2 * (1 - w)) ^ (2 * m + 1))⁻¹ *
      ((-1 : ℂ) ^ m * p / Real.sqrt π)) =
      (-1 : ℂ) ^ m * p * w ^ (m + 1) * (2 / π) ^ m / π := by
  set c : ℂ := (Real.sqrt π : ℂ) / 2 * (1 - w) with hc
  have hsq : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hs0 : ((Real.sqrt π : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw1 : 1 - w ≠ 0 := fun h => by
    have : w = 1 := by linear_combination -h
    rw [this] at hw; norm_num at hw
  have hc0 : c ≠ 0 := mul_ne_zero (div_ne_zero hs0 two_ne_zero) hw1
  have hc2 : c ^ 2 = -(π * w / 2) := by
    rw [hc, mul_pow, div_pow, hsq]; linear_combination (π / 4 : ℂ) * hw
  have hinv : (c ^ 2)⁻¹ = 2 * w / π := by
    rw [hc2]
    refine (eq_inv_of_mul_eq_one_left ?_).symm
    calc (2 * w / π) * (-(π * w / 2)) = -(w ^ 2) * (π * (π : ℂ)⁻¹) := by ring
      _ = 1 := by rw [mul_inv_cancel₀ hπ, hw]; ring
  have hA : (1 + w) / 2 / (Real.sqrt π * c) = w / π := by
    rw [hc]
    field_simp
    rw [hsq]
    linear_combination (π : ℂ) * hw
  rw [pow_succ', pow_mul, mul_inv, ← inv_pow, hinv]
  calc (1 + w) / 2 * (c⁻¹ * (2 * w / π) ^ m * ((-1 : ℂ) ^ m * p / Real.sqrt π))
      = (1 + w) / 2 / (Real.sqrt π * c) * ((-1 : ℂ) ^ m * p * (2 * w / π) ^ m) := by
        field_simp
    _ = _ := by rw [hA, show 2 * w / (π : ℂ) = w * (2 / π) by ring, mul_pow, pow_succ]; ring

/-- Signed combination `g(z) + εi f(z)` in the sector `|arg z| ≤ π/2 - δ`. -/
lemma fresnelAux_signed_sector_asymptotic {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ)
    (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(2*(n : ℂ)+1)))
      (fun n => (-1 : ℂ)^n * poch (1/2) n * (ε*I)^(n+1) * (2/π)^n / π)
      (fun z => fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z) := by
  have h1 := (exp_sq_mul_erfc_sector_asymptotic (δ := δ) hδ (by linarith)).comp_tendsto
    (tendsto_fresnelZetaComplex_sector hε hδ hδ1)
  have h2 := h1.smul_scale (ψ := fun (n : ℕ) (z : ℂ) => z^(-(2*(n : ℂ)+1)))
    (κ := fun n => (((Real.sqrt π : ℂ) / 2 * (1 - ε * I)) ^ (2 * n + 1))⁻¹)
    (fun n => Eventually.of_forall fun z => by
      simp only [fresnelZetaComplex]
      rw [show -(2*(n : ℂ)+1) = -(((2*n+1 : ℕ) : ℂ)) by push_cast; ring, cpow_neg, cpow_neg,
        cpow_natCast, cpow_natCast, mul_pow, mul_inv])
  have h3 := h2.const_smul ((1 + (ε : ℂ) * I) / 2)
  have hw : (ε * I : ℂ) ^ 2 = -1 := by
    rcases hε with rfl | rfl <;> simp
  have hcoef : (((1 + (ε : ℂ) * I) / 2) • fun n => (((Real.sqrt π : ℂ) / 2 * (1 - ε * I)) ^ (2 * n + 1))⁻¹ •
      ((-1 : ℂ)^n*poch (1/2) n/Real.sqrt π)) =
      fun n => (-1 : ℂ)^n * poch (1/2) n * (ε*I)^(n+1) * (2/π)^n / π := by
    funext n
    simp only [Pi.smul_apply, smul_eq_mul]
    exact fresnel_coeff_algebra hw _ n
  have hfun : (((1 + (ε : ℂ) * I) / 2) • ((fun z => exp (z^2) * erfc z) ∘ fresnelZetaComplex ε)) =
      fun z => fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Function.comp]
    rw [fresnelAux_signed_erfc z hε]; ring
  rw [hcoef, hfun] at h3
  exact h3

/-- fresnelAuxFComplex sector asymptotic. -/
@[dlmf 7.12.E2]
theorem fresnelAuxFComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+0)*(2/π)^(2*n+0)/π) fresnelAuxFComplex := by
  have hp := fresnelAux_signed_sector_asymptotic (Or.inl rfl) hδ hδ1
  have hm := fresnelAux_signed_sector_asymptotic (Or.inr rfl) hδ hδ1
  have h := (hp.sub hm).const_smul (1 / (2 * I))
  have hf : ((1 / (2 * I)) • ((fun z => fresnelAuxGComplex z + ((1:ℝ):ℂ)*I*fresnelAuxFComplex z) -
      (fun z => fresnelAuxGComplex z + ((-1:ℝ):ℂ)*I*fresnelAuxFComplex z))) = fresnelAuxFComplex := by
    funext z
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    field_simp
    ring
  rw [hf] at h
  have he := h.even (fun n => by
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul, pow_mul, mul_pow, mul_pow]
    simp [I_sq])
  refine (he.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, add_zero]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2, pow_mul (-1:ℂ) 2 n]
    field_simp
    ring

/-- In the open sector `|arg z| < π/4`, `|im z| < re z`. -/
lemma abs_im_lt_re_of_abs_arg_lt {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) :
    |z.im| < z.re := by
  have hu := abs_lt.mp hz
  have h0 : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  rw [← norm_mul_exp_arg_mul_I z, re_ofReal_mul, im_ofReal_mul, exp_ofReal_mul_I_re,
    exp_ofReal_mul_I_im, abs_mul, abs_of_pos h0]
  refine mul_lt_mul_of_pos_left ?_ h0
  rcases le_total 0 (arg z) with h | h
  · rw [abs_of_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h (by linarith)),
      ← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two h (by linarith) (by linarith)
  · rw [abs_of_nonpos (Real.sin_nonpos_of_nonpos_of_neg_pi_le h (by linarith)),
      ← Real.sin_neg, ← Real.cos_neg (arg z), ← Real.cos_pi_div_two_sub]
    exact Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (by linarith) (by linarith) (by linarith)

/-- `exp(ε π i/2) = ε i` for `ε = ±1`. -/
lemma exp_sign_mul_pi_div_two_mul_I' {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    exp (((ε * π / 2 : ℝ) : ℂ) * I) = ε * I := by
  rcases hε with rfl | rfl
  · push_cast; rw [show (1:ℂ) * π / 2 * I = π / 2 * I by ring, exp_pi_div_two_mul_I]; ring
  · push_cast; rw [show (-1:ℂ) * π / 2 * I = -π / 2 * I by ring, exp_neg_pi_div_two_mul_I]; ring

/-- **Laplace forms of `g ± i f`** (from DLMF 7.7.2 rotated by `±π/2`): for `z ≠ 0` with
`|arg z| < π/4` and `ε = ±1`,
`g(z) + εi f(z) = εi √2/(2π) ∫₀^∞ e^{-πz²r/2} r^{-1/2}/(1 + εir) dr`. -/
theorem fresnelAux_signed_laplace {ε : ℝ} (hε : ε = 1 ∨ ε = -1) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |arg z| < π/4) :
    fresnelAuxGComplex z + ε*I*fresnelAuxFComplex z = ε*I*(Real.sqrt 2/(2*π)) *
      ∫ r in Ioi (0:ℝ), cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹) := by
  have hε2 : (ε : ℂ)^2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  set θ : ℝ := ε * π / 2 with hθ
  have hθa : |θ| < π := by
    rw [hθ]; rcases hε with rfl | rfl
    · rw [abs_of_pos (by positivity)]; linarith [Real.pi_pos]
    · rw [show -(1:ℝ) * π / 2 = -(π / 2) by ring, abs_neg, abs_of_pos (by positivity)]
      linarith [Real.pi_pos]
  have he : exp (θ * I) = ε * I := exp_sign_mul_pi_div_two_mul_I' hε
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have h20 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hω : exp (((θ / 2 : ℝ) : ℂ) * I) = (1 + ε * I) / Real.sqrt 2 := by
    have h := one_sub_mul_I_eq (ε := -ε) (by rcases hε with rfl | rfl <;> norm_num)
    rw [eq_div_iff h20]
    push_cast at h ⊢
    rw [show (1:ℂ) - -(ε:ℂ) * I = 1 + ε * I by ring] at h
    rw [h, hθ]; push_cast; ring_nf
  set ζ := fresnelZetaComplex ε z with hζ
  have hζω : ζ * exp (((θ / 2 : ℝ) : ℂ) * I) = ((Real.sqrt π / Real.sqrt 2 : ℝ) : ℂ) * z := by
    have hprod : (1 - (ε:ℂ) * I) * (1 + ε * I) = 2 := by
      linear_combination (-(ε:ℂ)^2) * I_sq + hε2
    rw [hω, hζ, fresnelZetaComplex]
    push_cast
    calc (Real.sqrt π : ℂ) / 2 * (1 - ε * I) * z * ((1 + ε * I) / Real.sqrt 2)
        = (Real.sqrt π : ℂ) / 2 * z / Real.sqrt 2 * ((1 - ε * I) * (1 + ε * I)) := by ring
      _ = _ := by rw [hprod]; field_simp
  have hpos : 0 < Real.sqrt π / Real.sqrt 2 := by positivity
  have hcond : |(ζ * exp (((θ / 2 : ℝ) : ℂ) * I)).im| < (ζ * exp (((θ / 2 : ℝ) : ℂ) * I)).re := by
    rw [hζω, im_ofReal_mul, re_ofReal_mul, abs_mul, abs_of_pos hpos]
    exact mul_lt_mul_of_pos_left (abs_im_lt_re_of_abs_arg_lt hz0 hz) hpos
  have hrep := erfc_eq_integral_rotate_laplace hθa hcond
  have hs : ((Real.sqrt π : ℝ) : ℂ) ^ 2 = π := by
    rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hζ2 : ζ ^ 2 * exp (θ * I) = π * z ^ 2 / 2 := by
    rw [he, hζ, fresnelZetaComplex, mul_pow, mul_pow, div_pow, hs]
    have hq : (1 - (ε:ℂ) * I) ^ 2 * (ε * I) = 2 := by
      linear_combination ((-2)*((ε:ℂ)^2-1) - 2 + ε*I*((ε:ℂ)^2-1) + ε*I) * I_sq +
        (2 - (ε:ℂ)*I) * hε2
    linear_combination (π * z ^ 2 / 4 : ℂ) * hq
  have hθ1 : -π < θ := by linarith [(abs_lt.mp hθa).1]
  have hθ2 : θ ≤ π := (abs_lt.mp hθa).2.le
  have hpt : ∀ r ∈ Ioi (0:ℝ), cexp (-(ζ ^ 2 * exp (θ * I) * r)) *
      (((r : ℂ) * exp (θ * I)) ^ (-1/2 : ℂ) * (1 + (r : ℂ) * exp (θ * I))⁻¹) =
      exp (θ * I * (-1/2 : ℂ)) * (cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹)) := by
    intro r hr
    rw [hζ2, ofReal_mul_exp_cpow hr hθ1 hθ2, he]
    ring_nf
  have hsum := fresnelAux_signed_erfc z hε
  rw [← hζ] at hsum
  rw [hsum, hrep, setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
  have hex : exp (θ * I) * exp (θ * I * (-1/2 : ℂ)) = (1 + ε * I) / Real.sqrt 2 := by
    rw [← Complex.exp_add, ← hω]; congr 1; push_cast; ring
  have hsq : (1 + (ε:ℂ) * I) ^ 2 = 2 * (ε * I) := by
    linear_combination (ε:ℂ)^2 * I_sq - hε2
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  set J := ∫ r in Ioi (0:ℝ), cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ε*I*r)⁻¹)
  calc (1 + (ε:ℂ) * I) / 2 * exp (ζ ^ 2) * (exp (-ζ ^ 2) / π *
        (exp (θ * I) * (exp (θ * I * (-1/2 : ℂ)) * J)))
      = (1 + (ε:ℂ) * I) / 2 * (exp (ζ ^ 2) * exp (-ζ ^ 2)) / π *
        (exp (θ * I) * exp (θ * I * (-1/2 : ℂ))) * J := by ring
    _ = (1 + (ε:ℂ) * I) ^ 2 / (2 * π * Real.sqrt 2) * J := by
        rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, hex]; field_simp
    _ = _ := by
        rw [hsq]; field_simp; linear_combination (-(ε:ℂ) * J) * h2

/-- Laplace moments `∫₀^∞ e^{-πz²t/2} t^{M-1/2} dt`, integrability, for `|arg z| < π/4`. -/
lemma fresnel_moment_integrable {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2)) (Ioi 0) := by
  have hre : 0 < (π*z^2/2 : ℂ).re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : (π*z^2/2 : ℂ).re = π/2 * (z.re^2 - z.im^2) := by
      simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hs : 0 < ((M:ℂ) + 1/2).re := by simp; positivity
  have h := kummerU_laplace_integrable (b := (M:ℂ) + 1/2 + 1) hs hre
  refine h.congr_fun (fun t ht => ?_) measurableSet_Ioi
  beta_reduce
  rw [show (M:ℂ) + 1/2 + 1 - ((M:ℂ) + 1/2) - 1 = 0 by ring, cpow_zero, mul_one,
    show (M:ℂ) + 1/2 - 1 = (M:ℂ) - 1/2 by ring]
  congr 1; congr 1; ring

/-- Laplace moments for the Fresnel auxiliary functions:
`1/(π√2) ∫₀^∞ e^{-πz²t/2} t^{M-1/2} dt = (1/2)_M/(π z (πz²/2)^M)` for `|arg z| < π/4`. -/
lemma fresnel_moment {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    1/(π*Real.sqrt 2) * ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) =
      poch (1/2) M / (π*z*(π*z^2/2)^M) := by
  have hre : 0 < (π*z^2/2 : ℂ).re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : (π*z^2/2 : ℂ).re = π/2 * (z.re^2 - z.im^2) := by
      simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hs : 0 < ((M:ℂ) + 1/2).re := by simp; positivity
  have h := kummerU_laplace_shift_one hs hre
  rw [kummerU_shift_one _ (Or.inl hre)] at h
  have hI : ∫ t : ℝ in Ioi 0, exp (-(π*z^2/2) * t) * (t:ℂ)^((M:ℂ) + 1/2 - 1) *
      (1 + (t:ℂ))^(((M:ℂ) + 1/2 + 1) - ((M:ℂ) + 1/2) - 1) =
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [show ((M:ℂ) + 1/2 + 1) - ((M:ℂ) + 1/2) - 1 = 0 by ring, cpow_zero, mul_one,
      show (M:ℂ) + 1/2 - 1 = (M:ℂ) - 1/2 by ring]
    congr 2; ring
  rw [hI] at h
  -- `(πz²/2)^{-(M+1/2)} = y^{-(2M+1)}` with `y = √(π/2) z`
  set y : ℂ := (Real.sqrt (π/2) : ℂ) * z with hy
  have hpos : 0 < Real.sqrt (π/2) := Real.sqrt_pos.mpr (by positivity)
  have hy0 : y ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hpos.ne') hz0
  have hyarg : arg y = arg z := by rw [hy, arg_real_mul _ hpos]
  have hysq : y ^ 2 = π*z^2/2 := by
    rw [hy, mul_pow, ← ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
  have hcp : (π*z^2/2 : ℂ) ^ (-((M:ℂ) + 1/2)) = (y ^ (2*M+1))⁻¹ := by
    rw [← hysq, ← cpow_ofNat, ← cpow_mul]
    · rw [show (2:ℂ) * -((M:ℂ) + 1/2) = -(((2*M+1 : ℕ) : ℂ)) by push_cast; ring,
        cpow_neg, cpow_natCast]
    · have him : (log y * 2).im = 2 * arg z := by
        rw [← hyarg]; norm_num [mul_im, log_im]; try ring
      rw [him]; have := abs_lt.mp hz; nlinarith [Real.pi_pos]
    · have him : (log y * 2).im = 2 * arg z := by
        rw [← hyarg]; norm_num [mul_im, log_im]; try ring
      rw [him]; have := abs_lt.mp hz; nlinarith [Real.pi_pos]
  rw [hcp] at h
  have hG : Gamma ((M:ℂ) + 1/2) = Real.sqrt π * poch (1/2) M := by
    rw [poch_half_eq_Gamma, show ((M:ℂ) + 1/2) = (((M:ℝ) + 1/2 : ℝ) : ℂ) by push_cast; ring,
      Complex.Gamma_ofReal]
    have : (Real.sqrt π) ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    push_cast; field_simp
  have hGne : Gamma ((M:ℂ) + 1/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hs
  have hint : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) =
      Gamma ((M:ℂ) + 1/2) * (y ^ (2*M+1))⁻¹ := by
    rw [h, ← mul_assoc, mul_one_div_cancel hGne, one_mul]
  rw [hint, hG]
  have hpow : y ^ (2*M+1) = (Real.sqrt (π/2) : ℂ) * z * (π*z^2/2)^M := by
    rw [pow_succ', pow_mul, hysq, hy]
  rw [hpow]
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt (π/2) = Real.sqrt π := by
    rw [← ofReal_mul, ← Real.sqrt_mul (by norm_num)]; congr 2; ring
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have hsp : (Real.sqrt (π/2) : ℂ) ≠ 0 := ofReal_ne_zero.mpr hpos.ne'
  have hsπ : (Real.sqrt π : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hzp : (π*z^2/2 : ℂ)^M ≠ 0 := pow_ne_zero _ (by rw [← hysq]; exact pow_ne_zero _ hy0)
  rw [← h2]
  field_simp

/-- `1 + s i r ≠ 0` for real `s, r`, with `‖(1 + s i r)⁻¹‖ ≤ 1`. -/
lemma norm_one_add_sign_I_mul_inv_le (s r : ℝ) :
    1 + (s:ℂ)*I*r ≠ 0 ∧ ‖(1 + (s:ℂ)*I*r)⁻¹‖ ≤ 1 := by
  have hre : (1 + (s:ℂ)*I*r).re = 1 := by simp
  have h1 : 1 ≤ ‖1 + (s:ℂ)*I*r‖ := hre ▸ re_le_norm _
  have hne : 1 + (s:ℂ)*I*r ≠ 0 := fun h => by rw [h, norm_zero] at h1; linarith
  exact ⟨hne, by rw [norm_inv]; exact inv_le_one_of_one_le₀ h1⟩

/-- Partial fractions: `(1+ir)⁻¹ ± (1-ir)⁻¹`. -/
lemma one_add_I_mul_inv_add_sub (r : ℝ) :
    (1 + I*r)⁻¹ + (1 - I*r)⁻¹ = 2/((r:ℂ)^2+1) ∧
      (1 + I*r)⁻¹ - (1 - I*r)⁻¹ = -2*I*r/((r:ℂ)^2+1) := by
  have hu : (1 + I*r) ≠ 0 := by
    simpa using (norm_one_add_sign_I_mul_inv_le 1 r).1
  have hv : (1 - I*r) ≠ 0 := by
    have := (norm_one_add_sign_I_mul_inv_le (-1) r).1
    push_cast at this; rwa [show (1:ℂ) + -1*I*r = 1 - I*r by ring] at this
  have hw : (r:ℂ)^2 + 1 ≠ 0 := by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by positivity)
  constructor
  · rw [inv_add_inv hu hv, div_eq_div_iff (mul_ne_zero hu hv) hw]
    linear_combination (2*(r:ℂ)^2) * I_sq
  · rw [inv_sub_inv hu hv, div_eq_div_iff (mul_ne_zero hu hv) hw]
    linear_combination (-2*I*(r:ℂ)^3) * I_sq

/-- Integrability of the signed Fresnel Laplace integrands. -/
lemma integrableOn_fresnel_signed (s : ℝ) {z : ℂ} (hz0 : z ≠ 0)
    (hz : |arg z| < π/4) :
    IntegrableOn (fun r : ℝ => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + s*I*r)⁻¹))
      (Ioi 0) := by
  have h0 := fresnel_moment_integrable hz0 hz 0
  refine h0.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun r hr => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun r hr => ?_) measurableSet_Ioi
    have hr : (0:ℝ) < r := hr
    refine ContinuousAt.continuousWithinAt ?_
    have hm : (r:ℂ) ∈ slitPlane := by simp [mem_slitPlane_iff, hr]
    refine ContinuousAt.mul (by fun_prop) (ContinuousAt.mul ?_ ?_)
    · exact (continuousAt_ofReal_cpow_const _ _ (Or.inr hr.ne'))
    · exact ContinuousAt.inv₀ (by fun_prop) (norm_one_add_sign_I_mul_inv_le s r).1
  · rw [norm_mul, norm_mul, norm_mul]
    have := (norm_one_add_sign_I_mul_inv_le s r).2
    rw [show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring, show ((0:ℕ):ℂ) - 1/2 = -1/2 by push_cast; ring]
    calc ‖cexp (-π*z^2*r/2)‖ * (‖(r:ℂ)^(-1/2:ℂ)‖ * ‖(1 + (s:ℂ)*I*r)⁻¹‖)
        ≤ ‖cexp (-π*z^2*r/2)‖ * (‖(r:ℂ)^(-1/2:ℂ)‖ * 1) := by gcongr
      _ = _ := by rw [mul_one]

/-- **Laplace forms of `f` and `g`** (DLMF 7.7.10–7.7.11, on the open sector `|arg z| < π/4`):
`f(z), g(z) = 1/(π√2) ∫₀^∞ e^{-πz²t/2} t^{∓1/2}/(t²+1) dt`. -/
theorem fresnelAux_laplace_open (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) :
    (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z) = 1/(π*Real.sqrt 2) *
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^(((if aux then 1 else 0 : ℕ) : ℂ) - 1/2) /
        ((t:ℂ)^2+1) := by
  have hp := fresnelAux_signed_laplace (ε := 1) (Or.inl rfl) hz0 hz
  have hm := fresnelAux_signed_laplace (ε := -1) (Or.inr rfl) hz0 hz
  have ip := integrableOn_fresnel_signed 1 hz0 hz
  have im := integrableOn_fresnel_signed (-1) hz0 hz
  set fp : ℝ → ℂ := fun r => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ((1:ℝ):ℂ)*I*r)⁻¹)
  set fm : ℝ → ℂ := fun r => cexp (-(π*z^2/2*r)) * ((r:ℂ)^(-1/2:ℂ) * (1 + ((-1:ℝ):ℂ)*I*r)⁻¹)
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  have h2 : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have hc : (Real.sqrt 2 : ℂ) / (2 * π) = 1 / (π * Real.sqrt 2) := by
    rw [div_eq_div_iff (mul_ne_zero two_ne_zero hπ) (mul_ne_zero hπ hs2)]
    linear_combination (π : ℂ) * h2
  have hden : ∀ r : ℝ, (1 + ((1:ℝ):ℂ)*I*r) ≠ 0 ∧ (1 + ((-1:ℝ):ℂ)*I*r) ≠ 0 ∧
      ((r:ℂ)^2 + 1) ≠ 0 := by
    intro r
    refine ⟨(norm_one_add_sign_I_mul_inv_le 1 r).1,
      (norm_one_add_sign_I_mul_inv_le (-1) r).1, ?_⟩
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]
    exact ofReal_ne_zero.mpr (by positivity)
  cases aux
  · simp only [Bool.false_eq_true, ite_false, Nat.cast_zero, zero_sub]
    have hF : fresnelAuxFComplex z = (Real.sqrt 2 / (2*π)) / 2 *
        ((∫ r in Ioi (0:ℝ), fp r) + ∫ r in Ioi (0:ℝ), fm r) := by
      push_cast at hp hm ⊢
      apply mul_left_cancel₀ (show (2:ℂ) * I ≠ 0 by simp)
      linear_combination hp - hm
    rw [hF, ← integral_add ip im, hc, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    obtain ⟨d1, d2, d3⟩ := hden r
    rw [← mul_add, show (1:ℂ) + ((1:ℝ):ℂ)*I*r = 1 + I*r by push_cast; ring,
      show (1:ℂ) + ((-1:ℝ):ℂ)*I*r = 1 - I*r by push_cast; ring, ← mul_add,
      (one_add_I_mul_inv_add_sub r).1, show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring,
      show (-1/2:ℂ) = -(1/2) by ring]
    field_simp
  · simp only [ite_true, Nat.cast_one]
    have hG : fresnelAuxGComplex z = I * (Real.sqrt 2 / (2*π)) / 2 *
        ((∫ r in Ioi (0:ℝ), fp r) - ∫ r in Ioi (0:ℝ), fm r) := by
      push_cast at hp hm ⊢
      linear_combination (hp + hm) / 2
    rw [hG, ← integral_sub ip im, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    have hr : (0:ℝ) < r := hr
    obtain ⟨d1, d2, d3⟩ := hden r
    have hr0 : (r:ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
    have hcp : (r:ℂ)^((1:ℂ) - 1/2) = (r:ℂ)^(-1/2:ℂ) * r := by
      rw [show (1:ℂ) - 1/2 = -1/2 + 1 by ring, cpow_add _ _ hr0, cpow_one]
    rw [← mul_sub, show (1:ℂ) + ((1:ℝ):ℂ)*I*r = 1 + I*r by push_cast; ring,
      show (1:ℂ) + ((-1:ℝ):ℂ)*I*r = 1 - I*r by push_cast; ring, ← mul_sub,
      (one_add_I_mul_inv_add_sub r).2, show -(π*z^2/2*(r:ℂ)) = -π*z^2*r/2 by ring, hcp, ← hc,
      show (-1/2:ℂ) = -(1/2) by ring]
    field_simp
    ring_nf
    rw [I_sq]; ring

/-- Integrability of the Fresnel remainder integrands `e^{-πz²t/2} t^{M-1/2}/(t²+1)`. -/
lemma fresnel_kernel_integrable {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (M : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1))
      (Ioi 0) := by
  have h0 := fresnel_moment_integrable hz0 hz M
  have hw : ∀ t : ℝ, 1 ≤ ‖(t:ℂ)^2+1‖ := fun t => by
    rw [← ofReal_pow, ← ofReal_one, ← ofReal_add, Complex.norm_real, Real.norm_of_nonneg
      (by positivity)]
    nlinarith [sq_nonneg t]
  refine h0.norm.mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
    (Eventually.of_forall fun t ht => ?_))
  · refine ContinuousOn.aestronglyMeasurable (fun t ht => ?_) measurableSet_Ioi
    have ht : (0:ℝ) < t := ht
    refine ContinuousAt.continuousWithinAt ?_
    have hne : (t:ℂ)^2+1 ≠ 0 := fun h => by have := hw t; rw [h, norm_zero] at this; linarith
    exact ((by fun_prop : Continuous fun t : ℝ => exp (-π*z^2*t/2)).continuousAt.mul
      (continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne'))).div (by fun_prop) hne
  · rw [norm_div]
    exact div_le_self (norm_nonneg _) (hw t)

/-- **Remainder integrals for the Fresnel auxiliary expansions**, with
`M = 2N + (0 or 1)`: `R_N(z) = (-1)^N/(π√2) ∫₀^∞ e^{-πz²t/2} t^{M-1/2}/(t²+1) dt`. -/
lemma fresnel_remainder_eq (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder aux N z = (-1 : ℂ)^N/(π*Real.sqrt 2) *
      ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) *
        (t:ℂ)^(((2*N + if aux then 1 else 0 : ℕ) : ℂ) - 1/2) / ((t:ℂ)^2+1) := by
  induction N with
  | zero =>
    rw [fresnelAsymptoticRemainder, Finset.range_zero, Finset.sum_empty, sub_zero,
      fresnelAux_laplace_open aux hz0 hz]
    simp
  | succ N ih =>
    set M : ℕ := 2*N + if aux then 1 else 0 with hM
    have hM2 : (2*(N+1) + if aux then 1 else 0 : ℕ) = M + 2 := by rw [hM]; ring
    rw [fresnelAsymptoticRemainder, Finset.sum_range_succ, ← sub_sub,
      ← fresnelAsymptoticRemainder, ih, hM2]
    have hsplit : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
        (∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2)) -
        ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^(((M+2 : ℕ) : ℂ) - 1/2) / ((t:ℂ)^2+1) := by
      rw [← integral_sub (fresnel_moment_integrable hz0 hz M)
        (fresnel_kernel_integrable hz0 hz (M+2))]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht : (0:ℝ) < t := ht
      have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      have hne : (t:ℂ)^2+1 ≠ 0 := by
        rw [← ofReal_pow, ← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.mpr (by positivity)
      rw [show (((M+2 : ℕ) : ℂ) - 1/2) = ((M:ℂ) - 1/2) + 2 by push_cast; ring,
        cpow_add _ _ ht0, show (2:ℂ) = ((2:ℕ):ℂ) by norm_num, cpow_natCast]
      field_simp
      ring
    have hterm : fresnelAsymptoticTerm aux N z = (-1 : ℂ)^N/(π*Real.sqrt 2) *
        ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) := by
      rw [fresnelAsymptoticTerm, ← hM, mul_div_assoc, ← fresnel_moment hz0 hz M]
      ring
    rw [hsplit, hterm, pow_succ]
    ring

/-- fresnelAuxFComplex remainder integral. -/
@[dlmf 7.12.E6]
theorem fresnelAuxFComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder false N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+0-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  rw [fresnel_remainder_eq false hz0 hz N]
  simp

/-- fresnelAuxGComplex sector asymptotic. -/
@[dlmf 7.12.E3]
theorem fresnelAuxGComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+3))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+1)*(2/π)^(2*n+1)/π) fresnelAuxGComplex := by
  have hp := fresnelAux_signed_sector_asymptotic (Or.inl rfl) hδ hδ1
  have hm := fresnelAux_signed_sector_asymptotic (Or.inr rfl) hδ hδ1
  have h := (hp.add hm).const_smul (1 / 2 : ℂ)
  have hf : ((1 / 2 : ℂ) • ((fun z => fresnelAuxGComplex z + ((1:ℝ):ℂ)*I*fresnelAuxFComplex z) +
      (fun z => fresnelAuxGComplex z + ((-1:ℝ):ℂ)*I*fresnelAuxFComplex z))) = fresnelAuxGComplex := by
    funext z
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    push_cast
    ring
  rw [hf] at h
  have ho := h.odd (fun n => by
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1) = (-1)^n * I := by rw [pow_succ, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1) = -((-1)^n * I) := by rw [pow_succ, pow_mul]; simp
    rw [h1, h2]
    ring)
  refine (ho.congr_scale fun n => Eventually.of_forall fun z => ?_).congr_coeff ?_
  · simp only
    congr 1; push_cast; ring
  · funext n
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h1 : ((((1:ℝ):ℂ) * I))^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    have h2 : ((((-1:ℝ):ℂ) * I))^(2*n+1+1) = (-1)^(n+1) := by
      rw [show 2*n+1+1 = 2*(n+1) by ring, pow_mul]; simp
    rw [h1, h2, pow_succ (-1:ℂ) (2*n), pow_mul (-1:ℂ) 2 n, pow_succ (-1:ℂ) n]
    ring

/-- fresnelAuxGComplex remainder integral. -/
@[dlmf 7.12.E7]
theorem fresnelAuxGComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder true N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+1-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  rw [fresnel_remainder_eq true hz0 hz N]
  simp

/-- Sector-dependent Fresnel next-term bounds. -/
theorem fresnelAux_remainder_bound (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    ‖fresnelAsymptoticRemainder aux N z‖ ≤ (if |arg z| ≤ π/8 then 1 else |1/Real.sin (4*arg z)|)*‖fresnelAsymptoticTerm aux N z‖ := by
  set M : ℕ := 2*N + if aux then 1 else 0 with hM
  set α := arg z with hα
  set θ : ℝ := -2*α with hθ
  have hθa : |θ| < π/2 := by rw [hθ, abs_mul, abs_neg, abs_two]; linarith
  set a : ℂ := π*z^2/2 with ha
  set s : ℝ := ‖z‖ with hs
  have hs0 : 0 < s := by rw [hs]; exact norm_pos_iff.mpr hz0
  set A : ℝ := π/2 * s^2 with hA
  have hA0 : 0 < A := by positivity
  have hae : a * exp (θ * I) = (A : ℂ) := by
    have hzω : z * exp (((-α:ℝ):ℂ) * I) = (s : ℂ) := by
      conv_lhs => rw [← norm_mul_exp_arg_mul_I z]
      rw [mul_assoc, ← Complex.exp_add]
      push_cast
      simp [hs, hα]
    have : exp (θ * I) = (exp (((-α:ℝ):ℂ) * I))^2 := by
      rw [← Complex.exp_nat_mul, hθ]; push_cast; ring_nf
    rw [this, ha, hA]
    calc (π:ℂ) * z^2 / 2 * (exp (((-α:ℝ):ℂ) * I))^2
        = π / 2 * (z * exp (((-α:ℝ):ℂ) * I))^2 := by ring
      _ = _ := by rw [hzω]; push_cast; ring
  have hre : 0 < a.re := by
    have h := abs_im_lt_re_of_abs_arg_lt hz0 hz
    have : a.re = π/2 * (z.re^2 - z.im^2) := by rw [ha]; simp [sq, mul_re]; ring
    rw [this]
    have h' := abs_lt.mp h
    have : 0 < z.re ^ 2 - z.im ^ 2 := by nlinarith [abs_nonneg z.im]
    positivity
  have hreθ : 0 < (a * exp (θ * I)).re := by rw [hae, ofReal_re]; exact hA0
  -- lower bound for the denominator along the rotated rays
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_norm_one_add_ofReal_mul_exp (Φ := 2 * |θ|)
    (by linarith)
  have hden : ∀ r y : ℝ, ((r : ℂ) * exp (y * I)) ^ 2 + 1 =
      1 + ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    intro r y; rw [ofReal_mul_exp_ofReal_mul_I_sq]; ring
  have hdenc : ∀ r : ℝ, ∀ y : ℝ, |y| ≤ |θ| → c ≤ ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖ := by
    intro r y hy
    rw [hden r y]
    exact hc _ (sq_nonneg r) _ (by rw [abs_mul, abs_two]; linarith)
  have hFn : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖((r : ℂ) * exp (y * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤
        ‖((r : ℂ) * exp (y * I)) ^ 2 + 1‖⁻¹ * r ^ ((M:ℝ) - 1/2) := by
    intro r hr y hy
    have hy' : |y| < π := by linarith [Real.pi_pos]
    rw [abs_lt] at hy'
    rw [norm_div, ofReal_mul_exp_cpow hr hy'.1 hy'.2.le, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hr,
      show (y : ℂ) * I * ((M:ℂ) - 1/2) = ((y * ((M:ℝ) - 1/2) : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]
    have : ((M:ℂ) - 1/2).re = (M:ℝ) - 1/2 := by simp
    rw [this, div_eq_inv_mul]
  have hFc : ∀ r : ℝ, 0 < r → ∀ y : ℝ, |y| ≤ |θ| →
      ‖((r : ℂ) * exp (y * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (y * I)) ^ 2 + 1)‖ ≤
        1 / c * r ^ ((M:ℝ) - 1/2) := by
    intro r hr y hy
    refine (hFn r hr y hy).trans ?_
    gcongr
    rw [one_div]; exact inv_anti₀ hc0 (hdenc r y hy)
  have hrot := integral_cexp_neg_mul_mul_eq_rotate
    (F := fun t : ℂ => t ^ ((M:ℂ) - 1/2) / (t ^ 2 + 1)) (θ := θ) (σ := (M:ℝ) + 1/2)
    (C := 1 / c) (k := (M:ℝ) - 1/2) (z := a) (by positivity)
    (fun r hr y hy => by
      have hy1 := abs_le_abs_of_mem_uIcc_zero hy
      have hm := ofReal_mul_exp_mem_slitPlane hr (by linarith [Real.pi_pos] : |y| < π)
      have hne : ((r : ℂ) * exp (y * I)) ^ 2 + 1 ≠ 0 := fun h0 => by
        have := hdenc r y hy1; rw [h0, norm_zero] at this; linarith
      exact (differentiableAt_id.cpow (differentiableAt_const _) hm).div
        ((differentiableAt_pow 2).add_const 1) hne)
    (fun r hr _ y hy => by
      rw [show (M:ℝ) + 1/2 - 1 = (M:ℝ) - 1/2 by ring]
      exact hFc r hr y (abs_le_abs_of_mem_uIcc_zero hy))
    (fun r hr y hy => hFc r (by linarith) y (abs_le_abs_of_mem_uIcc_zero hy))
    (fun y hy => re_mul_exp_pos_of_mem_uIcc hθa hre hreθ hy)
  have hI : ∫ t in Ioi (0:ℝ), exp (-π*z^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
      ∫ t : ℝ in Ioi 0, cexp (-(a * t)) * ((t:ℂ) ^ ((M:ℂ) - 1/2) / ((t:ℂ) ^ 2 + 1)) :=
    setIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [ha]; ring_nf
  -- the sector constant
  set L : ℝ := if |α| ≤ π/8 then 1 else |Real.sin (4*α)| with hL
  have hL0 : 0 < L := by
    rw [hL]; split_ifs with h
    · exact one_pos
    · push Not at h
      refine abs_pos.mpr (fun h0 => ?_)
      have h4 : 0 < |4 * α| ∧ |4 * α| < π := by
        rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 4)]
        constructor <;> nlinarith [Real.pi_pos, abs_nonneg α]
      have : Real.sin |4 * α| = 0 := by
        rcases le_total 0 (4 * α) with hh | hh
        · rw [abs_of_nonneg hh, h0]
        · rw [abs_of_nonpos hh, Real.sin_neg, h0, neg_zero]
      exact (Real.sin_pos_of_pos_of_lt_pi h4.1 h4.2).ne' this
  have hLden : ∀ r : ℝ, L ≤ ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖ := by
    intro r
    rw [hden r θ, hL]; split_ifs with h
    · refine one_le_norm_one_add_ofReal_mul_exp (sq_nonneg r) ?_
      rw [← Real.cos_abs, abs_mul, abs_two, hθ, abs_mul, abs_neg, abs_two]
      exact Real.cos_nonneg_of_mem_Icc ⟨by linarith [abs_nonneg α, Real.pi_pos], by linarith⟩
    · have : |Real.sin (2 * θ)| = |Real.sin (4 * α)| := by
        rw [hθ, show 2 * (-2 * α) = -(4 * α) by ring, Real.sin_neg, abs_neg]
      rw [← this]; exact abs_sin_le_norm_one_add_ofReal_mul_exp _ _
  -- bound the rotated integral
  have hbound : ∀ r ∈ Ioi (0 : ℝ), ‖cexp (-((A:ℂ) * r)) *
      (((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (θ * I)) ^ 2 + 1))‖ ≤
      1 / L * (r ^ ((M:ℝ) + 1/2 - 1) * Real.exp (-(A * r))) := by
    intro r hr
    have hr : (0:ℝ) < r := hr
    rw [norm_mul, show -((A:ℂ) * r) = ((-(A * r) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_exp_ofReal]
    have h1 := hFn r hr θ le_rfl
    have h2 : ‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖⁻¹ ≤ 1 / L := by
      rw [one_div]; exact inv_anti₀ hL0 (hLden r)
    rw [show (M:ℝ) + 1/2 - 1 = (M:ℝ) - 1/2 by ring]
    calc Real.exp (-(A * r)) * ‖((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) /
          (((r : ℂ) * exp (θ * I)) ^ 2 + 1)‖
        ≤ Real.exp (-(A * r)) * (‖((r : ℂ) * exp (θ * I)) ^ 2 + 1‖⁻¹ * r ^ ((M:ℝ) - 1/2)) := by
          gcongr
      _ ≤ Real.exp (-(A * r)) * (1 / L * r ^ ((M:ℝ) - 1/2)) := by gcongr
      _ = _ := by ring
  have hs1 : (0:ℝ) < (M:ℝ) + 1/2 := by positivity
  have hint : IntegrableOn (fun r : ℝ => 1 / L * (r ^ ((M:ℝ) + 1/2 - 1) *
      Real.exp (-A * r ^ (1:ℝ)))) (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (M:ℝ) + 1/2 - 1)
      (b := A) (by linarith) one_pos hA0).const_mul (1 / L)
  have hint' : IntegrableOn (fun r : ℝ => 1 / L * (r ^ ((M:ℝ) + 1/2 - 1) * Real.exp (-(A * r))))
      (Ioi 0) := hint.congr_fun (fun r _ => by simp [Real.rpow_one, neg_mul]) measurableSet_Ioi
  have hnorm := norm_integral_le_of_norm_le hint'
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hbound))
  rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hs1 hA0] at hnorm
  -- assemble
  rw [fresnel_remainder_eq aux hz0 hz N, ← hM, hI, hrot, hae, norm_mul, norm_mul,
    norm_exp_ofReal_mul_I, one_mul]
  have hc1 : ‖(-1 : ℂ)^N/(π*Real.sqrt 2)‖ = 1/(π*Real.sqrt 2) := by
    rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_mul, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [hc1]
  have hterm : ‖fresnelAsymptoticTerm aux N z‖ =
      Real.Gamma ((M:ℝ) + 1/2) / Real.sqrt π / (π * s * A ^ M) := by
    rw [fresnelAsymptoticTerm, ← hM, poch_half_eq_Gamma, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (Real.Gamma_pos_of_pos hs1).le (Real.sqrt_nonneg _)), norm_mul, norm_mul,
      Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le, ← hs, ← ha]
    have hna : ‖a‖ = A := by
      have := congrArg norm hae
      rwa [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
        Real.norm_of_nonneg hA0.le] at this
    rw [norm_pow, hna]
  have hc : (if |α| ≤ π/8 then (1:ℝ) else |1/Real.sin (4*α)|) = 1 / L := by
    rw [hL]; split_ifs <;> simp
  rw [hterm, hc]
  have hAr : A ^ ((M:ℝ) + 1/2) = A ^ M * (Real.sqrt (π/2) * s) := by
    rw [Real.rpow_add hA0, Real.rpow_natCast, ← Real.sqrt_eq_rpow, hA,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hs0.le]
  have hsq : Real.sqrt 2 * Real.sqrt (π/2) = Real.sqrt π := by
    rw [← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hG0 : 0 < Real.Gamma ((M:ℝ) + 1/2) := Real.Gamma_pos_of_pos hs1
  calc 1 / (π * Real.sqrt 2) * ‖∫ r in Ioi (0:ℝ), cexp (-((A:ℂ) * r)) *
        (((r : ℂ) * exp (θ * I)) ^ ((M:ℂ) - 1/2) / (((r : ℂ) * exp (θ * I)) ^ 2 + 1))‖
      ≤ 1 / (π * Real.sqrt 2) * (1 / L * ((1 / A) ^ ((M:ℝ) + 1/2) * Real.Gamma ((M:ℝ) + 1/2))) := by
        gcongr
    _ = _ := by
        rw [Real.div_rpow zero_le_one hA0.le, Real.one_rpow, hAr, ← hsq]
        have : 0 < Real.sqrt (π/2) := Real.sqrt_pos.mpr (by positivity)
        have : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
        field_simp

/-- Signed real Fresnel remainder. -/
theorem fresnelAux_remainder_sign (aux : Bool) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(fresnelAsymptoticRemainder aux N x).re := by
  have hx0 : (x:ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  have harg : |arg (x:ℂ)| < π/4 := by
    rw [arg_ofReal_of_nonneg hx.le, abs_zero]; positivity
  set M : ℕ := 2*N + if aux then 1 else 0
  set g : ℝ → ℝ := fun t => Real.exp (-π*x^2*t/2) * t^((M:ℝ) - 1/2) / (t^2+1) with hg
  have hI : ∫ t in Ioi (0:ℝ), exp (-π*(x:ℂ)^2*t/2) * (t:ℂ)^((M:ℂ) - 1/2) / ((t:ℂ)^2+1) =
      ((∫ t in Ioi (0:ℝ), g t : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    simp only [hg]
    push_cast
    rw [ofReal_cpow ht.le]
    push_cast; ring_nf
  rw [fresnel_remainder_eq aux hx0 harg N, hI]
  have hre : ((-1 : ℂ)^N/(π*Real.sqrt 2) * ((∫ t in Ioi (0:ℝ), g t : ℝ) : ℂ)).re =
      (-1 : ℝ)^N/(π*Real.sqrt 2) * ∫ t in Ioi (0:ℝ), g t := by
    rw [show (-1 : ℂ)^N/(π*Real.sqrt 2) = (((-1 : ℝ)^N/(π*Real.sqrt 2) : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_mul, ofReal_re]
  rw [hre, ← mul_assoc, ← mul_div_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  have ht : (0:ℝ) < t := ht
  simp only [hg]; positivity

end AAR.Confluent
