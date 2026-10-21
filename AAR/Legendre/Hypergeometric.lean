/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated
public import AAR.Legendre.Connections
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Hypergeometric representations and parameter derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Classical Gauss function on its principal cut plane at regular c. This is a
continuation, not the totalized power series outside its convergence disk. -/
@[dlmf 14.3.E3]
def legendreGaussF (a b c z : ℂ) : ℂ :=
  Gamma c*regularizedGaussHG a b c z

/-- DLMF normalization; the unit-disk agreement is already
`AAR.Hypergeometric.ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG`. -/
@[dlmf 14.3.E3]
theorem legendreGaussF_normalization {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -n) :
    regularizedGaussHG a b c z=legendreGaussF a b c z/Gamma c := by
  have hG := Gamma_ne_zero hc
  simp [legendreGaussF, hG]

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E4]
theorem ferrersP_integer_hypergeometric_4 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)/2^m*(1-x^2:ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  unfold ferrersP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination ((-1)^(k+1) * poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-x)/2)) *
    ferrers_gauge_nat (k+1) hx

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E5]
theorem ferrersP_integer_hypergeometric_5 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)*((1-x)/(1+x):ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+1) (-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  have hr : 0 ≤ (1+x)/(1-x) := div_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have e : ((1-x)/(1+x):ℂ) = ((((1+x)/(1-x):ℝ):ℂ))⁻¹ := by push_cast; rw [inv_div]
  unfold ferrersP
  rw [regularizedGaussHG_legendre_neg_nat ν k hw, e, inv_cpow_ofReal_nonneg hr, poch_mul_poch_neg,
    ← cpow_neg, show -(((k+1:ℕ):ℂ)/2) = -((k+1:ℕ):ℂ)/2 by ring, ← ferrers_gauge_neg_nat (k+1) hx]
  ring

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E8]
theorem associatedP_integer_hypergeometric_8 (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν m z=poch (ν-m+1) (2*m)/2^m*legendreBranchPower m z*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-z)/2) := by
  rcases m with _ | k
  · simp [associatedP, legendreBranchPower, poch_zero]
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hg := associated_gauge_nat (k+1) hz
  unfold associatedP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination (poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-z)/2)) * hg

/-- associated hypergeometric 9. -/
@[dlmf 14.3.E9]
theorem associated_hypergeometric_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=exp (μ/2*(log (z-1)-log (z+1)))*regularizedGaussHG (ν+1) (-ν) (μ+1) ((1-z)/2) := by
  unfold associatedP
  rw [show 1-(-μ) = μ+1 by ring,
    show -μ/2*(log (z+1)-log (z-1)) = μ/2*(log (z-1)-log (z+1)) by ring]

/-- associated hypergeometric 15. -/
@[dlmf 14.3.E15]
theorem associated_hypergeometric_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=2^(-μ)*legendreBranchPower μ z*regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have h1 : z+1 ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hl2 : log (2:ℂ) = (Real.log 2:ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hp : (1-(1-z)/2)^μ = exp ((log (z+1) - Real.log 2)*μ) := by
    rw [show 1-(1-z)/2 = (z+1)*((1/2:ℝ):ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (mul_ne_zero h1 (by norm_num)), log_mul_ofReal _ (by norm_num) _ h1,
      one_div, Real.log_inv]
    push_cast; ring_nf
  have h2 : (2:ℂ)^(-μ) = exp (Real.log 2 * (-μ)) := by
    rw [cpow_def_of_ne_zero (by norm_num), hl2]
  unfold associatedP legendreBranchPower
  rw [show 1-(-μ) = μ+1 by ring, regularizedGaussHG_euler _ _ _ hw, show μ+1-(ν+1)-(-ν) = μ by ring,
    show μ+1-(ν+1) = μ-ν by ring, show μ+1-(-ν) = ν+μ+1 by ring, hp, h2]
  have he : exp (-μ/2*(log (z+1)-log (z-1))) * exp ((log (z+1) - Real.log 2)*μ) =
      exp (Real.log 2 * (-μ)) * exp (μ/2*(log (z-1)+log (z+1))) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) * he

/-- associated hypergeometric 16. -/
@[dlmf 14.3.E16]
theorem associated_hypergeometric_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=2^ν*Real.sqrt π*z^(ν-μ)*legendreBranchPower μ z/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/z^2)-Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*Gamma (μ-ν)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2) := by
  set D : Set ℂ := {z : ℂ | z-1 ∈ slitPlane} with hD
  have hDo : IsOpen D := isOpen_slitPlane.preimage (continuous_sub_right 1)
  have hDc : IsPreconnected D := by
    have : D = (fun w => w+1) '' slitPlane := by
      ext w; simp only [hD, mem_image]
      show w - 1 ∈ slitPlane ↔ _
      exact ⟨fun h => ⟨w-1, h, by ring⟩, fun ⟨u, hu, e⟩ => by rw [← e]; simpa using hu⟩
    rw [this]
    exact (StarConvex.isPathConnected starConvex_one_slitPlane (Or.inl (by simp))).isConnected.isPreconnected.image _ (by fun_prop : Continuous fun w : ℂ => w+1).continuousOn
  have hmem : ∀ w ∈ D, w + 1 ∈ slitPlane ∧ w - 1 ∈ slitPlane ∧ w ∈ slitPlane ∧
      (1-w)/2 ∈ cutPlane ∧ 1/w^2 ∈ cutPlane := by
    intro w hw
    have h2 : w - 1 ∈ slitPlane := hw
    have h1 : w + 1 ∈ slitPlane := by
      have := one_add_mem_slitPlane_of_sub_one h2; rwa [add_comm] at this
    have h3 : w ∈ slitPlane := by
      rw [mem_slitPlane_iff] at h2 ⊢
      rcases h2 with h | h
      · left; simp at h; linarith
      · right; simpa using h
    exact ⟨h1, h2, h3, mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one h2),
      one_sub_inv_sq_mem_slitPlane_of_sub_one h2⟩
  have hf : AnalyticOnNhd ℂ (fun z => cos (ν*π)*associatedP ν (-μ) z) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, -, h4, -⟩ := hmem w hw
    unfold associatedP
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := assumption)
  have hg : AnalyticOnNhd ℂ (fun z => 2^ν*Real.sqrt π*z^(ν-μ)*legendreBranchPower μ z/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/z^2)-Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*Gamma (μ-ν)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2)) D := by
    refine DifferentiableOn.analyticOnNhd (fun w hw => ?_) hDo
    obtain ⟨h1, h2, h3, -, h5⟩ := hmem w hw
    have h0 : w ^ 2 ≠ 0 := pow_ne_zero 2 (slitPlane_ne_zero h3)
    have h6 : w ^ (ν+μ+1) ≠ 0 := by rw [cpow_def_of_ne_zero (slitPlane_ne_zero h3)]; exact exp_ne_zero _
    unfold legendreBranchPower
    simp only [div_eq_mul_inv, mul_inv]
    apply DifferentiableAt.differentiableWithinAt
    fun_prop (disch := first | assumption | simpa [div_eq_mul_inv] using h5)
  have hreal : ∀ t : ℝ, t ∈ Ioo (1:ℝ) 2 → cos (ν*π)*associatedP ν (-μ) t = 2^ν*Real.sqrt π*(t:ℂ)^(ν-μ)*legendreBranchPower μ t/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)-Real.sqrt π*legendreBranchPower μ t/(2^(ν+1)*Gamma (μ-ν)*(t:ℂ)^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2) := by
    intro t ht
    have htp : (0:ℝ) < t := by linarith [ht.1]
    have ht0 : (t:ℂ) ≠ 0 := ofReal_ne_zero.mpr htp.ne'
    have hz1 : (t:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith [ht.1])
    rw [associatedP_neg_eq_quadratic ν μ hz1 (by simpa using htp)]
    have hinv : 1/(t:ℂ)^2 = ((1/t^2:ℝ):ℂ) := by push_cast; ring
    have hlt : 1/t^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith [ht.1]
    have hpos : 0 < 1/t^2 := by positivity
    have hw : ‖1-1/(t:ℂ)^2‖ < 1 := by
      rw [hinv, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have h1w : ‖1-(1-1/(t:ℂ)^2)‖ < 1 := by
      rw [sub_sub_cancel, hinv, norm_real, Real.norm_eq_abs, abs_lt]
      constructor <;> linarith
    have hc := regularized_connection_one_sub ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) hw h1w
    rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1w,
      ← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ h1w, sub_sub_cancel,
      show μ+1-(μ-ν)/2-(μ-ν+1)/2 = ν+1/2 by ring, show ν+1/2+1 = ν+3/2 by ring,
      show (μ-ν)/2+(μ-ν+1)/2-(μ+1)+1 = 1/2-ν by ring,
      show μ+1-(μ-ν)/2 = (ν+μ+2)/2 by ring, show μ+1-(μ-ν+1)/2 = (ν+μ+1)/2 by ring,
      show (π:ℂ)*(ν+1/2) = ν*π + π/2 by ring, Complex.sin_add_pi_div_two] at hc
    have hd1 := Complex.Gamma_mul_Gamma_add_half ((ν+μ+1)/2)
    rw [show (ν+μ+1)/2+1/2 = (ν+μ+2)/2 by ring, show 1-2*((ν+μ+1)/2) = -ν-μ by ring,
      show 2*((ν+μ+1)/2) = ν+μ+1 by ring] at hd1
    have hd2 := Complex.Gamma_mul_Gamma_add_half ((μ-ν)/2)
    rw [show (μ-ν)/2+1/2 = (μ-ν+1)/2 by ring, show 1-2*((μ-ν)/2) = 1-μ+ν by ring,
      show 2*((μ-ν)/2) = μ-ν by ring] at hd2
    rw [mul_comm (Gamma ((ν+μ+2)/2)), hd1, hd2] at hc
    have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    set s : ℂ := ((Real.sqrt π:ℝ):ℂ) with hs
    have hs0 : s ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hss : s*s = π := by rw [hs, ← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
    have f2 : (π:ℂ)*s⁻¹ = s := by rw [← hss]; field_simp
    have h2 : (2:ℂ) ≠ 0 := two_ne_zero
    have f1 : (2:ℂ)^(-μ)*((2:ℂ)^(-ν-μ))⁻¹ = 2^ν := by
      rw [← cpow_neg, ← cpow_add _ _ h2]; ring_nf
    have f3 : (2:ℂ)^(-μ)*((2:ℂ)^(1-μ+ν))⁻¹ = ((2:ℂ)^(ν+1))⁻¹ := by
      rw [← cpow_neg, ← cpow_neg, ← cpow_add _ _ h2]; ring_nf
    have f4 : (t:ℂ)^(ν-μ)*(1/(t:ℂ)^2)^(ν+1/2) = ((t:ℂ)^(ν+μ+1))⁻¹ := by
      have hl : log (1/(t:ℂ)^2) = -2*log (t:ℂ) := by
        rw [hinv, ← ofReal_log hpos.le, ← ofReal_log htp.le, Real.log_div one_ne_zero (by positivity),
          Real.log_one, Real.log_pow]; push_cast; ring
      have h10 : 1/(t:ℂ)^2 ≠ 0 := by simp [ht0]
      rw [cpow_def_of_ne_zero ht0, cpow_def_of_ne_zero h10, cpow_def_of_ne_zero ht0, hl, ← exp_add,
        ← exp_neg]
      congr 1; ring
    have hmain : cos (ν*π) * regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/(t:ℂ)^2) =
        π * (regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2) / (Gamma (ν+μ+1)*2^(-ν-μ)*s) -
          (1/(t:ℂ)^2)^(ν+1/2) / (Gamma (μ-ν)*2^(1-μ+ν)*s) *
            regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2)) := by
      rw [← hc]; field_simp
    set T := (t:ℂ)^(ν-μ)
    set Y := (1/(t:ℂ)^2)^(ν+1/2)
    set BP := legendreBranchPower μ t
    set F1 := regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)
    set F2 := regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2)
    set K1 := T*BP*F1*(Gamma (ν+μ+1))⁻¹
    set K2 := BP*F2*(Gamma (μ-ν))⁻¹
    linear_combination ((2:ℂ)^(-μ)*T*BP) * hmain + K1*(π*s⁻¹)*f1 + K1*2^ν*f2
      - K2*(π*s⁻¹)*(T*Y)*f3 - K2*((2:ℂ)^(ν+1))⁻¹*(T*Y)*f2 - K2*((2:ℂ)^(ν+1))⁻¹*s*f4
  have hfreq : ∃ᶠ w in 𝓝[≠] ((3/2:ℝ):ℂ), cos (ν*π)*associatedP ν (-μ) w = 2^ν*Real.sqrt π*w^(ν-μ)*legendreBranchPower μ w/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/w^2)-Real.sqrt π*legendreBranchPower μ w/(2^(ν+1)*Gamma (μ-ν)*w^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/w^2) := by
    have hT : Tendsto (fun t : ℝ => (t:ℂ)) (𝓝[≠] (3/2:ℝ)) (𝓝[≠] ((3/2:ℝ):ℂ)) :=
      (continuous_ofReal.tendsto _).inf (tendsto_principal_principal.mpr fun t ht =>
        fun h => ht (ofReal_injective h))
    apply hT.frequently
    have hev : ∀ᶠ t : ℝ in 𝓝[≠] (3/2:ℝ), cos (ν*π)*associatedP ν (-μ) t = 2^ν*Real.sqrt π*(t:ℂ)^(ν-μ)*legendreBranchPower μ t/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/(t:ℂ)^2)-Real.sqrt π*legendreBranchPower μ t/(2^(ν+1)*Gamma (μ-ν)*(t:ℂ)^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/(t:ℂ)^2) := by
      apply eventually_nhdsWithin_of_eventually_nhds
      filter_upwards [Ioo_mem_nhds (by norm_num : (1:ℝ) < 3/2) (by norm_num : (3/2:ℝ) < 2)]
        with t ht using hreal t ht
    exact hev.frequently
  have h32 : ((3/2:ℝ):ℂ) ∈ D := Or.inl (by simp; norm_num)
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hDc h32 hfreq hz

/-- associated hypergeometric 18. -/
@[dlmf 14.3.E18]
theorem associated_hypergeometric_18 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν (-μ) z=2^(-μ)*z^(ν-μ)*legendreBranchPower μ z*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/z^2) := by
  exact associatedP_neg_eq_quadratic ν μ hz hre

/-- associated hypergeometric 20. -/
@[dlmf 14.3.E20]
theorem associated_hypergeometric_20 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  exact associated_connection_15 ν μ hz

/-- Combined boundary value at the hypergeometric cut; separate totalized values on that cut are not used. -/
@[dlmf 14.3.E17]
theorem associatedP_square_hypergeometric (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => let u : ℂ := x^2+I*ε; π*legendreBranchPower μ x/2^μ*(regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) u/(Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2))-x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) u/(Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2)))) (𝓝[>] 0) (𝓝 (associatedP ν (-μ) x)) := by
  sorry

/-- Parameter limit includes the removable singularities of the gamma-prefactored representation. -/
@[dlmf 14.3.E19]
theorem olverQ_linear_hypergeometric (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => 2^v*Gamma (v+1)*exp (μ/2*log (z+1)-(μ/2+v+1)*log (z-1))*regularizedGaussHG (v+1) (v+μ+1) (2*v+2) (2/(1-z))) (𝓝[≠] ν) (𝓝 (olverQ ν μ z)) := by
  sorry

/-- legendreDegreeA. -/
@[dlmf 14.11.E3]
def legendreDegreeA (ν μ : ℂ) (x : ℝ) : ℂ :=
  sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*∑' k : ℕ, ((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))

/-- legendreDegreeA hasSum. -/
@[dlmf 14.11.E3]
theorem legendreDegreeA_hasSum {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun k : ℕ => sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))) (legendreDegreeA ν μ x) := by
  sorry

/-- ferrersP degree deriv. -/
@[dlmf 14.11.E1]
theorem ferrersP_degree_deriv {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersP ν μ x) (π*cos (ν*π)/sin (ν*π)*ferrersP ν μ x-legendreDegreeA ν μ x/π) ν := by
  sorry

/-- ferrersQ degree deriv. -/
@[dlmf 14.11.E2]
theorem ferrersQ_degree_deriv {ν μ : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (hplus : ∀ n : ℤ, ν+μ ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersQ ν μ x) (-π^2/2*ferrersP ν μ x+π*sin (μ*π)/(sin (ν*π)*sin ((ν+μ)*π))*ferrersQ ν μ x-cos ((ν+μ)*π)/(2*sin ((ν+μ)*π))*legendreDegreeA ν μ x+legendreDegreeA ν μ (-x)/(2*sin ((ν+μ)*π))) ν := by
  sorry

/-- ferrersP order deriv zero. -/
@[dlmf 14.11.E4]
theorem ferrersP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersP ν μ x) (digamma (ν+1)*ferrersP ν 0 x+ferrersQ ν 0 x) 0 := by
  sorry

/-- ferrersQ order deriv zero. -/
@[dlmf 14.11.E5]
theorem ferrersQ_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersQ ν μ x) (-π^2/4*ferrersP ν 0 x+digamma (ν+1)*ferrersQ ν 0 x) 0 := by
  sorry

/-- associatedP order deriv zero. -/
@[dlmf 14.11.E4]
theorem associatedP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (fun μ => associatedP ν μ z) (digamma (ν+1)*associatedP ν 0 z+associatedQ ν 0 z) 0 := by
  sorry

end AAR.Legendre
