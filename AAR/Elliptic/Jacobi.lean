/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Elliptic.Complete

/-!
# Incomplete elliptic integrals and Jacobi's elliptic functions (Temme §§12.2–12.3)

For a real parameter `m < 1` (`m = k²`), Legendre's incomplete integrals
`F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ` and `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ` are odd
and quasi-periodic, `F(φ + π|m) = F(φ|m) + 2K(m)`. Since `∂F/∂φ > 0` and `F(nπ|m) = 2nK(m)`,
`φ ↦ F(φ|m)` is an order isomorphism of `ℝ`; its inverse is Jacobi's amplitude `am(u|m)`
(Temme (12.21)–(12.22)), and `sn = sin ∘ am`, `cn = cos ∘ am`, `dn = (1 - m sn²)^{1/2}`. The
inverse function theorem gives `am' = dn` and the derivatives of DLMF 22.13.1–22.13.3.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace AAR.Elliptic

/-- Legendre's incomplete integral of the first kind `F(φ|m) = ∫₀^φ (1 - m sin²θ)^{-1/2} dθ`
(DLMF 19.2.4, Temme (12.15)). -/
@[dlmf 19.2.E4]
def ellipticF (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- Legendre's incomplete integral of the second kind `E(φ|m) = ∫₀^φ (1 - m sin²θ)^{1/2} dθ`
(DLMF 19.2.5, Temme (12.16)). -/
@[dlmf 19.2.E5]
def ellipticEInc (φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ (1 / 2 : ℝ)

/-- The integrand `(1 - m sin²θ)^p` is `π`-periodic and even, so its integral over a period is
twice the integral over `[0, π/2]`. -/
lemma integral_period {m : ℝ} (hm : m < 1) (p : ℝ) :
    ∫ θ in (0 : ℝ)..π, (1 - m * sin θ ^ 2) ^ p =
      2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
  have h := intervalIntegral.integral_comp_sub_left
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := π / 2) π
  simp only [sin_pi_sub, sub_zero, show π - π / 2 = π / 2 by ring] at h
  rw [← h]; ring

/-- Quasi-periodicity of the incomplete integrals in the amplitude. -/
lemma integral_add_pi {m : ℝ} (hm : m < 1) (p φ : ℝ) :
    ∫ θ in (0 : ℝ)..(φ + π), (1 - m * sin θ ^ 2) ^ p =
      (∫ θ in (0 : ℝ)..φ, (1 - m * sin θ ^ 2) ^ p) +
        2 * ∫ θ in (0 : ℝ)..(π / 2), (1 - m * sin θ ^ 2) ^ p := by
  have hc := continuous_one_sub_mul_sin_sq_rpow hm p
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), integral_period hm]
  have h := intervalIntegral.integral_comp_add_right
    (fun θ => (1 - m * sin θ ^ 2) ^ p) (a := 0) (b := φ) π
  simp only [sin_add_pi, neg_sq, zero_add] at h
  rw [← h, add_comm]

/-- `F(φ + π|m) = F(φ|m) + 2K(m)` (DLMF §19.2(ii)). -/
theorem ellipticF_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    ellipticF (φ + π) m = ellipticF φ m + 2 * ellipticK m := by
  unfold ellipticF ellipticK; exact integral_add_pi hm _ φ

/-- `E(φ + π|m) = E(φ|m) + 2E(m)` (DLMF §19.2(ii)). -/
theorem ellipticEInc_add_pi {m : ℝ} (hm : m < 1) (φ : ℝ) :
    ellipticEInc (φ + π) m = ellipticEInc φ m + 2 * ellipticE m := by
  unfold ellipticEInc ellipticE; exact integral_add_pi hm _ φ

/-- `F(π/2|m) = K(m)`. -/
theorem ellipticF_pi_div_two (m : ℝ) : ellipticF (π / 2) m = ellipticK m := rfl

/-- `E(π/2|m) = E(m)`. -/
theorem ellipticEInc_pi_div_two (m : ℝ) : ellipticEInc (π / 2) m = ellipticE m := rfl

/-- `F(-φ|m) = -F(φ|m)`. -/
theorem ellipticF_neg (φ m : ℝ) : ellipticF (-φ) m = -ellipticF φ m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ) =
      ∫ θ in (0 : ℝ)..(-φ), (1 - m * sin (-θ) ^ 2) ^ (-(1 / 2) : ℝ) := by
    simp only [sin_neg, neg_sq]
  rw [ellipticF, ellipticF, h,
    intervalIntegral.integral_comp_neg (fun θ => (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)), neg_neg,
    neg_zero,
    intervalIntegral.integral_symm]

/-- `F(φ|0) = φ`. -/
theorem ellipticF_zero_param (φ : ℝ) : ellipticF φ 0 = φ := by simp [ellipticF]

/-- `∂F/∂φ = (1 - m sin²φ)^{-1/2}`. -/
theorem hasDerivAt_ellipticF {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => ellipticF φ m) ((1 - m * sin φ ^ 2) ^ (-(1 / 2) : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `∂E/∂φ = (1 - m sin²φ)^{1/2}`. -/
theorem hasDerivAt_ellipticEInc {m : ℝ} (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => ellipticEInc φ m) ((1 - m * sin φ ^ 2) ^ (1 / 2 : ℝ)) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
    ((continuous_one_sub_mul_sin_sq_rpow hm _).stronglyMeasurableAtFilter _ _)
    (continuous_one_sub_mul_sin_sq_rpow hm _).continuousAt

/-- `φ ↦ F(φ|m)` is strictly increasing for `m < 1`. -/
lemma strictMono_ellipticF {m : ℝ} (hm : m < 1) : StrictMono fun φ => ellipticF φ m :=
  strictMono_of_deriv_pos fun φ => by
    rw [(hasDerivAt_ellipticF hm φ).deriv]
    exact rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm φ) _

/-- `φ ↦ F(φ|m)` maps `ℝ` onto `ℝ` for `m < 1`. -/
lemma surjective_ellipticF {m : ℝ} (hm : m < 1) : Function.Surjective fun φ => ellipticF φ m := by
  have hcont : Continuous fun φ => ellipticF φ m :=
    continuous_iff_continuousAt.mpr fun φ => (hasDerivAt_ellipticF hm φ).continuousAt
  have hK : 0 < ellipticK m := by
    rw [ellipticK]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_one_sub_mul_sin_sq_rpow hm _).intervalIntegrable _ _)
      (fun θ _ => rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm θ) _) (by positivity)
  -- `F(nπ) = 2nK`
  have hnat : ∀ n : ℕ, ellipticF (n * π) m = 2 * n * ellipticK m := by
    intro n
    induction n with
    | zero => simp [ellipticF]
    | succ n ih => push_cast; rw [add_mul, one_mul, ellipticF_add_pi hm, ih]; ring
  have hmono := strictMono_ellipticF hm
  refine hcont.surjective ?_ ?_
  · refine tendsto_atTop_atTop.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (b / (2 * ellipticK m))
    refine ⟨n * π, fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith
  · refine tendsto_atBot_atBot.mpr fun b => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (-b / (2 * ellipticK m))
    refine ⟨-(n * π), fun φ hφ => ?_⟩
    have := hmono.monotone hφ
    rw [ellipticF_neg, hnat] at this
    rw [div_lt_iff₀ (by positivity)] at hn
    linarith

/-- For `m < 1`, `φ ↦ F(φ|m)` as an order isomorphism of `ℝ`. -/
def ellipticFOrderIso {m : ℝ} (hm : m < 1) : ℝ ≃o ℝ :=
  StrictMono.orderIsoOfSurjective _ (strictMono_ellipticF hm) (surjective_ellipticF hm)

/-- Jacobi's amplitude `am(u|m)`, the inverse of `φ ↦ F(φ|m)` for `m < 1` (Temme (12.21),
DLMF §22.16(i)); it is set to `u` for `m ≥ 1`. -/
def jacobiAm (u m : ℝ) : ℝ := if h : m < 1 then (ellipticFOrderIso h).symm u else u

/-- `F(am(u|m)|m) = u`. -/
theorem ellipticF_jacobiAm {m : ℝ} (hm : m < 1) (u : ℝ) : ellipticF (jacobiAm u m) m = u := by
  simp only [jacobiAm, hm, ↓reduceDIte]
  exact (ellipticFOrderIso hm).apply_symm_apply u

/-- `am(F(φ|m)|m) = φ`. -/
theorem jacobiAm_ellipticF {m : ℝ} (hm : m < 1) (φ : ℝ) : jacobiAm (ellipticF φ m) m = φ := by
  simp only [jacobiAm, hm, ↓reduceDIte]
  exact (ellipticFOrderIso hm).symm_apply_apply φ

/-- The amplitude is continuous. -/
lemma continuous_jacobiAm {m : ℝ} (hm : m < 1) : Continuous fun u => jacobiAm u m := by
  simp only [jacobiAm, hm, ↓reduceDIte]
  exact (ellipticFOrderIso hm).symm.continuous

/-- `d am/du = dn(u|m) = (1 - m sin² am)^{1/2}`. -/
theorem hasDerivAt_jacobiAm {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => jacobiAm u m) ((1 - m * sin (jacobiAm u m) ^ 2) ^ (1 / 2 : ℝ)) u := by
  have hpos := one_sub_mul_sin_sq_pos hm (jacobiAm u m)
  have h := HasDerivAt.of_local_left_inverse (f := fun φ => ellipticF φ m)
    (continuous_jacobiAm hm).continuousAt (hasDerivAt_ellipticF hm (jacobiAm u m))
    (rpow_pos_of_pos hpos _).ne' (Eventually.of_forall fun y => ellipticF_jacobiAm hm y)
  rwa [rpow_neg hpos.le, inv_inv] at h

/-- `am(0|m) = 0`. -/
theorem jacobiAm_zero {m : ℝ} (hm : m < 1) : jacobiAm 0 m = 0 := by
  simpa [ellipticF] using jacobiAm_ellipticF hm 0

/-- `am(K|m) = π/2`. -/
theorem jacobiAm_ellipticK {m : ℝ} (hm : m < 1) : jacobiAm (ellipticK m) m = π / 2 := by
  rw [← ellipticF_pi_div_two, jacobiAm_ellipticF hm]

/-- `am(u + 2K|m) = am(u|m) + π`. -/
theorem jacobiAm_add_two_ellipticK {m : ℝ} (hm : m < 1) (u : ℝ) :
    jacobiAm (u + 2 * ellipticK m) m = jacobiAm u m + π := by
  conv_lhs => rw [← ellipticF_jacobiAm hm u, ← ellipticF_add_pi hm]
  exact jacobiAm_ellipticF hm _

/-- `am(-u|m) = -am(u|m)`. -/
theorem jacobiAm_neg {m : ℝ} (hm : m < 1) (u : ℝ) : jacobiAm (-u) m = -jacobiAm u m := by
  conv_lhs => rw [← ellipticF_jacobiAm hm u, ← ellipticF_neg]
  exact jacobiAm_ellipticF hm _

/-- `am(u|0) = u`. -/
theorem jacobiAm_zero_param (u : ℝ) : jacobiAm u 0 = u := by
  simpa [ellipticF_zero_param] using jacobiAm_ellipticF (m := 0) (by norm_num) u

/-- Jacobi's elliptic function `sn(u|m) = sin am(u|m)`. -/
def jacobiSn (u m : ℝ) : ℝ := sin (jacobiAm u m)

/-- Jacobi's elliptic function `cn(u|m) = cos am(u|m)`. -/
def jacobiCn (u m : ℝ) : ℝ := cos (jacobiAm u m)

/-- Jacobi's elliptic function `dn(u|m) = (1 - m sn²(u|m))^{1/2}` (DLMF 22.6.1). -/
def jacobiDn (u m : ℝ) : ℝ := (1 - m * jacobiSn u m ^ 2) ^ (1 / 2 : ℝ)

/-- `sn² + cn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem jacobiSn_sq_add_jacobiCn_sq (u m : ℝ) : jacobiSn u m ^ 2 + jacobiCn u m ^ 2 = 1 :=
  sin_sq_add_cos_sq _

/-- `m sn² + dn² = 1` (DLMF 22.6.1). -/
@[dlmf 22.6.E1]
theorem mul_jacobiSn_sq_add_jacobiDn_sq {m : ℝ} (hm : m < 1) (u : ℝ) :
    m * jacobiSn u m ^ 2 + jacobiDn u m ^ 2 = 1 := by
  have hx : 0 < 1 - m * jacobiSn u m ^ 2 := one_sub_mul_sin_sq_pos hm (jacobiAm u m)
  rw [jacobiDn, ← rpow_natCast ((1 - m * jacobiSn u m ^ 2) ^ (1 / 2 : ℝ)) 2, ← rpow_mul hx.le]
  norm_num

/-- `dn > 0` for `m < 1`. -/
theorem jacobiDn_pos {m : ℝ} (hm : m < 1) (u : ℝ) : 0 < jacobiDn u m :=
  rpow_pos_of_pos (one_sub_mul_sin_sq_pos hm _) _

/-- `d sn/du = cn dn` (DLMF 22.13.1). -/
@[dlmf 22.13.E1]
theorem hasDerivAt_jacobiSn {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => jacobiSn u m) (jacobiCn u m * jacobiDn u m) u :=
  (hasDerivAt_sin _).comp u (hasDerivAt_jacobiAm hm u)

/-- `d cn/du = -sn dn` (DLMF 22.13.2). -/
@[dlmf 22.13.E2]
theorem hasDerivAt_jacobiCn {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => jacobiCn u m) (-(jacobiSn u m * jacobiDn u m)) u := by
  have h := (hasDerivAt_cos _).comp u (hasDerivAt_jacobiAm hm u)
  exact h.congr_deriv (by simp [jacobiSn, jacobiDn])

/-- `d dn/du = -m sn cn` (DLMF 22.13.3). -/
@[dlmf 22.13.E3]
theorem hasDerivAt_jacobiDn {m : ℝ} (hm : m < 1) (u : ℝ) :
    HasDerivAt (fun u => jacobiDn u m) (-(m * jacobiSn u m * jacobiCn u m)) u := by
  have hx : 0 < 1 - m * jacobiSn u m ^ 2 := one_sub_mul_sin_sq_pos hm (jacobiAm u m)
  have h1 := (((hasDerivAt_jacobiSn hm u).pow 2).const_mul m).const_sub 1
  have h := h1.rpow_const (p := 1 / 2) (Or.inl hx.ne')
  have hdpos := jacobiDn_pos hm u
  have hr : (1 - m * jacobiSn u m ^ 2) ^ (1 / 2 - 1 : ℝ) = (jacobiDn u m)⁻¹ := by
    rw [show (1 / 2 - 1 : ℝ) = -(1 / 2) by norm_num, rpow_neg hx.le]
    rfl
  refine h.congr_deriv ?_
  simp only [Pi.pow_apply]
  rw [hr]
  field_simp
  ring

/-- `sn(u + 2K) = -sn u`, `cn(u + 2K) = -cn u`, `dn(u + 2K) = dn u` (DLMF Table 22.4.3). -/
theorem jacobi_add_two_ellipticK {m : ℝ} (hm : m < 1) (u : ℝ) :
    jacobiSn (u + 2 * ellipticK m) m = -jacobiSn u m ∧
      jacobiCn (u + 2 * ellipticK m) m = -jacobiCn u m ∧
      jacobiDn (u + 2 * ellipticK m) m = jacobiDn u m := by
  simp only [jacobiDn, jacobiSn, jacobiCn, jacobiAm_add_two_ellipticK hm, sin_add_pi,
    cos_add_pi, neg_sq, and_self]

/-- `sn` and `cn` have period `4K` (DLMF §22.4). -/
theorem jacobiSn_add_four_ellipticK {m : ℝ} (hm : m < 1) (u : ℝ) :
    jacobiSn (u + 4 * ellipticK m) m = jacobiSn u m ∧
      jacobiCn (u + 4 * ellipticK m) m = jacobiCn u m := by
  have h := jacobi_add_two_ellipticK hm (u + 2 * ellipticK m)
  have h' := jacobi_add_two_ellipticK hm u
  rw [show u + 2 * ellipticK m + 2 * ellipticK m = u + 4 * ellipticK m by ring] at h
  exact ⟨by rw [h.1, h'.1, neg_neg], by rw [h.2.1, h'.2.1, neg_neg]⟩

/-- Special values at `u = K` (DLMF Table 22.5.1): `sn K = 1`, `cn K = 0`, `dn K = (1-m)^{1/2}`. -/
theorem jacobi_ellipticK {m : ℝ} (hm : m < 1) :
    jacobiSn (ellipticK m) m = 1 ∧ jacobiCn (ellipticK m) m = 0 ∧
      jacobiDn (ellipticK m) m = (1 - m) ^ (1 / 2 : ℝ) := by
  simp [jacobiDn, jacobiSn, jacobiCn, jacobiAm_ellipticK hm]

/-- Values at `u = 0`: `sn 0 = 0`, `cn 0 = 1`, `dn 0 = 1`. -/
theorem jacobi_zero {m : ℝ} (hm : m < 1) :
    jacobiSn 0 m = 0 ∧ jacobiCn 0 m = 1 ∧ jacobiDn 0 m = 1 := by
  simp [jacobiDn, jacobiSn, jacobiCn, jacobiAm_zero hm]

/-- `sn` is odd and `cn`, `dn` are even. -/
theorem jacobi_neg {m : ℝ} (hm : m < 1) (u : ℝ) :
    jacobiSn (-u) m = -jacobiSn u m ∧ jacobiCn (-u) m = jacobiCn u m ∧
      jacobiDn (-u) m = jacobiDn u m := by
  simp [jacobiDn, jacobiSn, jacobiCn, jacobiAm_neg hm]

/-- For `m = 0` the Jacobi functions reduce to `sin`, `cos`, `1` (DLMF §22.5(ii)). -/
theorem jacobi_zero_param (u : ℝ) :
    jacobiSn u 0 = sin u ∧ jacobiCn u 0 = cos u ∧ jacobiDn u 0 = 1 := by
  simp [jacobiDn, jacobiSn, jacobiCn, jacobiAm_zero_param]

end AAR.Elliptic
