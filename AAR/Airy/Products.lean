/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Scorer
public import AAR.Airy.Zeros

/-!
# Products of Airy solutions, DLMF §9.11

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The derivative of a product of Airy solutions. -/
lemma airy_product_deriv {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') :
    deriv (fun z => f z * g z) = fun z => f' z * g z + f z * g' z :=
  funext fun z => ((hf z).1.mul (hg z).1).deriv

/-- The second derivative of a product of Airy solutions. -/
lemma airy_product_second_deriv {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') :
    deriv (deriv (fun z => f z * g z)) = fun z => 2 * z * f z * g z + 2 * f' z * g' z := by
  rw [airy_product_deriv hf hg]
  funext z
  have h := ((hf z).2.mul (hg z).1).add ((hf z).1.mul (hg z).2)
  exact h.deriv.trans (by ring)

/-- airy product ode (DLMF 9.11.1). -/
@[dlmf 9.11.E1]
theorem airy_product_ode {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    iteratedDeriv 3 (fun t => f t * g t) z - 4 * z * deriv (fun t => f t * g t) z - 2 * f z * g z = 0 := by
  have he := airy_product_second_deriv hf hg
  have h := ((((hasDerivAt_id z).const_mul 2).mul (hf z).1).mul (hg z).1).add
    (((hf z).2.mul (hg z).2).const_mul 2)
  have hd : deriv (fun t => 2 * t * f t * g t + 2 * f' t * g' t) z =
      2 * f z * g z + 4 * z * (f' z * g z + f z * g' z) := by
    have h0 : HasDerivAt (fun t => 2 * t * f t * g t + 2 * f' t * g' t) _ z :=
      h.congr_of_eventuallyEq (Eventually.of_forall fun t => by
        simp only [Pi.mul_apply, Pi.add_apply, _root_.id]; ring)
    rw [h0.deriv]
    simp only [Pi.mul_apply, _root_.id]
    ring
  simp only [iteratedDeriv_succ, iteratedDeriv_zero]
  rw [he, hd, airy_product_deriv hf hg]
  ring

/-- airy product wronskian (DLMF 9.11.2). -/
@[dlmf 9.11.E2]
theorem airy_product_wronskian (z : ℂ) :
    airyWronskian3 (fun t => airyAi t ^ 2) (fun t => airyAi t * airyBi t) (fun t => airyBi t ^ 2) z = 2 / π ^ 3 := by
  have hA : (fun t => airyAi t ^ 2) = fun t => airyAi t * airyAi t := by funext t; ring
  have hB : (fun t => airyBi t ^ 2) = fun t => airyBi t * airyBi t := by funext t; ring
  unfold airyWronskian3
  rw [hA, hB]
  rw [airy_product_second_deriv isAirySol_airyAi isAirySol_airyAi,
    airy_product_second_deriv isAirySol_airyAi isAirySol_airyBi,
    airy_product_second_deriv isAirySol_airyBi isAirySol_airyBi]
  simp only [airy_product_deriv isAirySol_airyAi isAirySol_airyAi,
    airy_product_deriv isAirySol_airyAi isAirySol_airyBi,
    airy_product_deriv isAirySol_airyBi isAirySol_airyBi]
  calc
    _ = 2 * (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) ^ 3 := by ring
    _ = 2 / π ^ 3 := by rw [wronskian_airyAi_airyBi]; ring

/-- airyAi sq bessel integral (DLMF 9.11.3). -/
@[dlmf 9.11.E3]
theorem airyAi_sq_bessel_integral {x : ℝ} (hx : 0 ≤ x) :
    HasIntegralAtTop (fun t : ℝ => Complex.besselJ 0 ((t : ℂ) ^ 3 / 12 + x * t) * t)
      0 (4 * π * Real.sqrt 3 * airyAi x ^ 2) := by
  sorry

/-- airy modulus sq exp integral (DLMF 9.11.4). -/
@[dlmf 9.11.E4]
theorem airy_modulus_sq_exp_integral (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) (Ioi 0) ∧
      airyAi z ^ 2 + airyBi z ^ 2 =
        (∫ t : ℝ in Ioi 0, exp (z * t - (t : ℂ) ^ 3 / 12) * (t : ℂ) ^ (-1 / 2 : ℂ)) /
          (π : ℂ) ^ (3 / 2 : ℂ) := by
  sorry

/-- airy product antiderivative 5 (DLMF 9.11.5). -/
@[dlmf 9.11.E5]
theorem airy_product_antiderivative_5 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => -f' t * g' t + t * f t * g t) (f z * g z) z := by
  have h := ((hf z).2.neg.mul (hg z).2).add
    (((hasDerivAt_id z).mul (hf z).1).mul (hg z).1)
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- airy product antiderivative 6 (DLMF 9.11.6). -/
@[dlmf 9.11.E6]
theorem airy_product_antiderivative_6 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g t + t * (f 0 * g' 0 - f' 0 * g 0)) / 2) (f z * g' z) z := by
  have h := (((hf z).1.mul (hg z).1).add
    ((hasDerivAt_id z).mul_const (f 0 * g' 0 - f' 0 * g 0))).div_const 2
  have hW := hf.wronskian_eq hg z
  exact h.congr_deriv (by linear_combination -hW / 2)

/-- airy product antiderivative 7 (DLMF 9.11.7). -/
@[dlmf 9.11.E7]
theorem airy_product_antiderivative_7 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g' t + f' t * g t + t * f' t * g' t - t ^ 2 * f t * g t) / 3) (f' z * g' z) z := by
  have h := (((((hf z).1.mul (hg z).2).add ((hf z).2.mul (hg z).1)).add
    (((hasDerivAt_id z).mul (hf z).2).mul (hg z).2)).sub
      (((hasDerivAt_pow 2 z).mul (hf z).1).mul (hg z).1)).div_const 3
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- airy product antiderivative 8 (DLMF 9.11.8). -/
@[dlmf 9.11.E8]
theorem airy_product_antiderivative_8 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => (f t * g' t + f' t * g t) / 6 - (t * f' t * g' t - t ^ 2 * f t * g t) / 3) (z * f z * g z) z := by
  have h := ((((hf z).1.mul (hg z).2).add ((hf z).2.mul (hg z).1)).div_const 6).sub
    (((((hasDerivAt_id z).mul (hf z).2).mul (hg z).2).sub
      (((hasDerivAt_pow 2 z).mul (hf z).1).mul (hg z).1)).div_const 3)
  exact h.congr_deriv (by simp only [_root_.id, Pi.mul_apply, Pi.neg_apply]; ring)

/-- airy product antiderivative 9 (DLMF 9.11.9). -/
@[dlmf 9.11.E9]
theorem airy_product_antiderivative_9 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => f' t * g' t / 2 + t ^ 2 * (f 0 * g' 0 - f' 0 * g 0) / 4) (z * f z * g' z) z := by
  have h := (((hf z).2.mul (hg z).2).div_const 2).add
    (((hasDerivAt_pow 2 z).mul_const (f 0 * g' 0 - f' 0 * g 0)).div_const 4)
  have hW := hf.wronskian_eq hg z
  exact h.congr_deriv (by linear_combination -(z / 2) * hW)

/-- airy product antiderivative 10 (DLMF 9.11.10). -/
@[dlmf 9.11.E10]
theorem airy_product_antiderivative_10 {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') (z : ℂ) :
    HasDerivAt (fun t => 3 / 10 * (-f t * g t + t * f t * g' t + t * f' t * g t) + (t ^ 2 * f' t * g' t - t ^ 3 * f t * g t) / 5) (z * f' z * g' z) z := by
  have h := (((((hf z).1.mul (hg z).1).neg.add
    (((hasDerivAt_id z).mul (hf z).1).mul (hg z).2)).add
      (((hasDerivAt_id z).mul (hf z).2).mul (hg z).1)).const_mul (3 / 10 : ℂ)).add
    (((((hasDerivAt_pow 2 z).mul (hf z).2).mul (hg z).2).sub
      (((hasDerivAt_pow 3 z).mul (hf z).1).mul (hg z).1)).div_const 5)
  convert h using 1
  · funext t
    simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, Pi.neg_apply, _root_.id]
    ring
  · simp only [Pi.mul_apply, _root_.id]
    ring

/-- airy quotient antiderivative (DLMF 9.11.11). -/
@[dlmf 9.11.E11]
theorem airy_quotient_antiderivative {f f' g g' : ℂ → ℂ} (hf : IsAirySol f f') (hg : IsAirySol g g') {F : ℂ → ℂ} {F' z : ℂ}
    (hF : HasDerivAt F F' (g z / f z)) (hfz : f z ≠ 0)
    (hW : f 0 * g' 0 - f' 0 * g 0 ≠ 0) :
    HasDerivAt (fun t => F (g t / f t) / (f 0 * g' 0 - f' 0 * g 0)) (F' / f z ^ 2) z := by
  have h := (hF.comp z ((hg z).1.div (hf z).1 hfz)).div_const (f 0 * g' 0 - f' 0 * g 0)
  have he : g' z * f z - g z * f' z = f 0 * g' 0 - f' 0 * g 0 := by
    linear_combination hf.wronskian_eq hg z
  exact h.congr_deriv (by rw [he]; field_simp)

/-- airyAi inv sq antiderivative (DLMF 9.11.12). -/
@[dlmf 9.11.E12]
theorem airyAi_inv_sq_antiderivative {z : ℂ} (hz : airyAi z ≠ 0) :
    HasDerivAt (fun t => π * airyBi t / airyAi t) (1 / airyAi z ^ 2) z := by
  have h := ((hasDerivAt_airyBi z).div (hasDerivAt_airyAi z) hz).const_mul (π : ℂ)
  have he : airyBiDeriv z * airyAi z - airyBi z * airyAiDeriv z = 1 / π := by
    linear_combination wronskian_airyAi_airyBi z
  convert h using 1
  · funext t; simp only [Pi.div_apply]; ring
  · rw [he]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp

/-- airyAiBi inv antiderivative (DLMF 9.11.13). -/
@[dlmf 9.11.E13]
theorem airyAiBi_inv_antiderivative {z : ℂ} (ha : airyAi z ≠ 0) (hb : airyBi z ≠ 0)
    (hlog : airyBi z / airyAi z ∈ slitPlane) :
    HasDerivAt (fun t => π * log (airyBi t / airyAi t)) (1 / (airyAi z * airyBi z)) z := by
  have hq := (hasDerivAt_airyBi z).div (hasDerivAt_airyAi z) ha
  have h := ((Complex.hasDerivAt_log hlog).comp z hq).const_mul (π : ℂ)
  have he : airyBiDeriv z * airyAi z - airyBi z * airyAiDeriv z = 1 / π := by
    linear_combination wronskian_airyAi_airyBi z
  convert h using 1
  · funext t
    simp only [Function.comp_apply, Pi.div_apply]
  · rw [he]
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp [ha, hb, hπ]

/-- airy modulus rational antiderivative (DLMF 9.11.14). -/
@[dlmf 9.11.E14]
theorem airy_modulus_rational_antiderivative {z : ℂ} (hz : airyAi z ^ 2 + airyBi z ^ 2 ≠ 0) :
    HasDerivAt (fun t => π / 2 * airyBi t ^ 2 / (airyAi t ^ 2 + airyBi t ^ 2))
      (airyAi z * airyBi z / (airyAi z ^ 2 + airyBi z ^ 2) ^ 2) z := by
  have hnum := ((hasDerivAt_airyBi z).pow 2).const_mul (π / 2 : ℂ)
  have hden := ((hasDerivAt_airyAi z).pow 2).add ((hasDerivAt_airyBi z).pow 2)
  have h := hnum.div hden hz
  simp only [Pi.pow_apply, Pi.add_apply] at h
  refine h.congr_deriv ?_
  have hW : (π : ℂ) * (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) = 1 := by
    rw [wronskian_airyAi_airyBi]
    simpa only [one_div] using mul_inv_cancel₀ (ofReal_ne_zero.mpr Real.pi_ne_zero : (π : ℂ) ≠ 0)
  field_simp
  linear_combination 2 * airyAi z * airyBi z * hW

/-- airyAi sq mellin (DLMF 9.11.15). -/
@[dlmf 9.11.E15]
theorem airyAi_sq_mellin {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t ^ 2) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) * airyAi t ^ 2) =
        2 * Gamma α / (Real.sqrt π * (12 : ℂ) ^ ((2 * α + 5) / 6) * Gamma (α / 3 + 5 / 6)) := by
  sorry

/-- airyAi cube integral (DLMF 9.11.16). -/
@[dlmf 9.11.E16]
theorem airyAi_cube_integral  :
    HasIntegralWholeLine (fun t => airyAi t ^ 3) (Gamma (1 / 3) ^ 2 / (4 * π ^ 2)) := by
  sorry

/-- airyAi sq airyBi integral (DLMF 9.11.17). -/
@[dlmf 9.11.E17]
theorem airyAi_sq_airyBi_integral  :
    HasIntegralWholeLine (fun t => airyAi t ^ 2 * airyBi t) (Gamma (1 / 3) ^ 2 / (4 * Real.sqrt 3 * π ^ 2)) := by
  sorry

/-- airyAi fourth integral (DLMF 9.11.18). -/
@[dlmf 9.11.E18]
theorem airyAi_fourth_integral  :
    (∫ t : ℝ in Ioi 0, airyAi t ^ 4) = log 3 / (24 * π ^ 2) := by
  sorry

/-- `Bi'(x) ≥ Bi'(0)` for `x ≥ 0`, since `Bi'' = x Bi ≥ 0` there. -/
lemma airyBiDerivReal_ge {x : ℝ} (hx : 0 ≤ x) : airyBiDerivReal 0 ≤ airyBiDerivReal x := by
  have hmono : MonotoneOn airyBiDerivReal (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_airyBiDerivReal t).continuousAt).continuousOn
      (fun t _ => (hasDerivAt_airyBiDerivReal t).differentiableAt.differentiableWithinAt)
      fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hasDerivAt_airyBiDerivReal t).deriv]
    exact mul_nonneg ht.le (airyBiReal_pos ht.le).le
  exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx

/-- `Bi(x) ≥ Bi(0) + Bi'(0) x` for `x ≥ 0`. -/
lemma airyBiReal_ge {x : ℝ} (hx : 0 ≤ x) :
    airyBiReal 0 + airyBiDerivReal 0 * x ≤ airyBiReal x := by
  have hmono : MonotoneOn (fun t => airyBiReal t - airyBiDerivReal 0 * t) (Ici 0) := by
    have hd : ∀ t, HasDerivAt (fun t => airyBiReal t - airyBiDerivReal 0 * t)
        (airyBiDerivReal t - airyBiDerivReal 0) t := fun t =>
      ((hasDerivAt_airyBiReal t).sub ((hasDerivAt_id t).const_mul _)).congr_deriv (by simp)
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (continuous_iff_continuousAt.mpr fun t => (hd t).continuousAt).continuousOn
      (fun t _ => (hd t).differentiableAt.differentiableWithinAt) fun t ht => ?_
    rw [interior_Ici, mem_Ioi] at ht
    rw [(hd t).deriv]
    linarith [airyBiDerivReal_ge ht.le]
  have := hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hx) hx
  simp only [mul_zero, sub_zero] at this
  linarith

/-- `Bi(x) → ∞` as `x → +∞`. -/
lemma tendsto_airyBiReal_atTop : Tendsto airyBiReal atTop atTop := by
  refine tendsto_atTop_mono' _ (eventually_ge_atTop 0 |>.mono fun x hx => airyBiReal_ge hx) ?_
  exact tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop airyBiDerivReal_zero_pos)

/-- `Ai(x)/Bi(x) → 0` as `x → +∞`. -/
lemma tendsto_airyAi_div_airyBi : Tendsto (fun x => airyAiReal x / airyBiReal x) atTop (𝓝 0) :=
  tendsto_airyAiReal_atTop.div_atTop tendsto_airyBiReal_atTop

/-- `Ai'(x)/Bi'(x) → 0` as `x → +∞`, via the Wronskian. -/
lemma tendsto_airyAiDeriv_div_airyBiDeriv :
    Tendsto (fun x => airyAiDerivReal x / airyBiDerivReal x) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x => airyBiReal x * airyBiDerivReal x) atTop atTop :=
    tendsto_atTop_mono' _ (eventually_ge_atTop 0 |>.mono fun x hx =>
      mul_le_mul_of_nonneg_left (airyBiDerivReal_ge hx) (airyBiReal_pos hx).le)
      (tendsto_airyBiReal_atTop.atTop_mul_const airyBiDerivReal_zero_pos)
  have h2 := (h1.const_mul_atTop Real.pi_pos).inv_tendsto_atTop
  have h3 := tendsto_airyAi_div_airyBi.sub h2
  rw [sub_zero] at h3
  refine h3.congr' (eventually_ge_atTop 0 |>.mono fun x hx => ?_)
  have hb := (airyBiReal_pos hx).ne'
  have hb' := (airyBiDerivReal_zero_pos.trans_le (airyBiDerivReal_ge hx)).ne'
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  simp only [Pi.inv_apply]
  field_simp
  field_simp at hW
  linear_combination hW

/-- `arctan(1/√3) = π/6`. -/
lemma arctan_inv_sqrt_three : Real.arctan (1 / Real.sqrt 3) = π / 6 := by
  rw [← Real.tan_pi_div_six, Real.arctan_tan (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])]

/-- `Ai(0)/Bi(0) = 1/√3`. -/
lemma airyReal_zero_ratio : airyAiReal 0 / airyBiReal 0 = 1 / Real.sqrt 3 := by
  have hA : airyAiReal 0 = 1 / ((3 : ℝ) ^ (2 / 3 : ℝ) * Real.Gamma (2 / 3)) := by
    have h := airyAi_zero
    rw [Gamma_two_thirds_eq, ← ofReal_mul, ← ofReal_one, ← ofReal_div] at h
    simp [airyAiReal, h]
  have hB : airyBiReal 0 = 1 / ((3 : ℝ) ^ (1 / 6 : ℝ) * Real.Gamma (2 / 3)) := by
    have h := airyBi_zero
    rw [Gamma_two_thirds_eq, ← ofReal_mul, ← ofReal_one, ← ofReal_div] at h
    simp [airyBiReal, h]
  have hG := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 2 / 3)).ne'
  have h1 : (3 : ℝ) ^ (1 / 6 : ℝ) = (3 : ℝ) ^ (2 / 3 : ℝ) * (Real.sqrt 3)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by norm_num), ← Real.rpow_add (by norm_num)]
    norm_num
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (2 / 3 : ℝ) := by positivity
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  rw [hA, hB, h1]
  field_simp

/-- `Ai'(0)/Bi'(0) = -1/√3`. -/
lemma airyDerivReal_zero_ratio : airyAiDerivReal 0 / airyBiDerivReal 0 = -(1 / Real.sqrt 3) := by
  have hG' : Complex.Gamma (1 / 3) = ((Real.Gamma (1 / 3) : ℝ) : ℂ) := by
    rw [← Complex.Gamma_ofReal]; push_cast; ring_nf
  have hA : airyAiDerivReal 0 = -1 / ((3 : ℝ) ^ (1 / 3 : ℝ) * Real.Gamma (1 / 3)) := by
    have h := airyAiDeriv_zero
    rw [hG', ← ofReal_mul, show (-1 : ℂ) = ((-1 : ℝ) : ℂ) by simp, ← ofReal_div] at h
    rw [airyAiDerivReal, ofReal_zero, h, ofReal_re]
  have hB : airyBiDerivReal 0 = (3 : ℝ) ^ (1 / 6 : ℝ) / Real.Gamma (1 / 3) := by
    have h := airyBiDeriv_zero
    rw [hG', ← ofReal_div] at h
    simp [airyBiDerivReal, h]
  have hG := (Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 3)).ne'
  have h1 : (3 : ℝ) ^ (1 / 3 : ℝ) * (3 : ℝ) ^ (1 / 6 : ℝ) = Real.sqrt 3 := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num)]; norm_num
  have h2 : (0 : ℝ) < (3 : ℝ) ^ (1 / 3 : ℝ) := by positivity
  have h2' : (0 : ℝ) < (3 : ℝ) ^ (1 / 6 : ℝ) := by positivity
  rw [hA, hB, ← h1]
  field_simp

/-- A primitive of `1/(Ai² + Bi²)` on `[0, ∞)`. -/
lemma hasDerivAt_arctan_airy_ratio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => -π * Real.arctan (airyAiReal t / airyBiReal t))
      (1 / (airyAiReal x ^ 2 + airyBiReal x ^ 2)) x := by
  have hb := (airyBiReal_pos hx).ne'
  have h := (((hasDerivAt_airyAiReal x).div (hasDerivAt_airyBiReal x) hb).arctan).const_mul (-π)
  refine h.congr_deriv ?_
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  have hM := (airyModulusSq_pos x).ne'
  simp only [Pi.div_apply]
  field_simp
  field_simp at hW
  linear_combination (airyAiReal x ^ 2 + airyBiReal x ^ 2) * hW

/-- A primitive of `x/(Ai'² + Bi'²)` on `[0, ∞)`. -/
lemma hasDerivAt_arctan_airyDeriv_ratio {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun t => π * Real.arctan (airyAiDerivReal t / airyBiDerivReal t))
      (x / (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2)) x := by
  have hb := (airyBiDerivReal_zero_pos.trans_le (airyBiDerivReal_ge hx)).ne'
  have h := (((hasDerivAt_airyAiDerivReal x).div (hasDerivAt_airyBiDerivReal x) hb).arctan).const_mul π
  refine h.congr_deriv ?_
  have hW := wronskian_airyReal x
  have hπ := Real.pi_ne_zero
  have hN := (airyDerivModulusSq_pos x).ne'
  simp only [Pi.div_apply]
  field_simp
  field_simp at hW
  linear_combination (x * (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2)) * hW

/-- airy modulus reciprocal integrals (DLMF 9.11.19). -/
@[dlmf 9.11.E19]
theorem airy_modulus_reciprocal_integrals  :
    (∫ t : ℝ in Ioi 0, 1 / (airyAi t ^ 2 + airyBi t ^ 2)) = (π : ℂ) ^ 2 / 6 ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) / (airyAiDeriv t ^ 2 + airyBiDeriv t ^ 2)) = (π : ℂ) ^ 2 / 6 := by
  have e1 : (fun t : ℝ => 1 / (airyAi t ^ 2 + airyBi t ^ 2)) =
      fun t : ℝ => ((1 / (airyAiReal t ^ 2 + airyBiReal t ^ 2) : ℝ) : ℂ) := by
    funext t; rw [airyAi_ofReal_eq, airyBi_ofReal_eq]; push_cast; ring
  have e2 : (fun t : ℝ => (t : ℂ) / (airyAiDeriv t ^ 2 + airyBiDeriv t ^ 2)) =
      fun t : ℝ => ((t / (airyAiDerivReal t ^ 2 + airyBiDerivReal t ^ 2) : ℝ) : ℂ) := by
    funext t; rw [airyAiDeriv_ofReal_eq, airyBiDeriv_ofReal_eq]; push_cast; ring
  rw [e1, e2, _root_.integral_complex_ofReal, _root_.integral_complex_ofReal]
  have i1 := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x hx => hasDerivAt_arctan_airy_ratio hx)
    (fun x _ => (one_div_pos.mpr (airyModulusSq_pos x)).le)
    (by simpa [Real.arctan_zero] using
      ((Real.continuous_arctan.tendsto 0).comp tendsto_airyAi_div_airyBi).const_mul (-π))
  have i2 := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun x hx => hasDerivAt_arctan_airyDeriv_ratio hx)
    (fun x hx => div_nonneg (le_of_lt hx) (airyDerivModulusSq_pos x).le)
    (by simpa [Real.arctan_zero] using
      ((Real.continuous_arctan.tendsto 0).comp tendsto_airyAiDeriv_div_airyBiDeriv).const_mul π)
  rw [i1, i2, airyReal_zero_ratio, airyDerivReal_zero_ratio, Real.arctan_neg,
    arctan_inv_sqrt_three]
  constructor <;> push_cast <;> ring

end AAR.Airy
