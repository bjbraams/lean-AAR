/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Scorer

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

/-- airy modulus reciprocal integrals (DLMF 9.11.19). -/
@[dlmf 9.11.E19]
theorem airy_modulus_reciprocal_integrals  :
    (∫ t : ℝ in Ioi 0, 1 / (airyAi t ^ 2 + airyBi t ^ 2)) = (π : ℂ) ^ 2 / 6 ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) / (airyAiDeriv t ^ 2 + airyBiDeriv t ^ 2)) = (π : ℂ) ^ 2 / 6 := by
  sorry

end AAR.Airy
