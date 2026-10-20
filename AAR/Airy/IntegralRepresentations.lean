/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework
public import AAR.Airy.GeneralizedContours

/-!
# Airy integral representations, DLMF §9.5

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- airyAi cos integral (DLMF 9.5.1). -/
@[dlmf 9.5.E1]
theorem airyAi_cos_integral (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => (Real.cos (t ^ 3 / 3 + x * t) : ℂ)) 0 (π * airyAi x) := by
  sorry

/-- airyAi neg cos integral (DLMF 9.5.2). -/
@[dlmf 9.5.E2]
theorem airyAi_neg_cos_integral {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => (Real.cos (x ^ (3 / 2 : ℝ) * (t ^ 3 / 3 + t ^ 2 - 2 / 3)) : ℂ))
      (-1) (π / Real.sqrt x * airyAi (-x)) := by
  sorry

/-- airyBi real integral (DLMF 9.5.3). -/
@[dlmf 9.5.E3]
theorem airyBi_real_integral (x : ℝ) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ) ^ 3 / 3 + x * t)) (Ioi 0) ∧
      HasIntegralAtTop (fun t : ℝ => (Real.sin (t ^ 3 / 3 + x * t) : ℂ)) 0
        (π * airyBi x - ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + x * t)) := by
  sorry

/-- `e^{(θ+π)i} = -e^{θi}`. -/
lemma exp_add_pi_mul_I (θ : ℝ) : exp (((θ + π : ℝ) : ℂ) * I) = -exp (θ * I) := by
  push_cast; rw [add_mul, exp_add, exp_pi_mul_I]; ring

/-- The Airy contour integrand at `u` equals the Reid kernel (p = 0) at `-u`. -/
lemma reidKernel_zero_eq_airyIntegrand (z w : ℂ) {u : ℂ} (hu : exp w = -u) :
    reidKernel z 0 w = exp (u ^ 3 / 3 - z * u) := by
  rw [reidKernel, show exp (3 * w) = exp w ^ 3 by rw [← exp_nat_mul]; push_cast; ring_nf, hu]
  congr 1; ring

/-- Airy rays are Reid rays (p = 0) rotated by `π`. -/
lemma rayIntegral_airy_eq_reidRay (z : ℂ) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) θ r = -reidRay z 0 (θ + π) r := by
  rw [rayIntegral, reidRay, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : r < t) => ?_
  have ht0 : 0 < t := hr.trans_lt ht
  rw [reidKernel_zero_eq_airyIntegrand z _ (u := t * exp (θ * I)), exp_add_pi_mul_I]
  · ring
  · rw [exp_add, exp_log (ofReal_ne_zero.mpr ht0.ne'), exp_add_pi_mul_I]; ring

/-- Airy arcs are Reid arcs (p = 0) rotated by `π`. -/
lemma arcIntegral_airy_eq_reidArc (z : ℂ) (α β : ℝ) :
    arcIntegral (fun t => exp (t ^ 3 / 3 - z * t)) α β = -reidArc z 0 (α + π) (β + π) := by
  rw [arcIntegral, reidArc, ← intervalIntegral.integral_comp_add_right, ← intervalIntegral.integral_neg]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [reidKernel_zero_eq_airyIntegrand z _ (u := exp (θ * I)), exp_add_pi_mul_I]
  · ring
  · exact exp_add_pi_mul_I θ

/-- Airy contours are Reid contours (p = 0) rotated by `π`. -/
lemma contourIntegral_airy_eq_reidContour (z : ℂ) (α β : ℝ) :
    contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) α β =
      -reidContour z 0 (α + π) (β + π) := by
  rw [contourIntegral, reidContour, rayIntegral_airy_eq_reidRay z α zero_le_one,
    rayIntegral_airy_eq_reidRay z β zero_le_one, arcIntegral_airy_eq_reidArc]
  ring

/-- Reversing the orientation of a contour. -/
lemma contourIntegral_swap (f : ℂ → ℂ) (α β : ℝ) :
    contourIntegral f α β = -contourIntegral f β α := by
  rw [contourIntegral, contourIntegral, arcIntegral, arcIntegral, intervalIntegral.integral_symm]
  ring

/-- Concatenation of Reid contours. -/
lemma reidContour_add_adjacent (z p : ℂ) (a b c : ℝ) :
    reidContour z p a b + reidContour z p b c = reidContour z p a c := by
  rw [reidContour, reidContour, reidContour, ← reidArc_add_adjacent z p a b c]
  ring

/-- airyAi contour integral (DLMF 9.5.4). -/
@[dlmf 9.5.E4]
theorem airyAi_contour_integral (z : ℂ) :
    airyAi z = contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) (π / 3) / (2 * π * I) := by
  rw [contourIntegral_swap, contourIntegral_airy_eq_reidContour, ← reidAiryA_zero_parameter,
    show π / 3 + π = 4 * π / 3 by ring, show -π / 3 + π = 2 * π / 3 by ring]
  simp only [reidAiryA, Fin.val_zero]
  ring

/-- airyBi contour integral (DLMF 9.5.5). -/
@[dlmf 9.5.E5]
theorem airyBi_contour_integral (z : ℂ) :
    airyBi z = (contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (π / 3) +
      contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (-π / 3)) / (2 * π) := by
  rw [contourIntegral_airy_eq_reidContour, contourIntegral_airy_eq_reidContour,
    show π + π = 2 * π by ring, show π / 3 + π = 4 * π / 3 by ring,
    show -π / 3 + π = 2 * π / 3 by ring, ← reidContour_add_adjacent z 0 (2 * π) (4 * π / 3) (2 * π / 3)]
  have h0 : reidContour z 0 (4 * π / 3) (2 * π / 3) = 2 * π * I * airyAi z := by
    rw [← reidAiryA_zero_parameter]; simp only [reidAiryA, Fin.val_zero]
    field_simp
  have h1 : reidContour z 0 (2 * π) (4 * π / 3) =
      2 * π * I * (exp (2 * π * I / 3) * airyAi (z * exp (2 * π * I / 3))) := by
    rw [← (reidAiryA_zero_rotations z).1]; simp only [reidAiryA, Fin.val_one]
    field_simp
  rw [h0, h1, airyBi_eq_airyAi_omega]
  have hs := airyAi_add_omega z
  set b := airyAi (z * exp (2 * π * I / 3))
  set c := airyAi (z * exp (-(2 * π * I / 3)))
  rw [exp_two_pi_I_div_three, exp_neg_two_pi_I_div_three] at hs
  rw [exp_two_pi_I_div_three, exp_pi_I_div_six, exp_neg_pi_I_div_six]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  linear_combination 2 * I * hs + 2 * (((Real.sqrt 3 / 2 : ℝ) : ℂ) * c + ((Real.sqrt 3 / 2 : ℝ) : ℂ) * b) * I_sq

/-- airyAi cubic integral (DLMF 9.5.6). -/
@[dlmf 9.5.E6]
theorem airyAi_cubic_integral {z : ℂ} (hz : |arg z| < π / 6) :
    airyAi z = Real.sqrt 3 / (2 * π) *
      ∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - z ^ 3 / (3 * (t : ℂ) ^ 3)) := by
  sorry

/-- airyAi gaussian cos integral (DLMF 9.5.7). -/
@[dlmf 9.5.E7]
theorem airyAi_gaussian_cos_integral {z : ℂ} (hz : z ∈ slitPlane) :
    airyAi z = exp (-airyZetaComplex z) / π *
      ∫ t : ℝ in Ioi 0, exp (-z ^ (1 / 2 : ℂ) * (t : ℂ) ^ 2) * cos ((t : ℂ) ^ 3 / 3) := by
  sorry

/-- airyAi laplace integral (DLMF 9.5.8). -/
@[dlmf 9.5.E8]
theorem airyAi_laplace_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = exp (-airyZetaComplex z) * exp (-airyLogZeta z / 6) /
      (Real.sqrt π * (48 : ℂ) ^ (1 / 6 : ℂ) * Gamma (5 / 6)) *
      ∫ t : ℝ in Ioi 0, exp (-t : ℂ) * (t : ℂ) ^ (-1 / 6 : ℂ) *
        (2 + (t : ℂ) / airyZetaComplex z) ^ (-1 / 6 : ℂ) := by
  sorry

end AAR.Airy
