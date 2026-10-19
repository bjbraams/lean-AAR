/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

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

/-- airyAi contour integral (DLMF 9.5.4). -/
@[dlmf 9.5.E4]
theorem airyAi_contour_integral (z : ℂ) :
    airyAi z = contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) (π / 3) / (2 * π * I) := by
  sorry

/-- airyBi contour integral (DLMF 9.5.5). -/
@[dlmf 9.5.E5]
theorem airyBi_contour_integral (z : ℂ) :
    airyBi z = (contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (π / 3) +
      contourIntegral (fun t => exp (t ^ 3 / 3 - z * t)) π (-π / 3)) / (2 * π) := by
  sorry

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
