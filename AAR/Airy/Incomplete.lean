/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Incomplete Airy functions, DLMF §9.14

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The incomplete contour integral, replacing the upper endpoint of 9.5.4 by a.
The lower endpoint remains infinity on the ray of angle -π/3. -/
def incompleteAiryAi (a z : ℂ) : ℂ :=
  (-rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (-π / 3) 1 +
    lineIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (exp (-π * I / 3)) a) / (2 * π * I)

/-- Differentiation with respect to the finite endpoint in DLMF §9.14. -/
theorem incompleteAiryAi_endpoint_derivative (a z : ℂ) :
    HasDerivAt (fun b => incompleteAiryAi b z) (exp (a ^ 3 / 3 - z * a) / (2 * π * I)) a := by
  sorry

/-- Recovery of the complete Airy contour in DLMF §9.14. -/
theorem incompleteAiryAi_complete_limit (z : ℂ) :
    Tendsto (fun R : ℝ => incompleteAiryAi ((R : ℂ) * exp (π * I / 3)) z) atTop (𝓝 (airyAi z)) := by
  sorry

/-- The incomplete integral with variable lower endpoint and the upper endpoint at infinity. -/
def incompleteAiryAiLower (a z : ℂ) : ℂ :=
  (lineIntegral (fun t => exp (t ^ 3 / 3 - z * t)) a (exp (π * I / 3)) +
    rayIntegral (fun t => exp (t ^ 3 / 3 - z * t)) (π / 3) 1) / (2 * π * I)

/-- The lower-endpoint version of the incomplete Airy integral, DLMF §9.14. -/
theorem incompleteAiryAiLower_endpoint_derivative (a z : ℂ) :
    HasDerivAt (fun b => incompleteAiryAiLower b z) (-exp (a ^ 3 / 3 - z * a) / (2 * π * I)) a := by
  sorry

/-- Splitting the complete contour at any finite endpoint, DLMF §9.14. -/
theorem incompleteAiryAi_split (a z : ℂ) :
    incompleteAiryAi a z + incompleteAiryAiLower a z = airyAi z := by
  sorry

/-- Recovery with the lower endpoint tending to its original infinite limit, DLMF §9.14. -/
theorem incompleteAiryAiLower_complete_limit (z : ℂ) :
    Tendsto (fun R : ℝ => incompleteAiryAiLower ((R : ℂ) * exp (-π * I / 3)) z) atTop (𝓝 (airyAi z)) := by
  sorry

end AAR.Airy
