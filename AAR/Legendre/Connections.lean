/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated

/-!
# Ferrers and associated Legendre connection formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrers connection 1. -/
@[dlmf 14.9.E1]
theorem ferrers_connection_1 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*sin (μ*π)/(2*Gamma (ν-μ+1))*ferrersP ν (-μ) x=-ferrersQ ν μ x/Gamma (ν+μ+1)+cos (μ*π)/Gamma (ν-μ+1)*ferrersQ ν (-μ) x := by
  sorry

/-- ferrers connection 2. -/
@[dlmf 14.9.E2]
theorem ferrers_connection_2 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2*sin (μ*π)/(π*Gamma (ν-μ+1))*ferrersQ ν (-μ) x=ferrersP ν μ x/Gamma (ν+μ+1)-cos (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x := by
  sorry

/-- ferrers connection 5. -/
@[dlmf 14.9.E5]
theorem ferrers_connection_5 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (-ν-1) μ x=ferrersP ν μ x := by
  sorry

/-- ferrers connection 6. -/
@[dlmf 14.9.E6]
theorem ferrers_connection_6 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) (hother : LegendreQRegular (-ν-1) μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*cos (ν*π)*cos (μ*π)*ferrersP ν μ x=sin ((ν+μ)*π)*ferrersQ ν μ x-sin ((ν-μ)*π)*ferrersQ (-ν-1) μ x := by
  sorry

/-- ferrers connection 7. -/
@[dlmf 14.9.E7]
theorem ferrers_connection_7 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    sin ((ν-μ)*π)/Gamma (ν+μ+1)*ferrersP ν μ x=sin (ν*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x-sin (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) (-x) := by
  sorry

/-- ferrers connection 8. -/
@[dlmf 14.9.E8]
theorem ferrers_connection_8 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π/2*sin ((ν-μ)*π)*ferrersP ν (-μ) x=-cos ((ν-μ)*π)*ferrersQ ν (-μ) x-ferrersQ ν (-μ) (-x) := by
  sorry

/-- ferrers connection 9. -/
@[dlmf 14.9.E9]
theorem ferrers_connection_9 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/(Gamma (ν+μ+1)*Gamma (μ-ν))*ferrersQ ν μ x=-cos (ν*π)*ferrersP ν (-μ) x+cos (μ*π)*ferrersP ν (-μ) (-x) := by
  sorry

/-- ferrers connection 10. -/
@[dlmf 14.9.E10]
theorem ferrers_connection_10 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/π*sin ((ν-μ)*π)*ferrersQ ν (-μ) x=cos ((ν-μ)*π)*ferrersP ν (-μ) x-ferrersP ν (-μ) (-x) := by
  sorry

/-- ferrersP negative integer order. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersP ν m x := by
  sorry

/-- ferrersQ negative integer order. -/
@[dlmf 14.9.E4]
theorem ferrersQ_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersQ ν m x := by
  sorry

/-- associated connection 11. -/
@[dlmf 14.9.E11]
theorem associated_connection_11 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (-ν-1) μ z=associatedP ν μ z := by
  sorry

/-- associated connection 12. -/
@[dlmf 14.9.E12]
theorem associated_connection_12 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=-olverQ ν μ z/Gamma (μ-ν)+olverQ (-ν-1) μ z/Gamma (ν+μ+1) := by
  sorry

/-- associated connection 14. -/
@[dlmf 14.9.E14]
theorem associated_connection_14 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν (-μ) z=olverQ ν μ z := by
  sorry

/-- associated connection 15. -/
@[dlmf 14.9.E15]
theorem associated_connection_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  sorry

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E16]
theorem associated_connection_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    olverQ ν μ z=(π/2:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*associatedP (-μ-1/2) (-ν-1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  sorry

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E17]
theorem associated_connection_17 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν μ z=(2/π:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*olverQ (-μ-1/2) (ν+1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  sorry

/-- associatedP negative integer order. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=Gamma (ν-m+1)/Gamma (ν+m+1)*associatedP ν m z := by
  sorry

end AAR.Legendre
