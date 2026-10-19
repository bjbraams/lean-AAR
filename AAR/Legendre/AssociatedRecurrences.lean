/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Connections

/-!
# Degree and order recurrences and integer derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrersP recurrence 1. -/
@[dlmf 14.10.E1]
theorem ferrersP_recurrence_1 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*ferrersP ν (μ+1) x+(ν-μ)*(ν+μ+1)*ferrersP ν μ x=0 := by
  sorry

/-- ferrersP recurrence 2. -/
@[dlmf 14.10.E2]
theorem ferrersP_recurrence_2 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersP ν (μ+1) x-(ν-μ+1)*ferrersP (ν+1) μ x+(ν+μ+1)*x*ferrersP ν μ x=0 := by
  sorry

/-- ferrersP recurrence 3. -/
@[dlmf 14.10.E3]
theorem ferrersP_recurrence_3 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ν-μ+2)*ferrersP (ν+2) μ x-(2*ν+3)*x*ferrersP (ν+1) μ x+(ν+μ+1)*ferrersP ν μ x=0 := by
  sorry

/-- ferrersP recurrence 4. -/
@[dlmf 14.10.E4]
theorem ferrersP_recurrence_4 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersP ν μ) x=(μ-ν-1)*ferrersP (ν+1) μ x+(ν+1)*x*ferrersP ν μ x := by
  sorry

/-- ferrersP recurrence 5. -/
@[dlmf 14.10.E5]
theorem ferrersP_recurrence_5 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersP ν μ) x=(ν+μ)*ferrersP (ν-1) μ x-ν*x*ferrersP ν μ x := by
  sorry

/-- ferrersQ recurrence 1. -/
@[dlmf 14.10.E1]
theorem ferrersQ_recurrence_1 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (μ+2) x+2*(μ+1)*x*(1-x^2:ℂ)^(-1/2:ℂ)*ferrersQ ν (μ+1) x+(ν-μ)*(ν+μ+1)*ferrersQ ν μ x=0 := by
  sorry

/-- ferrersQ recurrence 2. -/
@[dlmf 14.10.E2]
theorem ferrersQ_recurrence_2 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)^(1/2:ℂ)*ferrersQ ν (μ+1) x-(ν-μ+1)*ferrersQ (ν+1) μ x+(ν+μ+1)*x*ferrersQ ν μ x=0 := by
  sorry

/-- ferrersQ recurrence 3. -/
@[dlmf 14.10.E3]
theorem ferrersQ_recurrence_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ν-μ+2)*ferrersQ (ν+2) μ x-(2*ν+3)*x*ferrersQ (ν+1) μ x+(ν+μ+1)*ferrersQ ν μ x=0 := by
  sorry

/-- ferrersQ recurrence 4. -/
@[dlmf 14.10.E4]
theorem ferrersQ_recurrence_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersQ ν μ) x=(μ-ν-1)*ferrersQ (ν+1) μ x+(ν+1)*x*ferrersQ ν μ x := by
  sorry

/-- ferrersQ recurrence 5. -/
@[dlmf 14.10.E5]
theorem ferrersQ_recurrence_5 (ν μ : ℂ) (h : LegendreQRegular (ν-1) μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*deriv (ferrersQ ν μ) x=(ν+μ)*ferrersQ (ν-1) μ x-ν*x*ferrersQ ν μ x := by
  sorry

/-- associatedP recurrence 6. -/
@[dlmf 14.10.E6]
theorem associatedP_recurrence_6 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (μ+2) z+2*(μ+1)*z*legendreBranchPower (-1) z*associatedP ν (μ+1) z-(ν-μ)*(ν+μ+1)*associatedP ν μ z=0 := by
  sorry

/-- associatedP recurrence 7. -/
@[dlmf 14.10.E7]
theorem associatedP_recurrence_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    legendreBranchPower 1 z*associatedP ν (μ+1) z-(ν-μ+1)*associatedP (ν+1) μ z+(ν+μ+1)*z*associatedP ν μ z=0 := by
  sorry

/-- associatedP recurrence 3. -/
@[dlmf 14.10.E3]
theorem associatedP_recurrence_3 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν-μ+2)*associatedP (ν+2) μ z-(2*ν+3)*z*associatedP (ν+1) μ z+(ν+μ+1)*associatedP ν μ z=0 := by
  sorry

/-- associatedP recurrence 4. -/
@[dlmf 14.10.E4]
theorem associatedP_recurrence_4 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedP ν μ) z=(μ-ν-1)*associatedP (ν+1) μ z+(ν+1)*z*associatedP ν μ z := by
  sorry

/-- associatedP recurrence 5. -/
@[dlmf 14.10.E5]
theorem associatedP_recurrence_5 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedP ν μ) z=(ν+μ)*associatedP (ν-1) μ z-ν*z*associatedP ν μ z := by
  sorry

/-- associatedQ recurrence 6. -/
@[dlmf 14.10.E6]
theorem associatedQ_recurrence_6 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν (μ+2) z+2*(μ+1)*z*legendreBranchPower (-1) z*associatedQ ν (μ+1) z-(ν-μ)*(ν+μ+1)*associatedQ ν μ z=0 := by
  sorry

/-- associatedQ recurrence 7. -/
@[dlmf 14.10.E7]
theorem associatedQ_recurrence_7 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    legendreBranchPower 1 z*associatedQ ν (μ+1) z-(ν-μ+1)*associatedQ (ν+1) μ z+(ν+μ+1)*z*associatedQ ν μ z=0 := by
  sorry

/-- associatedQ recurrence 3. -/
@[dlmf 14.10.E3]
theorem associatedQ_recurrence_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (ν-μ+2)*associatedQ (ν+2) μ z-(2*ν+3)*z*associatedQ (ν+1) μ z+(ν+μ+1)*associatedQ ν μ z=0 := by
  sorry

/-- associatedQ recurrence 4. -/
@[dlmf 14.10.E4]
theorem associatedQ_recurrence_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedQ ν μ) z=(μ-ν-1)*associatedQ (ν+1) μ z+(ν+1)*z*associatedQ ν μ z := by
  sorry

/-- associatedQ recurrence 5. -/
@[dlmf 14.10.E5]
theorem associatedQ_recurrence_5 (ν μ : ℂ) (h : LegendreQRegular (ν-1) μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2:ℂ)*deriv (associatedQ ν μ) z=(ν+μ)*associatedQ (ν-1) μ z-ν*z*associatedQ ν μ z := by
  sorry

/-- ferrersQ nat order derivative. -/
@[dlmf 14.6.E2, dlmf 14.7.E9]
theorem ferrersQ_nat_order_derivative (ν : ℂ) (m : ℕ) (h : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν m x=(-1)^m*(1-x^2:ℂ)^((m:ℂ)/2)*iteratedDeriv m (ferrersQ ν 0) x := by
  sorry

/-- associatedP nat order derivative. -/
@[dlmf 14.6.E3, dlmf 14.7.E11]
theorem associatedP_nat_order_derivative (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν m z=legendreBranchPower m z*iteratedDeriv m (associatedP ν 0) z := by
  sorry

/-- associatedQ nat order derivative. -/
@[dlmf 14.6.E4, dlmf 14.7.E12]
theorem associatedQ_nat_order_derivative (ν : ℂ) (m : ℕ) (h : LegendreQRegular ν 0) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν m z=legendreBranchPower m z*iteratedDeriv m (associatedQ ν 0) z := by
  sorry

/-- olverQ nat order derivative. -/
@[dlmf 14.6.E5]
theorem olverQ_nat_order_derivative (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    poch (ν+1) m*olverQ ν m z=(-1)^m*legendreBranchPower m z*iteratedDeriv m (olverQ ν 0) z := by
  sorry

end AAR.Legendre
