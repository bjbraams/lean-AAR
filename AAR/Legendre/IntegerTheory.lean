/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.AssociatedRecurrences
public import AAR.Legendre.Integer
public import AAR.OrthogonalPolynomials.Classical

/-!
# Integer degrees and orders and Rodrigues formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/- DLMF 14.7.13: Mathlib `Polynomial.factorial_mul_shiftedLegendre_eq`
is Rodrigues’ formula for P_n(1-2x). The affine normalization is already
proved locally by `AAR.OrthogonalPolynomials.aeval_shiftedLegendre_eq_legendrePolyP`.
The upstream Rodrigues proof is not duplicated here. -/

/-- ferrersP nat polynomial. -/
@[dlmf 14.7.E1]
theorem ferrersP_nat_polynomial (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n 0 x=AAR.OrthogonalPolynomials.legendrePolyP n x := by
  rw [ferrersP_zero _ hx.1,legendreP_nat]
  left
  simp
  linarith [hx.1]

/-- ferrersP nat order rodrigues. -/
@[dlmf 14.7.E8, dlmf 14.7.E10]
theorem ferrersP_nat_order_rodrigues (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m x=(-1)^(m+n)*(1-x^2:ℂ)^((m:ℂ)/2)/(2^n*(n.factorial:ℂ))*iteratedDeriv (m+n) (fun x : ℝ => (1-x^2:ℂ)^n) x := by
  sorry

/-- associatedP nat order rodrigues. -/
@[dlmf 14.7.E14]
theorem associatedP_nat_order_rodrigues (n m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP n m z=legendreBranchPower m z/(2^n*(n.factorial:ℂ))*iteratedDeriv (m+n) (fun z : ℂ => (z^2-1)^n) z := by
  sorry

/-- associatedP equal nat order. -/
@[dlmf 14.7.E15]
theorem associatedP_equal_nat_order (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP m m z=((2*m).factorial:ℂ)/(2^m*(m.factorial:ℂ))*legendreBranchPower m z := by
  sorry

/-- ferrersP order gt degree. -/
@[dlmf 14.7.E16]
theorem ferrersP_order_gt_degree (n m : ℕ) (h : n < m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m x=0 := by
  sorry

/-- associatedP order gt degree. -/
@[dlmf 14.7.E16]
theorem associatedP_order_gt_degree (n m : ℕ) (h : n < m) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP n m z=0 := by
  sorry

/-- ferrersP nat reflection. -/
@[dlmf 14.7.E17]
theorem ferrersP_nat_reflection (n m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP n m (-x)=(-1)^(n+m)*ferrersP n m x := by
  sorry

/-- ferrersQ nat reflection 1. -/
@[dlmf 14.7.E18]
theorem ferrersQ_nat_reflection_1 (n m : ℕ) (h : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n (1*m) (-x)=(-1)^(n+m+1)*ferrersQ n (1*m) x := by
  sorry

/-- ferrersQ nat reflection 2. -/
@[dlmf 14.7.E18]
theorem ferrersQ_nat_reflection_2 (n m : ℕ) (h : m ≤ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n (-1*m) (-x)=(-1)^(n+m+1)*ferrersQ n (-1*m) x := by
  sorry

end AAR.Legendre
