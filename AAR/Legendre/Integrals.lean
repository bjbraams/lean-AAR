/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.IntegralRepresentations

/-!
# Definite integrals, orthogonality and primitive formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrers barnes integral. -/
@[dlmf 14.17.E5]
theorem ferrers_barnes_integral {σ μ : ℂ} (hσ : -1 < σ.re) (hμ : -1 < μ.re) (ν : ℂ) :
    (∫ x : ℝ in 0..1, (x:ℂ)^σ*(1-x^2:ℂ)^(μ/2)*ferrersP ν (-μ) x)=Gamma ((σ+1)/2)*Gamma (σ/2+1)/(2^(μ+1)*Gamma ((σ-ν+μ)/2+1)*Gamma ((σ+ν+μ+3)/2)) := by
  sorry

/-- ferrers orthogonality 6. -/
@[dlmf 14.17.E6]
theorem ferrers_orthogonality_6 (l m n : ℕ) (hl : m ≤ l) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (m) x=if l=n then ((n+m).factorial:ℂ)/((n-m).factorial*(n+1/2:ℂ)) else 0 := by
  sorry

/-- ferrers orthogonality 7. -/
@[dlmf 14.17.E7]
theorem ferrers_orthogonality_7 (l m n : ℕ) (hl : m ≤ l) (hn : m ≤ n) :
    ∫ x : ℝ in -1..1, 1*ferrersP l (m) x*ferrersP n (-m) x=if l=n then (-1)^m/(l+1/2:ℂ) else 0 := by
  sorry

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain their integrability conditions. -/
@[dlmf 14.17.E8]
theorem ferrers_orthogonality_8 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < m) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (m) x=if l=m then ((n+m).factorial:ℂ)/((n-m).factorial*m) else 0 := by
  sorry

/-- Nonzero polynomial degrees and integrability are explicit; singular-weight integrals retain their integrability conditions. -/
@[dlmf 14.17.E9]
theorem ferrers_orthogonality_9 (l m n : ℕ) (hl : l ≤ n) (hm : m ≤ n) (hp : 0 < l) :
    ∫ x : ℝ in -1..1, 1/(1-x^2:ℂ)*ferrersP n (l) x*ferrersP n (-m) x=if l=m then (-1)^l/(l:ℂ) else 0 := by
  sorry

/-- ferrers product integral 10. -/
@[dlmf 14.17.E10]
theorem ferrers_product_integral_10 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*sin (ν*π)*sin (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  sorry

/-- ferrers product integral 11. -/
@[dlmf 14.17.E11]
theorem ferrers_product_integral_11 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*(sin (ν*π))^2*deriv digamma (ν+1))/(π^2*(ν+1/2)) := by
  sorry

/-- ferrers product integral 12. -/
@[dlmf 14.17.E12]
theorem ferrers_product_integral_12 (ν : ℂ) (lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    (∫ x : ℝ in -1..1, ferrersQ ν 0 x*ferrersQ lam 0 x)=((digamma (ν+1)-digamma (lam+1))*(1+cos (ν*π)*cos (lam*π))+π/2*sin ((lam-ν)*π))/((lam-ν)*(lam+ν+1)) := by
  sorry

/-- ferrers product integral 13. -/
@[dlmf 14.17.E13]
theorem ferrers_product_integral_13 (ν : ℂ) (hν : ν ≠ -1/2) (hr : LegendreQRegular ν 0) :
    (∫ x : ℝ in -1..1, (ferrersQ ν 0 x)^2)=(π^2-2*(1+(cos (ν*π))^2)*deriv digamma (ν+1))/(2*(2*ν+1)) := by
  sorry

/-- ferrers product integral 14. -/
@[dlmf 14.17.E14]
theorem ferrers_product_integral_14 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : 0 < lam.re) (hne : lam ≠ ν) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ lam 0 x)=(2*sin (ν*π)*cos (lam*π)*(digamma (ν+1)-digamma (lam+1))+π*cos ((lam-ν)*π)-π)/(π*(lam-ν)*(lam+ν+1)) := by
  sorry

/-- ferrers product integral 15. -/
@[dlmf 14.17.E15]
theorem ferrers_product_integral_15 (ν : ℂ) (hν : 0 < ν.re) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersQ ν 0 x)=-sin (2*ν*π)*deriv digamma (ν+1)/(π*(2*ν+1)) := by
  sorry

/-- ferrersPQ nat integral. -/
@[dlmf 14.17.E16]
theorem ferrersPQ_nat_integral (l m n : ℕ) (h : l ≠ n) (hl : m ≤ l) :
    (∫ x : ℝ in -1..1, ferrersP l m x*ferrersQ n m x)=(1-(-1)^(l+n))*((l+m).factorial:ℂ)/(((l:ℂ)-n)*(l+n+1:ℂ)*(l-m).factorial) := by
  sorry

/-- ferrers triple integral. -/
@[dlmf 14.17.E17]
theorem ferrers_triple_integral (l m n : ℕ) (hl : 0 < l) (hm : 0 < m) (hn : 0 < n) (htri : (|((m:ℤ)-n)| < l ∧ l < m+n) ∨ Even (l+m+n)) :
    (∫ θ : ℝ in 0..π, ferrersQ l 0 (Real.cos θ)*ferrersP m 0 (Real.cos θ)*ferrersP n 0 (Real.cos θ)*Real.sin θ)=0 := by
  sorry

/-- legendre product integral 18. -/
@[dlmf 14.17.E18]
theorem legendre_product_integral_18 (ν : ℂ) (lam : ℂ) (hν : 0 < ν.re) (hlam : ν.re < lam.re) :
    HasIntegralAtTop (fun x : ℝ => associatedP ν 0 x*associatedQ lam 0 x) 1 (1/((lam-ν)*(ν+lam+1))) := by
  sorry

/-- legendre product integral 19. -/
@[dlmf 14.17.E19]
theorem legendre_product_integral_19 (ν : ℂ) (lam : ℂ) (h : -1 < (lam+ν).re) (hne : lam ≠ ν) (hν : LegendreQRegular ν 0) (hlam : LegendreQRegular lam 0) :
    HasIntegralAtTop (fun x : ℝ => associatedQ ν 0 x*associatedQ lam 0 x) 1 ((digamma (lam+1)-digamma (ν+1))/((lam-ν)*(lam+ν+1))) := by
  sorry

/-- legendre product integral 20. -/
@[dlmf 14.17.E20]
theorem legendre_product_integral_20 (ν : ℂ) (hν : -1/2 < ν.re) :
    HasIntegralAtTop (fun x : ℝ => (associatedQ ν 0 x)^2) 1 (deriv digamma (ν+1)/(2*ν+1)) := by
  sorry

end AAR.Legendre
