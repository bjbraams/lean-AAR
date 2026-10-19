/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated
public import AAR.Elliptic.Complete

/-!
# Associated Legendre and Ferrers special values

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrersP zero 1. -/
@[dlmf 14.5.E1]
theorem ferrersP_zero_1 (ν μ : ℂ) :
    ferrersP ν μ 0=2^μ*Real.sqrt π/(Gamma ((ν-μ)/2+1)*Gamma ((1-ν-μ)/2)) := by
  sorry

/-- ferrersP zero 2. -/
@[dlmf 14.5.E2]
theorem ferrersP_zero_2 (ν μ : ℂ) :
    HasDerivAt (ferrersP ν μ) (-2^(μ+1)*Real.sqrt π/(Gamma ((ν-μ+1)/2)*Gamma (-(ν+μ)/2))) 0 := by
  sorry

/-- ferrersQ zero 3. -/
@[dlmf 14.5.E3]
theorem ferrersQ_zero_3 (ν μ : ℂ) (h : LegendreQRegular ν μ) :
    ferrersQ ν μ 0=-2^(μ-1)*Real.sqrt π*sin ((ν+μ)*π/2)*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ)/2+1) := by
  sorry

/-- ferrersQ zero 4. -/
@[dlmf 14.5.E4]
theorem ferrersQ_zero_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) :
    HasDerivAt (ferrersQ ν μ) (2^μ*Real.sqrt π*cos ((ν+μ)*π/2)*Gamma ((ν+μ)/2+1)/Gamma ((ν-μ+1)/2)) 0 := by
  sorry

/-- ferrersP degree 0. -/
@[dlmf 14.5.E5]
theorem ferrersP_degree_0 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 0 0 x=1 := by
  sorry

/-- ferrersP degree 1. -/
@[dlmf 14.5.E6]
theorem ferrersP_degree_1 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 1 0 x=x := by
  sorry

/-- ferrersP degree 2. -/
@[dlmf 14.5.E28]
theorem ferrersP_degree_2 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP 2 0 x=(3*x^2-1)/2 := by
  sorry

/-- associatedP degree 0. -/
@[dlmf 14.5.E5]
theorem associatedP_degree_0 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 0 0 z=1 := by
  sorry

/-- associatedP degree 1. -/
@[dlmf 14.5.E6]
theorem associatedP_degree_1 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 1 0 z=z := by
  sorry

/-- associatedP degree 2. -/
@[dlmf 14.5.E28]
theorem associatedP_degree_2 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP 2 0 z=(3*z^2-1)/2 := by
  sorry

/-- ferrersQ degree 0. -/
@[dlmf 14.5.E7]
theorem ferrersQ_degree_0 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 0 0 x=1/2*log ((1+x)/(1-x):ℂ) := by
  sorry

/-- ferrersQ degree 1. -/
@[dlmf 14.5.E8]
theorem ferrersQ_degree_1 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 1 0 x=x/2*log ((1+x)/(1-x):ℂ)-1 := by
  sorry

/-- ferrersQ degree 2. -/
@[dlmf 14.5.E29]
theorem ferrersQ_degree_2 {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ 2 0 x=(3*x^2-1:ℂ)/4*log ((1+x)/(1-x):ℂ)-3*x/2 := by
  sorry

/-- olverQ degree 0. -/
@[dlmf 14.5.E9]
theorem olverQ_degree_0 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 0 0 z=1/2*(log (z+1)-log (z-1)) := by
  sorry

/-- olverQ degree 1. -/
@[dlmf 14.5.E10]
theorem olverQ_degree_1 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 1 0 z=z/2*(log (z+1)-log (z-1))-1 := by
  sorry

/-- olverQ degree 2. -/
@[dlmf 14.5.E30]
theorem olverQ_degree_2 {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ 2 0 z=(3*z^2-1)/8*(log (z+1)-log (z-1))-3*z/4 := by
  sorry

/-- ferrersP half order 11. -/
@[dlmf 14.5.E11]
theorem ferrersP_half_order_11 (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (1/2) (Real.cos θ)=(2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*cos ((ν+1/2)*θ)/(1) := by
  sorry

/-- ferrersP half order 12. -/
@[dlmf 14.5.E12]
theorem ferrersP_half_order_12 (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (-1/2) (Real.cos θ)=if ν=-1/2 then (2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*θ else (2/(π*Real.sin θ):ℂ)^(1/2:ℂ)*sin ((ν+1/2)*θ)/(ν+1/2) := by
  sorry

/-- ferrersQ half order 13. -/
@[dlmf 14.5.E13]
theorem ferrersQ_half_order_13 (ν : ℂ) (h : LegendreQRegular ν (1/2)) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ ν (1/2) (Real.cos θ)=-(π/(2*Real.sin θ):ℂ)^(1/2:ℂ)*sin ((ν+1/2)*θ)/(1) := by
  sorry

/-- ferrersQ half order 14. -/
@[dlmf 14.5.E14]
theorem ferrersQ_half_order_14 (ν : ℂ) (h : LegendreQRegular ν (-1/2)) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ ν (-1/2) (Real.cos θ)=(π/(2*Real.sin θ):ℂ)^(1/2:ℂ)*cos ((ν+1/2)*θ)/(ν+1/2) := by
  sorry

/-- associatedP half order 15. -/
@[dlmf 14.5.E15]
theorem associatedP_half_order_15 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP ν (1/2) (Real.cosh ξ)=(2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*cosh ((ν+1/2)*ξ) := by
  sorry

/-- associatedP half order 16. -/
@[dlmf 14.5.E16]
theorem associatedP_half_order_16 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP ν (-1/2) (Real.cosh ξ)=if ν=-1/2 then (2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*ξ else (2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*sinh ((ν+1/2)*ξ)/(ν+1/2) := by
  sorry

/-- olverQ half order 1. -/
@[dlmf 14.5.E17]
theorem olverQ_half_order_1 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ ν (1/2) (Real.cosh ξ)=(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*exp (-(ν+1/2)*ξ)/Gamma (ν+3/2) := by
  sorry

/-- olverQ half order 2. -/
@[dlmf 14.5.E17]
theorem olverQ_half_order_2 (ν : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ ν (-1/2) (Real.cosh ξ)=(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*exp (-(ν+1/2)*ξ)/Gamma (ν+3/2) := by
  sorry

/-- ferrersP negative degree order. -/
@[dlmf 14.5.E18]
theorem ferrersP_negative_degree_order (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν (-ν) (Real.cos θ)=(Real.sin θ:ℂ)^ν/(2^ν*Gamma (ν+1)) := by
  sorry

/-- associatedP negative degree order. -/
@[dlmf 14.5.E19]
theorem associatedP_negative_degree_order (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) :
    associatedP ν (-ν) (Real.cosh θ)=(Real.sinh θ:ℂ)^ν/(2^ν*Gamma (ν+1)) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E20]
theorem legendre_elliptic_20 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP (1/2) 0 (Real.cos θ)=2/π*(2*(AAR.Elliptic.Real.compEllIntEm ((Real.sin (θ/2))^2):ℂ)-(AAR.Elliptic.Real.compEllIntKm ((Real.sin (θ/2))^2):ℂ)) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E21]
theorem legendre_elliptic_21 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP (-1/2) 0 (Real.cos θ)=2/π*(AAR.Elliptic.Real.compEllIntKm ((Real.sin (θ/2))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E22]
theorem legendre_elliptic_22 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ (1/2) 0 (Real.cos θ)=(AAR.Elliptic.Real.compEllIntKm ((Real.cos (θ/2))^2):ℂ)-2*(AAR.Elliptic.Real.compEllIntEm ((Real.cos (θ/2))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E23]
theorem legendre_elliptic_23 {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersQ (-1/2) 0 (Real.cos θ)=(AAR.Elliptic.Real.compEllIntKm ((Real.cos (θ/2))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E24]
theorem legendre_elliptic_24 {θ : ℝ} (h0 : 0 < θ) :
    associatedP (1/2) 0 (Real.cosh θ)=2/π*Real.exp (θ/2)*(AAR.Elliptic.Real.compEllIntEm ((Real.sqrt (1-Real.exp (-2*θ)))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E25]
theorem legendre_elliptic_25 {θ : ℝ} (h0 : 0 < θ) :
    associatedP (-1/2) 0 (Real.cosh θ)=2/(π*Real.cosh (θ/2))*(AAR.Elliptic.Real.compEllIntKm ((Real.tanh (θ/2))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E26]
theorem legendre_elliptic_26 {θ : ℝ} (h0 : 0 < θ) :
    olverQ (1/2) 0 (Real.cosh θ)=2/Real.sqrt π*Real.cosh θ/Real.cosh (θ/2)*(AAR.Elliptic.Real.compEllIntKm ((1/Real.cosh (θ/2))^2):ℂ)-4/Real.sqrt π*Real.cosh (θ/2)*(AAR.Elliptic.Real.compEllIntEm ((1/Real.cosh (θ/2))^2):ℂ) := by
  sorry

/-- Complete elliptic integrals use parameter equal to the square of DLMF modulus. -/
@[dlmf 14.5.E27]
theorem legendre_elliptic_27 {θ : ℝ} (h0 : 0 < θ) :
    olverQ (-1/2) 0 (Real.cosh θ)=2/Real.sqrt π*Real.exp (-θ/2)*(AAR.Elliptic.Real.compEllIntKm ((Real.exp (-θ))^2):ℂ) := by
  sorry

end AAR.Legendre
