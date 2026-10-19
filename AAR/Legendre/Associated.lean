/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Ferrers
public import AAR.Legendre.SecondKind
public import AAR.DLMF.Framework

/-!
# Associated Legendre functions and Olver normalization

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- The inherited power of z squared minus one, continued from z greater than one. -/
def legendreBranchPower (μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z-1)+log (z+1)))

/-- associatedP. -/
@[dlmf 14.3.E6]
def associatedP (ν μ z : ℂ) : ℂ :=
  exp (μ/2*(log (z+1)-log (z-1)))*regularizedGaussHG (ν+1) (-ν) (1-μ) ((1-z)/2)

/-- Olver Q is regularized before multiplying by Gamma, so exceptional parameters are retained. -/
@[dlmf 14.3.E10]
def olverQ (ν μ z : ℂ) : ℂ :=
  Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2)

/-- Classical associated Q, defined mathematically when degree plus order is not a negative integer. -/
@[dlmf 14.3.E7]
def associatedQ (ν μ z : ℂ) : ℂ :=
  exp (μ*π*I)*Gamma (ν+μ+1)*olverQ ν μ z

/-- Domain in the parameters of classical Q and Ferrers Q. -/
def LegendreQRegular (ν μ : ℂ) : Prop :=
  ∀ n : ℕ, ν+μ ≠ -(n+1)

/-- ferrersW1. -/
@[dlmf 14.3.E13]
def ferrersW1 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+1)/2)/Gamma ((ν-μ+2)/2)*(1-x^2:ℂ)^(-μ/2)*regularizedGaussHG (-(ν+μ)/2) ((ν-μ+1)/2) (1/2) (x^2)

/-- ferrersW2. -/
@[dlmf 14.3.E14]
def ferrersW2 (ν μ : ℂ) (x : ℝ) : ℂ :=
  2^μ*Gamma ((ν+μ+2)/2)/Gamma ((ν-μ+1)/2)*x*(1-x^2:ℂ)^(-μ/2)*regularizedGaussHG ((1-ν-μ)/2) ((ν-μ+2)/2) (3/2) (x^2)

/-- This representation supplies integer-order limiting values without division by sin of the order. -/
@[dlmf 14.3.E12]
def ferrersQ (ν μ : ℂ) (x : ℝ) : ℂ :=
  -π/2*sin ((ν+μ)*π/2)*ferrersW1 ν μ x+π/2*cos ((ν+μ)*π/2)*ferrersW2 ν μ x

/-- ferrersQ hypergeometric. -/
@[dlmf 14.3.E2]
theorem ferrersQ_hypergeometric {ν μ : ℂ} (h : LegendreQRegular ν μ) (hμ : ∀ n : ℤ, μ ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν μ x = π/(2*sin (μ*π))*(cos (μ*π)*ferrersP ν μ x-Gamma (ν+μ+1)/Gamma (ν-μ+1)*ferrersP ν (-μ) x) := by
  sorry

/-- ferrersQ order limit. -/
@[dlmf 14.3.E2]
theorem ferrersQ_order_limit {ν : ℂ} (m : ℤ) (h : LegendreQRegular ν m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun μ : ℂ => π/(2*sin (μ*π))*(cos (μ*π)*ferrersP ν μ x-Gamma (ν+μ+1)/Gamma (ν-μ+1)*ferrersP ν (-μ) x)) (𝓝[≠] (m:ℂ)) (𝓝 (ferrersQ ν m x)) := by
  sorry

/-- ferrersP w1 w2. -/
@[dlmf 14.3.E11]
theorem ferrersP_w1_w2 {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν μ x=cos ((ν+μ)*π/2)*ferrersW1 ν μ x+sin ((ν+μ)*π/2)*ferrersW2 ν μ x := by
  sorry

/-- olverQ normalization. -/
@[dlmf 14.3.E10]
theorem olverQ_normalization {ν μ : ℂ} (h : LegendreQRegular ν μ) (z : ℂ) :
    olverQ ν μ z = exp (-μ*π*I)*associatedQ ν μ z/Gamma (ν+μ+1) := by
  have hG : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => h n (by linear_combination he))
  simp only [associatedQ, neg_mul, Complex.exp_neg]
  field_simp

/-- Compatibility with the existing degree-only Legendre function. -/
theorem associatedP_zero_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν 0 z=legendreP ν z := by
  have hz' : 1+z ∈ slitPlane := by
    rw [mem_slitPlane_iff] at hz ⊢
    rcases hz with h | h
    · left; simp at h ⊢; linarith
    · right; simpa using h
  simpa [associatedP,legendreP] using
    regularizedGaussHG_symm (ν+1) (-ν) 1 (mem_cutPlane_of_one_add hz')

/-- Compatibility of the totalized degree-only APIs; classical Q additionally requires regular degree. -/
theorem associatedQ_zero_order (ν : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν 0 z=legendreQ ν z := by
  simp only [associatedQ, olverQ, legendreQ, legendreBranchPower, zero_mul, zero_div,
    Complex.exp_zero, mul_one, one_mul, add_zero, cpow_neg]
  ring

/-- associatedP analytic. -/
theorem associatedP_analytic (ν μ : ℂ) :
    AnalyticOnNhd ℂ (associatedP ν μ) {z : ℂ | z-1 ∈ slitPlane} := by
  sorry

/-- Entire parameter dependence on the principal sheet. -/
theorem associatedP_entire_degree (μ : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun ν => associatedP ν μ z) := by
  sorry

/-- Entire parameter dependence on the principal sheet. -/
theorem associatedP_entire_order (ν : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun μ => associatedP ν μ z) := by
  sorry

/-- associatedP ode. -/
@[dlmf 14.2.E2, dlmf 14.21.E1]
theorem associatedP_ode (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*iteratedDeriv 2 (associatedP ν μ) z-2*z*deriv (associatedP ν μ) z+(ν*(ν+1)-μ^2/(1-z^2))*associatedP ν μ z=0 := by
  sorry

/-- associatedP real. -/
theorem associatedP_real (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    (associatedP ν μ x).im=0 := by
  sorry

/-- olverQ analytic. -/
theorem olverQ_analytic (ν μ : ℂ) :
    AnalyticOnNhd ℂ (olverQ ν μ) {z : ℂ | z-1 ∈ slitPlane} := by
  sorry

/-- Entire parameter dependence on the principal sheet. -/
theorem olverQ_entire_degree (μ : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun ν => olverQ ν μ z) := by
  sorry

/-- Entire parameter dependence on the principal sheet. -/
theorem olverQ_entire_order (ν : ℂ) :
    ∀ z : ℂ, z-1 ∈ slitPlane → Differentiable ℂ (fun μ => olverQ ν μ z) := by
  sorry

/-- olverQ ode. -/
@[dlmf 14.2.E2, dlmf 14.21.E1]
theorem olverQ_ode (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    (1-z^2)*iteratedDeriv 2 (olverQ ν μ) z-2*z*deriv (olverQ ν μ) z+(ν*(ν+1)-μ^2/(1-z^2))*olverQ ν μ z=0 := by
  sorry

/-- olverQ real. -/
theorem olverQ_real (ν μ : ℝ) {x : ℝ} (hx : 1 < x) :
    (olverQ ν μ x).im=0 := by
  sorry

/-- ferrersQ ode. -/
@[dlmf 14.2.E2]
theorem ferrersQ_ode {ν μ : ℂ} (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*iteratedDeriv 2 (ferrersQ ν μ) x-2*x*deriv (ferrersQ ν μ) x+(ν*(ν+1)-μ^2/(1-x^2:ℂ))*ferrersQ ν μ x=0 := by
  sorry

/-- ferrersP real. -/
theorem ferrersP_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP ν μ x).im=0 := by
  sorry

/-- ferrersQ real. -/
theorem ferrersQ_real (ν μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (h : LegendreQRegular ν μ) :
    (ferrersQ ν μ x).im=0 := by
  sorry

/-- ferrersP conical real. -/
theorem ferrersP_conical_real (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (ferrersP (-1/2+I*τ) μ x).im=0 := by
  sorry

/-- Complex Wronskian. -/
def LegendreWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z*deriv g z-g z*deriv f z

/-- Real-argument complex-valued Wronskian. -/
def ferrersWronskian (f g : ℝ → ℂ) (x : ℝ) : ℂ :=
  f x*deriv g x-g x*deriv f x

/-- ferrers wronskian 3. -/
@[dlmf 14.2.E3]
theorem ferrers_wronskian_3 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (fun x => ferrersP ν (-μ) (-x)) x=2/(Gamma (μ-ν)*Gamma (ν+μ+1)*(1-x^2:ℂ)) := by
  sorry

/-- ferrers wronskian 4. -/
@[dlmf 14.2.E4]
theorem ferrers_wronskian_4 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν μ) (ferrersQ ν μ) x=Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(1-x^2:ℂ)) := by
  sorry

/-- ferrers wronskian 5. -/
@[dlmf 14.2.E5]
theorem ferrers_wronskian_5 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (ν+1) μ x*ferrersQ ν μ x-ferrersP ν μ x*ferrersQ (ν+1) μ x=Gamma (ν+μ+1)/Gamma (ν-μ+2) := by
  sorry

/-- ferrers wronskian 6. -/
@[dlmf 14.2.E6]
theorem ferrers_wronskian_6 (ν μ : ℂ) (h : LegendreQRegular ν μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersQ ν μ) x=cos (μ*π)/(1-x^2:ℂ) := by
  sorry

/-- ferrers wronskian 7. -/
@[dlmf 14.2.E7]
theorem ferrers_wronskian_7 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (ferrersP ν (-μ)) (ferrersP ν μ) x=2*sin (μ*π)/(π*(1-x^2:ℂ)) := by
  sorry

/-- associated wronskian 7. -/
@[dlmf 14.2.E7]
theorem associated_wronskian_7 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν (-μ)) (associatedP ν μ) z=2*sin (μ*π)/(π*(1-z^2)) := by
  sorry

/-- associated wronskian 8. -/
@[dlmf 14.2.E8]
theorem associated_wronskian_8 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν (-μ)) (olverQ ν μ) z=-1/(Gamma (ν+μ+1)*(z^2-1)) := by
  sorry

/-- associated wronskian 9. -/
@[dlmf 14.2.E9]
theorem associated_wronskian_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (olverQ ν μ) (olverQ (-ν-1) μ) z=cos (ν*π)/(z^2-1) := by
  sorry

/-- associated wronskian 10. -/
@[dlmf 14.2.E10]
theorem associated_wronskian_10 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    LegendreWronskian (associatedP ν μ) (associatedQ ν μ) z=-exp (μ*π*I)*Gamma (ν+μ+1)/(Gamma (ν-μ+1)*(z^2-1)) := by
  sorry

/-- associated wronskian 11. -/
@[dlmf 14.2.E11]
theorem associated_wronskian_11 (ν μ : ℂ) (h : LegendreQRegular ν μ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (ν+1) μ z*associatedQ ν μ z-associatedP ν μ z*associatedQ (ν+1) μ z=exp (μ*π*I)*Gamma (ν+μ+1)/Gamma (ν-μ+2) := by
  sorry

/-- IsGeneralizedLegendreSolution. -/
@[dlmf 14.29.E1]
def IsGeneralizedLegendreSolution (ν μ₁ μ₂ : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ₁^2/(2*(1-z))-μ₂^2/(2*(1+z)))*f z=0

/-- generalizedLegendre equal orders. -/
@[dlmf 14.29.E1]
theorem generalizedLegendre_equal_orders (ν μ : ℂ) (f : ℂ → ℂ) {z : ℂ} (hz : z ≠ 1) (hzm : z ≠ -1) :
    IsGeneralizedLegendreSolution ν μ μ f z ↔ (1-z^2)*iteratedDeriv 2 f z-2*z*deriv f z+(ν*(ν+1)-μ^2/(1-z^2))*f z=0 := by
  unfold IsGeneralizedLegendreSolution
  have h1 : 1-z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h2 : 1+z ≠ 0 := by intro h; apply hzm; linear_combination h
  have he : μ^2/(2*(1-z))+μ^2/(2*(1+z))=μ^2/(1-z^2) := by
    have h3 : 1-z^2=(1-z)*(1+z) := by ring
    rw [h3]
    field_simp
    ring
  have heq : ν*(ν+1)-μ^2/(2*(1-z))-μ^2/(2*(1+z))=ν*(ν+1)-μ^2/(1-z^2) := by
    linear_combination -he
  rw [heq]

end AAR.Legendre
