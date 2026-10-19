/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Lommel
public import AAR.Struve.Representations
public import AAR.ErrorFunctions.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Anger and Weber functions: entire definitions and identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel AAR.Confluent

/-- angerJ. -/
@[dlmf 11.10.E1]
def angerJ (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, cos (ν*θ-z*Real.sin θ)

/-- Entire dependence on the argument. -/
theorem angerJ_entire (ν : ℂ) :
    Differentiable ℂ (angerJ ν) := by
  sorry

/-- Entire dependence on the order. -/
theorem angerJ_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => angerJ ν z) := by
  sorry

/-- weberE. -/
@[dlmf 11.10.E2]
def weberE (ν z : ℂ) : ℂ :=
  1/π*∫ θ : ℝ in 0..π, sin (ν*θ-z*Real.sin θ)

/-- Entire dependence on the argument. -/
theorem weberE_entire (ν : ℂ) :
    Differentiable ℂ (weberE ν) := by
  sorry

/-- Entire dependence on the order. -/
theorem weberE_entire_order (z : ℂ) :
    Differentiable ℂ (fun ν => weberE ν z) := by
  sorry

/-- Associated Anger–Weber function at nonintegral order. -/
def angerARegular (ν z : ℂ) : ℂ :=
  (angerJ ν z-besselJ ν z)/sin (π*ν)

/-- Continuation in order supplies removable values at integral orders. -/
@[dlmf 11.10.E4]
def angerA (ν z : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun n => angerARegular n z)

/-- angerA regular. -/
theorem angerA_regular {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerA ν z = angerARegular ν z := by
  sorry

/-- angerA order limit. -/
theorem angerA_order_limit (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun n => angerARegular n z) (𝓝[≠] ν) (𝓝 (angerA ν z)) := by
  sorry

/-- angerA integral. -/
@[dlmf 11.10.E4]
theorem angerA_integral (ν : ℂ) {z : ℂ} (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-ν*t-z*Real.sinh t)/π) 0 (angerA ν z) := by
  sorry

/-- Boundary extension of the defining integral. -/
theorem angerA_boundary_integral {ν z : ℂ} (hν : 0 < ν.re) (hz : z.re = 0) (hz0 : z ≠ 0) :
    HasIntegralAtTop (fun t : ℝ => exp (-ν*t-z*Real.sinh t)/π) 0 (angerA ν z) := by
  sorry

/-- angerJ double integral. -/
@[dlmf 11.10.E3]
theorem angerJ_double_integral (ν z : ℂ) :
    (1/π*∫ θ : ℝ in 0..2*π, cos (ν*θ-z*Real.sin θ)) = (1+cos (2*π*ν))*angerJ ν z+sin (2*π*ν)*weberE ν z := by
  sorry

/-- angerJ ode. -/
@[dlmf 11.10.E5, dlmf 11.10.E6]
theorem angerJ_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (angerJ ν) z+deriv (angerJ ν) z/z+(1-ν^2/z^2)*angerJ ν z = (z-ν)/(π*z^2)*sin (π*ν) := by
  sorry

/-- weberE ode. -/
@[dlmf 11.10.E5, dlmf 11.10.E7]
theorem weberE_ode (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    iteratedDeriv 2 (weberE ν) z+deriv (weberE ν) z/z+(1-ν^2/z^2)*weberE ν z = -(z+ν+(z-ν)*cos (π*ν))/(π*z^2) := by
  sorry

/-- angerS1. -/
@[dlmf 11.10.E10]
def angerS1 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))

/-- hasSum angerS1. -/
@[dlmf 11.10.E10]
theorem hasSum_angerS1 (ν z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k)/(Gamma (k+ν/2+1)*Gamma (k-ν/2+1))) (angerS1 ν z) := by
  sorry

/-- angerS2. -/
@[dlmf 11.10.E11]
def angerS2 (ν z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma (k-ν/2+3/2))

/-- hasSum angerS2. -/
@[dlmf 11.10.E11]
theorem hasSum_angerS2 (ν z : ℂ) :
    HasSum (fun k : ℕ => (-1)^k*(z/2)^(2*k+1)/(Gamma (k+ν/2+3/2)*Gamma (k-ν/2+3/2))) (angerS2 ν z) := by
  sorry

/-- angerJ series. -/
@[dlmf 11.10.E8]
theorem angerJ_series (ν z : ℂ) :
    angerJ ν z = cos (π*ν/2)*angerS1 ν z+sin (π*ν/2)*angerS2 ν z := by
  sorry

/-- weberE series. -/
@[dlmf 11.10.E9]
theorem weberE_series (ν z : ℂ) :
    weberE ν z = sin (π*ν/2)*angerS1 ν z-cos (π*ν/2)*angerS2 ν z := by
  sorry

/-- angerJ neg. -/
@[dlmf 11.10.E12]
theorem angerJ_neg (ν z : ℂ) :
    angerJ ν (-z) = angerJ (-ν) z := by
  unfold angerJ
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, cos_neg]

/-- weberE neg. -/
@[dlmf 11.10.E12]
theorem weberE_neg (ν z : ℂ) :
    weberE ν (-z) = -weberE (-ν) z := by
  unfold weberE
  rw [← mul_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ hθ
  dsimp only
  rw [show (-ν)*(θ:ℂ)-z*Real.sin θ=-(ν*θ-(-z)*Real.sin θ) by ring, sin_neg, neg_neg]

/-- anger weber. -/
@[dlmf 11.10.E13]
theorem anger_weber (ν z : ℂ) :
    sin (π*ν)*angerJ ν z = cos (π*ν)*weberE ν z-weberE (-ν) z := by
  sorry

/-- weber anger. -/
@[dlmf 11.10.E14]
theorem weber_anger (ν z : ℂ) :
    sin (π*ν)*weberE ν z = angerJ (-ν) z-cos (π*ν)*angerJ ν z := by
  sorry

/-- anger bessel. -/
@[dlmf 11.10.E15]
theorem anger_bessel (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ ν z = besselJ ν z+sin (π*ν)*angerA ν z := by
  sorry

/-- weber bessel. -/
@[dlmf 11.10.E16]
theorem weber_bessel (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ν z = -besselY ν z-cos (π*ν)*angerA ν z-angerA (-ν) z := by
  sorry

/-- angerJ lommel. -/
@[dlmf 11.10.E17]
theorem angerJ_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ ν z = sin (π*ν)/π*(lommelS 0 ν z-ν*lommelS (-1) ν z) := by
  sorry

/-- weberE lommel. -/
@[dlmf 11.10.E18]
theorem weberE_lommel {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE ν z = -(1+cos (π*ν))/π*lommelS 0 ν z-ν/π*(1-cos (π*ν))*lommelS (-1) ν z := by
  sorry

/-- angerFresnelPlus. -/
@[dlmf 11.10.E21]
def angerFresnelPlus (z : ℂ) : ℂ :=
  fresnelCosInt z+fresnelSinInt z

/-- angerFresnelMinus. -/
@[dlmf 11.10.E21]
def angerFresnelMinus (z : ℂ) : ℂ :=
  fresnelCosInt z-fresnelSinInt z

/-- angerJ half 19. -/
@[dlmf 11.10.E19]
theorem angerJ_half_19 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (-1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*cos z-angerFresnelMinus ((2*z/π)^(1/2:ℂ))*sin z) := by
  sorry

/-- angerJ half 20. -/
@[dlmf 11.10.E20]
theorem angerJ_half_20 {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ (1/2) z = (π*z/2)^(-1/2:ℂ)*(angerFresnelPlus ((2*z/π)^(1/2:ℂ))*sin z+angerFresnelMinus ((2*z/π)^(1/2:ℂ))*cos z) := by
  sorry

/-- anger weber half. -/
@[dlmf 11.10.E19, dlmf 11.10.E20]
theorem anger_weber_half (z : ℂ) :
    angerJ (-1/2) z = weberE (1/2) z ∧ angerJ (1/2) z = -weberE (-1/2) z := by
  sorry

/-- Number of terms floor((n-1)/2)+1, with empty case n=0. -/
@[dlmf 11.10.E24]
def weberM1 (n : ℕ) : ℕ :=
  n/2

/-- Number of terms ceil((n-3)/2)+1 for n positive. -/
@[dlmf 11.10.E24]
def weberM2 (n : ℕ) : ℕ :=
  n/2

/-- weberE nat. -/
@[dlmf 11.10.E22]
theorem weberE_nat (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE n z = -struveH n z+1/π*∑ k ∈ Finset.range (weberM1 n), Gamma (k+1/2)/Gamma (n+1/2-k)*(z/2)^((n:ℤ)-2*k-1) := by
  sorry

/-- weberE neg nat. -/
@[dlmf 11.10.E23]
theorem weberE_neg_nat (n : ℕ) (hn : 0 < n) {z : ℂ} (hz : z ∈ slitPlane) :
    weberE (-n) z = -struveH (-n) z+(-1)^(n+1)/π*∑ k ∈ Finset.range (weberM2 n), Gamma (n-k-1/2)/Gamma (k+3/2)*(z/2)^(-(n:ℤ)+2*k+1) := by
  sorry

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem angerJ_zero (ν : ℂ) :
    angerJ ν 0 = if ν=0 then 1 else sin (π*ν)/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [angerJ]
  · rw [if_neg hν]
    unfold angerJ
    simp only [zero_mul, sub_zero]
    rw [integral_cos_mul_complex hν]
    try simp only [Complex.ofReal_zero, mul_zero, sin_zero, zero_div, sub_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- Special value with the removable order-zero value retained. -/
@[dlmf 11.10.E25]
theorem weberE_zero (ν : ℂ) :
    weberE ν 0 = if ν=0 then 0 else (1-cos (π*ν))/(π*ν) := by
  by_cases hν : ν=0
  · subst ν
    simp [weberE]
  · rw [if_neg hν]
    have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -cos (ν*t)/ν) (sin (ν*t)) t := by
      have hh := (((Complex.hasDerivAt_cos (ν*t)).comp (t:ℂ)
        ((hasDerivAt_id (t:ℂ)).const_mul ν)).neg.div_const ν).comp_ofReal
      convert hh using 1
      · funext x; simp only [Function.comp_apply, Pi.neg_apply]
      · field_simp
    have hi:=intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
      ((by fun_prop : Continuous (fun t : ℝ => sin (ν*t))).intervalIntegrable 0 π)
    unfold weberE
    simp only [zero_mul,sub_zero]
    rw [hi]
    simp only [Complex.ofReal_zero, mul_zero, cos_zero]
    rw [mul_comm ν (π:ℂ)]
    ring

/-- weberE zero order. -/
@[dlmf 11.10.E26]
theorem weberE_zero_order (z : ℂ) :
    weberE 0 z = -struveH 0 z := by
  sorry

/-- weberE one order. -/
@[dlmf 11.10.E26]
theorem weberE_one_order (z : ℂ) :
    weberE 1 z = 2/π-struveH 1 z := by
  sorry

/-- angerJ order deriv zero. -/
@[dlmf 11.10.E27]
theorem angerJ_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => angerJ ν z) (π/2*struveH 0 z) 0 := by
  sorry

/-- weberE order deriv zero. -/
@[dlmf 11.10.E28]
theorem weberE_order_deriv_zero (z : ℂ) :
    HasDerivAt (fun ν => weberE ν z) (π/2*besselJ 0 z) 0 := by
  sorry

/-- angerJ int. -/
@[dlmf 11.10.E29]
theorem angerJ_int (n : ℤ) {z : ℂ} (hz : z ∈ slitPlane) :
    angerJ n z = besselJ n z := by
  sorry

/-- angerJ bessel products. -/
@[dlmf 11.10.E30]
theorem angerJ_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*sin (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*cos (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (angerJ ν z) := by
  sorry

/-- weberE bessel products. -/
@[dlmf 11.10.E31]
theorem weberE_bessel_products (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => -2*cos (ν*π/2)*(-1)^k*besselJ (k-ν/2+1/2) (z/2)*besselJ (k+ν/2+1/2) (z/2)+2*sin (ν*π/2)*(if k=0 then 1/2 else 1)*(-1)^k*besselJ (k-ν/2) (z/2)*besselJ (k+ν/2) (z/2)) (weberE ν z) := by
  sorry

/-- angerJ recurrence. -/
@[dlmf 11.10.E32]
theorem angerJ_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    angerJ (ν-1) z+angerJ (ν+1) z = 2*ν/z*angerJ ν z-2/(π*z)*(sin (π*ν)) := by
  sorry

/-- angerJ deriv. -/
@[dlmf 11.10.E34]
theorem angerJ_deriv (ν z : ℂ) :
    HasDerivAt (angerJ ν) ((angerJ (ν-1) z-angerJ (ν+1) z)/2) z := by
  sorry

/-- angerJ weighted deriv add. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_add (ν z : ℂ) :
    z*deriv (angerJ ν) z+(1:ℂ)*ν*angerJ ν z = (1:ℂ)*z*angerJ (ν-1) z+(1:ℂ)*(sin (π*ν))/π := by
  sorry

/-- angerJ weighted deriv sub. -/
@[dlmf 11.10.E36]
theorem angerJ_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (angerJ ν) z+(-1:ℂ)*ν*angerJ ν z = (-1:ℂ)*z*angerJ (ν-(-1)) z+(-1:ℂ)*(sin (π*ν))/π := by
  sorry

/-- weberE recurrence. -/
@[dlmf 11.10.E33]
theorem weberE_recurrence (ν : ℂ) {z : ℂ} (hz : z ≠ 0) :
    weberE (ν-1) z+weberE (ν+1) z = 2*ν/z*weberE ν z-2/(π*z)*(1-cos (π*ν)) := by
  sorry

/-- weberE deriv. -/
@[dlmf 11.10.E35]
theorem weberE_deriv (ν z : ℂ) :
    HasDerivAt (weberE ν) ((weberE (ν-1) z-weberE (ν+1) z)/2) z := by
  sorry

/-- weberE weighted deriv add. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_add (ν z : ℂ) :
    z*deriv (weberE ν) z+(1:ℂ)*ν*weberE ν z = (1:ℂ)*z*weberE (ν-1) z+(1:ℂ)*(1-cos (π*ν))/π := by
  sorry

/-- weberE weighted deriv sub. -/
@[dlmf 11.10.E37]
theorem weberE_weighted_deriv_sub (ν z : ℂ) :
    z*deriv (weberE ν) z+(-1:ℂ)*ν*weberE ν z = (-1:ℂ)*z*weberE (ν-(-1)) z+(-1:ℂ)*(1-cos (π*ν))/π := by
  sorry

end AAR.Struve
