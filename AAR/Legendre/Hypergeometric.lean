/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated
public import AAR.Legendre.Connections
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Hypergeometric representations and parameter derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Classical Gauss function on its principal cut plane at regular c. This is a
continuation, not the totalized power series outside its convergence disk. -/
@[dlmf 14.3.E3]
def legendreGaussF (a b c z : ℂ) : ℂ :=
  Gamma c*regularizedGaussHG a b c z

/-- DLMF normalization; the unit-disk agreement is already
`AAR.Hypergeometric.ordinaryHypergeometric_eq_Gamma_mul_regularizedGaussHG`. -/
@[dlmf 14.3.E3]
theorem legendreGaussF_normalization {a b c z : ℂ} (hc : ∀ n : ℕ, c ≠ -n) :
    regularizedGaussHG a b c z=legendreGaussF a b c z/Gamma c := by
  have hG := Gamma_ne_zero hc
  simp [legendreGaussF, hG]

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E4]
theorem ferrersP_integer_hypergeometric_4 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)/2^m*(1-x^2:ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  unfold ferrersP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination ((-1)^(k+1) * poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-x)/2)) *
    ferrers_gauge_nat (k+1) hx

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E5]
theorem ferrersP_integer_hypergeometric_5 (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν m x=(-1)^m*poch (ν-m+1) (2*m)*((1-x)/(1+x):ℂ)^((m:ℂ)/2)*regularizedGaussHG (ν+1) (-ν) (m+1) ((1-x)/2) := by
  rcases m with _ | k
  · simp [ferrersP, poch_zero]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  have hr : 0 ≤ (1+x)/(1-x) := div_nonneg (by linarith [hx.1]) (by linarith [hx.2])
  have e : ((1-x)/(1+x):ℂ) = ((((1+x)/(1-x):ℝ):ℂ))⁻¹ := by push_cast; rw [inv_div]
  unfold ferrersP
  rw [regularizedGaussHG_legendre_neg_nat ν k hw, e, inv_cpow_ofReal_nonneg hr, poch_mul_poch_neg,
    ← cpow_neg, show -(((k+1:ℕ):ℂ)/2) = -((k+1:ℕ):ℂ)/2 by ring, ← ferrers_gauge_neg_nat (k+1) hx]
  ring

/-- Pochhammer products supply the limiting gamma quotient at exceptional degrees. -/
@[dlmf 14.3.E8]
theorem associatedP_integer_hypergeometric_8 (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν m z=poch (ν-m+1) (2*m)/2^m*legendreBranchPower m z*regularizedGaussHG (ν+m+1) (m-ν) (m+1) ((1-z)/2) := by
  rcases m with _ | k
  · simp [associatedP, legendreBranchPower, poch_zero]
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hg := associated_gauge_nat (k+1) hz
  unfold associatedP
  rw [show 1-((k+1:ℕ):ℂ) = -(k:ℂ) by push_cast; ring, regularizedGaussHG_neg_nat _ _ _ hw,
    show ν+1+k+1 = ν+((k+1:ℕ):ℂ)+1 by push_cast; ring,
    show -ν+k+1 = ((k+1:ℕ):ℂ)-ν by push_cast; ring,
    show (k:ℂ)+2 = ((k+1:ℕ):ℂ)+1 by push_cast; ring, poch_mul_poch_neg]
  linear_combination (poch (ν-((k+1:ℕ):ℂ)+1) (2*(k+1)) *
    regularizedGaussHG (ν+((k+1:ℕ):ℂ)+1) (((k+1:ℕ):ℂ)-ν) (((k+1:ℕ):ℂ)+1) ((1-z)/2)) * hg

/-- associated hypergeometric 9. -/
@[dlmf 14.3.E9]
theorem associated_hypergeometric_9 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=exp (μ/2*(log (z-1)-log (z+1)))*regularizedGaussHG (ν+1) (-ν) (μ+1) ((1-z)/2) := by
  unfold associatedP
  rw [show 1-(-μ) = μ+1 by ring,
    show -μ/2*(log (z+1)-log (z-1)) = μ/2*(log (z-1)-log (z+1)) by ring]

/-- associated hypergeometric 15. -/
@[dlmf 14.3.E15]
theorem associated_hypergeometric_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-μ) z=2^(-μ)*legendreBranchPower μ z*regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) := by
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have h1 : z+1 ≠ 0 := by
    simpa [add_comm] using slitPlane_ne_zero (one_add_mem_slitPlane_of_sub_one hz)
  have hl2 : log (2:ℂ) = (Real.log 2:ℂ) := by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num, ofReal_log (by norm_num)]
  have hp : (1-(1-z)/2)^μ = exp ((log (z+1) - Real.log 2)*μ) := by
    rw [show 1-(1-z)/2 = (z+1)*((1/2:ℝ):ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (mul_ne_zero h1 (by norm_num)), log_mul_ofReal _ (by norm_num) _ h1,
      one_div, Real.log_inv]
    push_cast; ring_nf
  have h2 : (2:ℂ)^(-μ) = exp (Real.log 2 * (-μ)) := by
    rw [cpow_def_of_ne_zero (by norm_num), hl2]
  unfold associatedP legendreBranchPower
  rw [show 1-(-μ) = μ+1 by ring, regularizedGaussHG_euler _ _ _ hw, show μ+1-(ν+1)-(-ν) = μ by ring,
    show μ+1-(ν+1) = μ-ν by ring, show μ+1-(-ν) = ν+μ+1 by ring, hp, h2]
  have he : exp (-μ/2*(log (z+1)-log (z-1))) * exp ((log (z+1) - Real.log 2)*μ) =
      exp (Real.log 2 * (-μ)) * exp (μ/2*(log (z-1)+log (z+1))) := by
    rw [← exp_add, ← exp_add]; congr 1; ring
  linear_combination regularizedGaussHG (μ-ν) (ν+μ+1) (μ+1) ((1-z)/2) * he

/-- associated hypergeometric 16. -/
@[dlmf 14.3.E16]
theorem associated_hypergeometric_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=2^ν*Real.sqrt π*z^(ν-μ)*legendreBranchPower μ z/Gamma (ν+μ+1)*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (1/2-ν) (1/z^2)-Real.sqrt π*legendreBranchPower μ z/(2^(ν+1)*Gamma (μ-ν)*z^(ν+μ+1))*regularizedGaussHG ((ν+μ+2)/2) ((ν+μ+1)/2) (ν+3/2) (1/z^2) := by
  sorry

/-- associated hypergeometric 18. -/
@[dlmf 14.3.E18]
theorem associated_hypergeometric_18 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν (-μ) z=2^(-μ)*z^(ν-μ)*legendreBranchPower μ z*regularizedGaussHG ((μ-ν)/2) ((μ-ν+1)/2) (μ+1) (1-1/z^2) := by
  sorry

/-- associated hypergeometric 20. -/
@[dlmf 14.3.E20]
theorem associated_hypergeometric_20 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  exact associated_connection_15 ν μ hz

/-- Combined boundary value at the hypergeometric cut; separate totalized values on that cut are not used. -/
@[dlmf 14.3.E17]
theorem associatedP_square_hypergeometric (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => let u : ℂ := x^2+I*ε; π*legendreBranchPower μ x/2^μ*(regularizedGaussHG ((μ-ν)/2) ((ν+μ+1)/2) (1/2) u/(Gamma ((μ-ν+1)/2)*Gamma ((ν+μ+2)/2))-x*regularizedGaussHG ((μ-ν+1)/2) ((ν+μ+2)/2) (3/2) u/(Gamma ((μ-ν)/2)*Gamma ((ν+μ+1)/2)))) (𝓝[>] 0) (𝓝 (associatedP ν (-μ) x)) := by
  sorry

/-- Parameter limit includes the removable singularities of the gamma-prefactored representation. -/
@[dlmf 14.3.E19]
theorem olverQ_linear_hypergeometric (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => 2^v*Gamma (v+1)*exp (μ/2*log (z+1)-(μ/2+v+1)*log (z-1))*regularizedGaussHG (v+1) (v+μ+1) (2*v+2) (2/(1-z))) (𝓝[≠] ν) (𝓝 (olverQ ν μ z)) := by
  sorry

/-- legendreDegreeA. -/
@[dlmf 14.11.E3]
def legendreDegreeA (ν μ : ℂ) (x : ℝ) : ℂ :=
  sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*∑' k : ℕ, ((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))

/-- legendreDegreeA hasSum. -/
@[dlmf 14.11.E3]
theorem legendreDegreeA_hasSum {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun k : ℕ => sin (ν*π)*((1+x)/(1-x):ℂ)^(μ/2)*((1-x)/2:ℂ)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))) (legendreDegreeA ν μ x) := by
  sorry

/-- ferrersP degree deriv. -/
@[dlmf 14.11.E1]
theorem ferrersP_degree_deriv {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersP ν μ x) (π*cos (ν*π)/sin (ν*π)*ferrersP ν μ x-legendreDegreeA ν μ x/π) ν := by
  sorry

/-- ferrersQ degree deriv. -/
@[dlmf 14.11.E2]
theorem ferrersQ_degree_deriv {ν μ : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (hplus : ∀ n : ℤ, ν+μ ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun ν => ferrersQ ν μ x) (-π^2/2*ferrersP ν μ x+π*sin (μ*π)/(sin (ν*π)*sin ((ν+μ)*π))*ferrersQ ν μ x-cos ((ν+μ)*π)/(2*sin ((ν+μ)*π))*legendreDegreeA ν μ x+legendreDegreeA ν μ (-x)/(2*sin ((ν+μ)*π))) ν := by
  sorry

/-- ferrersP order deriv zero. -/
@[dlmf 14.11.E4]
theorem ferrersP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersP ν μ x) (digamma (ν+1)*ferrersP ν 0 x+ferrersQ ν 0 x) 0 := by
  sorry

/-- ferrersQ order deriv zero. -/
@[dlmf 14.11.E5]
theorem ferrersQ_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun μ => ferrersQ ν μ x) (-π^2/4*ferrersP ν 0 x+digamma (ν+1)*ferrersQ ν 0 x) 0 := by
  sorry

/-- associatedP order deriv zero. -/
@[dlmf 14.11.E4]
theorem associatedP_order_deriv_zero {ν : ℂ} (hν : LegendreQRegular ν 0) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasDerivAt (fun μ => associatedP ν μ z) (digamma (ν+1)*associatedP ν 0 z+associatedQ ν 0 z) 0 := by
  sorry

end AAR.Legendre
