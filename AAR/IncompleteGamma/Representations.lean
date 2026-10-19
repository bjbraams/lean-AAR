/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues

/-!
# Real, contour and Mellin–Barnes representations, DLMF §8.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- lowerIncGamma trigonometric integral. -/
@[dlmf 8.6.E1]
theorem lowerIncGamma_trigonometric_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) (z : ℂ) :
    lowerIncGamma a z=z^a/sin (π*a)*(∫ t : ℝ in 0..π, exp (z*Real.cos t)*cos (a*t+z*Real.sin t)) := by
  sorry

/-- lowerIncGamma besselJ integral. -/
@[dlmf 8.6.E2]
theorem lowerIncGamma_besselJ_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    lowerIncGamma a z=z^(a/2)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(a/2-1)*besselJ a (2*(z*t)^(1/2 : ℂ))) := by
  sorry

/-- lowerIncGamma logarithmic integral. -/
@[dlmf 8.6.E3]
theorem lowerIncGamma_logarithmic_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (-a*t-z*Real.exp (-t))) := by
  sorry

/-- upperIncGamma stieltjes integral. -/
@[dlmf 8.6.E4]
theorem upperIncGamma_stieltjes_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=z^a*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, (t : ℂ)^(-a)*exp (-t : ℂ)/(z+t)) := by
  sorry

/-- upperIncGamma laplace integral complex. -/
@[dlmf 8.6.E5]
theorem upperIncGamma_laplace_integral_complex (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*exp (-z)*(∫ t : ℝ in Ioi 0, exp (-z*t)*(1+(t : ℂ))^(a-1)) := by
  sorry

/-- upperIncGamma besselK integral. -/
@[dlmf 8.6.E6]
theorem upperIncGamma_besselK_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    upperIncGamma a z=2*z^(a/2)*exp (-z)/Gamma (1-a)*(∫ t : ℝ in Ioi 0, exp (-t : ℂ)*(t : ℂ)^(-a/2)*AAR.Bessel.besselK a (2*(z*t)^(1/2 : ℂ))) := by
  sorry

/-- upperIncGamma logarithmic integral. -/
@[dlmf 8.6.E7]
theorem upperIncGamma_logarithmic_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma a z=z^a*(∫ t : ℝ in Ioi 0, exp (a*t-z*Real.exp t)) := by
  sorry

/-- lowerIncGamma circle integral. -/
@[dlmf 8.6.E8]
theorem lowerIncGamma_circle_integral {a : ℂ} (ha : ∀ n : ℤ, a ≠ n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z = -I*z^a/(2*sin (π*a))*(∫ θ : ℝ in (-π)..π, I*exp (a*I*θ+z*exp (I*θ))) := by
  sorry

/-- Symmetric principal value underlying the indented contour of 8.6.9. -/
def upperGammaIndentPV (a z : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => (∫ t : ℝ in 0..(1-ε), (t : ℂ)^a*exp (-z*t)/(t-1)) + improperAtTop (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) (1+ε))

/-- upperGammaIndentPV converges. -/
@[dlmf 8.6.E9]
theorem upperGammaIndentPV_converges {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) :
    HasPrincipalValueIoi (fun t : ℝ => (t : ℂ)^a*exp (-z*t)/(t-1)) 0 1 (upperGammaIndentPV a z) := by
  sorry

/-- upperIncGamma indented integral. -/
@[dlmf 8.6.E9]
theorem upperIncGamma_indented_integral {a z : ℂ} (ha : -1 < a.re) (hz : 0 < z.re) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog (-a) (log z+ε*π*I)=exp z*exp (-ε*π*I*a)/Gamma (1+a)*(upperGammaIndentPV a z-ε*π*I*exp (-z)) := by
  sorry

/-- The separating contour expressed by a vertical line and its crossed-pole residue. -/
@[dlmf 8.6.E10]
theorem lowerIncGamma_mellinBarnes {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : c ≠ a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma s/(a-s)*z^(a-s)) (2*π*(lowerIncGamma a z-(if a.re < c then Gamma a else 0))) := by
  sorry

/-- upperIncGamma mellinBarnes. -/
@[dlmf 8.6.E11]
theorem upperIncGamma_mellinBarnes (a : ℂ) {z : ℂ} (hz : 0 < z.re) {c : ℝ} (hc : 0 < c) (hca : 0 < c+a.re) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+a)*z^(-s)/s) (2*π*upperIncGamma a z) := by
  sorry

/-- Finitely many residues recording indentation past right-hand Gamma poles. -/
def gammaBarnesResidueSum (a w : ℂ) (c : ℝ) : ℂ :=
  ∑ n ∈ Finset.range ⌈a.re-1-c⌉₊, limUnder (𝓝[≠] (a-1-n)) (fun s : ℂ => (s-(a-1-n))*Gamma (s+1-a)*π/sin (π*s)*exp (-s*w))

/-- Logarithmic-plane formula with explicit separating-contour residues. -/
@[dlmf 8.6.E12]
theorem upperIncGamma_mellinBarnes_continued {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1) (w : ℂ) (hw : |w.im| < 3*π/2) {c : ℝ} (hc0 : -1 < c) (hc1 : c < 0) (hca : ∀ n : ℕ, a.re-1-n ≠ c) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; Gamma (s+1-a)*π/sin (π*s)*exp (-s*w)) (2*π*(-Gamma (1-a)*exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-gammaBarnesResidueSum a w c)) := by
  sorry

end AAR.Confluent
