/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues

/-!
# Series, recurrences and derivatives, DLMF §§8.7–8.8

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- scIncGamma hasSum exponential. -/
@[dlmf 8.7.E1]
theorem scIncGamma_hasSum_exponential (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-z)*z^k/Gamma (a+k+1)) (scIncGamma a z) := by
  sorry

/-- scIncGamma hasSum alternating. -/
@[dlmf 8.7.E1]
theorem scIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => (-z)^k/(Gamma a*(k.factorial : ℂ)*(a+k))) (scIncGamma a z) := by
  sorry

/-- incompleteGamma increment series. -/
@[dlmf 8.7.E2]
theorem incompleteGamma_increment_series {a x y : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hx : x ∈ slitPlane) (hxy : x+y ∈ slitPlane) (hy : ‖y‖ < ‖x‖) :
    HasSum (fun n : ℕ => exp (-x)*x^(a-1)*poch (1-a) n/(-x)^n*(1-exp (-y)*expPartialSum n y)) (lowerIncGamma a (x+y)-lowerIncGamma a x) ∧ lowerIncGamma a (x+y)-lowerIncGamma a x=upperIncGamma a x-upperIncGamma a (x+y) := by
  sorry

/-- upperIncGamma hasSum alternating. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_alternating {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(a+k)/((k.factorial : ℂ)*(a+k))) (Gamma a-upperIncGamma a z) := by
  sorry

/-- upperIncGamma hasSum exponential. -/
@[dlmf 8.7.E3]
theorem upperIncGamma_hasSum_exponential {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => Gamma a*z^a*exp (-z)*z^k/Gamma (a+k+1)) (Gamma a-upperIncGamma a z) := by
  sorry

/-- lowerIncGamma besselI series. -/
@[dlmf 8.7.E4]
theorem lowerIncGamma_besselI_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => Gamma a*(x : ℂ)^(a/2)*exp (-x : ℂ)*expPartialSum n (-1)*(x : ℂ)^((n : ℂ)/2)*AAR.Bessel.besselI (n+a) (2*Real.sqrt x)) (lowerIncGamma a x) := by
  sorry

/-- scIncGamma sphericalI series. -/
@[dlmf 8.7.E5]
theorem scIncGamma_sphericalI_series (a z : ℂ) :
    HasSum (fun n : ℕ => exp (-z/2)*poch (1-a) n/Gamma (n+a+1)*(2*n+1)*sphericalI n (z/2)) (scIncGamma a z) := by
  sorry

/-- upperIncGamma laguerre series. -/
@[dlmf 8.7.E6]
theorem upperIncGamma_laguerre_series {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ => (x : ℂ)^a*exp (-x : ℂ)*AAR.OrthogonalPolynomials.laguerrePolyL a n x/(n+1)) (upperIncGamma a x) := by
  sorry

/-- incompleteGamma threeTerm. -/
@[dlmf 8.8.E3]
theorem incompleteGamma_threeTerm {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    ∀ f ∈ ({lowerIncGamma,upperIncGamma} : Set (ℂ → ℂ → ℂ)), f (a+2) z-(a+1+z)*f (a+1) z+a*z*f a z=0 := by
  sorry

/-- scIncGamma recurrence. -/
@[dlmf 8.8.E4]
theorem scIncGamma_recurrence (a z : ℂ) :
    z*scIncGamma (a+1) z=scIncGamma a z-exp (-z)/Gamma (a+1) := by
  sorry

/-- lowerIncGamma shift up. -/
@[dlmf 8.8.E7]
theorem lowerIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (a+n) z=poch a n*lowerIncGamma a z - z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  sorry

/-- lowerIncGamma shift down. -/
@[dlmf 8.8.E8]
theorem lowerIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=Gamma a/Gamma (a-n)*lowerIncGamma (a-n) z - z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  sorry

/-- upperIncGamma shift up. -/
@[dlmf 8.8.E9]
theorem upperIncGamma_shift_up (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (a+n) z=poch a n*upperIncGamma a z + z^a*exp (-z)*(∑ k ∈ Finset.range n, Gamma (a+n)/Gamma (a+k+1)*z^k) := by
  sorry

/-- upperIncGamma shift down. -/
@[dlmf 8.8.E10]
theorem upperIncGamma_shift_down (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=Gamma a/Gamma (a-n)*upperIncGamma (a-n) z + z^(a-1)*exp (-z)*(∑ k ∈ Finset.range n, Gamma a/Gamma (a-k)*z^(-(k : ℤ))) := by
  sorry

/-- normIncGammaPContinued shift up. -/
@[dlmf 8.8.E11]
theorem normIncGammaPContinued_shift_up (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaPContinued (a+n) z=normIncGammaPContinued a z - z^a*exp (-z)*(∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
  sorry

/-- normIncGammaQContinued shift up. -/
@[dlmf 8.8.E12]
theorem normIncGammaQContinued_shift_up (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued (a+n) z=normIncGammaQContinued a z + z^a*exp (-z)*(∑ k ∈ Finset.range n, z^k/Gamma (a+k+1)) := by
  sorry

/-- hasDerivAt incompleteGamma. -/
@[dlmf 8.8.E13]
theorem hasDerivAt_incompleteGamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (lowerIncGamma a) (z^(a-1)*exp (-z)) z ∧ HasDerivAt (upperIncGamma a) (-z^(a-1)*exp (-z)) z := by
  sorry

/-- scIncGamma deriv parameter zero. -/
@[dlmf 8.8.E14]
theorem scIncGamma_deriv_parameter_zero {z : ℂ} (hz : z ≠ 0) :
    deriv (fun a => scIncGamma a z) 0 = -genExpIntE 1 z-log z := by
  sorry

/-- lowerIncGamma iteratedDeriv scaled power. -/
@[dlmf 8.8.E15]
theorem lowerIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*lowerIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*lowerIncGamma (a+n) z := by
  sorry

/-- upperIncGamma iteratedDeriv scaled power. -/
@[dlmf 8.8.E16]
theorem upperIncGamma_iteratedDeriv_scaled_power (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^(-a)*upperIncGamma a t) z=(-1 : ℂ)^n*z^(-a-n)*upperIncGamma (a+n) z := by
  sorry

/-- lowerIncGamma iteratedDeriv scaled exp. -/
@[dlmf 8.8.E17]
theorem lowerIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*lowerIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*lowerIncGamma (a-n) z := by
  sorry

/-- upperIncGamma iteratedDeriv scaled exp. -/
@[dlmf 8.8.E19]
theorem upperIncGamma_iteratedDeriv_scaled_exp (n : ℕ) {a : ℂ} (ha : ∀ k : ℕ, a-n ≠ -k) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => exp t*upperIncGamma a t) z=(-1 : ℂ)^n*poch (1-a) n*exp z*upperIncGamma (a-n) z := by
  sorry

/-- scIncGamma iteratedDeriv scaled. -/
@[dlmf 8.8.E18]
theorem scIncGamma_iteratedDeriv_scaled (n : ℕ) (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv n (fun t => t^a*exp t*scIncGamma a t) z=z^(a-n)*exp z*scIncGamma (a-n) z := by
  sorry

end AAR.Confluent
