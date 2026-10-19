/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.ExponentialIntegral

/-!
# Generalized sine and cosine integrals, DLMF §8.21

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Generalized lower sine integral on the logarithmic plane away from its parameter poles. -/
def genSinIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k+1 : ℂ)*w)/((2*k+a+1)*(2*k+1).factorial)

/-- Generalized lower cosine integral on the logarithmic plane away from its parameter poles. -/
def genCosIntOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*∑' k : ℕ, (-1 : ℂ)^k*exp ((2*k : ℂ)*w)/((2*k+a)*(2*k).factorial)

/-- Generalized upper sine integral, entire in a. -/
def genSinIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)-exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/(2*I)

/-- Generalized upper cosine integral, entire in a. -/
def genCosIntTailOnLog (a w : ℂ) : ℂ :=
  (exp (π*I*a/2)*upperIncGammaOnLog a (w-π*I/2)+exp (-π*I*a/2)*upperIncGammaOnLog a (w+π*I/2))/2

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinInt (a z : ℂ) : ℂ :=
  genSinIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosInt (a z : ℂ) : ℂ :=
  genCosIntOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genSinIntTail (a z : ℂ) : ℂ :=
  genSinIntTailOnLog a (log z)

/-- Principal branch for nonzero z by continued logarithmic coordinates. -/
def genCosIntTail (a z : ℂ) : ℂ :=
  genCosIntTailOnLog a (log z)

/-- genUpperTrig gamma. -/
@[dlmf 8.21.E1]
theorem genUpperTrig_gamma (a w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntTailOnLog a w+ε*I*genSinIntTailOnLog a w=exp (ε*π*I*a/2)*upperIncGammaOnLog a (w-ε*π*I/2) := by
  sorry

/-- genLowerTrig gamma. -/
@[dlmf 8.21.E2]
theorem genLowerTrig_gamma {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (w : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    genCosIntOnLog a w+ε*I*genSinIntOnLog a w=exp (ε*π*I*a/2)*lowerIncGammaOnLog a (w-ε*π*I/2) := by
  sorry

/-- genSinIntTail parameter entire. -/
theorem genSinIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genSinIntTailOnLog a w) := by
  sorry

/-- genCosIntTail parameter entire. -/
theorem genCosIntTail_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun a => genCosIntTailOnLog a w) := by
  sorry

/-- genSinInt parameter analytic. -/
theorem genSinInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genSinIntOnLog b w) a := by
  sorry

/-- genCosInt parameter analytic. -/
theorem genCosInt_parameter_analytic {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (w : ℂ) :
    AnalyticAt ℂ (fun b => genCosIntOnLog b w) a := by
  sorry

/-- genSinInt parameter residue. -/
theorem genSinInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+(2*n+1))*genSinIntOnLog a w) (𝓝[≠] (-(2*n+1 : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n+1).factorial)) := by
  sorry

/-- genCosInt parameter residue. -/
theorem genCosInt_parameter_residue (n : ℕ) (w : ℂ) :
    Tendsto (fun a : ℂ => (a+2*n)*genCosIntOnLog a w) (𝓝[≠] (-(2*n : ℂ))) (𝓝 ((-1 : ℂ)^n/(2*n).factorial)) := by
  sorry

/-- gamma rotated oscillatory integral. -/
@[dlmf 8.21.E3]
theorem gamma_rotated_oscillatory_integral {a : ℂ} (ha0 : 0 < a.re) (ha1 : a.re < 1) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    HasIntegralAtTop (fun t : ℝ => (t : ℂ)^(a-1)*exp (ε*I*t)) 0 (exp (ε*π*I*a/2)*Gamma a) := by
  sorry

/-- genSinIntTail horizontal integral. -/
@[dlmf 8.21.E4]
theorem genSinIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*sin (z+t)) 0 (genSinIntTail a z) := by
  sorry

/-- genCosIntTail horizontal integral. -/
@[dlmf 8.21.E5]
theorem genCosIntTail_horizontal_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*cos (z+t)) 0 (genCosIntTail a z) := by
  sorry

/-- genSinInt segment integral. -/
@[dlmf 8.21.E6]
theorem genSinInt_segment_integral {a : ℂ} (ha : -1 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genSinInt a z=primitive (fun t => t^(a-1)*sin t) z := by
  sorry

/-- genCosInt segment integral. -/
@[dlmf 8.21.E7]
theorem genCosInt_segment_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    genCosInt a z=primitive (fun t => t^(a-1)*cos t) z := by
  sorry

/-- Γ(a)sin(πa/2), with removable even-integer singularities filled by limits. -/
def gammaSinHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*sin (π*b/2))

/-- Γ(a)cos(πa/2), with removable odd-integer singularities filled by limits. -/
def gammaCosHalfPiContinued (a : ℂ) : ℂ :=
  limUnder (𝓝[≠] a) (fun b : ℂ => Gamma b*cos (π*b/2))

/-- genSinInt complement. -/
@[dlmf 8.21.E8]
theorem genSinInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    genSinInt a z=gammaSinHalfPiContinued a-genSinIntTail a z := by
  sorry

/-- genCosInt complement. -/
@[dlmf 8.21.E9]
theorem genCosInt_complement {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    genCosInt a z=gammaCosHalfPiContinued a-genCosIntTail a z := by
  sorry

/-- genTrig order zero. -/
@[dlmf 8.21.E10]
theorem genTrig_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinIntTail 0 z = -sinIntTail z ∧ genCosIntTail 0 z = -cosInt z := by
  sorry

/-- genSinInt order zero. -/
@[dlmf 8.21.E11]
theorem genSinInt_order_zero {z : ℂ} (hz : z ≠ 0) :
    genSinInt 0 z=sinInt z := by
  sorry

/-- Ordinary infinity limits need Re a<1; other values are interpreted by parameter continuation. -/
@[dlmf 8.21.E12]
theorem genSinInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genSinInt a x) atTop (𝓝 (gammaSinHalfPiContinued a)) := by
  sorry

/-- genCosInt value at infinity. -/
@[dlmf 8.21.E13]
theorem genCosInt_value_at_infinity {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) (ha1 : a.re < 1) :
    Tendsto (fun x : ℝ => genCosInt a x) atTop (𝓝 (gammaCosHalfPiContinued a)) := by
  sorry

/-- genSinInt hasSum. -/
@[dlmf 8.21.E14]
theorem genSinInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k+1)/((2*k+a+1)*(2*k+1).factorial)) (genSinInt a z) := by
  sorry

/-- genCosInt hasSum. -/
@[dlmf 8.21.E15]
theorem genCosInt_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(-1 : ℂ)^k*z^(2*k)/((2*k+a)*(2*k).factorial)) (genCosInt a z) := by
  sorry

/-- genSinInt spherical series. -/
@[dlmf 8.21.E16]
theorem genSinInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n+1)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+3/2 : ℂ)*poch (1-a/2) k/poch (1/2+a/2) (k+1)*sphericalJ (2*k+1) z) (genSinInt a z) := by
  sorry

/-- genCosInt spherical series. -/
@[dlmf 8.21.E17]
theorem genCosInt_spherical_series {a : ℂ} (ha : ∀ n : ℕ, a ≠ -(2*n : ℂ)) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^a*(2*k+1/2 : ℂ)*poch (1/2-a/2) k/poch (a/2) (k+1)*sphericalJ (2*k) z) (genCosInt a z) := by
  sorry

/-- Generalized auxiliary f. -/
@[dlmf 8.21.E18]
def genTrigAuxF (a z : ℂ) : ℂ :=
  genSinIntTail a z*cos z-genCosIntTail a z*sin z

/-- Generalized auxiliary g. -/
@[dlmf 8.21.E19]
def genTrigAuxG (a z : ℂ) : ℂ :=
  genSinIntTail a z*sin z+genCosIntTail a z*cos z

/-- genSinIntTail aux. -/
@[dlmf 8.21.E20]
theorem genSinIntTail_aux (a z : ℂ) :
    genSinIntTail a z=genTrigAuxF a z*cos z+genTrigAuxG a z*sin z := by
  sorry

/-- genCosIntTail aux. -/
@[dlmf 8.21.E21]
theorem genCosIntTail_aux (a z : ℂ) :
    genCosIntTail a z = -genTrigAuxF a z*sin z+genTrigAuxG a z*cos z := by
  sorry

/-- genTrigAuxF oscillatory integral. -/
@[dlmf 8.21.E22]
theorem genTrigAuxF_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin t*(t+z)^(a-1)) 0 (genTrigAuxF a z) := by
  sorry

/-- genTrigAuxG oscillatory integral. -/
@[dlmf 8.21.E23]
theorem genTrigAuxG_oscillatory_integral {a : ℂ} (ha : a.re < 1) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos t*(t+z)^(a-1)) 0 (genTrigAuxG a z) := by
  sorry

/-- genTrigAuxF laplace integral. -/
@[dlmf 8.21.E24]
theorem genTrigAuxF_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxF a z=z^a/2*(∫ t : ℝ in Ioi 0, ((1+I*t)^(a-1)+(1-I*t)^(a-1))*exp (-z*t)) := by
  sorry

/-- genTrigAuxG laplace integral. -/
@[dlmf 8.21.E25]
theorem genTrigAuxG_laplace_integral (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genTrigAuxG a z=z^a/(2*I)*(∫ t : ℝ in Ioi 0, ((1-I*t)^(a-1)-(1+I*t)^(a-1))*exp (-z*t)) := by
  sorry

/-- genTrigAuxF sector asymptotic. -/
@[dlmf 8.21.E26]
theorem genTrigAuxF_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-0)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+0)) (genTrigAuxF a) := by
  sorry

/-- genTrigAuxG sector asymptotic. -/
@[dlmf 8.21.E27]
theorem genTrigAuxG_sector_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun k z => z^(a-1-2*k-1)) (fun k => (-1 : ℂ)^k*poch (1-a) (2*k+1)) (genTrigAuxG a) := by
  sorry

end AAR.Confluent
