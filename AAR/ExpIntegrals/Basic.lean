/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.DLMF.Framework

/-!
# Entire and principal exponential, trigonometric and hyperbolic integrals

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- The entire complementary exponential integral. -/
@[dlmf 6.2.E3]
def expIntEin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(k+1) / ((k+1).factorial * (k+1 : ℂ))

/-- The entire sine integral. -/
@[dlmf 6.2.E9]
def sinInt (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- The entire complementary cosine integral. -/
@[dlmf 6.2.E12]
def cosIntCin (z : ℂ) : ℂ :=
  ∑' k : ℕ, (-1 : ℂ)^k * z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Principal cosine integral. -/
@[dlmf 6.2.E13]
def cosInt (z : ℂ) : ℂ :=
  -cosIntCin z + log z + Real.eulerMascheroniConstant

/-- The shifted sine integral si. -/
@[dlmf 6.2.E10]
def sinIntTail (z : ℂ) : ℂ :=
  sinInt z - π/2

/-- The entire hyperbolic sine integral. -/
@[dlmf 6.2.E15]
def sinhInt (z : ℂ) : ℂ :=
  ∑' k : ℕ, z^(2*k+1) / ((2*k+1).factorial * (2*k+1 : ℂ))

/-- Principal hyperbolic cosine integral. -/
@[dlmf 6.2.E16]
def coshInt (z : ℂ) : ℂ :=
  Real.eulerMascheroniConstant + log z + ∑' k : ℕ, z^(2*k+2) / ((2*k+2).factorial * (2*k+2 : ℂ))

/-- Real Ei, with a totalized value at zero outside its mathematical domain. -/
@[dlmf 6.2.E5]
def Real.expIntEi (x : ℝ) : ℝ :=
  Real.eulerMascheroniConstant + Real.log |x| - (AAR.Confluent.expIntEin (-x)).re

/-- Real logarithmic integral, singular at x=1. -/
@[dlmf 6.2.E8]
def Real.logIntLi (x : ℝ) : ℝ :=
  Real.expIntEi (Real.log x)

/-- Auxiliary sine/cosine integral f. -/
@[dlmf 6.2.E17]
def expIntAuxF (z : ℂ) : ℂ :=
  cosInt z * sin z - sinIntTail z * cos z

/-- Auxiliary sine/cosine integral g. -/
@[dlmf 6.2.E18]
def expIntAuxG (z : ℂ) : ℂ :=
  -cosInt z * cos z - sinIntTail z * sin z

/-- Entire differentiability from the defining convergent series. -/
theorem expIntEin_entire  :
    Differentiable ℂ expIntEin := by
  sorry

/-- Entire differentiability from the defining convergent series. -/
theorem sinInt_entire  :
    Differentiable ℂ sinInt := by
  sorry

/-- Entire differentiability from the defining convergent series. -/
theorem cosIntCin_entire  :
    Differentiable ℂ cosIntCin := by
  sorry

/-- Entire differentiability from the defining convergent series. -/
theorem sinhInt_entire  :
    Differentiable ℂ sinhInt := by
  sorry

/-- Agreement with the existing real-variable definition. -/
theorem expIntEin_ofReal (x : ℝ) :
    expIntEin x = (Real.expIntEin x : ℂ) := by
  sorry

/-- Agreement with the existing real-variable definition. -/
theorem sinInt_ofReal (x : ℝ) :
    sinInt x = (Real.sinInt x : ℂ) := by
  sorry

/-- Agreement with the existing real-variable definition. -/
theorem cosIntCin_ofReal (x : ℝ) :
    cosIntCin x = (Real.cosIntCin x : ℂ) := by
  sorry

/-- cosInt ofReal. -/
theorem cosInt_ofReal {x : ℝ} (hx : 0 < x) :
    cosInt x = (Real.cosInt x : ℂ) := by
  sorry

/-- sinInt odd. -/
theorem sinInt_odd (z : ℂ) :
    sinInt (-z) = -sinInt z := by
  sorry

/-- cosIntCin even. -/
theorem cosIntCin_even (z : ℂ) :
    cosIntCin (-z) = cosIntCin z := by
  sorry

/-- expIntEin segment integral. -/
@[dlmf 6.2.E3]
theorem expIntEin_segment_integral (z : ℂ) :
    expIntEin z = primitive (fun t => (1-exp (-t))/t) z := by
  sorry

/-- sinInt segment integral. -/
@[dlmf 6.2.E9]
theorem sinInt_segment_integral (z : ℂ) :
    sinInt z = primitive (fun t => sin t/t) z := by
  sorry

/-- cosIntCin segment integral. -/
@[dlmf 6.2.E12]
theorem cosIntCin_segment_integral (z : ℂ) :
    cosIntCin z = primitive (fun t => (1-cos t)/t) z := by
  sorry

/-- sinhInt segment integral. -/
@[dlmf 6.2.E15]
theorem sinhInt_segment_integral (z : ℂ) :
    sinhInt z = primitive (fun t => sinh t/t) z := by
  sorry

/-- coshInt segment integral. -/
@[dlmf 6.2.E16]
theorem coshInt_segment_integral {z : ℂ} (hz : z ∈ slitPlane) :
    coshInt z = Real.eulerMascheroniConstant + log z + primitive (fun t => (cosh t-1)/t) z := by
  sorry

/-- expIntE1 horizontal integral. -/
@[dlmf 6.2.E1]
theorem expIntE1_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => exp (-(z+t))/(z+t)) 0 (genExpIntE 1 z) := by
  sorry

/-- expIntE1 stieltjes. -/
@[dlmf 6.2.E2]
theorem expIntE1_stieltjes {z : ℂ} (hz : z ∈ slitPlane) :
    genExpIntE 1 z = exp (-z) * ∫ t : ℝ in Ioi 0, exp (-t : ℂ)/(t+z) := by
  sorry

/-- expIntE1 eq Ein complex. -/
@[dlmf 6.2.E4]
theorem expIntE1_eq_Ein_complex {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = expIntEin z - log z - Real.eulerMascheroniConstant := by
  sorry

/-- Real.expIntEi principalValue. -/
@[dlmf 6.2.E5]
theorem Real.expIntEi_principalValue {x : ℝ} (hx : 0 < x) :
    HasPrincipalValueIoi (fun t : ℝ => exp (-t : ℂ)/(t : ℂ)) (-x) 0 (-Real.expIntEi x) := by
  sorry

/-- Real.expIntEi negative. -/
@[dlmf 6.2.E6]
theorem Real.expIntEi_negative {x : ℝ} (hx : 0 < x) :
    (Real.expIntEi (-x) : ℂ) = -genExpIntE 1 x := by
  sorry

/-- Real.expIntEi Ein. -/
@[dlmf 6.2.E7]
theorem Real.expIntEi_Ein {x : ℝ} (hx : 0 < x) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    (Real.expIntEi (ε*x) : ℂ) = -expIntEin (-ε*x) + Real.log x + Real.eulerMascheroniConstant := by
  sorry

/-- Real.logIntLi principalValue. -/
@[dlmf 6.2.E8]
theorem Real.logIntLi_principalValue {x : ℝ} (hx : 1 < x) :
    Tendsto (fun ε : ℝ => (∫ t in (0 : ℝ)..(1-ε), 1/Real.log t) + ∫ t in (1+ε)..x, 1/Real.log t) (𝓝[>] (0 : ℝ)) (𝓝 (Real.logIntLi x)) := by
  sorry

/-- sinIntTail horizontal integral. -/
@[dlmf 6.2.E10]
theorem sinIntTail_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => sin (z+t)/(z+t)) 0 (-sinIntTail z) := by
  sorry

/-- cosInt horizontal integral. -/
@[dlmf 6.2.E11]
theorem cosInt_horizontal_integral {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => cos (z+t)/(z+t)) 0 (-cosInt z) := by
  sorry

/-- cosInt tendsto atTop. -/
@[dlmf 6.2.E14]
theorem cosInt_tendsto_atTop  :
    Tendsto (fun x : ℝ => cosInt x) atTop (𝓝 0) := by
  sorry

/-- sinInt eq aux. -/
@[dlmf 6.2.E19]
theorem sinInt_eq_aux (z : ℂ) :
    sinInt z = π/2 - expIntAuxF z * cos z - expIntAuxG z * sin z := by
  sorry

/-- cosInt eq aux. -/
@[dlmf 6.2.E20]
theorem cosInt_eq_aux (z : ℂ) :
    cosInt z = expIntAuxF z * sin z - expIntAuxG z * cos z := by
  sorry

/-- hasDerivAt expIntAuxF. -/
@[dlmf 6.2.E21]
theorem hasDerivAt_expIntAuxF {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt expIntAuxF (-expIntAuxG z) z := by
  sorry

/-- hasDerivAt expIntAuxG. -/
@[dlmf 6.2.E21]
theorem hasDerivAt_expIntAuxG {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt expIntAuxG (expIntAuxF z - 1/z) z := by
  sorry

end AAR.Confluent
