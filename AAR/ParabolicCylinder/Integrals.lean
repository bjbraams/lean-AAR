/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Relations

/-!
# Cylinder real and contour integrals

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- pcfU integral 2. -/
@[dlmf 12.5.E2]
theorem pcfU_integral_2 {a z : ℂ} (ha : -1/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => z*exp (-z^2/4)/Gamma (a/2+1/4)*((t:ℂ)^(a/2-3/4)*exp (-t)*(z^2+2*t)^(-a/2-3/4))) 0 (pcfU a z) := by
  sorry

/-- pcfU integral 3. -/
@[dlmf 12.5.E3]
theorem pcfU_integral_3 {a z : ℂ} (ha : -3/2 < a.re) (hz : 0 < z.re) :
    HasIntegralAtTop (fun t : ℝ => exp (-z^2/4)/Gamma (a/2+3/4)*((t:ℂ)^(a/2-1/4)*exp (-t)*(z^2+2*t)^(-a/2-1/4))) 0 (pcfU a z) := by
  sorry

/-- pcfU integral 4. -/
@[dlmf 12.5.E4]
theorem pcfU_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => (Real.sqrt (2/π):ℂ)*exp (z^2/4)*((t:ℂ)^(-a-1/2)*exp (-t^2/2)*cos (z*t+(a/2+1/4)*π))) 0 (pcfU a z) := by
  sorry

/-- pcfU vertical integral. -/
@[dlmf 12.5.E6]
theorem pcfU_vertical_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; exp (z^2/4)/Real.sqrt (2*π)*exp (-z*t+t^2/2)*t^(-a-1/2)) (pcfU a z) := by
  sorry

/-- pcfV horizontal integral. -/
@[dlmf 12.5.E7]
theorem pcfV_horizontal_integral (a z : ℂ) {c : ℝ} (hc : 0 < c) :
    ∃ u v : ℂ, HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x-c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) u ∧ HasIntegralWholeLine (fun x : ℝ => let t : ℂ := x+c*I; exp (-z^2/4)/(2*π)*exp (z*t-t^2/2)*t^(a-1/2)) v ∧ u+v=pcfV a z := by
  sorry

/-- Hankel loop from negative infinity below the cut around zero to negative infinity above. -/
def pcfNegativeLoop (a z : ℂ) (r R : ℝ) : ℂ :=
  (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t-π*I))) + (∫ θ : ℝ in -π..π, let t := r*exp (I*θ); exp (z*t-t^2/2)*exp ((a-1/2)*(Real.log r+I*θ))*I*t) - (∫ t : ℝ in r..R, exp (-z*t-t^2/2)*exp ((a-1/2)*(Real.log t+π*I)))

/-- pcfU hankel integral. -/
@[dlmf 12.5.E5]
theorem pcfU_hankel_integral {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun R => Gamma (1/2-a)/(2*π*I)*exp (-z^2/4)*pcfNegativeLoop a z r R) atTop (𝓝 (pcfU a z)) := by
  sorry

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E8]
theorem pcfU_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, 1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) (2*π*Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z) := by
  sorry

/-- Straight separating Barnes contour; exceptional-parameter deformations need residue corrections. -/
@[dlmf 12.5.E9]
theorem pcfV_barnes_integral {a z : ℂ} (ha : ∀ n : ℕ, -1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < π/4) {c : ℝ} (hc : 0 < c) (hca : 2*c < 1/2+-1*a.re) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) (2*π*Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z) := by
  sorry

/-- pcf integral 1. -/
@[dlmf 12.12.E1]
theorem pcf_integral_1 {μ : ℂ} (hμ : 0 < μ.re) (a : ℂ) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(μ-1)*pcfU a t) 0 (Real.sqrt π*2^(-(μ+a+1/2)/2)*Gamma μ/Gamma ((μ+a+3/2)/2)) := by
  sorry

/-- pcf integral 2. -/
@[dlmf 12.12.E2]
theorem pcf_integral_2 {a : ℂ} (ha : a.re < -1/2) :
    HasIntegralAtTop (fun t : ℝ => exp (-3*t^2/4)*(t:ℂ)^(-a-3/2)*pcfU a t) 0 (2^(1/4+a/2)*Gamma (-a-1/2)*cos ((a/4+1/8)*π)) := by
  sorry

/-- pcf integral 3. -/
@[dlmf 12.12.E3]
theorem pcf_integral_3 {a : ℂ} (ha : a.re < 1/2) {x : ℝ} (hx : 0 < x) :
    HasIntegralAtTop (fun t : ℝ => exp (-t^2/4)*(t:ℂ)^(-a-1/2)/(x^2+t^2:ℂ)*pcfU a t) 0 ((Real.sqrt (π/2):ℂ)*Gamma (1/2-a)*(x:ℂ)^(-a-3/2)*exp (x^2/4)*pcfU (-a) x) := by
  sorry

/-- pcf integral 4. -/
@[dlmf 12.12.E4]
theorem pcf_integral_4 {a : ℂ} (ha : a.re < 1/2) (z : ℂ) :
    HasIntegralAtTop (fun t : ℝ => 2^(3/2:ℂ)/π*Gamma (1/2-a)*exp (2*a*t+z^2/2*Real.tanh t)/(Real.sqrt (Real.sinh (2*t)):ℂ)) 0 ((pcfU a z)^2+(pcfUBar a z)^2) := by
  sorry

end AAR.Confluent
