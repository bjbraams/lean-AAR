/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Basic

/-!
# Incomplete Gamma continuation, definitions and differential equations, DLMF §8.2

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- Upper incomplete Gamma on the logarithmic plane, also at integral a. -/
def upperIncGammaOnLog (a w : ℂ) : ℂ :=
  upperIncGamma a (exp w) - segmentIntegral (fun u => exp (a*u-exp u)) (log (exp w)) w

/-- Lower incomplete Gamma on the logarithmic plane away from its parameter poles. -/
def lowerIncGammaOnLog (a w : ℂ) : ℂ :=
  Gamma a*exp (a*w)*scIncGamma a (exp w)

/-- Analytically continued P; at nonpositive integral a it differs from the old totalized quotient. -/
@[dlmf 8.2.E4]
def normIncGammaPContinued (a z : ℂ) : ℂ :=
  z^a*scIncGamma a z

/-- Analytically continued Q. -/
@[dlmf 8.2.E4]
def normIncGammaQContinued (a z : ℂ) : ℂ :=
  1-normIncGammaPContinued a z

/-- Continued P on the logarithmic plane. -/
def normIncGammaPOnLog (a w : ℂ) : ℂ :=
  exp (a*w)*scIncGamma a (exp w)

/-- Continued Q on the logarithmic plane. -/
def normIncGammaQOnLog (a w : ℂ) : ℂ :=
  1-normIncGammaPOnLog a w

/-- normIncGammaPContinued eq. -/
@[dlmf 8.2.E4]
theorem normIncGammaPContinued_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    normIncGammaPContinued a z=normIncGammaP a z := by
  sorry

/-- normIncGammaQContinued eq. -/
@[dlmf 8.2.E4]
theorem normIncGammaQContinued_eq {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued a z=normIncGammaQ a z := by
  sorry

/-- lowerIncGamma segment integral. -/
@[dlmf 8.2.E1]
theorem lowerIncGamma_segment_integral {a : ℂ} (ha : 0 < a.re) {z : ℂ} (hz : z ∈ slitPlane) :
    lowerIncGamma a z=primitive (fun t => t^(a-1)*exp (-t)) z := by
  sorry

/-- upperIncGamma horizontal integral. -/
@[dlmf 8.2.E2]
theorem upperIncGamma_horizontal_integral (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(a-1)*exp (-(z+t))) 0 (upperIncGamma a z) := by
  sorry

/-- normIncGammaContinued complement. -/
@[dlmf 8.2.E5]
theorem normIncGammaContinued_complement (a z : ℂ) :
    normIncGammaPContinued a z+normIncGammaQContinued a z=1 := by
  simp [normIncGammaQContinued]

/-- scIncGamma integral. -/
@[dlmf 8.2.E7]
theorem scIncGamma_integral {a : ℂ} (ha : 0 < a.re) (z : ℂ) :
    scIncGamma a z=1/Gamma a*(∫ t : ℝ in 0..1, (t : ℂ)^(a-1)*exp (-z*t)) := by
  sorry

/-- Joint entire differentiability asserted in DLMF §8.2(ii). -/
theorem scIncGamma_joint_entire  :
    Differentiable ℂ (fun p : ℂ × ℂ => scIncGamma p.1 p.2) := by
  sorry

/-- Entire parameter dependence in DLMF §8.2(ii). -/
theorem upperIncGamma_parameter_entire {z : ℂ} (hz : z ≠ 0) :
    Differentiable ℂ (fun a => upperIncGamma a z) := by
  sorry

/-- Meromorphic parameter dependence away from the listed poles. -/
theorem lowerIncGamma_parameter_analytic {a z : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (hz : z ≠ 0) :
    AnalyticAt ℂ (fun b => lowerIncGamma b z) a := by
  sorry

/-- Simple parameter poles and their residues in DLMF §8.2(ii). -/
theorem lowerIncGamma_parameter_residue (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun a : ℂ => (a+n)*lowerIncGamma a z) (𝓝[≠] (-(n : ℂ))) (𝓝 ((-1 : ℂ)^n/n.factorial)) := by
  sorry

/-- lowerIncGammaOnLog monodromy. -/
@[dlmf 8.2.E8]
theorem lowerIncGammaOnLog_monodromy (w : ℂ) (m : ℤ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) :
    lowerIncGammaOnLog a (w+2*π*m*I)=exp (2*π*m*I*a)*lowerIncGammaOnLog a w := by
  sorry

/-- upperIncGammaOnLog monodromy. -/
@[dlmf 8.2.E9]
theorem upperIncGammaOnLog_monodromy (w : ℂ) (m : ℤ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) :
    upperIncGammaOnLog a (w+2*π*m*I)=exp (2*π*m*I*a)*upperIncGammaOnLog a w+(1-exp (2*π*m*I*a))*Gamma a := by
  sorry

/-- upperIncGammaOnLog monodromy limit. -/
@[dlmf 8.2.E9]
theorem upperIncGammaOnLog_monodromy_limit (w : ℂ) (m : ℤ) (n : ℕ) :
    Tendsto (fun a : ℂ => exp (2*π*m*I*a)*upperIncGammaOnLog a w+(1-exp (2*π*m*I*a))*Gamma a) (𝓝[≠] (-(n : ℂ))) (𝓝 (upperIncGammaOnLog (-n) (w+2*π*m*I))) := by
  sorry

/-- upperIncGammaOnLog jump. -/
@[dlmf 8.2.E10]
theorem upperIncGammaOnLog_jump (a w : ℂ) :
    exp (-π*I*a)*upperIncGammaOnLog a (w+π*I)-exp (π*I*a)*upperIncGammaOnLog a (w-π*I) = -2*π*I/Gamma (1-a) := by
  sorry

/-- upperIncGammaOnLog halfTurn. -/
@[dlmf 8.2.E11]
theorem upperIncGammaOnLog_halfTurn (w : ℂ) {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    upperIncGammaOnLog a (w+ε*π*I)=Gamma a*(1-exp (a*w+ε*π*I*a)*scIncGamma a (-exp w)) := by
  sorry

/-- lower upperIncGamma ode. -/
@[dlmf 8.2.E12]
theorem lower_upperIncGamma_ode {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    (∀ f ∈ ({lowerIncGamma a,upperIncGamma a} : Set (ℂ → ℂ)), deriv (deriv f) z+(1+(1-a)/z)*deriv f z=0) := by
  sorry

/-- upperIncGamma scaled ode. -/
@[dlmf 8.2.E13]
theorem upperIncGamma_scaled_ode (a : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    let w := fun t => exp t*t^(1-a)*upperIncGamma a t; deriv (deriv w) z-(1+(1-a)/z)*deriv w z+(1-a)/z^2*w z=0 := by
  sorry

/-- scIncGamma ode. -/
@[dlmf 8.2.E14]
theorem scIncGamma_ode (a z : ℂ) :
    z*deriv (deriv (scIncGamma a)) z+(a+1+z)*deriv (scIncGamma a) z+a*scIncGamma a z=0 := by
  sorry

end AAR.Confluent
