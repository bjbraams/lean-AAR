/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations

/-!
# Voigt functions and their properties, DLMF §7.19

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Voigt U for t>0. -/
@[dlmf 7.19.E1]
def Real.voigtU (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt V for t>0. -/
@[dlmf 7.19.E2]
def Real.voigtV (x t : ℝ) : ℝ :=
  1/Real.sqrt (4*π*t)*(∫ y : ℝ, y*Real.exp (-(x-y)^2/(4*t))/(1+y^2))

/-- Voigt line-broadening profile for a>0. -/
@[dlmf 7.19.E4]
def Real.voigtH (a u : ℝ) : ℝ :=
  a/π*(∫ t : ℝ, Real.exp (-t^2)/((u-t)^2+a^2))

/-- voigt erfc. -/
@[dlmf 7.19.E3]
theorem voigt_erfc (x : ℝ) {t : ℝ} (ht : 0 < t) :
    (Real.voigtU x t : ℂ)+I*Real.voigtV x t=(π/(4*t : ℂ))^(1/2 : ℂ)*exp (((1-I*x)/(2*Real.sqrt t))^2)*erfc ((1-I*x)/(2*Real.sqrt t)) := by
  sorry

/-- Real.voigtH eq voigtU. -/
@[dlmf 7.19.E4]
theorem Real.voigtH_eq_voigtU {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtH a u=Real.voigtU (u/a) (1/(4*a^2))/(a*Real.sqrt π) := by
  sorry

/-- Real.voigt limits. -/
@[dlmf 7.19.E5]
theorem Real.voigt_limits (x : ℝ) :
    Tendsto (Real.voigtU x) (𝓝[>] 0) (𝓝 (1/(1+x^2))) ∧ Tendsto (Real.voigtV x) (𝓝[>] 0) (𝓝 (x/(1+x^2))) := by
  sorry

/-- Real.voigt symmetry. -/
@[dlmf 7.19.E6]
theorem Real.voigt_symmetry (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtU (-x) t=Real.voigtU x t ∧ Real.voigtV (-x) t = -Real.voigtV x t := by
  sorry

/-- Real.voigt bounds. -/
@[dlmf 7.19.E7]
theorem Real.voigt_bounds (x : ℝ) {t : ℝ} (ht : 0 < t) :
    0 < Real.voigtU x t ∧ Real.voigtU x t ≤ 1 ∧ -1 ≤ Real.voigtV x t ∧ Real.voigtV x t ≤ 1 := by
  sorry

/-- Real.voigtV derivative relation. -/
@[dlmf 7.19.E8]
theorem Real.voigtV_derivative_relation (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtV x t=x*Real.voigtU x t+2*t*deriv (fun u => Real.voigtU u t) x := by
  sorry

/-- Real.voigtU derivative relation. -/
@[dlmf 7.19.E9]
theorem Real.voigtU_derivative_relation (x : ℝ) {t : ℝ} (ht : 0 < t) :
    Real.voigtU x t=1-x*Real.voigtV x t-2*t*deriv (fun u => Real.voigtV u t) x := by
  sorry

/-- Real.voigtU fourier laplace. -/
@[dlmf 7.19.E10]
theorem Real.voigtU_fourier_laplace {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtU (u/a) (1/(4*a^2))=a*(∫ t : ℝ in Ioi 0, Real.exp (-a*t-t^2/4)*Real.cos (u*t)) := by
  sorry

/-- Real.voigtV fourier laplace. -/
@[dlmf 7.19.E11]
theorem Real.voigtV_fourier_laplace {a : ℝ} (ha : 0 < a) (u : ℝ) :
    Real.voigtV (u/a) (1/(4*a^2))=a*(∫ t : ℝ in Ioi 0, Real.exp (-a*t-t^2/4)*Real.sin (u*t)) := by
  sorry

end AAR.Confluent
