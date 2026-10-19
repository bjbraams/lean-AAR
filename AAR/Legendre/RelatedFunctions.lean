/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Hypergeometric
public import Mathlib.Analysis.SpecialFunctions.Arsinh

/-!
# Gegenbauer and Jacobi representations and degree derivatives

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Gegenbauer function at regular parameters; gamma singularities of representations are handled by limits of the complete expression. -/
def gegenbauerFunction (α β z : ℂ) : ℂ :=
  Gamma (α+2*β)*Gamma (β+1/2)/(Gamma (2*β)*Gamma (α+1))*regularizedGaussHG (-α) (α+2*β) (β+1/2) ((1-z)/2)

/-- Jacobi function at regular alpha, with Gauss continuation. -/
def jacobiFunction (α β lam t : ℂ) : ℂ :=
  Gamma (α+1)*regularizedGaussHG ((α+β+1+I*lam)/2) ((α+β+1-I*lam)/2) (α+1) (-(sinh t)^2)

/-- Removable exceptional parameters use the limit of the whole representation. -/
@[dlmf 14.3.E21]
theorem ferrersP_gegenbauer (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun m : ℂ => 2^m*Gamma (1-2*m)*Gamma (ν+m+1)/(Gamma (ν-m+1)*Gamma (1-m)*(1-x^2:ℂ)^(m/2))*gegenbauerFunction (ν+m) (1/2-m) x) (𝓝[≠] μ) (𝓝 (ferrersP ν μ x)) := by
  sorry

/-- Removable exceptional parameters use the limit of the whole representation. -/
@[dlmf 14.3.E22]
theorem associatedP_gegenbauer (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    Tendsto (fun m : ℂ => 2^m*Gamma (1-2*m)*Gamma (ν+m+1)/(Gamma (ν-m+1)*Gamma (1-m)*legendreBranchPower m z)*gegenbauerFunction (ν+m) (1/2-m) z) (𝓝[≠] μ) (𝓝 (associatedP ν μ z)) := by
  sorry

/-- associatedP jacobi. -/
@[dlmf 14.3.E23]
theorem associatedP_jacobi (ν μ : ℂ) {x : ℝ} (hx : 1 < x) :
    Tendsto (fun m : ℂ => 1/Gamma (1-m)*((x+1)/(x-1):ℂ)^(m/2)*jacobiFunction (-m) m (-I*(2*ν+1)) (Real.arsinh (Real.sqrt (x/2-1/2)))) (𝓝[≠] μ) (𝓝 (associatedP ν μ x)) := by
  sorry

/-- The outside-interval degree-derivative series, convergent when abs(1-z) is less than two. -/
def associatedDegreeA (ν μ z : ℂ) : ℂ :=
  sin (ν*π)*exp (μ/2*(log (z+1)-log (z-1)))*∑' k : ℕ, ((1-z)/2)^k*Gamma (k-ν)*Gamma (k+ν+1)/((k.factorial:ℂ)*Gamma (k-μ+1))*(digamma (k+ν+1)-digamma (k-ν))

/-- associatedP degree deriv. -/
@[dlmf 14.11.E1]
theorem associatedP_degree_deriv {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) (μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hdisk : ‖1-z‖ < 2) :
    HasDerivAt (fun ν => associatedP ν μ z) (π*cos (ν*π)/sin (ν*π)*associatedP ν μ z-associatedDegreeA ν μ z/π) ν := by
  sorry

/- DLMF 14.27’s unqualified left-cut zero rule is not admitted: for
ν=1, μ=-1/2 the first-kind function has its only algebraic zero at x=-1/2,
whereas the first listed case predicts one zero in (-∞,-1). This source
claim requires correction or additional hypotheses; see the acquisition ledger. -/

end AAR.Legendre
