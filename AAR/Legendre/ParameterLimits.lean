/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Integrals
public import AAR.Legendre.Connections

/-!
# Removable parameter values in source formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Sine-weighted digamma with its removable values at negative integral degree. -/
def legendreSinDigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => sin (π*v)*digamma (v+1))

/-- Sine-squared-weighted trigamma with removable values. -/
def legendreSinSqTrigamma (ν : ℂ) : ℂ :=
  limUnder (𝓝[≠] ν) (fun v => (sin (π*v))^2*deriv digamma (v+1))

/-- legendreSinDigamma limit. -/
theorem legendreSinDigamma_limit (ν : ℂ) :
    Tendsto (fun v => sin (π*v)*digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinDigamma ν)) := by
  sorry

/-- legendreSinSqTrigamma limit. -/
theorem legendreSinSqTrigamma_limit (ν : ℂ) :
    Tendsto (fun v => (sin (π*v))^2*deriv digamma (v+1)) (𝓝[≠] ν) (𝓝 (legendreSinSqTrigamma ν)) := by
  sorry

/-- ferrersPP integral all degrees. -/
@[dlmf 14.17.E10]
theorem ferrersPP_integral_all_degrees (ν lam : ℂ) (h0 : lam ≠ ν) (h1 : lam ≠ -ν-1) :
    (∫ x : ℝ in -1..1, ferrersP ν 0 x*ferrersP lam 0 x)=2*(2*(sin (π*lam)*legendreSinDigamma ν-sin (π*ν)*legendreSinDigamma lam)+π*sin ((lam-ν)*π))/(π^2*(lam-ν)*(lam+ν+1)) := by
  sorry

/-- ferrersP sq integral all degrees. -/
@[dlmf 14.17.E11]
theorem ferrersP_sq_integral_all_degrees {ν : ℂ} (hν : ν ≠ -1/2) :
    (∫ x : ℝ in -1..1, (ferrersP ν 0 x)^2)=(π^2-2*legendreSinSqTrigamma ν)/(π^2*(ν+1/2)) := by
  sorry

/-- ferrersP negative order parameter limit. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    Tendsto (fun v : ℂ => (-1)^m*Gamma (v-m+1)/Gamma (v+m+1)*ferrersP v m x) (𝓝[≠] ν) (𝓝 (ferrersP ν (-m) x)) := by
  sorry

/-- associatedP negative order parameter limit. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_order_parameter_limit (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    Tendsto (fun v : ℂ => Gamma (v-m+1)/Gamma (v+m+1)*associatedP v m z) (𝓝[≠] ν) (𝓝 (associatedP ν (-m) z)) := by
  sorry

end AAR.Legendre
