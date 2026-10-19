/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations

/-!
# Power and spherical Bessel series, DLMF §7.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- hasSum erf complex. -/
@[dlmf 7.6.E1]
theorem hasSum_erf_complex (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*(-1 : ℂ)^n*z^(2*n+1)/((n.factorial : ℂ)*(2*n+1))) (erf z) := by
  sorry

/-- hasSum erf scaled. -/
@[dlmf 7.6.E2]
theorem hasSum_erf_scaled (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*exp (-z^2)*(2 : ℂ)^n*z^(2*n+1)/oddProduct n) (erf z) := by
  sorry

/-- hasSum faddeevaW. -/
@[dlmf 7.6.E3]
theorem hasSum_faddeevaW (z : ℂ) :
    HasSum (fun n : ℕ => (I*z)^n/Gamma ((n : ℂ)/2+1)) (faddeevaW z) := by
  sorry

/-- fresnelCosInt hasSum. -/
@[dlmf 7.6.E4]
theorem fresnelCosInt_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+0)*z^(4*n+1)/((2*n+0).factorial*(4*n+1 : ℂ))) (fresnelCosInt z) := by
  sorry

/-- fresnelSinInt hasSum. -/
@[dlmf 7.6.E6]
theorem fresnelSinInt_hasSum (z : ℂ) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*(π/2)^(2*n+1)*z^(4*n+3)/((2*n+1).factorial*(4*n+3 : ℂ))) (fresnelSinInt z) := by
  sorry

/-- Convergent auxiliary series of DLMF 7.6.5 and 7.6.7. -/
def fresnelAlternateSeries (odd : Bool) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)

/-- fresnelAlternateSeries summable. -/
theorem fresnelAlternateSeries_summable (odd : Bool) (z : ℂ) :
    Summable (fun n : ℕ => (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)) := by
  sorry

/-- fresnelCosInt alternate series. -/
@[dlmf 7.6.E5]
theorem fresnelCosInt_alternate_series (z : ℂ) :
    fresnelCosInt z=cos (π*z^2/2)*fresnelAlternateSeries false z+sin (π*z^2/2)*fresnelAlternateSeries true z := by
  sorry

/-- fresnelSinInt alternate series. -/
@[dlmf 7.6.E7]
theorem fresnelSinInt_alternate_series (z : ℂ) :
    fresnelSinInt z = -cos (π*z^2/2)*fresnelAlternateSeries true z+sin (π*z^2/2)*fresnelAlternateSeries false z := by
  sorry

/-- erf spherical series. -/
@[dlmf 7.6.E8]
theorem erf_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n) (z^2)-sphericalI (2*n+1) (z^2))) (erf z) := by
  sorry

/-- erf chebyshev spherical series. -/
@[dlmf 7.6.E9]
theorem erf_chebyshev_spherical_series {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*exp ((1/2-(a : ℂ)^2)*z^2)*(Polynomial.Chebyshev.T ℝ (2*n+1 : ℤ)).eval a*sphericalI n (z^2/2)) (erf (a*z)) := by
  sorry

/-- fresnelCosInt spherical series. -/
@[dlmf 7.6.E10]
theorem fresnelCosInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+0) (π*z^2/2)) (fresnelCosInt z) := by
  sorry

/-- fresnelSinInt spherical series. -/
@[dlmf 7.6.E11]
theorem fresnelSinInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+1) (π*z^2/2)) (fresnelSinInt z) := by
  sorry

end AAR.Confluent
