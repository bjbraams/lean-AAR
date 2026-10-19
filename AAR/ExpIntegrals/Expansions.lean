/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ExpIntegrals.Continuation

/-!
# Power, inverse factorial and spherical Bessel series, DLMF §§6.6 and 6.10–6.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Real.hasSum expIntEi. -/
@[dlmf 6.6.E1]
theorem Real.hasSum_expIntEi {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => x^(k+1)/((k+1).factorial*(k+1 : ℝ))) (Real.expIntEi x - Real.eulerMascheroniConstant - Real.log x) := by
  sorry

/-- expIntE1 hasSum. -/
@[dlmf 6.6.E2]
theorem expIntE1_hasSum {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-z)^(k+1)/((k+1).factorial*(k+1 : ℂ))) (-genExpIntE 1 z - Real.eulerMascheroniConstant - log z) := by
  sorry

/-- expIntE1 digamma series. -/
@[dlmf 6.6.E3]
theorem expIntE1_digamma_series {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => z^k/(k.factorial : ℂ)*digamma (k+1)) (exp z*(genExpIntE 1 z+log z)) := by
  sorry

/-- hasSum Ein complex. -/
@[dlmf 6.6.E4]
theorem hasSum_Ein_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(k+1)/((k+1).factorial*(k+1 : ℂ))) (expIntEin z) := by
  sorry

/-- hasSum Si complex. -/
@[dlmf 6.6.E5]
theorem hasSum_Si_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^k*z^(2*k+1)/((2*k+1).factorial*(2*k+1 : ℂ))) (sinInt z) := by
  sorry

/-- hasSum Ci complex. -/
@[dlmf 6.6.E6]
theorem hasSum_Ci_complex (z : ℂ) :
    HasSum (fun k : ℕ => (-1 : ℂ)^(k+1)*z^(2*k+2)/((2*k+2).factorial*(2*k+2 : ℂ))) (cosInt z-Real.eulerMascheroniConstant-log z) := by
  sorry

/-- Inverse factorial coefficients, with the recurrence of DLMF 6.10.3. -/
@[dlmf 6.10.E3]
def expIntInverseFactorialCoeff : ℕ → ℂ
  | 0 => 1
  | k+1 => -∑ j ∈ Finset.range (k+1), expIntInverseFactorialCoeff (k-j) / (j+1 : ℂ)
termination_by k => k

/-- expIntInverseFactorialCoeff initial. -/
@[dlmf 6.10.E2]
theorem expIntInverseFactorialCoeff_initial  :
    ∀ k < 5, expIntInverseFactorialCoeff k = ([1,-1,1/2,-1/3,1/6] : List ℂ)[k]! := by
  intro k hk
  interval_cases k <;> norm_num [expIntInverseFactorialCoeff, Finset.sum_range_succ]

/-- expIntE1 inverse factorial series. -/
@[dlmf 6.10.E1]
theorem expIntE1_inverse_factorial_series {z : ℂ} (hz : 0 < z.re) :
    HasSum (fun k : ℕ => (k.factorial : ℂ)*expIntInverseFactorialCoeff k / poch z (k+1)) (exp z*genExpIntE 1 z) := by
  sorry

/-- Spherical-Bessel expansion coefficients. -/
@[dlmf 6.10.E7]
def expIntSphericalCoeff (n : ℕ) : ℂ :=
  (2*n+1 : ℂ)*(1-(-1 : ℂ)^n+digamma (n+1)-digamma 1)

/-- sinInt spherical series. -/
@[dlmf 6.10.E4]
theorem sinInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ n (z/2)^2) (sinInt z) := by
  sorry

/-- cosIntCin spherical series. -/
@[dlmf 6.10.E5]
theorem cosIntCin_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => expIntSphericalCoeff (n+1)*sphericalJ (n+1) (z/2)^2) (cosIntCin z) := by
  sorry

/-- expIntEi spherical series. -/
@[dlmf 6.10.E6]
theorem expIntEi_spherical_series {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℕ => (-1 : ℂ)^n*((x : ℂ)-expIntSphericalCoeff n)*sphericalI n (x/2)^2) ((Real.expIntEi x : ℂ)-Real.eulerMascheroniConstant-Real.log |x|) := by
  sorry

/-- Ein spherical series. -/
@[dlmf 6.10.E8]
theorem Ein_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*exp (-z/2)*(2*(n+1)+1 : ℂ)/((n+1 : ℂ)*(n+2))*sphericalI (n+1) (z/2)) (expIntEin z-z*exp (-z/2)*sphericalI 0 (z/2)) := by
  sorry

/-- expIntE1 eq upperIncGamma. -/
@[dlmf 6.11.E1]
theorem expIntE1_eq_upperIncGamma {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = upperIncGamma 0 z := by
  simp [genExpIntE]

/-- expIntE1 eq kummerU. -/
@[dlmf 6.11.E2]
theorem expIntE1_eq_kummerU {z : ℂ} (hz : z ≠ 0) :
    genExpIntE 1 z = exp (-z)*kummerU 1 1 z := by
  simpa only [show (2 : ℂ)-1=1 by norm_num] using genExpIntE_eq_exp_mul_kummerU 1 hz

/-- expIntAux eq kummerU. -/
@[dlmf 6.11.E3]
theorem expIntAux_eq_kummerU {z : ℂ} (hz : 0 < z.re) :
    expIntAuxG z+I*expIntAuxF z = kummerU 1 1 (-I*z) := by
  sorry

end AAR.Confluent
