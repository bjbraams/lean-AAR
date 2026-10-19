/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.DLMF.Framework
public import AAR.Bessel.SecondKind

/-!
# Struve functions: definitions, convergence and differential equations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel

/-- Reciprocal gamma coefficients; zeros of reciprocal gamma retain exceptional orders. -/
def struveCoeff (ν : ℂ) (n : ℕ) : ℂ :=
  1 / (Gamma (n+3/2) * Gamma (n+ν+3/2))

/-- Entire normalized Struve series. -/
def struveHCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1)^n * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve H function. -/
@[dlmf 11.2.E1]
def struveH (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveHCore ν z

/-- Continuation on the logarithmic plane. -/
def struveHOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveHCore ν (exp w)

/-- Absolute convergence of the defining series, including exceptional orders. -/
@[dlmf 11.2.E1]
theorem hasSum_struveHCore (ν z : ℂ) :
    HasSum (fun n : ℕ => (-1)^n * (z/2)^(2*n) * struveCoeff ν n) (struveHCore ν z) := by
  sorry

/-- The normalized function is entire in the argument. -/
theorem entire_struveHCore (ν : ℂ) :
    Differentiable ℂ (struveHCore ν) := by
  sorry

/-- The normalized function is entire in the order. -/
theorem entire_order_struveHCore (z : ℂ) :
    Differentiable ℂ (fun ν => struveHCore ν z) := by
  sorry

/-- Continuation with inherited logarithm, not reapplication of a principal power. -/
@[dlmf 11.4.E16]
theorem struveHOnLog_shift (ν w : ℂ) (m : ℤ) :
    struveHOnLog ν (w+m*π*I) = exp (m*π*I*(ν+1))*struveHOnLog ν w := by
  sorry

/-- Entire normalized Struve series. -/
def struveLCore (ν z : ℂ) : ℂ :=
  ∑' n : ℕ, 1 * (z/2)^(2*n) * struveCoeff ν n

/-- Principal Struve L function. -/
@[dlmf 11.2.E2]
def struveL (ν z : ℂ) : ℂ :=
  (z/2)^(ν+1) * struveLCore ν z

/-- Continuation on the logarithmic plane. -/
def struveLOnLog (ν w : ℂ) : ℂ :=
  exp ((ν+1)*(w-log 2)) * struveLCore ν (exp w)

/-- Absolute convergence of the defining series, including exceptional orders. -/
@[dlmf 11.2.E2]
theorem hasSum_struveLCore (ν z : ℂ) :
    HasSum (fun n : ℕ => 1 * (z/2)^(2*n) * struveCoeff ν n) (struveLCore ν z) := by
  sorry

/-- The normalized function is entire in the argument. -/
theorem entire_struveLCore (ν : ℂ) :
    Differentiable ℂ (struveLCore ν) := by
  sorry

/-- The normalized function is entire in the order. -/
theorem entire_order_struveLCore (z : ℂ) :
    Differentiable ℂ (fun ν => struveLCore ν z) := by
  sorry

/-- Continuation with inherited logarithm, not reapplication of a principal power. -/
@[dlmf 11.4.E17]
theorem struveLOnLog_shift (ν w : ℂ) (m : ℤ) :
    struveLOnLog ν (w+m*π*I) = exp (m*π*I*(ν+1))*struveLOnLog ν w := by
  sorry

/-- struveK. -/
@[dlmf 11.2.E5]
def struveK (ν z : ℂ) : ℂ :=
  struveH ν z - besselY ν z

/-- struveM. -/
@[dlmf 11.2.E6]
def struveM (ν z : ℂ) : ℂ :=
  struveL ν z - besselI ν z

/-- struveEquation. -/
@[dlmf 11.2.E7, dlmf 11.2.E9]
def struveEquation (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  iteratedDeriv 2 f z + deriv f z/z + ((if modified then -1 else 1)-ν^2/z^2)*f z = (z/2)^(ν-1)/(Real.sqrt π*Gamma (ν+1/2))

/-- struveH ode. -/
@[dlmf 11.2.E8]
theorem struveH_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν false (struveH ν) z := by
  sorry

/-- struveK ode. -/
@[dlmf 11.2.E8]
theorem struveK_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν false (struveK ν) z := by
  sorry

/-- struveL ode. -/
@[dlmf 11.2.E10]
theorem struveL_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν true (struveL ν) z := by
  sorry

/-- struveM ode. -/
@[dlmf 11.2.E10]
theorem struveM_ode (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveEquation ν true (struveM ν) z := by
  sorry

/-- IsStruveSolutionOn. -/
def IsStruveSolutionOn (ν : ℂ) (modified : Bool) (f : ℂ → ℂ) (S : Set ℂ) : Prop :=
  AnalyticOnNhd ℂ f S ∧ ∀ z ∈ S, struveEquation ν modified f z

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E11]
theorem struve_general_solution_11 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*besselY ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E12]
theorem struve_general_solution_12 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveK ν z + A*besselJ ν z + B*besselY ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E13]
theorem struve_general_solution_13 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*hankelH1 ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E14]
theorem struve_general_solution_14 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveH ν z + A*besselJ ν z + B*hankelH2 ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E15]
theorem struve_general_solution_15 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν false f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveK ν z + A*hankelH1 ν z + B*hankelH2 ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E16]
theorem struve_general_solution_16 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν true f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveL ν z + A*besselK ν z + B*besselI ν z := by
  sorry

/-- General analytic solutions on the principal slit plane; numerical stability is not asserted. -/
@[dlmf 11.2.E17]
theorem struve_general_solution_17 (ν : ℂ) (f : ℂ → ℂ) :
    IsStruveSolutionOn ν true f slitPlane ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z = struveM ν z + A*besselK ν z + B*besselI ν z := by
  sorry

/-- struveH zero order series. -/
@[dlmf 11.2.E3]
theorem struveH_zero_order_series (z : ℂ) :
    HasSum (fun n : ℕ => 2/π * (-1)^n * z^(2*n+1)/(oddProduct n)^2) (struveH 0 z) := by
  sorry

/-- struveL zero order series. -/
@[dlmf 11.2.E4]
theorem struveL_zero_order_series (z : ℂ) :
    HasSum (fun n : ℕ => 2/π * 1 * z^(2*n+1)/(oddProduct n)^2) (struveL 0 z) := by
  sorry

end AAR.Struve
