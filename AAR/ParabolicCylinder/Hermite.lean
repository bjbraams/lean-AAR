/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Relations

/-!
# Both Hermite normalizations of cylinder functions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- pcfU physicists hermite. -/
@[dlmf 12.7.E2]
theorem pcfU_physicists_hermite (n : ℕ) (z : ℂ) :
    pcfU (-n-1/2) z=2^(-(n:ℂ)/2)*exp (-z^2/4)*Polynomial.aeval (z/Real.sqrt 2) (AAR.OrthogonalPolynomials.hermitePolyH n) := by
  sorry

/-- pcfV physicists hermite. -/
@[dlmf 12.7.E3]
theorem pcfV_physicists_hermite (n : ℕ) (z : ℂ) :
    pcfV (n+1/2) z=(Real.sqrt (2/π):ℂ)*exp (z^2/4)*(-I)^n*2^(-(n:ℂ)/2)*Polynomial.aeval (I*z/Real.sqrt 2) (AAR.OrthogonalPolynomials.hermitePolyH n) := by
  sorry

end AAR.Confluent
