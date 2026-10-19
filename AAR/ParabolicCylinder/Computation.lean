/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.WeberUniform

/-!
# Cylinder Chebyshev-series existence claims

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied by the source. -/
theorem pcfU_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam, HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1)) (pcfU a x) := by
  sorry

/-- DLMF 12.20: Chebyshev expansion on a compact interval; coefficients and degree are not supplied by the source. -/
theorem pcfV_chebyshev_compact (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x ∈ Icc (0:ℝ) lam, HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (2*(x:ℂ)/lam-1)) (pcfV a x) := by
  sorry

/-- DLMF 12.20: compactification of the half-line for the recessive solution. -/
theorem pcfU_chebyshev_infinite (a : ℂ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ c : ℕ → ℂ, Summable c ∧ ∀ x : ℝ, lam ≤ x → HasSum (fun k : ℕ => c k*(Polynomial.Chebyshev.T ℂ (k:ℤ)).eval (1-2*(lam:ℂ)/x)) (pcfU a x) := by
  sorry

/- DLMF 12.6 points to a continued-fraction reference without specifying
coefficients; it adds no displayed fraction to acquire. Sections 12.18–21
contain computational references, a bibliography of external tables, the above
Chebyshev existence claims, and software listings. -/

end AAR.Confluent
