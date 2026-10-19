/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Asymptotics

/-!
# Mathematical approximation claims in DLMF computational sections

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

/-- DLMF 11.15(ii): existence and stated uniform error, without inventing unpublished coefficients or a degree bound. -/
theorem struveH_polynomial_approximation (n : ℕ) (hn : n ≤ 1) :
    ∃ p : Polynomial ℝ, ∀ x ∈ Icc (0:ℝ) 3, ‖struveH n x-((p.eval x:ℝ):ℂ)‖ ≤ 12/10^9 := by
  sorry

/-- DLMF 11.15(ii): the denominator has no poles on the approximation interval. -/
theorem struveK_rational_approximation (n : ℕ) (hn : n ≤ 1) :
    ∃ p q : Polynomial ℝ, ∀ x : ℝ, 3 ≤ x → q.eval x ≠ 0 ∧ ‖struveK n x-((p.eval x/q.eval x:ℝ):ℂ)‖ ≤ 25/10^9 := by
  sorry

/- DLMF 11.8, 11.13–16 contain bibliographic guidance and numerical
method recommendations. The convergence statements in 11.13(ii) are covered by
the HasSum declarations. No running-time, cancellation, or numerical-stability
bound is inferred from qualitative computational recommendations. Tables in
11.14 are bibliographies of external tables, not numeric tables reproduced in DLMF. -/

end AAR.Struve
