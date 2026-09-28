/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Disk and triangle orthogonal polynomials

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.37.E6]
def diskPolynomial (α : ℂ) (m n : ℕ) (z : ℂ) : ℂ :=
  ∑ j ∈ Finset.range (min m n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
    poch (-(m : ℂ)) j * poch (-(n : ℂ)) j /
    (poch (α + 1) m * poch (α + 1) n * j.factorial) * z ^ (m - j) * star z ^ (n - j)

/-- Triangle polynomials: the meaningful degree range is `n ≤ m`. The product
at `x = 0` is used only off the boundary in the integral statements below. -/
@[dlmf 18.37.E7]
def trianglePolynomial (α β γ : ℂ) (m n : ℕ) (x y : ℂ) : ℂ :=
  jacobiP α (β + γ + 2 * n + 1) (m - n) (2 * x - 1) * x ^ n *
    jacobiP β γ n (2 * y / x - 1)

@[dlmf 18.37.E1]
theorem diskPolynomial_polar {α : ℝ} (hα : -1 < α) (m n : ℕ) (r θ : ℝ) (hr : 0 ≤ r) :
    diskPolynomial α m n ((r : ℂ) * exp (I * θ)) =
      exp (I * ((m : ℂ) - n) * θ) * (r : ℂ) ^ (Int.natAbs ((m : ℤ) - n)) *
      jacobiP α (Int.natAbs ((m : ℤ) - n)) (min m n) (2 * (r : ℂ) ^ 2 - 1) /
      jacobiP α (Int.natAbs ((m : ℤ) - n)) (min m n) 1 := by
  sorry

@[dlmf 18.37.E5]
theorem diskPolynomial_at_one {α : ℂ} (hα : -1 < α.re) (m n : ℕ) : diskPolynomial α m n 1 = 1 := by
  sorry

@[dlmf 18.37.E2]
theorem diskPolynomial_orthogonal {α : ℝ} (hα : -1 < α) (m n j k : ℕ) (hne : (m, n) ≠ (j, k)) :
    ∫ p : ℝ × ℝ in {p | p.1 ^ 2 + p.2 ^ 2 < 1},
      diskPolynomial α m n (p.1 + I * p.2) * diskPolynomial α j k (p.1 - I * p.2) *
        (Real.rpow (1 - p.1 ^ 2 - p.2 ^ 2) α : ℂ) = 0 := by
  sorry

@[dlmf 18.37.E8]
theorem trianglePolynomial_orthogonal {α β γ : ℝ} (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ)
    {m n j k : ℕ} (hn : n ≤ m) (hk : k ≤ j) (hne : (m, n) ≠ (j, k)) :
    ∫ p : ℝ × ℝ in {p | 0 < p.2 ∧ p.2 < p.1 ∧ p.1 < 1},
      trianglePolynomial α β γ m n p.1 p.2 * trianglePolynomial α β γ j k p.1 p.2 *
      (Real.rpow (1 - p.1) α * Real.rpow (p.1 - p.2) β * Real.rpow p.2 γ : ℝ) = 0 := by
  sorry


end AAR.OrthogonalPolynomials
