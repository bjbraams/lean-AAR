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
  have hnp : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hm := poch_ne_zero_of_not_neg_nat hnp m
  have hn := poch_ne_zero_of_not_neg_nat hnp n
  unfold diskPolynomial
  simp only [one_pow, mul_one, star_one]
  have hsub : ∑ j ∈ Finset.range (min m n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) =
      ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) := by
    apply Finset.sum_subset
    · intro j hj; simp at hj ⊢; omega
    · intro j hj hj'
      simp at hj hj'
      have : m < j := by omega
      rw [poch_neg_nat_eq_zero this]; simp
  rw [hsub]
  have key : ∑ j ∈ Finset.range (n + 1), (-1 : ℂ) ^ j * poch (α + 1) (m + n - j) *
      poch (-(m : ℂ)) j * poch (-(n : ℂ)) j / (poch (α + 1) m * poch (α + 1) n * j.factorial) =
      (∑ j ∈ Finset.range (n + 1), (n.choose j : ℂ) * poch (-(m : ℂ)) j * poch (α + 1 + m) (n - j)) /
        poch (α + 1) n := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hsplit : poch (α + 1) (m + n - j) = poch (α + 1) m * poch (α + 1 + m) (n - j) := by
      rw [show m + n - j = m + (n - j) by omega, poch_add]
    have hpn : poch (-(n : ℂ)) j = (-1) ^ j * (j.factorial * n.choose j : ℕ) := by
      rw [poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose]
    have hf : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hs : ((-1 : ℂ) ^ j) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; simp
    rw [hsplit, hpn]
    push_cast
    field_simp
    linear_combination (poch (α + 1 + m) (n - j) * poch (-(m : ℂ)) j * (n.choose j : ℂ)) * hs
  rw [key, poch_add_binomial, show -(m : ℂ) + (α + 1 + m) = α + 1 by ring, div_self hn]

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
