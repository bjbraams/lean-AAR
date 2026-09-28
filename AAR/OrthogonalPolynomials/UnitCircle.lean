/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.QSeries.Pochhammer
/-!
# Orthogonal polynomials on the unit circle

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

/-- Reverse-conjugation at a specified degree; meaningful even if the constant
coefficient vanishes. -/
@[dlmf 18.33.E22]
def reflectedPolynomial (n : ℕ) (p : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (star (p.coeff (n - k))) * X ^ k

/-- Monic orthogonal polynomials for a probability measure supported on the unit
circle. Positive norms in every degree exclude finite support. -/
@[dlmf 18.33.E17]
def IsUnitCircleOP (μ : Measure ℂ) (p : ℕ → ℂ[X]) : Prop :=
  IsProbabilityMeasure μ ∧ (∀ᵐ z ∂μ, ‖z‖ = 1) ∧
    (∀ n, (p n).Monic ∧ (p n).natDegree = n) ∧
    (∀ n, Integrable (fun z => ‖(p n).eval z‖ ^ 2) μ) ∧
    (∀ n, 0 < ∫ z, ‖(p n).eval z‖ ^ 2 ∂μ) ∧
    ∀ m n, m ≠ n → ∫ z, (p m).eval z * star ((p n).eval z) ∂μ = 0

@[dlmf 18.33.E25]
def verblunskyCoefficient (p : ℕ → ℂ[X]) (n : ℕ) : ℂ := -star ((p (n + 1)).eval 0)

@[dlmf 18.33.E13]
def szegoAskey (lam : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (lam + 1) k * poch lam (n - k) /
    ((k.factorial : ℂ) * (n - k).factorial) * z ^ k

@[dlmf 18.33.E15]
def szegoAskeyQ (a q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), qPochhammer (a * q ^ 2) (q ^ 2) k *
    qPochhammer a (q ^ 2) (n - k) / (qPochhammer (q ^ 2) (q ^ 2) k *
      qPochhammer (q ^ 2) (q ^ 2) (n - k)) * (z / q) ^ k

@[dlmf 18.33.E23]
theorem szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    p (n + 1) = X * p n - C (star (verblunskyCoefficient p n)) * reflectedPolynomial n (p n) := by
  sorry

@[dlmf 18.33.E24]
theorem szego_reflected_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    reflectedPolynomial (n + 1) (p (n + 1)) = reflectedPolynomial n (p n) -
      C (verblunskyCoefficient p n) * X * p n := by
  sorry

@[dlmf 18.33.E25]
theorem verblunskyCoefficient_norm_lt_one {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    ‖verblunskyCoefficient p n‖ < 1 := by
  sorry

@[dlmf 18.33.E26]
theorem unitCircle_norm_ratio {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    (∫ z, ‖(p (n + 1)).eval z‖ ^ 2 ∂μ) =
      (1 - ‖verblunskyCoefficient p n‖ ^ 2) * ∫ z, ‖(p n).eval z‖ ^ 2 ∂μ := by
  sorry

@[dlmf 18.33.E27]
theorem inverse_szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (1 - ((‖verblunskyCoefficient p n‖ ^ 2 : ℝ) : ℂ)) * X * p n = p (n + 1) +
      C (star (verblunskyCoefficient p n)) * reflectedPolynomial (n + 1) (p (n + 1)) := by
  sorry

@[dlmf 18.33.E28]
theorem inverse_reflected_szego_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (1 - ((‖verblunskyCoefficient p n‖ ^ 2 : ℝ) : ℂ)) * reflectedPolynomial n (p n) =
      reflectedPolynomial (n + 1) (p (n + 1)) + C (verblunskyCoefficient p n) * p (n + 1) := by
  sorry

@[dlmf 18.33.E30]
theorem unitCircle_three_term_recurrence {μ : Measure ℂ} {p : ℕ → ℂ[X]} (h : IsUnitCircleOP μ p) (n : ℕ) :
    C (star (verblunskyCoefficient p n)) * p (n + 2) =
      (C (star (verblunskyCoefficient p (n + 1))) + C (star (verblunskyCoefficient p n)) * X) * p (n + 1) -
      C (star (verblunskyCoefficient p (n + 1)) * (1 - (‖verblunskyCoefficient p n‖ ^ 2 : ℝ))) * X * p n := by
  sorry

@[dlmf 18.33.vi]
theorem verblunsky_theorem (a : ℕ → ℂ) (ha : ∀ n, ‖a n‖ < 1) :
    ∃! μ : Measure ℂ, ∃ p : ℕ → ℂ[X], IsUnitCircleOP μ p ∧ verblunskyCoefficient p = a := by
  sorry

@[dlmf 18.33.E14]
theorem szegoAskey_orthogonal {lam : ℝ} (hlam : -1 / 2 < lam) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskey lam m (exp (I * θ)) *
      star (szegoAskey lam n (exp (I * θ))) * (Real.rpow (1 - Real.cos θ) lam : ℂ) = 0 := by
  sorry

@[dlmf 18.33.E16]
theorem szegoAskeyQ_orthogonal {a q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ha : |a * q| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..(2 * Real.pi), szegoAskeyQ a q m (exp (I * θ)) *
      star (szegoAskeyQ a q n (exp (I * θ))) *
      (‖qPochhammerInf (q * exp (I * θ)) (q ^ 2) / qPochhammerInf (a * q * exp (I * θ)) (q ^ 2)‖ ^ 2 : ℝ) = 0 := by
  sorry


end AAR.OrthogonalPolynomials
