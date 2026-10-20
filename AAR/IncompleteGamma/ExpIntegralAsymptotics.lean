/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.ExponentialIntegral

/-!
# Generalized exponential integral asymptotics, DLMF §8.20

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- genExpIntE exact remainder. -/
@[dlmf 8.20.E1]
theorem genExpIntE_exact_remainder (p : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    genExpIntE p z=exp (-z)/z*(∑ k ∈ Finset.range N, (-1 : ℂ)^k*poch p k/z^k)+(-1 : ℂ)^N*poch p N/z^N*genExpIntE (N+p) z := by
  induction N with
  | zero => simp [poch]
  | succ N ih =>
    have h := genExpIntE_add_one ((N:ℂ)+p) hz
    rw [show (N:ℂ)+p+1 = ((N+1:ℕ):ℂ)+p by push_cast; ring] at h
    rw [ih, Finset.sum_range_succ, poch_succ, pow_succ, pow_succ]
    have hzN : z^N ≠ 0 := pow_ne_zero _ hz
    set S := ∑ k ∈ Finset.range N, (-1 : ℂ)^k*poch p k/z^k
    field_simp
    linear_combination (-1:ℂ)^N*poch p N*h

/-- genExpIntE log sector asymptotic. -/
@[dlmf 8.20.E2]
theorem genExpIntE_log_sector_asymptotic (p : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*poch p k) (genExpIntEOnLog p) := by
  sorry

/-- genExpIntE extended sector asymptotic. -/
@[dlmf 8.20.E3]
theorem genExpIntE_extended_sector_asymptotic (p : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (comap (fun w : ℂ => Real.exp w.re) atTop ⊓ 𝓟 {w : ℂ | π/2+δ ≤ ε*w.im ∧ ε*w.im ≤ 7*π/2-δ}) (fun k w => exp (-exp w-(k+1 : ℂ)*w)) (fun k => (-1 : ℂ)^k*poch p k) (fun w => genExpIntEOnLog p w-ε*2*π*I/Gamma p*exp (-ε*p*π*I+(p-1)*w)) := by
  sorry

/-- Large-order polynomials A_k(λ), including A₀=1. -/
@[dlmf 8.20.E4]
def expIntLargeOrderPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => (1-Polynomial.C (2*(k : ℂ))*Polynomial.X)*expIntLargeOrderPolynomial k+
      Polynomial.X*(Polynomial.X+1)*(expIntLargeOrderPolynomial k).derivative

/-- expIntLargeOrderPolynomial initial. -/
@[dlmf 8.20.E5]
theorem expIntLargeOrderPolynomial_initial  :
    expIntLargeOrderPolynomial 1=1 ∧ expIntLargeOrderPolynomial 2=1-2*Polynomial.X ∧ expIntLargeOrderPolynomial 3=1-8*Polynomial.X+6*Polynomial.X^2 := by
  norm_num [expIntLargeOrderPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

open Polynomial in
/-- Degree bound and leading coefficient of `A_{m+1}`. -/
lemma expIntLargeOrderPolynomial_succ_degree_coeff (m : ℕ) :
    (expIntLargeOrderPolynomial (m+1)).natDegree ≤ m ∧
      (expIntLargeOrderPolynomial (m+1)).coeff m = (-1 : ℂ)^m*(m+1).factorial := by
  induction m with
  | zero =>
    simp [expIntLargeOrderPolynomial]
  | succ m ih =>
    obtain ⟨hd, hc⟩ := ih
    set A := expIntLargeOrderPolynomial (m+1) with hA
    have hrec : expIntLargeOrderPolynomial (m+1+1) =
        (1-C (2*((m+1:ℕ) : ℂ))*X)*A + X*(X+1)*A.derivative := rfl
    have hAd : A.derivative.natDegree ≤ m - 1 := by
      have := natDegree_derivative_le A; omega
    have hA1 : A.coeff (m+1) = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    rw [hrec]
    constructor
    · refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
      · refine (natDegree_mul_le).trans ?_
        have : (1-C (2*((m+1:ℕ) : ℂ))*X).natDegree ≤ 1 := by
          refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
          exact (natDegree_C_mul_le _ _).trans (by simp)
        omega
      · rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          rw [derivative_of_natDegree_zero (by omega)]
          simp
        · refine (natDegree_mul_le).trans ?_
          have : (X*(X+1) : ℂ[X]).natDegree ≤ 2 := by
            refine (natDegree_mul_le).trans ?_
            have : (X+1 : ℂ[X]).natDegree ≤ 1 := (natDegree_add_le _ _).trans (by simp)
            have : (X : ℂ[X]).natDegree ≤ 1 := by simp
            omega
          omega
    · have he : (1-C (2*((m+1:ℕ) : ℂ))*X)*A + X*(X+1)*A.derivative =
          A - C (2*((m+1:ℕ) : ℂ))*(X*A) + X*(X*A.derivative) + X*A.derivative := by ring
      rw [he, coeff_add, coeff_add, coeff_sub, coeff_C_mul, coeff_X_mul, coeff_X_mul,
        coeff_X_mul, coeff_derivative, hA1, hc]
      have hmid : (X*A.derivative).coeff m = (m : ℂ)*((-1 : ℂ)^m*(m+1).factorial) := by
        rcases m with _ | k
        · simp
        · rw [coeff_X_mul, coeff_derivative, hc]; push_cast; ring
      rw [hmid, Nat.factorial_succ (m+1)]
      push_cast
      ring

/-- The degree statement in the prose of DLMF §8.20(ii). -/
theorem expIntLargeOrderPolynomial_degree {k : ℕ} (hk : 1 ≤ k) :
    (expIntLargeOrderPolynomial k).natDegree=k-1 := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k-1, by omega⟩
  obtain ⟨hd, hc⟩ := expIntLargeOrderPolynomial_succ_degree_coeff m
  rw [Nat.add_sub_cancel]
  refine Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hd ?_
  rw [hc]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num)) (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- genExpIntE large order uniform. -/
@[dlmf 8.20.E6]
theorem genExpIntE_large_order_uniform (N : ℕ) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.1 ∧ 0 ≤ p.2}) (fun p => exp (p.1*p.2 : ℂ)*(p.2+1)*p.1*genExpIntEExtended p.1 (p.2*p.1)-∑ k ∈ Finset.range N, (expIntLargeOrderPolynomial k).eval (p.2 : ℂ)/(((p.2+1 : ℂ)^(2*k))*(p.1 : ℂ)^k)) (fun p => p.1^(-(N : ℤ))) := by
  sorry

end AAR.Confluent
