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
  sorry

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

/-- The degree statement in the prose of DLMF §8.20(ii). -/
theorem expIntLargeOrderPolynomial_degree {k : ℕ} (hk : 1 ≤ k) :
    (expIntLargeOrderPolynomial k).natDegree=k-1 := by
  sorry

/-- genExpIntE large order uniform. -/
@[dlmf 8.20.E6]
theorem genExpIntE_large_order_uniform (N : ℕ) :
    IsBigO (comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 1 < p.1 ∧ 0 ≤ p.2}) (fun p => exp (p.1*p.2 : ℂ)*(p.2+1)*p.1*genExpIntEExtended p.1 (p.2*p.1)-∑ k ∈ Finset.range N, (expIntLargeOrderPolynomial k).eval (p.2 : ℂ)/(((p.2+1 : ℂ)^(2*k))*(p.1 : ℂ)^k)) (fun p => p.1^(-(N : ℤ))) := by
  sorry

end AAR.Confluent
