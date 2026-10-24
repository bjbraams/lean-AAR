/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import DLMF.Gamma.QGamma
public import DLMF.Bailey
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# q-elementary functions and Carlitz polynomials (DLMF §17.3)

DLMF scales the two q-exponentials by1−q. Their product definitions retain analytic
continuation, while the series statements below retain their actual convergence domains.
The existing Jackson calculus, shifted factorials and Gaussian polynomial are reused.

The Carlitz Stirling polynomial is defined by its polynomial recurrence, so the values at
q=0 and q=1 are removable extensions rather than totalized0/0 values of the closed formula.
The Eulerian expression likewise uses geometric polynomials at these removable points.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The scaled little q-exponential, including its meromorphic product continuation. -/
@[dlmf 17.3.E1]
def qExp (q x : ℂ) : ℂ := (qPochhammerInf ((1-q)*x) q)⁻¹
/-- The scaled big q-exponential, an entire product in its argument when |q|<1. -/
@[dlmf 17.3.E2]
def qExpBig (q x : ℂ) : ℂ := qPochhammerInf (-(1-q)*x) q
/-- The little q-sine. -/
@[dlmf 17.3.E3]
def qSin (q x : ℂ) : ℂ := (qExp q (I*x)-qExp q (-I*x))/(2*I)
/-- The big q-sine. -/
@[dlmf 17.3.E4]
def qSinBig (q x : ℂ) : ℂ := (qExpBig q (I*x)-qExpBig q (-I*x))/(2*I)
/-- The little q-cosine. -/
@[dlmf 17.3.E5]
def qCos (q x : ℂ) : ℂ := (qExp q (I*x)+qExp q (-I*x))/2
/-- The big q-cosine. -/
@[dlmf 17.3.E6]
def qCosBig (q x : ℂ) : ℂ := (qExpBig q (I*x)+qExpBig q (-I*x))/2
/-- Carlitz's q-Bernoulli expression, with the principal power q^(rx). -/
@[dlmf 17.3.E7]
def qBernoulli (n : ℕ) (x q : ℂ) : ℂ :=
  (1-q)^((1:ℤ)-n)*∑ j∈range (n+1), (-1:ℂ)^j*(n.choose j:ℂ)*
    (j+1:ℂ)/(1-q^(j+1))*q^((j:ℂ)*x)
/-- Carlitz's Eulerian polynomial, using the removable geometric-polynomial q-number. -/
def qEulerian (m s : ℕ) (q : ℂ) : ℂ :=
  q^((DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s).toNat)*
    ∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (m+1) j*
      (∑ k∈range (s-j), q^k)^m
/-- Carlitz's second-kind q-Stirling polynomial, including removable endpoint values. -/
def qStirlingSecond (q : ℂ) : ℕ → ℕ → ℂ
  | 0,0 => 1
  | 0,_+1 => 0
  | _+1,0 => 0
  | m+1,s+1 => qStirlingSecond q m s+(∑ k∈range (s+1), q^k)*qStirlingSecond q m (s+1)
/-- qExp hasSum. -/
@[dlmf 17.3.E1]
theorem qExp_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^n*x^n/qPochhammer q q n) (qExp q x) := by
  sorry

/-- qExpBig hasSum. -/
@[dlmf 17.3.E2]
theorem qExpBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^n*q^(n.choose 2)*x^n/qPochhammer q q n) (qExpBig q x) := by
  sorry

/-- qSin hasSum. -/
@[dlmf 17.3.E3]
theorem qSin_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^(2*n+1)*(-1:ℂ)^n*x^(2*n+1)/qPochhammer q q (2*n+1)) (qSin q x) := by
  sorry

/-- qSinBig hasSum. -/
@[dlmf 17.3.E4]
theorem qSinBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^(2*n+1)*q^(n*(2*n+1))*(-1:ℂ)^n*x^(2*n+1)/qPochhammer q q (2*n+1)) (qSinBig q x) := by
  sorry

/-- qCos hasSum. -/
@[dlmf 17.3.E5]
theorem qCos_hasSum {q x : ℂ} (hq : ‖q‖<1) (hx : ‖(1-q)*x‖<1) : HasSum (fun n : ℕ => (1-q)^(2*n)*(-1:ℂ)^n*x^(2*n)/qPochhammer q q (2*n)) (qCos q x) := by
  sorry

/-- qCosBig hasSum. -/
@[dlmf 17.3.E6]
theorem qCosBig_hasSum {q : ℂ} (hq : ‖q‖<1) (x : ℂ) : HasSum (fun n : ℕ => (1-q)^(2*n)*q^(n*(2*n-1))*(-1:ℂ)^n*x^(2*n)/qPochhammer q q (2*n)) (qCosBig q x) := by
  sorry

/-- qEulerian closed. -/
@[dlmf 17.3.E8]
theorem qEulerian_closed {q : ℂ} (hq1 : q≠1) (m s : ℕ) : qEulerian m s q=q^(DLMF.QSeries.TripleProduct.tri ((s:ℤ)-m)+DLMF.QSeries.TripleProduct.tri s)*(∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q (m+1) j*(1-q^(s-j))^m/(1-q)^m) := by
  sorry

/-- qStirling closed. -/
@[dlmf 17.3.E9]
theorem qStirling_closed {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (m s : ℕ) : qStirlingSecond q m s=q^(-(s.choose 2:ℤ))*(1-q)^s/qPochhammer q q s*(∑ j∈range (s+1), (-1:ℂ)^j*q^(j.choose 2)*qBinom q s j*(1-q^(s-j))^m/(1-q)^m) := by
  sorry

/-- qEulerian polynomial. -/
theorem qEulerian_polynomial (m s : ℕ) : ∃ P : Polynomial ℂ, ∀ q : ℂ, qEulerian m s q=P.eval q := by
  sorry

/-- qStirling polynomial. -/
theorem qStirling_polynomial (m s : ℕ) : ∃ P : Polynomial ℂ, ∀ q : ℂ, qStirlingSecond q m s=P.eval q := by
  sorry

/-- qBernoulli polynomial in qpow. -/
theorem qBernoulli_polynomial_in_qpow {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) : ∃ P : Polynomial ℂ, P.natDegree≤n ∧ ∀ x : ℂ, qBernoulli n x q=P.eval (q^x) := by
  sorry

/-- qBernoulli rational integer argument. -/
theorem qBernoulli_rational_integer_argument (n : ℕ) (x : ℤ) : ∃ P Q : Polynomial ℂ, ∀ q : ℂ, q≠0 → ‖q‖<1 → Q.eval q≠0 ∧ qBernoulli n x q=P.eval q/Q.eval q := by
  sorry

end DLMF.QHypergeometric
