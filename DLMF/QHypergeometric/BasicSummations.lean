/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import DLMF.QHypergeometric.Calculus
public import DLMF.Gamma.QGamma
public import ToMathlib.Analysis.Complex.SeparatingContour
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Low-order basic hypergeometric functions (DLMF §§17.5–17.6)

The series retain DLMF's integer phase exponents. Literal product quotients are used only
where their denominators are nonzero; cancelled product forms and removable-limit statements
retain exceptional upper parameters. Finite identities require lower-parameter regularity
only through the final retained term. Continuation is separate from totalized divergent sums.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- The product quotient giving the meromorphic continuation of one-phi-zero on its regular set. -/
def qOnePhiZeroContinuation (a q z : ℂ) : ℂ := qPochhammerInf (a*z) q/qPochhammerInf z q
/-- The Jackson expression in Heine's integral, kept separate from its removable parameter values. -/
def qHeineJacksonValue (q : ℝ) (a b c z : ℂ) : ℂ :=
  qGamma q c/(qGamma q b*qGamma q (c-b))*
    jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a)
/-- The integrand in the Mellin–Barnes representation of two-phi-one. -/
def qHeineBarnesKernel (a b c q z s : ℂ) : ℂ :=
  qPochhammerListInf [q^(1+s),c*q^s] q/qPochhammerListInf [a*q^s,b*q^s] q*
    π*(-z)^s/Complex.sin (π*s)
/-- The denominator-pole set on the logarithmic q-plane in the Barnes representation. -/
def qHeineBarnesLeft (a b q : ℂ) : Set ℂ :=
  {s | qPochhammerListInf [a*q^s,b*q^s] q=0}
/-- The nonnegative-integer poles belonging to the right side of the Barnes contour. -/
def qHeineBarnesRight : Set ℂ := Set.range (fun n : ℕ => (n:ℂ))

/-- The shared integer triangular exponent agrees with n-choose-two on nonnegative indices. -/
lemma qTri_nat (n : ℕ) : DLMF.QSeries.TripleProduct.tri n=(n.choose 2:ℤ) := by
  simpa using (DLMF.QSeries.TripleProduct.tri_sub_cast n 0).symm
/-- zero phi zero. -/
@[dlmf 17.5.E1]
theorem zero_phi_zero {q : ℂ} (hq : ‖q‖<1) (z : ℂ) : qPhi [] [] q z=qPochhammerInf z q := by
  calc
    qPhi [] [] q z=∑' n : ℕ, q^(n.choose 2)*(-z)^n/qPochhammer q q n := by
      unfold qPhi
      apply tsum_congr
      intro n
      change (1/(1*qPochhammer q q n))*
        (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^(1:ℤ))*z^n=
          q^(n.choose 2)*(-z)^n/qPochhammer q q n
      rw [qTri_nat,zpow_natCast,zpow_one,neg_pow]
      ring
    _ = _ := by simpa using tsum_qExp hq (-z)

/-- one phi zero. -/
@[dlmf 17.5.E2]
theorem one_phi_zero {a q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) :
    qPhi [a] [] q z=qPochhammerInf (a*z) q/qPochhammerInf z q := by
  rw [qPhi_eq_basicHG (by simp)]
  simpa [basicHG] using (q_binomial_theorem (a := a) hq hz).symm

/-- one phi zero terminating. -/
@[dlmf 17.5.E3]
theorem one_phi_zero_terminating {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (z : ℂ) (n : ℕ) :
    qPhi [q^(-(n:ℤ))] [] q z=qPochhammer (z*q^(-(n:ℤ))) q n := by
  sorry

/-- one phi zero upper zero. -/
@[dlmf 17.5.E4]
theorem one_phi_zero_upper_zero {q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) :
    qPhi [0] [] q z=(qPochhammerInf z q)⁻¹ := by
  rw [one_phi_zero hq hz]
  simp [qPochhammerInf]

/-- one phi one sum. -/
@[dlmf 17.5.E5]
theorem one_phi_one_sum {a c q : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hc : qDenominatorRegular [c] q) :
    qPhi [a] [c] q (c/a)=qPochhammerInf (c/a) q/qPochhammerInf c q := by
  sorry

/-- one phi zero continuation analytic. -/
theorem one_phi_zero_continuation_analytic {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} := by
  sorry

/-- Common product zeros have a removable germ, rather than the quotient totalization0/0. -/
theorem one_phi_zero_common_zeros_removable {a q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hd : qPochhammerInf z q=0) (hn : qPochhammerInf (a*z) q=0) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F U ∧
      ∀ w∈U, qPochhammerInf w q≠0 → F w=qOnePhiZeroContinuation a q w := by
  sorry

/-- q gauss. -/
@[dlmf 17.6.E1]
theorem q_gauss {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖c‖<‖a*b‖)
    (hc : qDenominatorRegular [c] q) :
    qPhi [a,b] [c] q (c/(a*b))=qPochhammerListInf [c/a,c/b] q/qPochhammerListInf [c,c/(a*b)] q := by
  sorry

/-- q chu vandermonde first. -/
@[dlmf 17.6.E2]
theorem q_chu_vandermonde_first {a c q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : qDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q (c*q^n/a)=qPochhammer (c/a) q n/qPochhammer c q n := by
  sorry

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.6.E3]
theorem q_chu_vandermonde_second {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hc : qDenominatorRegularThrough [c] q n) :
    qPhi [a,q^(-(n:ℤ))] [c] q q=((range n).prod (fun j => a-c*q^j))/qPochhammer c q n := by
  sorry

/-- The cancelled product form retains b=±q^(-m) whenever the left series is regular. -/
@[dlmf 17.6.E4]
theorem q_even_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q‖<‖b^2‖)
    (hc : qDenominatorRegular [c] (q^2)) :
    qPhi [b^2,b^2/c] [c] (q^2) (c*q/b^2)=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
         qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  sorry

/-- q odd heine. -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine {b c q : ℂ} (hb : b≠0) (hc0 : c≠0) (hq : ‖q‖<1) (hz : ‖c*q^3‖<‖b^2‖)
    (hc : qDenominatorRegular [c*q^2] (q^2))
    (hd : qPochhammerInf (c*q/b^2) (q^2)≠0) :
    qPhi [b^2,b^2/c] [c*q^2] (q^2) (c*q^3/b^2)=
      qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
        (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
         qPochhammerInf b q*qPochhammerInf (-c*q/b) q) := by
  sorry

/-- The only additional common product zero inside the stated convergence domain is handled as a removable limit. -/
@[dlmf 17.6.E4_5]
theorem q_odd_heine_removable {b q : ℂ} (hb : b≠0) (hq0 : q≠0) (hq : ‖q‖<1)
    (hc : qDenominatorRegular [b^2*q] (q^2)) :
    Tendsto (fun c : ℂ => qPochhammerInf q (q^2)/(2*b*qPochhammerListInf [c*q^2,c*q/b^2] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c*q/b) q-
       qPochhammerInf b q*qPochhammerInf (-c*q/b) q))
      (𝓝[≠] (b^2/q)) (𝓝 (qPhi [b^2,q] [b^2*q] (q^2) (q^2))) := by
  sorry

/-- q bailey daum. -/
@[dlmf 17.6.E5]
theorem q_bailey_daum {a b q : ℂ} (hq : ‖q‖<1) (hb : ‖q‖<‖b‖)
    (hc : qDenominatorRegular [a*q/b] q) :
    qPhi [a,b] [a*q/b] q (-q/b)=qPochhammerInf (-q) q*
      qPochhammerListInf [a*q,a*q^2/b^2] (q^2)/qPochhammerListInf [-q/b,a*q/b] q := by
  sorry

/-- heine first. -/
@[dlmf 17.6.E6]
theorem heine_first {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1) (hb0 : b≠0)
    (hc : qDenominatorRegular [c,a*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,a*z] q/qPochhammerListInf [c,z] q*
      qPhi [c/b,z] [a*z] q b := by
  rw [qPhi_eq_basicHG (by simp),qPhi_eq_basicHG (by simp)]
  simpa [qPochhammerListInf] using DLMF.QSeries.heine_transformation hq hz hb hb0
    (hc c (by simp)) (hc (a*z) (by simp))

/-- heine second. -/
@[dlmf 17.6.E7]
theorem heine_second {a b c q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0) (hcb : ‖c‖<‖b‖)
    (hc : qDenominatorRegular [c,b*z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [c/b,b*z] q/qPochhammerListInf [c,z] q*
      qPhi [a*b*z/c,b] [b*z] q (c/b) := by
  sorry

/-- heine third. -/
@[dlmf 17.6.E8]
theorem heine_third {a b c q z : ℂ} (ha : a≠0) (hb : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc0 : c≠0) (habz : ‖a*b*z‖<‖c‖) (hc : qDenominatorRegular [c] q) :
    qPhi [a,b] [c] q z=qPochhammerInf (a*b*z/c) q/qPochhammerInf z q*
      qPhi [c/a,c/b] [c] q (a*b*z/c) := by
  sorry

/-- heine fine expansion. -/
@[dlmf 17.6.E9]
theorem heine_fine_expansion {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [b*q,a*z*q^2/b,a*q/b] q) :
    qPhi [q,a*q] [b*q] q z= -(1-b)*(a*q/b)/(1-a*q/b)*
      (∑' n : ℕ, qPochhammerList [a*q,a*z*q/b] q n*q^n/qPochhammer (a*z*q^2/b) q n)+
      qPochhammerListInf [a*q,a*z*q/b] q/qPochhammerInf (a*q/b) q*qPhi [q,0] [b*q] q z := by
  sorry

/-- heine fine expansion second. -/
@[dlmf 17.6.E10]
theorem heine_fine_expansion_second {a b q z : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=
      ∑' n : ℕ, qPochhammer (b/a) q n*(-a*z)^n*q^((n*(n+1))/2)/qPochhammerList [b*q,z*q] q n := by
  sorry

/-- heine fine expansion third. -/
@[dlmf 17.6.E11]
theorem heine_fine_expansion_third {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hb : ‖b‖<1)
    (hd : qDenominatorRegular [b*q,a*q/b] q) :
    (1-z)/(1-b)*qPhi [q,a*q] [b*q] q z=
      (∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n)*b^n/qPochhammerList [z*q,a*q/b] q n)-
      a*q*∑' n : ℕ, qPochhammer (a*q) q n*qPochhammer (a*z*q/b) q (2*n+1)*(b*q)^n/
        (qPochhammer (z*q) q n*qPochhammer (a*q/b) q (n+1)) := by
  sorry

/-- heine fine expansion fourth. -/
@[dlmf 17.6.E12]
theorem heine_fine_expansion_fourth {a b q z : ℂ} (hb0 : b≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [b*q] q) :
    (1-z)*qPhi [q,a*q] [b*q] q z=∑' n : ℕ,
      qPochhammerList [a*q,a*z*q/b] q n/qPochhammerList [b*q,z*q] q n*
        (1-a*z*q^(2*n+1))*(b*z)^n*q^(n*n) := by
  sorry

/-- heine nonterminating sum. -/
@[dlmf 17.6.E13]
theorem heine_nonterminating_sum {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc0 : c≠0)
    (hd : qDenominatorRegular [c,q^2/c,c/q,a*q/c,b*q/c] q) :
    qPhi [a,b] [c] q q+qPochhammerListInf [q/c,a,b] q/qPochhammerListInf [c/q,a*q/c,b*q/c] q*
      qPhi [a*q/c,b*q/c] [q^2/c] q q=qPochhammerListInf [q/c,a*b*q/c] q/qPochhammerListInf [a*q/c,b*q/c] q := by
  sorry

/-- heine mixed base. -/
@[dlmf 17.6.E14]
theorem heine_mixed_base {a b q z : ℂ} (hq : ‖q‖<1)
    (hd : qDenominatorRegular [a*z*b,b*z] (q^2))
    (hD : qPochhammerListInf [z,a*z*b] (q^2)≠0)
    (hL : Summable (fun n : ℕ => qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n)))
    (hR : Summable (qPhiTerm [a,b] [b*z] (q^2) (z*q))) :
    (∑' n : ℕ, qPochhammer a q n*qPochhammer b (q^2) n*z^n/
      (qPochhammer q q n*qPochhammer (a*z*b) (q^2) n))=
      qPochhammerListInf [a*z,b*z] (q^2)/qPochhammerListInf [z,a*z*b] (q^2)*qPhi [a,b] [b*z] (q^2) (z*q) := by
  sorry

/-- heine connection first. -/
@[dlmf 17.6.E15]
theorem heine_connection_first {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (hbc : ‖b*q‖<‖c‖)
    (hd : qDenominatorRegular [c,c*q/(a*z),q^2/c,a*z/c,q/a,c/q,b*q/c] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [a*b*z/c,q/c] q/qPochhammerListInf [a*z/c,q/a] q*
      qPhi [c/a,c*q/(a*b*z)] [c*q/(a*z)] q (b*q/c)-
      qPochhammerListInf [b,q/c,c/a,a*z/q,q^2/(a*z)] q/
        qPochhammerListInf [c/q,b*q/c,q/a,a*z/c,c*q/(a*z)] q*qPhi [a*q/c,b*q/c] [q^2/c] q z := by
  sorry

/-- heine connection second. -/
@[dlmf 17.6.E16]
theorem heine_connection_second {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (habcz : a*b*c*z≠0) (harg : ‖c*q‖<‖a*b*z‖)
    (hd : qDenominatorRegular [c,a*q/b,b*q/a,b/a,a/b,z,q/z] q) :
    qPhi [a,b] [c] q z=qPochhammerListInf [b,c/a,a*z,q/(a*z)] q/qPochhammerListInf [c,b/a,z,q/z] q*
      qPhi [a,a*q/c] [a*q/b] q (c*q/(a*b*z))+
      qPochhammerListInf [a,c/b,b*z,q/(b*z)] q/qPochhammerListInf [c,a/b,z,q/z] q*
      qPhi [b,b*q/c] [b*q/a] q (c*q/(a*b*z)) := by
  sorry

/-- heine contiguous 17. -/
@[dlmf 17.6.E17]
theorem heine_contiguous_17 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c/q] q) :
    qPhi [a,b] [c/q] q z-qPhi [a,b] [c] q z=c*z*(1-a)*(1-b)/((q-c)*(1-c))*qPhi [a*q,b*q] [c*q] q z := by
  sorry

/-- heine contiguous 18. -/
@[dlmf 17.6.E18]
theorem heine_contiguous_18 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    qPhi [a*q,b] [c] q z-qPhi [a,b] [c] q z=a*z*(1-b)/(1-c)*qPhi [a*q,b*q] [c*q] q z := by
  sorry

/-- heine contiguous 19. -/
@[dlmf 17.6.E19]
theorem heine_contiguous_19 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    qPhi [a*q,b] [c*q] q z-qPhi [a,b] [c] q z=z*(1-b)*(a-c)/((1-c)*(1-c*q))*qPhi [a*q,b*q] [c*q^2] q z := by
  sorry

/-- heine contiguous 20. -/
@[dlmf 17.6.E20]
theorem heine_contiguous_20 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    qPhi [a*q,b/q] [c] q z-qPhi [a,b] [c] q z=z*(a-b/q)/(1-c)*qPhi [a*q,b] [c*q] q z := by
  sorry

/-- heine contiguous 21. -/
@[dlmf 17.6.E21]
theorem heine_contiguous_21 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    b*(1-a)*qPhi [a*q,b] [c] q z-a*(1-b)*qPhi [a,b*q] [c] q z=(b-a)*qPhi [a,b] [c] q z := by
  sorry

/-- heine contiguous 22. -/
@[dlmf 17.6.E22]
theorem heine_contiguous_22 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    a*(c-b)*qPhi [a,b/q] [c] q z-b*(c-a)*qPhi [a/q,b] [c] q z=(a-b)*(c-a*b*z/q)*qPhi [a,b] [c] q z := by
  sorry

/-- heine contiguous 23. -/
@[dlmf 17.6.E23]
theorem heine_contiguous_23 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c] q) :
    q*(c-a)*qPhi [a/q,b] [c] q z+(1-a)*(c-a*b*z)*qPhi [a*q,b] [c] q z=(c*(1+q-a)-a*q+a^2*z-a*b*z)*qPhi [a,b] [c] q z := by
  sorry

/-- heine contiguous 24. -/
@[dlmf 17.6.E24]
theorem heine_contiguous_24 {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hd : qDenominatorRegular [c/q] q) :
    (1-c)*(q-c)*(a*b*z-c)*qPhi [a,b] [c/q] q z+z*(c-a)*(c-b)*qPhi [a,b] [c*q] q z=(c-1)*(c*(q-c)+z*(c*a+c*b-a*b-a*b*q))*qPhi [a,b] [c] q z := by
  sorry

/-- heine qDerivative. -/
@[dlmf 17.6.E25]
theorem heine_qDerivative {a b c d q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖d*z‖<1)
    (hc : qDenominatorRegular [c] q) (n : ℕ) :
    qDerivIterate n q (fun w => qPhi [a,b] [c] q (w*d)) z=
      qPochhammerList [a,b] q n*d^n/(qPochhammer c q n*(1-q)^n)*qPhi [a*q^n,b*q^n] [c*q^n] q (d*z) := by
  sorry

/-- heine weighted qDerivative. -/
@[dlmf 17.6.E26]
theorem heine_weighted_qDerivative {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1) (hc0 : c≠0)
    (hc : qDenominatorRegular [c] q) (hD : qPochhammerInf (a*b*z/c) q≠0) (n : ℕ) :
    qDerivIterate n q (fun w => qPochhammerInf w q/qPochhammerInf (a*b*w/c) q*qPhi [a,b] [c] q w) z=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (c^n*qPochhammer c q n*(1-q)^n)*qPochhammerInf (z*q^n) q/qPochhammerInf (a*b*z/c) q*
        qPhi [a,b] [c*q^n] q (z*q^n) := by
  sorry

/-- heine qDifferentialEquation. -/
@[dlmf 17.6.E27]
theorem heine_qDifferentialEquation {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz : ‖z‖<1)
    (hc : qDenominatorRegular [c] q) :
    let F := fun w => qPhi [a,b] [c] q w
    z*(c-a*b*q*z)*qDerivIterate 2 q F z+
      ((1-c)/(1-q)+((1-a)*(1-b)-(1-a*b*q))/(1-q)*z)*qDerivExtended q F z-
      (1-a)*(1-b)/(1-q)^2*F z=0 := by
  sorry

/-- heine classical derivative limit. -/
theorem heine_classical_derivative_limit {a b c z : ℂ} (hc : ∀ n : ℕ, c≠ -(n:ℂ)) (hz : ‖z‖<1) (n : ℕ) :
    Tendsto (fun q : ℝ => qDerivIterate n q
      (fun w => qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q w) z)
      (𝓝[<] 1) (𝓝 (iteratedDeriv n (ordinaryHypergeometric a b c) z)) := by
  sorry

/-- heine qDifferentialEquation classical coefficients. -/
theorem heine_qDifferentialEquation_classical_coefficients (a b c z : ℂ) :
    Tendsto (fun q : ℝ =>
      (z*((q:ℂ)^c-(q:ℂ)^(a+b+1)*z),
       (1-(q:ℂ)^c)/(1-q)+((1-(q:ℂ)^a)*(1-(q:ℂ)^b)-(1-(q:ℂ)^(a+b+1)))/(1-q)*z,
       -(1-(q:ℂ)^a)*(1-(q:ℂ)^b)/(1-q)^2))
      (𝓝[<] 1) (𝓝 (z*(1-z),c-(a+b+1)*z,-a*b)) := by
  sorry

/-- heine jackson integral. -/
@[dlmf 17.6.E28]
theorem heine_jackson_integral {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {a b c z : ℂ}
    (hb : 0<b.re) (hz : ‖z‖<1)
    (hc : qDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q) :
    qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c] q z=
      qGamma q c/(qGamma q b*qGamma q (c-b))*
      jacksonIntegral q 1 (fun t => t^(b-1)*qPochhammerOrder (t*q) q (c-b-1)/qPochhammerOrder (z*t) q a) := by
  sorry

/-- heine mellin barnes. -/
@[dlmf 17.6.E29]
theorem heine_mellin_barnes {a b c q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hz0 : z≠0) (hz : ‖z‖<1)
    (harg : |Complex.arg (-z)|<π) (hc : qDenominatorRegular [c] q)
    (L : ℝ → ℂ) (hL : ContDiff ℝ 1 L) (htail : Complex.hasVerticalTails L)
    (hsep : Complex.separatesPoleSets L (qHeineBarnesLeft a b q) qHeineBarnesRight)
    (hleft : Complex.staysAwayFrom L (qHeineBarnesLeft a b q))
    (hright : Complex.staysAwayFrom L qHeineBarnesRight) :
    Integrable (fun t : ℝ => qHeineBarnesKernel a b c q z (L t)*deriv L t) ∧
    qPhi [a,b] [c] q z= -1/(2*π*I)*qPochhammerListInf [a,b] q/qPochhammerListInf [q,c] q*
      ∫ t : ℝ, qHeineBarnesKernel a b c q z (L t)*deriv L t := by
  sorry

/-- The one-phi-zero product gives continuation of the actual series germ from zero. -/
theorem one_phi_zero_continues {a q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (qOnePhiZeroContinuation a q) {z | qPochhammerInf z q≠0} ∧
    (qPhi [a] [] q=ᶠ[𝓝 0] qOnePhiZeroContinuation a q) ∧
    TauCeti.ContinuesInside (qPhi [a] [] q) {z | qPochhammerInf z q≠0} 0 := by
  sorry

/-- The Jackson representation at Gamma-factor poles is its regular-parameter limit. -/
@[dlmf 17.6.E28]
theorem heine_jackson_parameter_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1)
    {a b c₀ z : ℂ} (hb : 0<b.re) (hz : ‖z‖<1)
    (hc₀ : qDenominatorRegular [(q:ℂ)^c₀] q) :
    Tendsto (fun c : ℂ => qHeineJacksonValue q a b c z)
      (𝓝[{c : ℂ | qDenominatorRegular [(q:ℂ)^c,(q:ℂ)^(c-b)] q}] c₀)
      (𝓝 (qPhi [(q:ℂ)^a,(q:ℂ)^b] [(q:ℂ)^c₀] q z)) := by
  sorry

end DLMF.QHypergeometric
