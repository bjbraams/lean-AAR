/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import DLMF.Bailey

/-!
# Higher basic summations (DLMF §17.7)

Finite sums retain parameter poles occurring only after the final retained term. Infinite
sums retain their actual convergence disks. Cleared products handle regular zero upper
parameters without evaluating0 times an infinite product quotient.

Two printed DLMF formulas have explicit counterexamples below. The corrected17.7.19 uses
Gasper–Rahman, Basic Hypergeometric Series, (1.9.7), with argument a⁻¹q^(−Σm).
The corrected17.7.23 follows George Gasper, Lecture Notes for an Introductory Minicourse on
q-Series (1995), (4.1.23), with p and q interchanged:
https://sites.math.northwestern.edu/~george/preprints/ggLecNotesq-Series/ggLecNotesq-Series.pdf .
The first denominator is(p;p)_k and the final shifted-factorial base is p. No false printed
identity is admitted. These references support the corrected statements; their proofs remain
admitted where a complete local proof is not yet available.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory DLMF.QSeries
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Shifted upper parameters for the q-Karlsson–Minton formulas. -/
def qMintonUpper (p : List (ℂ × ℕ)) (q : ℂ) : List ℂ := p.map fun x => x.1*q^x.2
/-- The corresponding unshifted lower parameters. -/
def qMintonLower (p : List (ℂ × ℕ)) : List ℂ := p.map Prod.fst
/-- Total nonnegative parameter displacement. -/
def qMintonWeight (p : List (ℂ × ℕ)) : ℕ := (p.map Prod.snd).sum
/-- The square-root-product cancellation in the four-phi-three sum. -/
def qFourPhiThreeValue (a b c q : ℂ) : ℂ :=
  let r := Complex.sqrt a
  let t := Complex.sqrt q
  qPochhammerListInf [r*t,-r*t,-r*q,q*r/b,q*r/c,a*q/(b*c)] q/
    qPochhammerListInf [a*q/b,a*q/c,q*r/(b*c)] q
/-- Pointwise definedness of integer shifted factorials before taking ratios. -/
def qIntPochhammerListDefined (p : List ℂ) (q : ℂ) (k : ℤ) : Prop :=
  0≤k ∨ ∀ a∈p, qPochhammer (a*q^k) q (-k).toNat≠0
/-- two phi two sum. -/
@[dlmf 17.7.E1]
theorem two_phi_two_sum {a b q : ℂ} (ha : a≠0) (hq : ‖q‖<1) (hd : qDenominatorRegular [-q,b] q) :
    qPhi [a,q/a] [-q,b] q (-b)=qPochhammerListInf [a*b,b*q/a] (q^2)/qPochhammerInf b q := by
  sorry

/-- two phi two square sum. -/
@[dlmf 17.7.E2]
theorem two_phi_two_square_sum {a b q : ℂ} (hq : ‖q‖<1)
    (hd : qDenominatorRegular [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q) :
    qPhi [a^2,b^2] [a*b*Complex.sqrt q,-a*b*Complex.sqrt q] q (-q)=
      qPochhammerListInf [a^2*q,b^2*q] (q^2)/qPochhammerListInf [q,a^2*b^2*q] (q^2) := by
  sorry

/-- The cancelled product retains b=±q^(-m) whenever the lower parameters are regular. -/
@[dlmf 17.7.E3]
theorem two_phi_two_even_sum {b c q : ℂ} (hb : b≠0) (hq : ‖q‖<1) (hd : qDenominatorRegular [c,c*q] (q^2)) :
    qPhi [c^2/b^2,b^2] [c,c*q] (q^2) q=
      qPochhammerInf q (q^2)/(2*qPochhammerListInf [c,c*q] (q^2))*
      (qPochhammerInf (-b) q*qPochhammerInf (c/b) q+
       qPochhammerInf b q*qPochhammerInf (-c/b) q) := by
  sorry

/-- The cleared finite product includes regular a=0 and b=0. -/
@[dlmf 17.7.E4]
theorem q_pfaff_saalschutz {a b c q : ℂ} (hc0 : c≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegularThrough [c,a*b*q^(1-(n:ℤ))/c] q n) :
    qPhi [a,b,q^(-(n:ℤ))] [c,a*b*q^(1-(n:ℤ))/c] q q=
      ((range n).prod (fun j => a-c*q^j))*((range n).prod (fun j => b-c*q^j))/
        (qPochhammer c q n*((range n).prod (fun j => a*b-c*q^j))) := by
  sorry

/-- nonterminating saalschutz. -/
@[dlmf 17.7.E5]
theorem nonterminating_saalschutz {a b c e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (he : e≠0) (hf : f≠0) (hbal : e*f=a*b*c*q)
    (hd : qDenominatorRegular [e,f,q^2/e,q*f/e,e/q,a*q/e,b*q/e,c*q/e] q) :
    qPhi [a,b,c] [e,f] q q+
      qPochhammerListInf [q/e,a,b,c,q*f/e] q/qPochhammerListInf [e/q,a*q/e,b*q/e,c*q/e,f] q*
        qPhi [a*q/e,b*q/e,c*q/e] [q^2/e,q*f/e] q q=
      qPochhammerListInf [q/e,f/a,f/b,f/c] q/qPochhammerListInf [a*q/e,b*q/e,c*q/e,f] q := by
  sorry

/-- q dixon terminating. -/
@[dlmf 17.7.E6]
theorem q_dixon_terminating {b c q : ℂ} (hb : b≠0) (hc : c≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegularThrough [q^(1-(2*n:ℤ))/b,q^(1-(2*n:ℤ))/c] q (2*n)) :
    qPhi [q^(-(2*n:ℤ)),b,c] [q^(1-(2*n:ℤ))/b,q^(1-(2*n:ℤ))/c] q (q^(2-(n:ℤ))/(b*c))=
      qPochhammerList [b,c] q n*qPochhammerList [q,b*c] q (2*n)/
        (qPochhammerList [q,b*c] q n*qPochhammerList [b,c] q (2*n)) := by
  sorry

/-- four phi three sum. -/
@[dlmf 17.7.E7]
theorem four_phi_three_sum {a b c q : ℂ} (hq : ‖q‖<1) (hz : ‖q*Complex.sqrt a‖<‖b*c‖)
    (hd : qDenominatorRegular [-Complex.sqrt a,a*q/b,a*q/c] q) :
    qPhi [a,-q*Complex.sqrt a,b,c] [-Complex.sqrt a,a*q/b,a*q/c] q
      (q*Complex.sqrt a/(b*c))=qFourPhiThreeValue a b c q := by
  sorry

/-- eight phi seven quadratic sum. -/
@[dlmf 17.7.E8]
theorem eight_phi_seven_quadratic_sum {a b c q ell : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (hc : c≠0)
    (hell : ell= -c*Complex.sqrt (a*b/q)) (hz : ‖ell*q‖<‖a*b‖)
    (hd : qDenominatorRegular [Complex.sqrt ell,-Complex.sqrt ell,ell*q/a,ell*q/b,ell*q/c,-ell*q/c,c^2] q) :
    qPhi [ell,q*Complex.sqrt ell,-q*Complex.sqrt ell,a,b,c,-c,ell*q/c^2]
      [Complex.sqrt ell,-Complex.sqrt ell,ell*q/a,ell*q/b,ell*q/c,-ell*q/c,c^2] q (-ell*q/(a*b))=
      qPochhammerListInf [ell*q,c^2/ell] q*qPochhammerListInf [a*q,b*q,c^2*q/a,c^2*q/b] (q^2)/
        (qPochhammerListInf [ell*q/a,ell*q/b] q*qPochhammerListInf [q,a*b*q,c^2*q,c^2*q/(a*b)] (q^2)) := by
  sorry

/-- four phi three parity. -/
@[dlmf 17.7.E9]
theorem four_phi_three_parity {a c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegularThrough [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q n) :
    qPhi [q^(-(n:ℤ)),a*q^n,c,-c] [Complex.sqrt (a*q),-Complex.sqrt (a*q),c^2] q q=
      if Odd n then 0 else qPochhammer q (q^2) (n/2)*
        ((range (n/2)).prod (fun j => c^2-a*q^(2*j+1)))/
        qPochhammerList [a*q,c^2*q] (q^2) (n/2) := by
  sorry

/-- eight phi seven even sum. -/
@[dlmf 17.7.E10]
theorem eight_phi_seven_even_sum {a c d q : ℂ} (ha : a≠0) (hd0 : d≠0) (hq : ‖q‖<1) (hc : ‖c‖<1)
    (hd : qDenominatorRegular [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q) :
    qPhi [-c,q*Complex.sqrt (-c),-q*Complex.sqrt (-c),a,q/a,c,-d,-q/d]
      [Complex.sqrt (-c),-Complex.sqrt (-c),-c*q/a,-a*c,-q,c*q/d,c*d] q c=
      qPochhammerListInf [-c,-c*q] q*qPochhammerListInf [a*c*d,a*c*q/d,c*d*q/a,c*q^2/(a*d)] (q^2)/
        qPochhammerListInf [c*d,c*q/d,-a*c,-c*q/a] q := by
  sorry

/-- four phi three infinite product. -/
@[dlmf 17.7.E11]
theorem four_phi_three_infinite_product {c e q : ℂ} (he : e≠0) (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegular [e,c^2*q/e,-q] q) :
    qPhi [q^(-(n:ℤ)),q^(n+1),c,-c] [e,c^2*q/e,-q] q q=
      q^((n+1).choose 2)*qPochhammerListInf [e*q^(-(n:ℤ)),e*q^(n+1),c^2*q^(1-(n:ℤ))/e,c^2*q^(n+2)/e] (q^2)/
        qPochhammerListInf [e,c^2*q/e] q := by
  sorry

/-- The cleared product retains the regular upper parameter a=0. -/
@[dlmf 17.7.E12]
theorem four_phi_three_base_square_first {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegularThrough [b,b*q,a^2*q^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*n),q^(-(2*n:ℤ))] [b,b*q,a^2*q^2] (q^2) (q^2)=
      qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))/qPochhammerList [-a*q,b] q n := by
  sorry

/-- The n=0 removable quotient is1, and the cleared product retains a=0. -/
@[dlmf 17.7.E13]
theorem four_phi_three_base_square_second {a b q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qDenominatorRegularThrough [b,b*q,a^2] (q^2) n) :
    qPhi [a,a*q,b^2*q^(2*(n:ℤ)-2),q^(-(2*n:ℤ))] [b,b*q,a^2] (q^2) (q^2)=
      if n=0 then 1 else qPochhammer (-q) q n*((range n).prod (fun j => a-b*q^j))*(1-b*q^((n:ℤ)-1))/
        (qPochhammerList [-a,b] q n*(1-b*q^(2*(n:ℤ)-1))) := by
  sorry

/-- jackson eight phi seven. -/
@[dlmf 17.7.E14]
theorem jackson_eight_phi_seven {a b c d e q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hbcd : b*c*d≠0) (he : e≠0) (hbal : a^2*q=b*c*d*e*q^(-(n:ℤ)))
    (hd : qDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q^(n+1)] q q=
      qPochhammerList [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q n/
        qPochhammerList [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q n := by
  sorry

/-- six phi five sum. -/
@[dlmf 17.7.E15]
theorem six_phi_five_sum {a b c d q : ℂ} (hq : ‖q‖<1) (hz : ‖a*q‖<‖b*c*d‖)
    (hd : qDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d] q (a*q/(b*c*d))=
      qPochhammerListInf [a*q,a*q/(b*c),a*q/(b*d),a*q/(c*d)] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/(b*c*d)] q := by
  sorry

/-- six phi five terminating. -/
@[dlmf 17.7.E16]
theorem six_phi_five_terminating {a b c q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ) (hbc : b*c≠0)
    (hd : qDenominatorRegularThrough [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q n) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,q^(-(n:ℤ))]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q^(n+1)] q (a*q^(n+1)/(b*c))=
      qPochhammerList [a*q,a*q/(b*c)] q n/qPochhammerList [a*q/b,a*q/c] q n := by
  sorry

/-- nonterminating eight phi seven. -/
@[dlmf 17.7.E17]
theorem nonterminating_eight_phi_seven {a b c d e f q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (habcdef : a*b*c*d*e*f≠0) (hbal : q*a^2=b*c*d*e*f)
    (hd : qDenominatorRegular [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,
      b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f,
      b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q) :
    qPhi [a,q*Complex.sqrt a,-q*Complex.sqrt a,b,c,d,e,f]
      [Complex.sqrt a,-Complex.sqrt a,a*q/b,a*q/c,a*q/d,a*q/e,a*q/f] q q-
      b/a*qPochhammerListInf [a*q,c,d,e,f,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q/
        qPochhammerListInf [a*q/b,a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a,b^2*q/a] q*
        qPhi [b^2/a,q*b/Complex.sqrt a,-q*b/Complex.sqrt a,b,b*c/a,b*d/a,b*e/a,b*f/a]
          [b/Complex.sqrt a,-b/Complex.sqrt a,b*q/a,b*q/c,b*q/d,b*q/e,b*q/f] q q=
      qPochhammerListInf [a*q,b/a,a*q/(c*d),a*q/(c*e),a*q/(c*f),a*q/(d*e),a*q/(d*f),a*q/(e*f)] q/
        qPochhammerListInf [a*q/c,a*q/d,a*q/e,a*q/f,b*c/a,b*d/a,b*e/a,b*f/a] q := by
  sorry

/-- The cleared finite product includes b=0 without a spurious0 times infinity. -/
@[dlmf 17.7.E18]
theorem q_karlsson_minton {a b q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹*q^(1-(qMintonWeight p:ℤ))‖<1)
    (hd : qDenominatorRegular (b*q::qMintonLower p) q) :
    qPhi (a::b::qMintonUpper p q) (b*q::qMintonLower p) q (a⁻¹*q^(1-(qMintonWeight p:ℤ)))=
      qPochhammerListInf [q,b*q/a] q/qPochhammerListInf [b*q,q/a] q*
      (p.map (fun x => (range x.2).prod (fun j => b-x.1*q^j))).prod/
        (p.map fun x => qPochhammer x.1 q x.2).prod := by
  sorry

/-- The primary-source argument is q^(−Σm)/a; the printed extra q is disproved below. -/
@[dlmf 17.7.E19]
theorem q_karlsson_minton_zero_corrected {a q : ℂ} (ha : a≠0) (hq0 : q≠0) (hq : ‖q‖<1) (p : List (ℂ × ℕ))
    (hz : ‖a⁻¹*q^(-(qMintonWeight p:ℤ))‖<1) (hd : qDenominatorRegular (qMintonLower p) q) :
    qPhi (a::qMintonUpper p q) (qMintonLower p) q (a⁻¹*q^(-(qMintonWeight p:ℤ)))=0 := by
  sorry

/-- bibasic gosper. -/
@[dlmf 17.7.E20]
theorem bibasic_gosper {a c p q : ℂ} (ha : a≠1) (hc : c≠0) (n : ℕ)
    (hd : qPochhammer q q n*qPochhammer (a*p/c) p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)/(1-a)*qPochhammer a p k*qPochhammer c q k/
      (qPochhammer q q k*qPochhammer (a*p/c) p k)*c^(-(k:ℤ)))=
      qPochhammer (a*p) p n*qPochhammer (c*q) q n/
        (qPochhammer q q n*qPochhammer (a*p/c) p n)*c^(-(n:ℤ)) := by
  sorry

/-- bibasic gasper. -/
@[dlmf 17.7.E21]
theorem bibasic_gasper {a b c p q : ℂ} (ha : a≠1) (hb : b≠1) (hbc : b*c≠0) (hq : q≠0) (n : ℕ)
    (hd : qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n≠0) :
    (∑ k∈range (n+1), (1-a*p^k*q^k)*(1-b*p^k*q^(-(k:ℤ)))/((1-a)*(1-b))*
      qPochhammerList [a,b] p k*qPochhammerList [c,a/(b*c)] q k/
        (qPochhammerList [q,a*q/b] q k*qPochhammerList [a*p/c,b*c*p] p k)*q^k)=
      qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*q/(b*c)] q n/
        (qPochhammerList [q,a*q/b] q n*qPochhammerList [a*p/c,b*c*p] p n) := by
  sorry

/-- bibasic bilateral finite. -/
@[dlmf 17.7.E22]
theorem bibasic_bilateral_finite {a b c d p q : ℂ} (hbc : b*c≠0) (hp : p≠0) (hq : q≠0) (m n : ℕ)
    (hP : d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c))≠0)
    (hF : ∀ k∈Finset.Icc (-(m:ℤ)) (n:ℤ),
      qIntPochhammerListDefined [a,b] p k ∧ qIntPochhammerListDefined [c,a*d^2/(b*c)] q k ∧
      qIntPochhammerListDefined [d*q,a*d*q/b] q k ∧ qIntPochhammerListDefined [a*d*p/c,b*c*p/d] p k ∧
      qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k≠0)
    (hR : qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1)≠0) :
    (∑ k∈Finset.Icc (-(m:ℤ)) (n:ℤ), (1-a*d*p^k*q^k)*(1-b*p^k/(d*q^k))/((1-a*d)*(1-b/d))*
      qPochhammerListInt [a,b] p k*qPochhammerListInt [c,a*d^2/(b*c)] q k/
        (qPochhammerListInt [d*q,a*d*q/b] q k*qPochhammerListInt [a*d*p/c,b*c*p/d] p k)*q^k)=
      (1-a)*(1-b)*(1-c)*(1-a*d^2/(b*c))/(d*(1-a*d)*(1-b/d)*(1-c/d)*(1-a*d/(b*c)))*
      (qPochhammerList [a*p,b*p] p n*qPochhammerList [c*q,a*d^2*q/(b*c)] q n/
        (qPochhammerList [d*q,a*d*q/b] q n*qPochhammerList [a*d*p/c,b*c*p/d] p n)-
       qPochhammerList [c/(a*d),d/(b*c)] p (m+1)*qPochhammerList [1/d,b/(a*d)] q (m+1)/
        (qPochhammerList [1/c,b*c/(a*d^2)] q (m+1)*qPochhammerList [1/a,1/b] p (m+1))) := by
  sorry

/-- Gasper1995(4.1.23), with p and q swapped, gives both corrected denominator entries. -/
@[dlmf 17.7.E23]
theorem bibasic_difference_corrected {a b p q : ℂ} (hb : b≠0) (hp : p≠0) (hq : q≠0) (n : ℕ)
    (h0 : n=0 → a≠q ∧ b≠q)
    (hP : qPochhammer p p n≠0)
    (hD : ∀ k≤n, qPochhammer (a*p^k/b) p (n+1)≠0) :
    (1-a/q)*(1-b/q)*(∑ k∈range (n+1), qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*
      (1-a*p^(2*k)/b)/(qPochhammer p p k*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) p (n+1))*
      (-1:ℂ)^k*p^(k.choose 2))=(if n=0 then 1 else 0) := by
  sorry

/-- The printed argument in17.7.19 gives a nonzero terminating series. -/
@[dlmf 17.7.E19]
theorem karlsson_printed_counter : qPhi [2] [] (1/2) (1/4)=(1/2:ℂ) := by
  have hzero (k : ℕ) (hk : 2≤k) : qPochhammer (2:ℂ) (1/2) k=0 := by
    have h := qPochhammer_recip_pow_eq_zero (q := (1/2:ℂ)) (by norm_num) (n := 1) (k := k) (by omega)
    norm_num at h
    exact h
  rw [qPhi_eq_basicHG (by simp)]
  unfold basicHG
  rw [tsum_eq_sum (s := range 2) (fun k hk => by
    have h := hzero k (by simp only [Finset.mem_range, not_lt] at hk; exact hk)
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,h,zero_div,zero_mul])]
  norm_num [sum_range_succ, qPochhammer]

/-- The expression printed in17.7.23, before the primary-source corrections. -/
def bibasicDifferencePrinted (p q a b : ℂ) (n : ℕ) : ℂ :=
  (1-a/q)*(1-b/q)*∑ k∈range (n+1),
    qPochhammerListInt [a*p^k,b*p^(-(k:ℤ))] q ((n:ℤ)-1)*(1-a*p^(2*k)/b)/
      (qPochhammer p p n*qPochhammer p p (n-k)*qPochhammer (a*p^k/b) q (n+1))*
      (-1:ℂ)^k*p^(k.choose 2)

/-- An exact nonzero value disproving the printed n=1 delta identity. -/
@[dlmf 17.7.E23]
theorem bibasic_printed_counter :
    bibasicDifferencePrinted (1/2) (1/3) (1/4) 1 1= -(1884/1771:ℂ) := by
  norm_num [bibasicDifferencePrinted, sum_range_succ, qPochhammerListInt,
    qPochhammerInt, qPochhammer]

end DLMF.QHypergeometric
