/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic
public import DLMF.GeneralizedHypergeometric.Basic
public import Mathlib.Analysis.RCLike.Sqrt
public import DLMF.QSeries.Identities
public import DLMF.QSeries.QCalculus
public import DLMF.QSeries.QExponential
public import DLMF.QSeries.Saalschutz

/-!
# Basic hypergeometric series: common definitions (DLMF §§17.1,17.2,17.4)

The finite, infinite and integer-index shifted factorials, the q-derivative, and the Jackson
integral reuse `DLMF.QSeries`. The integer triangular exponent reuses
`DLMF.QSeries.TripleProduct.tri`. The general unilateral and bilateral series below include
the phase factors specified by DLMF/Gasper–Rahman; both differences of parameter counts
are integers. `tsum` is totalized outside convergence, and all identities below state their
convergence and exceptional-parameter hypotheses separately.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- A product of finite q-shifted factorials; parameter repetitions are retained. -/
@[dlmf 17.2.E5]
def qPochhammerList (a : List ℂ) (q : ℂ) (n : ℕ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammer ai q n).prod
/-- A product of integer-index q-shifted factorials, reusing the negative-index convention. -/
def qPochhammerListInt (a : List ℂ) (q : ℂ) (n : ℤ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInt ai q n).prod
/-- A product of infinite q-shifted factorials. -/
@[dlmf 17.2.E6]
def qPochhammerListInf (a : List ℂ) (q : ℂ) : ℂ :=
  (a.map fun ai => DLMF.QSeries.qPochhammerInf ai q).prod
/-- The DLMF phase exponent for a unilateral series, computed in the integers. -/
def qPhiExponent (a b : List ℂ) : ℤ := 1+(b.length:ℤ)-(a.length:ℤ)
/-- The DLMF phase exponent for a bilateral series, computed in the integers. -/
def qPsiExponent (a b : List ℂ) : ℤ := (b.length:ℤ)-(a.length:ℤ)
/-- General unilateral basic-hypergeometric term, including the integer phase exponent. -/
def qPhiTerm (a b : List ℂ) (q z : ℂ) (n : ℕ) : ℂ :=
  qPochhammerList a q n/(qPochhammerList b q n*DLMF.QSeries.qPochhammer q q n)*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri (n:ℤ))^qPhiExponent a b)*z^n
/-- General unilateral basic-hypergeometric series r-phi-s. -/
@[dlmf 17.4.E1]
def qPhi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℕ, qPhiTerm a b q z n
/-- General bilateral basic-hypergeometric term, with integer index and phase exponent. -/
def qPsiTerm (a b : List ℂ) (q z : ℂ) (n : ℤ) : ℂ :=
  qPochhammerListInt a q n/qPochhammerListInt b q n*
    (((-1:ℂ)^n*q^DLMF.QSeries.TripleProduct.tri n)^qPsiExponent a b)*z^n
/-- General bilateral basic-hypergeometric series r-psi-s. -/
@[dlmf 17.4.E3]
def qPsi (a b : List ℂ) (q z : ℂ) : ℂ := ∑' n : ℤ, qPsiTerm a b q z n
/-- A finite unilateral sum, including its term of index N. -/
def qPhiPartial (a b : List ℂ) (q z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ range (N+1), qPhiTerm a b q z n
/-- Denominator parameters avoid the nonpositive q-lattice. -/
def qDenominatorRegular (b : List ℂ) (q : ℂ) : Prop :=
  ∀ bi∈b, ∀ n : ℕ, bi*q^n≠1
/-- Bilateral parameters avoid the additional positive q-lattice in the numerator. -/
def qBilateralRegular (a b : List ℂ) (q : ℂ) : Prop :=
  qDenominatorRegular b q ∧ ∀ ai∈a, ∀ n : ℕ, ai≠q^(n+1)
/-- Termination by an upper parameter q^(-N); lower-parameter validity is independent. -/
def qTerminating (a : List ℂ) (q : ℂ) : Prop :=
  ∃ ai∈a, ∃ N : ℕ, ai=q^(-(N:ℤ))

/-- The general definition agrees with the existing phase-free basicHG when r=s+1. -/
theorem qPhi_eq_basicHG {a b : List ℂ} (h : a.length=b.length+1) (q z : ℂ) :
    qPhi a b q z=DLMF.QSeries.basicHG a b q z := by
  have he : qPhiExponent a b=0 := by simp only [qPhiExponent]; omega
  unfold qPhi DLMF.QSeries.basicHG
  apply tsum_congr
  intro n
  simp [qPhiTerm, qPochhammerList, he]

/-- Integer shifted-factorial products agree with finite products at nonnegative indices. -/
theorem qPochhammerListInt_natCast (a : List ℂ) (q : ℂ) (n : ℕ) :
    qPochhammerListInt a q n=qPochhammerList a q n := by
  simp [qPochhammerListInt,qPochhammerList]

/-- Rogers–Ramanujan G; the term n=0 supplies the initial1. -/
def rogersG (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*n)/DLMF.QSeries.qPochhammer q q n
/-- Rogers–Ramanujan H; the term n=0 supplies the initial1. -/
def rogersH (q : ℂ) : ℂ := ∑' n : ℕ, q^(n*(n+1))/DLMF.QSeries.qPochhammer q q n
/-- Complex-order shifted factorial, on the principal branch of q^ν. -/
def qPochhammerOrder (a q ν : ℂ) : ℂ :=
  DLMF.QSeries.qPochhammerInf a q/DLMF.QSeries.qPochhammerInf (a*q^ν) q
/-- Lower parameters are regular only through the final retained index of a terminating sum. -/
def qDenominatorRegularThrough (b : List ℂ) (q : ℂ) (N : ℕ) : Prop :=
  qPochhammerList b q N≠0
/-- Balanced/Saalschuetzian unilateral series: termination, r=s+1, z=q, and the product balance. -/
@[dlmf 17.4.E9]
def qBalanced (a b : List ℂ) (q z : ℂ) : Prop :=
  qTerminating a q ∧ a.length=b.length+1 ∧ z=q ∧ q*a.prod=b.prod
/-- k-balanced series; k=1 gives the product condition in the balanced case. -/
@[dlmf 17.4.E10]
def qKBalanced (k : ℤ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length+1 ∧ q^k*a.prod=b.prod
/-- Well-poised parameters, with a0 singled out and paired remaining upper/lower lists. -/
@[dlmf 17.4.E11]
def qWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  List.Forall₂ (fun ai bi => a0*q=ai*bi) a b
/-- Very-well-poised parameters, preserving the first two principal square-root parameters. -/
@[dlmf 17.4.E12]
def qVeryWellPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  qWellPoised a0 a b q ∧ ∃ bb : List ℂ,
    b=Complex.sqrt a0 :: -Complex.sqrt a0 :: bb
/-- Nearly-poised parameters: the paired relations hold except possibly at the last pair. -/
@[dlmf 17.4.E13]
def qNearlyPoised (a0 : ℂ) (a b : List ℂ) (q : ℂ) : Prop :=
  a.length=b.length ∧ List.Forall₂ (fun ai bi => a0*q=ai*bi) a.dropLast b.dropLast
/-- The idem notation is the sum obtained by singling out every parameter except the first. -/
def qIdem (f : ℂ → List ℂ → ℂ) (a : List ℂ) : ℂ :=
  ∑ j ∈ range (a.length-1), f (a[j+1]!) (a.eraseIdx (j+1))

open DLMF.QSeries
/-- qPochhammer negative. -/
@[dlmf 17.2.E2]
theorem qPochhammer_negative {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ)
    (hd : qPochhammer (q/a) q n≠0) :
    qPochhammerInt a q (-(n:ℤ))=(qPochhammer (a*q^(-(n:ℤ))) q n)⁻¹ ∧
    qPochhammerInt a q (-(n:ℤ))=(-q/a)^n*q^(n.choose 2)/qPochhammer (q/a) q n := by
  sorry

/-- qPochhammer order hasProd. -/
@[dlmf 17.2.E3]
theorem qPochhammer_order_hasProd {a q ν : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hd : ∀ j : ℕ, 1-a*q^(ν+j)≠0) :
    HasProd (fun j : ℕ => (1-a*q^j)/(1-a*q^(ν+j))) (qPochhammerOrder a q ν) := by
  sorry

/-- qPochhammer order nat. -/
theorem qPochhammer_order_nat {a q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n : ℕ)
    (hd : qPochhammerInf (a*q^n) q≠0) : qPochhammerOrder a q n=qPochhammer a q n := by
  sorry

/-- qPochhammer invert base. -/
@[dlmf 17.2.E7]
theorem qPochhammer_invert_base {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q⁻¹ n=qPochhammer a⁻¹ q n*(-a)^n*q^(-(n.choose 2:ℤ)) := by
  sorry

/-- qPochhammer invert base ratio. -/
@[dlmf 17.2.E8]
theorem qPochhammer_invert_base_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q⁻¹ n/qPochhammer b q⁻¹ n=qPochhammer a⁻¹ q n/qPochhammer b⁻¹ q n*(a/b)^n := by
  sorry

/-- qPochhammer reverse. -/
@[dlmf 17.2.E9]
theorem qPochhammer_reverse {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q n=qPochhammer (q^(1-(n:ℤ))/a) q n*(-a)^n*q^(n.choose 2) := by
  sorry

/-- qPochhammer reverse ratio. -/
@[dlmf 17.2.E10]
theorem qPochhammer_reverse_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer a q n/qPochhammer b q n=qPochhammer (q^(1-(n:ℤ))/a) q n/qPochhammer (q^(1-(n:ℤ))/b) q n*(a/b)^n := by
  sorry

/-- qPochhammer shift negative. -/
@[dlmf 17.2.E11]
theorem qPochhammer_shift_negative {a q : ℂ} (ha : a≠0) (hq : q≠0) (n : ℕ) : qPochhammer (a*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n*(-a/q)^n*q^(-(n.choose 2:ℤ)) := by
  sorry

/-- qPochhammer shift negative ratio. -/
@[dlmf 17.2.E12]
theorem qPochhammer_shift_negative_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) (n : ℕ) : qPochhammer (a*q^(-(n:ℤ))) q n/qPochhammer (b*q^(-(n:ℤ))) q n=qPochhammer (q/a) q n/qPochhammer (q/b) q n*(a/b)^n := by
  sorry

/-- qPochhammer sub index. -/
@[dlmf 17.2.E13]
theorem qPochhammer_sub_index {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hd : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) : qPochhammer a q (n-k)=qPochhammer a q n/qPochhammer (q^(1-(n:ℤ))/a) q k*(-q/a)^k*q^((k.choose 2:ℤ)-(n:ℤ)*k) := by
  sorry

/-- qPochhammer sub index ratio. -/
@[dlmf 17.2.E14]
theorem qPochhammer_sub_index_ratio {a b q : ℂ} (ha : a≠0) (hb : b≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hda : qPochhammer (q^(1-(n:ℤ))/a) q k≠0) (hdb : qPochhammer (q^(1-(n:ℤ))/b) q k≠0) : qPochhammer a q (n-k)/qPochhammer b q (n-k)=qPochhammer a q n/qPochhammer b q n*(qPochhammer (q^(1-(n:ℤ))/b) q k/qPochhammer (q^(1-(n:ℤ))/a) q k)*(b/a)^k := by
  sorry

/-- qPochhammer shift negative general. -/
@[dlmf 17.2.E15]
theorem qPochhammer_shift_negative_general {a q : ℂ} (ha : a≠0) (hq : q≠0) (k n : ℕ) (hd : qPochhammer (q^(1-(k:ℤ))/a) q n≠0) : qPochhammer (a*q^(-(n:ℤ))) q k=qPochhammer a q k*qPochhammer (q/a) q n/qPochhammer (q^(1-(k:ℤ))/a) q n*q^(-(n:ℤ)*k) := by
  sorry

/-- qPochhammer shift negative sub. -/
@[dlmf 17.2.E16]
theorem qPochhammer_shift_negative_sub {a q : ℂ} (ha : a≠0) (hq : q≠0) {k n : ℕ} (hk : k≤n) (hd : qPochhammer (q/a) q k≠0) : qPochhammer (a*q^(-(n:ℤ))) q (n-k)=qPochhammer (q/a) q n/qPochhammer (q/a) q k*(-a/q)^(n-k)*q^((k.choose 2:ℤ)-(n.choose 2:ℤ)) := by
  sorry

/-- qPochhammer shift positive. -/
@[dlmf 17.2.E17]
theorem qPochhammer_shift_positive {a q : ℂ} (k n : ℕ) (hd : qPochhammer a q n≠0) : qPochhammer (a*q^n) q k=qPochhammer a q k*qPochhammer (a*q^k) q n/qPochhammer a q n := by
  sorry

/-- qPochhammer shift sub. -/
@[dlmf 17.2.E18]
theorem qPochhammer_shift_sub {a q : ℂ} {k n : ℕ} (hk : k≤n) (hd : qPochhammer a q k≠0) : qPochhammer (a*q^k) q (n-k)=qPochhammer a q n/qPochhammer a q k := by
  sorry

/-- qPochhammer even. -/
@[dlmf 17.2.E19]
theorem qPochhammer_even (a q : ℂ) (n : ℕ) : qPochhammer a q (2*n)=qPochhammerList [a,a*q] (q^2) n := by
  sorry

/-- qPochhammer blocks. -/
@[dlmf 17.2.E20]
theorem qPochhammer_blocks (a q : ℂ) (k n : ℕ) : qPochhammer a q (k*n)=∏ j∈range k, qPochhammer (a*q^j) (q^k) n := by
  sorry

/-- qPochhammer squared. -/
@[dlmf 17.2.E21]
theorem qPochhammer_squared (a q : ℂ) (n : ℕ) : qPochhammer (a^2) (q^2) n=qPochhammer a q n*qPochhammer (-a) q n := by
  sorry

/-- qPochhammer vwp ratio. -/
@[dlmf 17.2.E22]
theorem qPochhammer_vwp_ratio {a q : ℂ} (n : ℕ) (hd : qPochhammer a (q^2) n≠0) (ha : a≠1) : qPochhammerList [q*Complex.sqrt a,-q*Complex.sqrt a] q n/qPochhammerList [Complex.sqrt a,-Complex.sqrt a] q n=qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n ∧ qPochhammer (a*q^2) (q^2) n/qPochhammer a (q^2) n=(1-a*q^(2*n))/(1-a) := by
  sorry

/-- qPochhammer root ratio. -/
@[dlmf 17.2.E23]
theorem qPochhammer_root_ratio {a q : ℂ} {k : ℕ} (hk : 0<k) (n : ℕ) (hd : qPochhammer a (q^k) n≠0) (ha : a≠1) : let ω := Complex.exp (2*π*I/k); let r := a^(1/(k:ℂ)); (∏ j∈range k, qPochhammer (q*ω^j*r) q n)/(∏ j∈range k, qPochhammer (ω^j*r) q n)=qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n ∧ qPochhammer (a*q^k) (q^k) n/qPochhammer a (q^k) n=(1-a*q^(k*n))/(1-a) := by
  sorry

/-- qPochhammer parameter limit. -/
@[dlmf 17.2.E24]
theorem qPochhammer_parameter_limit (a q : ℂ) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*τ^n) (𝓝[≠] 0) (𝓝 ((-a)^n*q^(n.choose 2))) ∧ Tendsto (fun σ : ℂ => qPochhammer (a*σ) q n*σ^(-(n:ℤ))) (Filter.cocompact ℂ) (𝓝 ((-a)^n*q^(n.choose 2))) := by
  sorry

/-- qPochhammer parameter ratio limit. -/
@[dlmf 17.2.E25]
theorem qPochhammer_parameter_ratio_limit {a b q : ℂ} (hb : b≠0) (hq : q≠0) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n/qPochhammer (b/τ) q n) (𝓝[≠] 0) (𝓝 ((a/b)^n)) ∧ Tendsto (fun σ : ℂ => qPochhammer (a*σ) q n/qPochhammer (b*σ) q n) (Filter.cocompact ℂ) (𝓝 ((a/b)^n)) := by
  sorry

/-- qPochhammer double parameter limit. -/
@[dlmf 17.2.E26]
theorem qPochhammer_double_parameter_limit {a b c q : ℂ} (hc : c≠0) (hq : q≠0) (n : ℕ) : Tendsto (fun τ : ℂ => qPochhammer (a/τ) q n*qPochhammer (b/τ) q n/qPochhammer (c/τ^2) q n) (𝓝[≠] 0) (𝓝 ((-1:ℂ)^n*(a*b/c)^n*q^(n.choose 2))) := by
  sorry

/-- qPhi hasSum. -/
theorem qPhi_hasSum {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q)
    (hr : a.length≤b.length+1) (hz : a.length=b.length+1 → ‖z‖<1) :
    HasSum (qPhiTerm a b q z) (qPhi a b q z) := by
  sorry

/-- qPsi hasSum. -/
theorem qPsi_hasSum {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) : HasSum (qPsiTerm a b q z) (qPsi a b q z) := by
  sorry

/-- qPsi split. -/
@[dlmf 17.4.E3]
theorem qPsi_split {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hb0 : b.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) :
    qPsi a b q z=(∑' n : ℕ, qPsiTerm a b q z n)+
      ∑' n : ℕ, qPochhammerList (b.map fun bi => q/bi) q (n+1)/
        qPochhammerList (a.map fun ai => q/ai) q (n+1)*(b.prod/(a.prod*z))^(n+1) := by
  sorry

/-- qPhi terminates. -/
theorem qPhi_terminates {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (N : ℕ) (hb : qDenominatorRegularThrough b q N) :
    qPhi (q^(-(N:ℤ))::a) b q z=qPhiPartial (q^(-(N:ℤ))::a) b q z N := by
  sorry

/-- qIdem expansion. -/
theorem qIdem_expansion (f : ℂ → List ℂ → ℂ) (x : ℂ) (a : List ℂ) :
    f x a+qIdem f (x::a)=∑ j∈range (a.length+1), f ((x::a)[j]!) ((x::a).eraseIdx j) := by
  sorry

/-- The bilateral split by actual negative indices, valid also for lower parameter zero. -/
@[dlmf 17.4.E3]
theorem qPsi_split_indices {a b : List ℂ} {q z : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hz0 : z≠0)
    (hr : a.length≤b.length) (hz : ‖b.prod/(a.prod*z)‖<1)
    (hz' : a.length=b.length → ‖z‖<1) :
    qPsi a b q z=(∑' n : ℕ, qPsiTerm a b q z n)+
      ∑' n : ℕ, qPsiTerm a b q z (-(n:ℤ)-1) := by
  sorry

/-- Formal coefficient limit in17.4.2, with its integer phase/scaling exponent. -/
@[dlmf 17.4.E2]
theorem qPhi_coefficient_classical_limit (a b : List ℂ) (z : ℂ) (n : ℕ)
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ)) :
    Tendsto (fun q : ℝ => qPhiTerm (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z) n)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genCoeff (a:Multiset ℂ) (b:Multiset ℂ) n*z^n)) := by
  sorry

/-- The analytic unilateral limit on the genuine classical convergence domain. -/
@[dlmf 17.4.E2]
theorem qPhi_classical_limit (a b : List ℂ) (z : ℂ)
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ))
    (hr : a.length≤b.length+1) (hz : a.length=b.length+1 → ‖z‖<1) :
    Tendsto (fun q : ℝ => qPhi (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z))
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genHG (a:Multiset ℂ) (b:Multiset ℂ) z)) := by
  sorry

/-- The finite limit retains bottom poles that occur only after the final retained term. -/
@[dlmf 17.4.E2]
theorem qPhi_finite_classical_limit (a b : List ℂ) (z : ℂ) (N : ℕ)
    (hb : ∀ bi∈b, ∀ j<N, bi≠ -(j:ℂ)) :
    Tendsto (fun q : ℝ => qPhiPartial (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q (((q:ℂ)-1)^qPhiExponent a b*z) N)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genFiniteHG N (a:Multiset ℂ) (b:Multiset ℂ) z)) := by
  sorry

/-- The bilateral limit is formal/coefficientwise; its analytic annulus collapses as q→1. -/
@[dlmf 17.4.E4]
theorem qPsi_coefficient_classical_limit (a b : List ℂ) (n : ℤ)
    (hlen : a.length=b.length)
    (ha : ∀ ai∈a, ∀ m : ℕ, ai≠(m+1:ℂ))
    (hb : DLMF.Hypergeometric.genDenRegular (b:Multiset ℂ)) :
    Tendsto (fun q : ℝ => qPsiTerm (a.map fun ai => (q:ℂ)^ai)
      (b.map fun bi => (q:ℂ)^bi) q 1 n)
      (𝓝[<] 1) (𝓝 (DLMF.Hypergeometric.genBilateralCoeff (a:Multiset ℂ) (b:Multiset ℂ) n)) := by
  sorry

/-- The infinite shifted factorial is entire in its first argument for a fixed base in the unit disk. -/
theorem qPochhammerInf_analytic {q : ℂ} (hq : ‖q‖<1) :
    AnalyticOnNhd ℂ (fun a : ℂ => qPochhammerInf a q) Set.univ := by
  sorry

/-- Every convergent unilateral series is analytic on the open unit disk. -/
theorem qPhi_analytic_disc {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length+1) :
    AnalyticOnNhd ℂ (qPhi a b q) {z | ‖z‖<1} := by
  sorry

/-- Unilateral series with at most as many upper as lower parameters are entire. -/
theorem qPhi_analytic_entire {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hb : qDenominatorRegular b q) (hr : a.length≤b.length) :
    AnalyticOnNhd ℂ (qPhi a b q) Set.univ := by
  sorry

/-- Bilateral series are analytic on their actual open annulus, including valid lower zeros. -/
theorem qPsi_analytic_annulus {a b : List ℂ} {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1)
    (hab : qBilateralRegular a b q) (ha : a.prod≠0) (hr : a.length≤b.length) :
    AnalyticOnNhd ℂ (qPsi a b q)
      {z | z≠0 ∧ ‖b.prod/(a.prod*z)‖<1 ∧ (a.length=b.length → ‖z‖<1)} := by
  sorry

/-- A holomorphic RHS germ continues the actual unilateral-series germ inside its domain.
This is a direct adapter of TauCeti's proved germ continuation API. -/
theorem qPhi_continuesInside_of_eq {a b : List ℂ} {q z₀ : ℂ} {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hz₀ : z₀∈U) (hF : AnalyticOnNhd ℂ F U)
    (heq : qPhi a b q=ᶠ[𝓝 z₀] F) : TauCeti.ContinuesInside (qPhi a b q) U z₀ := by
  exact (TauCeti.ContinuesInside.of_differentiableOn hU hF.differentiableOn).congr heq.symm

/-- A holomorphic RHS germ continues the actual bilateral-series germ inside its domain.
Only the germ in the convergence annulus is used, never a totalized value outside it. -/
theorem qPsi_continuesInside_of_eq {a b : List ℂ} {q z₀ : ℂ} {U : Set ℂ} {F : ℂ → ℂ}
    (hU : IsOpen U) (hz₀ : z₀∈U) (hF : AnalyticOnNhd ℂ F U)
    (heq : qPsi a b q=ᶠ[𝓝 z₀] F) : TauCeti.ContinuesInside (qPsi a b q) U z₀ := by
  exact (TauCeti.ContinuesInside.of_differentiableOn hU hF.differentiableOn).congr heq.symm

end DLMF.QHypergeometric
