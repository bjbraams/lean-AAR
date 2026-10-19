/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.Basic

/-!
# Special values and confluent representations, DLMF §§8.4–8.5

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- The finite exponential sum e_n. -/
@[dlmf 8.4.E11]
def expPartialSum (n : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n+1), z^k/(k.factorial : ℂ)

/-- lowerIncGamma half square. -/
@[dlmf 8.4.E1]
theorem lowerIncGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    lowerIncGamma (1/2) (z^2)=2*primitive (fun t => exp (-t^2)) z ∧ lowerIncGamma (1/2) (z^2)=Real.sqrt π*erf z := by
  sorry

/-- scIncGamma zero. -/
@[dlmf 8.4.E2]
theorem scIncGamma_zero (a : ℂ) :
    scIncGamma a 0=1/Gamma (a+1) := by
  sorry

/-- scIncGamma half negative square. -/
@[dlmf 8.4.E3]
theorem scIncGamma_half_negative_square {z : ℂ} (hz : z ≠ 0) :
    scIncGamma (1/2) (-z^2)=2*exp (z^2)/(z*Real.sqrt π)*dawsonF z := by
  sorry

/-- upperIncGamma zero E1. -/
@[dlmf 8.4.E4]
theorem upperIncGamma_zero_E1 {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma 0 z=genExpIntE 1 z := by
  simp [genExpIntE]

/-- upperIncGamma half square. -/
@[dlmf 8.4.E6]
theorem upperIncGamma_half_square {z : ℂ} (hz : 0 < z.re) :
    upperIncGamma (1/2) (z^2)=Real.sqrt π*erfc z := by
  sorry

/-- lowerIncGamma nat succ expPartialSum. -/
@[dlmf 8.4.E7]
theorem lowerIncGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma (n+1) z=(n.factorial : ℂ)*(1-exp (-z)*expPartialSum n z) := by
  sorry

/-- upperIncGamma nat succ expPartialSum. -/
@[dlmf 8.4.E8]
theorem upperIncGamma_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (n+1) z=(n.factorial : ℂ)*exp (-z)*expPartialSum n z := by
  sorry

/-- normIncGammaPContinued nat succ expPartialSum. -/
@[dlmf 8.4.E9]
theorem normIncGammaPContinued_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaPContinued (n+1) z=1-exp (-z)*expPartialSum n z := by
  sorry

/-- normIncGammaQContinued nat succ expPartialSum. -/
@[dlmf 8.4.E10]
theorem normIncGammaQContinued_nat_succ_expPartialSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    normIncGammaQContinued (n+1) z=exp (-z)*expPartialSum n z := by
  sorry

/-- upperIncGamma one minus nat. -/
@[dlmf 8.4.E13]
theorem upperIncGamma_one_minus_nat (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (1-n) z=z^(1-(n : ℂ))*genExpIntE n z := by
  sorry

/-- normIncGammaQ half nat. -/
@[dlmf 8.4.E14]
theorem normIncGammaQ_half_nat (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    normIncGammaQContinued (n+1/2) (z^2)=erfc z+exp (-z^2)/Real.sqrt π*(∑ k ∈ Finset.range n, z^(2*k+1)/poch (1/2) (k+1)) := by
  sorry

/-- upperIncGamma neg nat finite. -/
@[dlmf 8.4.E15]
theorem upperIncGamma_neg_nat_finite (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma (-n) z=(-1 : ℂ)^n/n.factorial*(genExpIntE 1 z-exp (-z)*∑ k ∈ Finset.range n, (-1 : ℂ)^k*(k.factorial : ℂ)/z^(k+1)) := by
  sorry

/-- upperIncGamma neg nat hasSum. -/
@[dlmf 8.4.E15]
theorem upperIncGamma_neg_nat_hasSum (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n then 0 else (-z)^k/((k.factorial : ℂ)*((k : ℂ)-n))) (z^(n : ℤ)*((-1 : ℂ)^n/n.factorial*(digamma (n+1)-log z)-upperIncGamma (-n) z)) := by
  sorry

/-- lowerIncGamma kummerM pair. -/
@[dlmf 8.5.E1]
theorem lowerIncGamma_kummerM_pair {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    lowerIncGamma a z=z^a/a*exp (-z)*kummerM 1 (1+a) z ∧ lowerIncGamma a z=z^a/a*kummerM a (1+a) (-z) := by
  sorry

/-- scIncGamma regularized pair. -/
@[dlmf 8.5.E2]
theorem scIncGamma_regularized_pair (a z : ℂ) :
    scIncGamma a z=exp (-z)*regularizedHGFun {1} {1+a} z ∧ scIncGamma a z=regularizedHGFun {a} {1+a} (-z) := by
  sorry

/-- upperIncGamma kummerU pair. -/
@[dlmf 8.5.E3]
theorem upperIncGamma_kummerU_pair (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=exp (-z)*kummerU (1-a) (1-a) z ∧ upperIncGamma a z=z^a*exp (-z)*kummerU 1 (1+a) z := by
  constructor
  · rfl
  · simpa [add_comm] using upperIncGamma_eq_cpow_mul_kummerU a hz

/-- lowerIncGamma whittakerM. -/
@[dlmf 8.5.E4]
theorem lowerIncGamma_whittakerM {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) {z : ℂ} (hz : z ≠ 0) :
    lowerIncGamma a z=z^(a/2-1/2)*exp (-z/2)/a*whittakerM (a/2-1/2) (a/2) z := by
  sorry

/-- upperIncGamma whittakerW. -/
@[dlmf 8.5.E5]
theorem upperIncGamma_whittakerW (a : ℂ) {z : ℂ} (hz : z ≠ 0) :
    upperIncGamma a z=exp (-z/2)*z^(a/2-1/2)*whittakerW (a/2-1/2) (a/2) z := by
  sorry

/-- The square argument retains its inherited logarithm in the full punctured plane. -/
@[dlmf 7.11.E1, dlmf 8.4.E1]
theorem erf_lowerIncGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erf z=lowerIncGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  sorry

/-- erfc upperIncGammaOnLog square. -/
@[dlmf 7.11.E2, dlmf 8.4.E6]
theorem erfc_upperIncGammaOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=upperIncGammaOnLog (1/2) (2*log z)/Real.sqrt π := by
  sorry

/-- erfc kummerUOnLog square. -/
@[dlmf 7.11.E5]
theorem erfc_kummerUOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=exp (-z^2)/Real.sqrt π*kummerUOnLog (1/2) (1/2) (2*log z) ∧ erfc z=z/Real.sqrt π*exp (-z^2)*kummerUOnLog 1 (3/2) (2*log z) := by
  sorry

end AAR.Confluent
