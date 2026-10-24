/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import TauCeti.Analysis.Complex.Conformal.Continuation.Basic

/-!
# Analytic properties and zeros: DLMF §§16.2,16.9

Natural-order convergence is distinguished from absolute convergence on the unit
circle. The statement for `p>q+1` concerns the formal coefficient series, without
assigning its divergent sum an analytic meaning. Analytic continuation uses the
pinned TauCeti predicate for continuation along a path; no new continuation notion
is introduced. Parameter holomorphy applies to every such continued branch.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- For p≤q the full ordinary principal function is entire, with regular lower parameters. -/
theorem genHG_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) (hb : genDenRegular b) :
    AnalyticOnNhd ℂ (genHG a b) univ := by
  have hne : a.card ≠ b.card + 1 := by omega
  unfold genHG genRegularizedHG
  simp only [dite_eq_right hne]
  exact analyticOnNhd_const.mul (Complex.analyticOnNhd_regularizedHGFun_of_card_le h)

/-- The entire case has an absolutely convergent series for every finite z. -/
theorem genHG_hasSum_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    HasSum (fun n : ℕ => genCoeff a b n * z ^ n) (genHG a b z) := by
  sorry

/-- Any nonpositive integer upper parameter gives a polynomial for every p,q. -/
theorem genHG_terminating_entire {a b : Multiset ℂ} (hb : genDenRegular b) (ha : genTerminates a) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, genHG a b z = P.eval z := by
  sorry

/-- The nonterminating p=q+1 series has exactly radius one. -/
theorem genHG_radius_one {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 1 := by
  sorry

/-- The principal branch is analytic on the plane cut from one to positive infinity. -/
theorem genHG_principal_analytic {a b : Multiset ℂ} (h : a.card = b.card + 1) :
    AnalyticOnNhd ℂ (genHG a b) cutPlane := by
  sorry

/-- Full criterion for absolute convergence on the unit circle in the nonterminating case. -/
theorem genHG_unit_absolute_iff {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : ‖z‖ = 1) :
    genSeriesAbsolutelyConverges a b z ↔ 0 < (genExcess a b).re := by
  sorry

/-- Every nonunit point of the unit circle converges in natural order when the excess exceeds minus one. -/
theorem genHG_unit_conditional {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1)
    (hγ : -1 < (genExcess a b).re) : genSeriesConvergesTo a b z (genHG a b z) := by
  sorry

/-- At one, natural-order convergence requires strictly positive real excess unless the series terminates. -/
theorem genHG_one_converges_iff {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (∃ v : ℂ, genSeriesConvergesTo a b 1 v) ↔ 0 < (genExcess a b).re := by
  sorry

/-- Positive excess gives absolute convergence to the declared endpoint value. -/
theorem genHG_one_hasSum {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (hγ : 0 < (genExcess a b).re) :
    HasSum (fun n : ℕ => genCoeff a b n) (genHG a b 1) := by
  sorry

/-- At real excess at most minus one, no point of the unit circle converges in the nonterminating case. -/
theorem genHG_unit_diverges {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : ‖z‖ = 1)
    (hγ : (genExcess a b).re ≤ -1) : ¬∃ v : ℂ, genSeriesConvergesTo a b z v := by
  sorry

/-- The nonterminating p>q+1 formal series has radius zero. -/
theorem genHG_radius_zero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 0 := by
  sorry

/-- The nonterminating overbalanced formal series diverges at every nonzero argument. -/
theorem genHG_diverges_nonzero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : z ≠ 0) :
    ¬∃ v : ℂ, genSeriesConvergesTo a b z v := by
  sorry

/-- General branches continue along every path avoiding the possible finite singularities zero and one. -/
theorem genHG_continuation_along {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0 ∧ γ t ≠ 1) (h0 : ‖γ 0‖ < 1) :
    ∃ F : ℝ → ℂ → ℂ, TauCeti.IsAnalyticContinuationAlong F γ (Icc 0 1) ∧
      F 0 =ᶠ[𝓝 (γ 0)] Complex.regularizedHGFun a b := by
  sorry

/-- The regularized principal branch is jointly entire in all parameters at every nonsingular fixed argument. -/
@[dlmf 16.2.E5]
theorem genRegularizedHG_parameter_entire {p q : ℕ} (h : p ≤ q + 1) {z : ℂ} (hz : p = q + 1 → z ≠ 1) :
    Differentiable ℂ (fun P : (Fin p → ℂ) × (Fin q → ℂ) =>
      genRegularizedHG (genParams P.1) (genParams P.2) z) := by
  sorry

/-- Every fixed analytically continued regularized branch is jointly entire in its parameters. -/
@[dlmf 16.2.E5]
theorem genContinued_parameter_entire {q : ℕ} (γ : ℝ → ℂ) (hc : ContinuousOn γ (Icc 0 1))
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0 ∧ γ t ≠ 1) (h0 : ‖γ 0‖ < 1)
    (F : ((Fin (q + 1) → ℂ) × (Fin q → ℂ)) → ℝ → ℂ → ℂ)
    (hF : ∀ P, TauCeti.IsAnalyticContinuationAlong (F P) γ (Icc 0 1) ∧
      F P 0 =ᶠ[𝓝 (γ 0)] Complex.regularizedHGFun (genParams P.1) (genParams P.2)) :
    Differentiable ℂ (fun P => F P 1 (γ 1)) := by
  sorry

/-- Equal-order generalized hypergeometric functions have finitely many complex zeros exactly for a matched nonnegative-integer parameter difference. -/
theorem genHG_finite_zeros_iff {p : ℕ} (a b : Fin p → ℂ)
    (hb : genDenRegular (genParams b)) (ha : ¬genTerminates (genParams a)) :
    {z : ℂ | genHG (genParams a) (genParams b) z = 0}.Finite ↔
      ∃ σ : Equiv.Perm (Fin p), ∀ j, ∃ n : ℕ, a (σ j) - b j = n := by
  sorry

/-- Equal-order real parameters and real coefficient ratios give only finitely many real zeros. -/
theorem genHG_finite_real_zeros {p : ℕ} (a b : Fin p → ℂ)
    (hb : genDenRegular (genParams b)) (ha : ∀ j, (a j).im = 0)
    (hr : ∀ n : ℕ, (genPoch (genParams a) n / genPoch (genParams b) n).im = 0) :
    {x : ℝ | genHG (genParams a) (genParams b) x = 0}.Finite := by
  sorry

end DLMF.Hypergeometric
