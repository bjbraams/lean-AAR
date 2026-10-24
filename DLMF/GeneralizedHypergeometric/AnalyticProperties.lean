/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Copyright (c) 2026 Moritz Doll. All rights reserved.
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

The finite-product coefficient-ratio estimates adapt Moritz Doll's private lemmas
in `Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric`, extending them
to positive degree. The adaptation is identified again at the helper lemmas.
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
  simp only [ite_eq_right hne]
  exact analyticOnNhd_const.mul (Complex.analyticOnNhd_regularizedHGFun_of_card_le h)

/-- The entire case has an absolutely convergent series for every finite z. -/
theorem genHG_hasSum_entire {a b : Multiset ℂ} (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    HasSum (fun n : ℕ => genCoeff a b n * z ^ n) (genHG a b z) := by
  have hne : a.card ≠ b.card + 1 := by omega
  have hs : HasSum (fun n => Complex.regularizedHGFunCoeff a b n * z ^ n)
      (Complex.regularizedHGFun a b z) := by
    simpa [Complex.regularizedHGFun, Complex.regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (Complex.regularizedHGFunSeries a b).hasSum (x := z)
        (by simp [Complex.radius_regularizedHGFunSeries_eq_top h])
  unfold genHG genRegularizedHG
  simp only [ite_eq_right hne]
  refine (hs.mul_left (genGamma b)).congr_fun fun n => ?_
  rw [genCoeff_eq_gamma_mul_regularized hb]
  ring

/-- Any nonpositive integer upper parameter gives a polynomial for every p,q. -/
theorem genHG_terminating_entire {a b : Multiset ℂ} (hb : genDenRegular b) (ha : genTerminates a) :
    ∃ P : Polynomial ℂ, ∀ z : ℂ, genHG a b z = P.eval z := by
  obtain ⟨x, hx, m, rfl⟩ := ha
  refine ⟨∑ n ∈ range (m + 1), Polynomial.monomial n (genCoeff a b n), ?_⟩
  intro z
  rw [genHG_eq_finite hb hx]
  simp [genFiniteHG, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

/-- The nonterminating p=q+1 series has exactly radius one. -/
theorem genHG_radius_one {a b : Multiset ℂ} (h : a.card = b.card + 1)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 1 := by
  rw [genScalarSeries_eq_gamma_smul hb,
    FormalMultilinearSeries.radius_smul_eq _ (genGamma_ne_zero hb)]
  apply Complex.radius_regularizedHGFunSeries_eq_one h
  intro x hx n hxn
  exact ha ⟨x, hx, n, hxn⟩

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

/- The next finite-product normalization follows the private ratio-test lemmas
in Mathlib's `RegularizedHypergeometric`, due to Moritz Doll.  Here it is
extended to the positive-degree case, where the coefficient ratio tends to infinity. -/
private lemma gen_prod_shift (a : Multiset ℂ) {n : ℕ} (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod = n ^ a.card * (a.map (· / (n : ℂ) + 1)).prod := calc
  _ = (a.map (fun j ↦ n * (j / (n : ℂ) + 1))).prod := by
    congr; ext; field_simp
  _ = _ := by simp [Multiset.prod_map_mul]

private lemma gen_prod_ratio (a b : Multiset ℂ) {n : ℕ} (hn : n ≠ 0) :
    (a.map (· + (n : ℂ))).prod / ((b.map (· + (n : ℂ))).prod * (n + 1)) =
      n ^ (a.card - (b.card : ℤ) - 1) * (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹)) := by
  rw [gen_prod_shift a hn, gen_prod_shift b hn]
  field_simp
  congr 1
  calc
    _ = n * n ^ b.card * n ^ (a.card - b.card - (1 : ℤ)) *
        (a.map (fun x : ℂ ↦ (x + n) / n)).prod := by
      congr 1
      rw [← pow_succ', ← zpow_natCast, ← zpow_natCast, ← zpow_add' (by left; norm_cast)]
      grind
    _ = _ := by ring

private lemma gen_prod_normalized_tendsto (a : Multiset ℂ) :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod) atTop (𝓝 1) := by
  suffices ∀ i ∈ a, Tendsto (fun n : ℕ ↦ (i / n + 1)) atTop (𝓝 ((fun _ : ℂ ↦ 1) i)) by
    simpa using tendsto_multiset_prod _ this
  intro i hi
  simpa using (tendsto_const_div_atTop_nhds_zero_nat i).add_const 1

private lemma gen_prod_normalized_ratio_tendsto (a b : Multiset ℂ) :
    Tendsto (fun n : ℕ ↦ (a.map (· / (n : ℂ) + 1)).prod /
      ((b.map (· / (n : ℂ) + 1)).prod * (1 + (n : ℂ)⁻¹))) atTop (𝓝 1) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_nhds_zero_nat
  have := (gen_prod_normalized_tendsto a).div
    ((gen_prod_normalized_tendsto b).mul (h.const_add 1)) (by simp)
  simp only [add_zero, mul_one, ne_eq, one_ne_zero, not_false_eq_true, div_self] at this
  apply this.congr
  simp

/-- The nonterminating p>q+1 formal series has radius zero. -/
theorem genHG_radius_zero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) :
    (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).radius = 0 := by
  rw [genScalarSeries_eq_gamma_smul hb,
    FormalMultilinearSeries.radius_smul_eq _ (genGamma_ne_zero hb)]
  apply FormalMultilinearSeries.ofScalars_radius_eq_zero_of_tendsto
  have hp : 0 < (a.card : ℤ) - b.card - 1 := by omega
  have ht : Tendsto (fun n : ℕ => (n : ℝ) ^ ((a.card : ℤ) - b.card - 1)) atTop atTop :=
    (tendsto_zpow_atTop_atTop hp).comp tendsto_natCast_atTop_atTop
  have hprod := (gen_prod_normalized_ratio_tendsto a b).norm
  simp only [norm_one] at hprod
  have hlim := Filter.Tendsto.atTop_mul_pos (by norm_num : (0 : ℝ) < 1) ht hprod
  apply hlim.congr'
  have h_ne := Complex.eventually_atTop_regularizedHGFunCoeff_ne_zero b
    (fun x hx n hxn => ha ⟨x, hx, n, hxn⟩)
  filter_upwards [h_ne, Filter.eventually_ne_atTop 0] with n hn₁ hn₂
  rw [Nat.succ_eq_add_one, ← Complex.norm_div,
    Complex.regularizedHGFunCoeff_add_one_div_self hn₁, gen_prod_ratio a b hn₂, ← mul_div,
    norm_mul, norm_zpow, Complex.norm_natCast]

/-- The nonterminating overbalanced formal series diverges at every nonzero argument. -/
theorem genHG_diverges_nonzero {a b : Multiset ℂ} (h : b.card + 1 < a.card)
    (hb : genDenRegular b) (ha : ¬genTerminates a) {z : ℂ} (hz : z ≠ 0) :
    ¬∃ v : ℂ, genSeriesConvergesTo a b z v := by
  rintro ⟨v, hv⟩
  have hS : Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v) := hv
  have hS' : Tendsto (fun N : ℕ => ∑ n ∈ range (N + 1), genCoeff a b n * z ^ n)
      atTop (𝓝 v) := (tendsto_add_atTop_iff_nat 1).2 hS
  have ht : Tendsto (fun n : ℕ => genCoeff a b n * z ^ n) atTop (𝓝 0) := by
    simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hS'.sub hS
  have htn : Tendsto (fun n : ℕ => ‖genCoeff a b n‖ * ‖z‖ ^ n) atTop (𝓝 0) := by
    simpa only [norm_mul, norm_pow, norm_zero] using ht.norm
  have hr := (FormalMultilinearSeries.ofScalars ℂ (genCoeff a b)).le_radius_of_tendsto
    (r := ‖z‖₊) (by simpa only [FormalMultilinearSeries.ofScalars_norm, coe_nnnorm] using htn)
  rw [genHG_radius_zero h hb ha] at hr
  have : z = 0 := by simpa using hr
  exact hz this

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
