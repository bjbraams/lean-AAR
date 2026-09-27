/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import AAR.Gamma.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.ZPow
public import Mathlib.Topology.Instances.Nat
public import AAR.Hypergeometric.Continuation
public import Mathlib.Topology.Instances.Int
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-!
# Polygamma functions (DLMF §5.15)

The trigamma series 5.15.1 is `trigamma_eq_tsum` in `Digamma.lean` (real
positive argument). Complex polygamma is the iterated derivative of Mathlib's
`Complex.digamma`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Polygamma `ψ^{(n)}(z)`. -/
def polygamma (n : ℕ) (z : ℂ) : ℂ :=
  iteratedDeriv n Complex.digamma z

@[dlmf 5.15.E2]
theorem polygamma_one (n : ℕ) (hn : 0 < n) :
    polygamma n 1 = (-1 : ℂ) ^ (n + 1) * n.factorial * riemannZeta (n + 1) := by
  sorry

@[dlmf 5.15.E3]
theorem polygamma_one_div_two (n : ℕ) (hn : 0 < n) :
    polygamma n (1 / 2) =
      (-1 : ℂ) ^ (n + 1) * n.factorial * ((2 : ℂ) ^ (n + 1) - 1) * riemannZeta (n + 1) := by
  sorry

/-- The trigamma recurrence `ψ'(x+1) = ψ'(x) - 1/x²` for `x > 0`. -/
theorem trigamma_add_one {x : ℝ} (hx : 0 < x) :
    Real.trigamma (x + 1) = Real.trigamma x - x⁻¹ ^ 2 := by
  rw [Real.trigamma_eq_tsum hx, Real.trigamma_eq_tsum (by linarith),
    (Real.summable_trigamma hx).tsum_eq_zero_add]
  have h : ∀ n : ℕ, (x + ((n + 1 : ℕ) : ℝ))⁻¹ ^ 2 = (x + 1 + n)⁻¹ ^ 2 := by
    intro n; push_cast; ring_nf
  simp only [h, Nat.cast_zero, add_zero]
  ring

@[dlmf 5.15.E4]
theorem trigamma_nat_sub_half (n : ℕ) (hn : 1 ≤ n) :
    Real.trigamma (n - 1 / 2) =
      π ^ 2 / 2 - 4 * ∑ k ∈ Finset.range (n - 1), (1 / (2 * (k : ℝ) + 1) ^ 2) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  clear hn
  simp only [Nat.add_sub_cancel]
  induction m with
  | zero =>
    rw [show ((0 + 1 : ℕ) : ℝ) - 1 / 2 = 1 / 2 by norm_num, trigamma_one_div_two]
    simp
  | succ m ih =>
    have hpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) - 1 / 2 := by
      push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have h := trigamma_add_one hpos
    have h3 : (((m + 1 : ℕ) : ℝ) - 1 / 2)⁻¹ ^ 2 = 4 / (2 * (m : ℝ) + 1) ^ 2 := by
      push_cast
      rw [show (m : ℝ) + 1 - 1 / 2 = (2 * m + 1) / 2 by ring, inv_div, div_pow]
      norm_num
    rw [show ((m + 1 + 1 : ℕ) : ℝ) - 1 / 2 = ((m + 1 : ℕ) : ℝ) - 1 / 2 + 1 by push_cast; ring,
      h, ih, Finset.sum_range_succ, h3]
    ring

/-- The complement of the nonpositive integers is open in `ℂ`. -/
lemma isOpen_not_neg_nat : IsOpen {s : ℂ | ∀ m : ℕ, s ≠ -(m : ℂ)} :=
  AAR.Hypergeometric.isOpen_not_neg_nat

/-- `Γ` is analytic away from the nonpositive integers. -/
lemma analyticAt_Gamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.Gamma s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_not_neg_nat.mem_nhds hs] with w hw
  exact Complex.differentiableAt_Gamma w hw

/-- `ψ` is analytic away from the nonpositive integers. -/
lemma analyticAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.digamma s := by
  have hG := analyticAt_Gamma hs
  exact hG.deriv.div hG (Complex.Gamma_ne_zero hs)

@[dlmf 5.15.E5]
theorem polygamma_add_one (n : ℕ) {z : ℂ} (hz : ∀ k : ℕ, z ≠ -k) :
    polygamma n (z + 1) = polygamma n z + (-1 : ℂ) ^ n * n.factorial * z ^ (-(n + 1 : ℕ) : ℂ) := by
  have hz0 : z ≠ 0 := by simpa using hz 0
  have heq : (fun w => Complex.digamma (w + 1)) =ᶠ[𝓝 z] fun w => Complex.digamma w + w⁻¹ := by
    filter_upwards [isOpen_not_neg_nat.mem_nhds hz] with w hw
    exact Complex.digamma_apply_add_one w hw
  unfold polygamma
  have h1 : iteratedDeriv n Complex.digamma (z + 1) =
      iteratedDeriv n (fun w => Complex.digamma (w + 1)) z := by
    rw [iteratedDeriv_comp_add_const]
  rw [h1, heq.iteratedDeriv_eq n,
    iteratedDeriv_fun_add (analyticAt_digamma hz).contDiffAt (contDiffAt_inv ℂ hz0)]
  congr 1
  rw [iteratedDeriv_eq_iterate, iter_deriv_inv,
    show (-(n + 1 : ℕ) : ℂ) = ((-1 - n : ℤ) : ℂ) by push_cast; ring, Complex.cpow_intCast]

/-- The complement of the integers is open in `ℂ`. -/
lemma isOpen_not_int : IsOpen {s : ℂ | ∀ k : ℤ, s ≠ (k : ℂ)} := by
  have hce : Topology.IsClosedEmbedding (fun k : ℤ => ((k : ℝ) : ℂ)) :=
    Complex.isometry_ofReal.isClosedEmbedding.comp Int.isClosedEmbedding_coe_real
  have hset : {s : ℂ | ∀ k : ℤ, s ≠ (k : ℂ)} = (Set.range fun k : ℤ => ((k : ℝ) : ℂ))ᶜ := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_range, not_exists,
      Complex.ofReal_intCast]
    exact ⟨fun h k hk => h k hk.symm, fun h k hk => h k hk.symm⟩
  rw [hset]
  exact hce.isClosed_range.isOpen_compl

/-- `cot (π w)` is smooth away from the integers. -/
lemma contDiffAt_cot_pi_mul {n : ℕ} {z : ℂ} (hz : ∀ k : ℤ, z ≠ (k : ℂ)) :
    ContDiffAt ℂ n (fun w : ℂ => cot (π * w)) z := by
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsin : sin (π * z) ≠ 0 := by
    intro h
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp h
    exact hz k (mul_left_cancel₀ hπ (by rw [hk]; ring))
  have hc : ContDiffAt ℂ n (fun w : ℂ => cos (π * w)) z :=
    Complex.contDiff_cos.contDiffAt.comp z (contDiffAt_const.mul contDiffAt_id)
  have hs : ContDiffAt ℂ n (fun w : ℂ => sin (π * w)) z :=
    Complex.contDiff_sin.contDiffAt.comp z (contDiffAt_const.mul contDiffAt_id)
  refine (hc.div hs hsin).congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => ?_)
  simp [Complex.cot_eq_cos_div_sin]

@[dlmf 5.15.E6]
theorem polygamma_reflection (n : ℕ) {z : ℂ} (hz : ∀ k : ℤ, z ≠ k) :
    polygamma n (1 - z) + (-1 : ℂ) ^ (n - 1 : ℤ) * polygamma n z =
      (-1 : ℂ) ^ n * π * iteratedDeriv n (fun w : ℂ => cot (π * w)) z := by
  have hnat : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => hz (-m) (by rw [h]; push_cast; ring)
  have heq : (fun w => Complex.digamma (1 - w)) =ᶠ[𝓝 z]
      fun w => Complex.digamma w + π * cot (π * w) := by
    filter_upwards [isOpen_not_int.mem_nhds hz] with w hw
    exact Complex.digamma_one_sub hw
  have hcomp := congrFun (iteratedDeriv_comp_const_sub n Complex.digamma 1) z
  simp only [smul_eq_mul] at hcomp
  rw [heq.iteratedDeriv_eq n,
    iteratedDeriv_fun_add (analyticAt_digamma hnat).contDiffAt
      (contDiffAt_const.mul (contDiffAt_cot_pi_mul hz))] at hcomp
  have h2 : iteratedDeriv n (fun w => (π : ℂ) * cot (π * w)) z =
      π * iteratedDeriv n (fun w => cot (π * w)) z :=
    iteratedDeriv_const_mul_field (π : ℂ) (fun w => cot (π * w))
  rw [h2] at hcomp
  have hsq : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by rw [← mul_pow]; simp
  have hz1 : (-1 : ℂ) ^ (n - 1 : ℤ) = -(-1) ^ n := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_natCast]
    simp
  unfold polygamma
  linear_combination (-(-1 : ℂ) ^ n) * hcomp - (iteratedDeriv n Complex.digamma (1 - z)) * hsq +
    (iteratedDeriv n Complex.digamma z) * hz1

/-- Multiplication formula for positive-order polygamma functions. The order-zero
digamma formula has an additional logarithmic term. -/
@[dlmf 5.15.E7]
theorem polygamma_multiplication (n m : ℕ) (hn : 0 < n) (hm : 0 < m) {z : ℂ}
    (hz : ∀ k : ℕ, m * z ≠ -k) :
    polygamma n (m * z) =
      (m : ℂ) ^ (-(n + 1 : ℕ) : ℂ) *
        ∑ k ∈ Finset.range m, polygamma n (z + k / m) := by
  sorry

@[dlmf 5.15.E8]
theorem trigamma_asymptotic (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.trigamma (t + x) -
        (1 / (t + x) + 1 / (2 * (t + x) ^ 2) +
          ∑ k ∈ Finset.Icc 1 n, bernoulli (2 * k) / (t + x) ^ (2 * k + 1)))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 3)) := by
  sorry

@[dlmf 5.15.E9]
theorem polygamma_asymptotic (n m : ℕ) (hn : 0 < n) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => polygamma n (t + x) -
        (-1 : ℂ) ^ (n - 1) *
          ((n - 1).factorial / (t + x : ℂ) ^ n +
            n.factorial / (2 * (t + x : ℂ) ^ (n + 1)) +
            ∑ k ∈ Finset.Icc 1 m,
              ((2 * k + n - 1).factorial / (2 * k).factorial) *
                bernoulli (2 * k) / (t + x : ℂ) ^ (2 * k + n)))
      (fun t : ℝ => (t : ℂ) ^ (-(2 * m + n + 2 : ℕ) : ℂ)) := by
  sorry

end AAR.Gamma
