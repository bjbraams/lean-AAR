/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Basic
public import AAR.Hypergeometric.Continuation

/-!
# Parameter dependence and boundary convergence (DLMF §§15.2, 15.4)

Already in Mathlib, without duplicate declarations here:
* DLMF 15.2.E1: `ordinaryHypergeometric_eq_tsum`.
* DLMF 15.2.E2: `coeff_regularizedGaussHGFunSeries` and the definition
  `regularizedGaussHGFun`; `ordinaryHypergeometric_div_Gamma_eq` compares them.
* DLMF 15.2.i: `ordinaryHypergeometricSeries_radius_eq_one` and
  `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂/₃` cover the series radius.
See https://dlmf.nist.gov/15.2 . These Mathlib functions are sums of series;
their values outside convergence are not DLMF's analytic continuations.
Conditional convergence is therefore stated with ordered finite partial sums.
The terminating identity E4 and absolute convergence on the unit circle already
appear in `Basic`. E5/E6 prescribe different singular-parameter limit conventions;
the diagonal convention E6 must not be confused with totalized division.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.2.E3_5]
theorem regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b (-n) z =
      poch a (n + 1) * poch b (n + 1) / ((n + 1).factorial : ℂ) * z ^ (n + 1) *
        ₂F₁ (a + n + 1) (b + n + 1) (n + 2) z := by
  rw [regularizedGaussHGFun_eq_tsum]
  have hs := summable_regularizedGaussHGFun_term a b (-n) hz
  rw [← hs.sum_add_tsum_nat_add (n + 1)]
  have hzero : ∀ k ∈ Finset.range (n + 1),
      (ascPochhammer ℂ k).eval a * (ascPochhammer ℂ k).eval b * z ^ k / k.factorial *
        (Gamma (-(n : ℂ) + k))⁻¹ = 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-(n : ℂ) + k) = -((n - k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hk']; ring
    rw [this, Complex.Gamma_neg_nat_eq_zero, inv_zero, mul_zero]
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hF := (hasFPowerSeriesOnBall_ordinaryHypergeometric (a + n + 1) (b + n + 1)
    (n + 2)).hasSum_mul_pow (mem_eball_one_of_norm_lt_one hz)
  rw [← hF.tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  have hpole : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.neg_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hΓ : Gamma ((n : ℂ) + 2 + j) = (ascPochhammer ℂ j).eval ((n : ℂ) + 2) * Gamma ((n : ℂ) + 2) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := j) ((n : ℂ) + 2) hpole]
    field_simp [Gamma_ne_zero hpole]
  have hΓ1 : Gamma ((n : ℂ) + 2 + j) = ((n + 1 + j).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 + j = ((n + 1 + j : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ2 : Gamma ((n : ℂ) + 2) = ((n + 1).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ3 : Gamma (-(n : ℂ) + ((n + 1 + j : ℕ) : ℂ)) = (j.factorial : ℂ) := by
    rw [show -(n : ℂ) + ((n + 1 + j : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hp : (ascPochhammer ℂ j).eval ((n : ℂ) + 2) ≠ 0 := poch_ne_zero_of_not_neg_nat hpole j
  have hf1 : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((n + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hΓ1, hΓ2] at hΓ
  simp only [gaussHGCoeff, poch]
  rw [add_comm j (n + 1), ascPochhammer_eval_add a, ascPochhammer_eval_add b, hΓ3,
    show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
    show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring, pow_add]
  field_simp
  linear_combination (-((ascPochhammer ℂ (n + 1)).eval a * (ascPochhammer ℂ j).eval (a + n + 1) *
    (ascPochhammer ℂ (n + 1)).eval b * (ascPochhammer ℂ j).eval (b + n + 1) *
    z ^ (n + 1) * z ^ j)) * hΓ

@[dlmf 15.2.ii]
theorem entire_regularized_parameters {z : ℂ} (hz : ‖z‖ < 1) :
    Differentiable ℂ (fun p : ℂ × ℂ × ℂ =>
      regularizedGaussHGFun p.1 p.2.1 p.2.2 z) := by
  sorry

@[dlmf 15.2.E3_5]
theorem tendsto_regularized_at_neg_nat (a b : ℂ) (n : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun c : ℂ => ₂F₁ a b c z / Gamma c) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedGaussHGFun a b (-n) z)) := by
  have hcont : ContinuousAt (fun c => regularizedGaussHGFun a b c z) (-(n : ℂ)) :=
    ((analyticOnNhd_regularizedGaussHGFun_c a b hz) _ (Set.mem_univ _)).continuousAt
  refine (hcont.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [eventually_nhdsWithin_ne_neg_nat n] with c hc
  exact regularizedGaussHGFun_eq_div_Gamma hc z

@[dlmf 15.2.i]
theorem conditional_convergence_on_circle
    {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ))
    (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ = 1)
    (hz1 : z ≠ 1)
    (hlo : -1 < (c - a - b).re) (hhi : (c - a - b).re ≤ 0) :
    (∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s)) ∧
      ¬ Summable (fun k : ℕ => ‖gaussHGCoeff a b c k * z ^ k‖) := by
  sorry

@[dlmf 15.2.i]
theorem divergence_on_circle
    {a b c z : ℂ}
    (ha : ∀ k : ℕ, a ≠ -(k : ℂ))
    (hb : ∀ k : ℕ, b ≠ -(k : ℂ))
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hz : ‖z‖ = 1)
    (h :
    (c - a - b).re ≤ -1) :
    ¬ ∃ s : ℂ, Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff a b c k * z ^ k) atTop (𝓝 s) := by
  sorry

@[dlmf 15.4.E21]
theorem zero_balanced_limit {a b : ℂ} (hc : ∀ k : ℕ, a + b ≠ -(k : ℂ)) :
    Tendsto (fun x : ℝ => ₂F₁ a b (a + b) (x : ℂ) / (-Real.log (1 - x) : ℂ))
      (𝓝[<] 1) (𝓝 (Gamma (a + b) / (Gamma a * Gamma b))) := by
  sorry

@[dlmf 15.4.E22]
theorem imaginary_excess_limit
    {a b c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (h :
    (c - a - b).re = 0)
    (hne : c ≠ a + b) :
    Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (a + b - c) *
      (₂F₁ a b c (x : ℂ) - Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))))
      (𝓝[<] 1) (𝓝 (Gamma c * Gamma (a + b - c) / (Gamma a * Gamma b))) := by
  sorry

@[dlmf 15.2.E5]
theorem terminating_iterated_parameter_limit (b : ℂ) (m l : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun c : ℂ => Filter.limUnder (𝓝[≠] (-(m : ℂ))) (fun a => ₂F₁ a b c z))
      (𝓝[≠] (-(m : ℂ) - l)) (𝓝 (₂F₁ (-m : ℂ) b (-(m : ℂ) - l) z)) := by
  -- the inner limit is the value at `a = -m`, by continuity in `a` off the poles of `Γ(c)`
  have hlim : ∀ c : ℂ, (∀ k : ℕ, c ≠ -(k : ℂ)) →
      Filter.limUnder (𝓝[≠] (-(m : ℂ))) (fun a => ₂F₁ a b c z) = ₂F₁ (-(m : ℂ)) b c z := by
    intro c hc
    apply Filter.Tendsto.limUnder_eq
    have hfun : (fun a => ₂F₁ a b c z) = fun a => Gamma c * regularizedGaussHGFun a b c z := by
      funext a
      rw [regularizedGaussHGFun_eq_div_Gamma hc, mul_div_cancel₀ _ (Gamma_ne_zero hc)]
    have hcont : ContinuousAt (fun a => ₂F₁ a b c z) (-(m : ℂ)) := by
      rw [hfun]
      exact continuousAt_const.mul
        ((analyticOnNhd_regularizedGaussHGFun_a b c hz) _ (Set.mem_univ _)).continuousAt
    exact hcont.tendsto.mono_left nhdsWithin_le_nhds
  -- the outer limit, by continuity of the terminating series in `c` at `c = -m-l`
  have hmem : (-(m : ℂ) - l) ∈ {c : ℂ | ∀ j : ℕ, j < m → c ≠ -(j : ℂ)} := fun j hj h => by
    have : ((m + l : ℕ) : ℂ) = j := by push_cast; linear_combination -h
    have : m + l = j := by exact_mod_cast this
    omega
  have hcont2 : ContinuousAt (fun c => ₂F₁ (-(m : ℂ)) b c z) (-(m : ℂ) - l) :=
    ((analyticOnNhd_gauss_neg_nat_param m b z) _ hmem).continuousAt
  refine (hcont2.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
  have hev := eventually_nhdsWithin_ne_neg_nat (m + l)
  rw [show -((m + l : ℕ) : ℂ) = -(m : ℂ) - l by push_cast; ring] at hev
  filter_upwards [hev] with c hc
  exact (hlim c hc).symm

/-- The diagonal limit has a different coefficient ratio from the terminating convention E5. -/
@[dlmf 15.2.E6]
theorem diagonal_parameter_limit (b : ℂ) (m l : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun a : ℂ => ₂F₁ a b (a - l) z) (𝓝[≠] (-(m : ℂ)))
      (𝓝 (∑' k : ℕ, poch (-(m : ℂ) - l + k) l * poch b k /
        (poch (-(m : ℂ) - l) l * (k.factorial : ℂ)) * z ^ k)) := by
  sorry

end AAR.Hypergeometric
