/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Recurrence
public import AAR.Hypergeometric.Continuation

/-!
# Analytic continuation of Kummer's function in its parameters (DLMF §13.2(i))

Mathlib's regularized function `𝐌(a,b,z) = regularizedHGFun {a} {b} z = M(a,b,z)/Γ(b)` is
entire in `a`, in `b` and in `z`. We prove that it is entire along any entire curve in the
parameter plane, and use the identity principle to remove every parameter hypothesis from the
contiguous relations of §13.3, from the derivative formula 13.3.15 and from Kummer's
transformation 13.2.39. The classical statements with hypotheses remain in
`AAR.Confluent.Recurrence` and `AAR.Confluent.Basic`.
-/

@[expose] public section

open Complex Filter Set FormalMultilinearSeries AAR.Hypergeometric
open scoped Real Nat Topology ENNReal

noncomputable section

set_option autoImplicit false

namespace AAR.Confluent

/-! ### Series and majorants -/

/-- The regularized Kummer function as a series with explicit terms. -/
lemma regularizedConfluent_eq_tsum (a b z : ℂ) :
    regularizedHGFun {a} {b} z =
      ∑' n : ℕ, poch a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹ := by
  rw [regularizedHGFun_eq_tsum]
  congr 1
  funext n
  rw [regularizedHGFunCoeff_singleton]
  ring

lemma radius_regularizedConfluentSeries (a b : ℂ) :
    (regularizedHGFunSeries {a} {b}).radius = ⊤ :=
  radius_regularizedHGFunSeries_eq_top (by simp)

/-- The regularized Kummer series converges on all of `ℂ`. -/
lemma hasFPowerSeriesOnBall_regularizedConfluent (a b : ℂ) :
    HasFPowerSeriesOnBall (regularizedHGFun {a} {b})
      (ofScalars ℂ (regularizedHGFunCoeff {a} {b})) 0 ⊤ := by
  have hr := radius_regularizedConfluentSeries a b
  change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {b}).sum
    (regularizedHGFunSeries {a} {b}) 0 ⊤
  simpa only [hr] using (regularizedHGFunSeries {a} {b}).hasFPowerSeriesOnBall (by rw [hr]; simp)

lemma summable_regularizedConfluent_term (a b z : ℂ) :
    Summable fun n : ℕ => poch a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹ := by
  have h := (hasFPowerSeriesOnBall_regularizedConfluent a b).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  refine h.summable.congr fun n => ?_
  rw [regularizedHGFunCoeff_singleton]
  ring

lemma norm_regularizedConfluentSeries_apply_ofReal (α : ℝ) (N n : ℕ) (hn : N ≤ n) :
    ‖regularizedHGFunSeries {(α : ℂ)} {1 - (N : ℂ)} n‖ =
      ‖poch (α : ℂ) n‖ / (n.factorial * (n - N).factorial) := by
  have hΓ : Gamma ((1 : ℂ) - N + n) = ((n - N).factorial : ℂ) := by
    rw [show (1 : ℂ) - N + n = ((n - N : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hn]; ring]
    exact Complex.Gamma_nat_eq_factorial _
  rw [norm_apply_eq_norm_coef, regularizedHGFunSeries_coeff, regularizedHGFunCoeff_singleton, hΓ,
    norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast]

/-- The tail-domination step: the `n`-th term is bounded by the `n`-th term of the majorant
series `𝐌(α, 1 - N, ‖z‖)`. -/
lemma norm_confluent_term_le_majorant {a b z : ℂ} {α : ℝ} (ha : ‖a‖ ≤ α) {N : ℕ}
    (hre : 1 ≤ (b + N).re) {m : ℝ} (hm : 0 < m) (hΓ : m ≤ ‖Gamma (b + N)‖) {n : ℕ}
    (hn : N ≤ n) :
    ‖poch a n * z ^ n / n.factorial * (Gamma (b + n))⁻¹‖ ≤
      m⁻¹ * (‖regularizedHGFunSeries {(α : ℂ)} {1 - (N : ℂ)} n‖ * ‖z‖ ^ n) := by
  rw [norm_regularizedConfluentSeries_apply_ofReal α N n hn, norm_mul, norm_div, norm_mul,
    norm_pow, Complex.norm_natCast]
  have hA : ‖poch a n‖ ≤ ‖poch (α : ℂ) n‖ := norm_ascPochhammer_eval_le ha n
  have hG := norm_inv_Gamma_add_nat_le hre hm hΓ hn
  have hf : (0 : ℝ) < n.factorial := by positivity
  have hf' : (0 : ℝ) < (n - N).factorial := by positivity
  calc ‖poch a n‖ * ‖z‖ ^ n / n.factorial * ‖(Gamma (b + n))⁻¹‖
      ≤ ‖poch (α : ℂ) n‖ * ‖z‖ ^ n / n.factorial * (((n - N).factorial : ℝ)⁻¹ * m⁻¹) := by
        gcongr
    _ = _ := by field_simp

/-! ### Analyticity in the parameters -/

/-- The regularized Kummer function is entire along any entire curve in the parameter plane
(DLMF §13.2(i)): for entire `A B`, `w ↦ 𝐌(A w, B w, z)` is entire. -/
theorem analyticOnNhd_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) :
    AnalyticOnNhd ℂ (fun w => regularizedHGFun {A w} {B w} z) univ := by
  simp_rw [regularizedConfluent_eq_tsum]
  refine analyticOnNhd_tsum_of_eventually_dominated ?_ ?_ ?_
  · intro n
    have h1 : Differentiable ℂ fun w => poch (A w) n :=
      (Polynomial.differentiable (ascPochhammer ℂ n)).comp hA
    exact ((h1.mul_const _).div_const _).mul (differentiable_one_div_Gamma.comp (hB.add_const _))
  · intro w
    exact summable_regularizedConfluent_term _ _ z
  · intro w₀
    obtain ⟨N, hN⟩ : ∃ N : ℕ, 3 - (B w₀).re ≤ N := exists_nat_ge _
    have hre0 : 2 ≤ (B w₀ + N).re := by
      simp only [Complex.add_re, Complex.natCast_re]
      linarith
    obtain ⟨V, hVopen, hc₀V, hV⟩ := exists_open_norm_Gamma_add_nat_gt hre0
    have hevA : ∀ᶠ w in 𝓝 w₀, ‖A w‖ < ‖A w₀‖ + 1 :=
      hA.continuous.continuousAt.norm.eventually (gt_mem_nhds (by linarith))
    have hevC : ∀ᶠ w in 𝓝 w₀, (B w₀).re - 1 < (B w).re :=
      (Complex.continuous_re.comp hB.continuous).continuousAt.eventually
        (lt_mem_nhds (by show (B w₀).re - 1 < (B w₀).re; linarith))
    have hevV : ∀ᶠ w in 𝓝 w₀, B w ∈ V := hB.continuous.continuousAt (hVopen.mem_nhds hc₀V)
    obtain ⟨U, hU, hUopen, hw₀U⟩ := eventually_nhds_iff.mp (hevA.and (hevC.and hevV))
    refine ⟨U, hUopen, hw₀U, N, ?_⟩
    set p := regularizedHGFunSeries {((‖A w₀‖ + 1 : ℝ) : ℂ)} {1 - (N : ℂ)} with hp
    have hz' : (‖z‖₊ : ENNReal) < p.radius := by
      rw [hp, radius_regularizedConfluentSeries]
      exact ENNReal.coe_lt_top
    have hm : 0 < ‖Gamma (B w₀ + N)‖ / 2 := by
      have hpole : ∀ k : ℕ, B w₀ + N ≠ -k := fun k h => by
        have := congrArg Complex.re h
        simp only [Complex.neg_re, Complex.natCast_re] at this
        linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
      have := norm_pos_iff.mpr (Gamma_ne_zero hpole)
      positivity
    refine ⟨fun n => (‖Gamma (B w₀ + N)‖ / 2)⁻¹ * (‖p n‖ * (‖z‖₊ : ℝ) ^ n),
      (p.summable_norm_mul_pow hz').mul_left _, ?_⟩
    intro n hn w hw
    obtain ⟨hAw, hCw, hVw⟩ := hU w hw
    have hre : 1 ≤ (B w + N).re := by
      simp only [Complex.add_re, Complex.natCast_re] at hre0 ⊢
      linarith
    simpa only [coe_nnnorm] using norm_confluent_term_le_majorant hAw.le hre hm (hV _ hVw).le hn

/-- `𝐌(a,b,z)` is entire in `b`. -/
theorem analyticOnNhd_regularizedConfluent_b (a z : ℂ) :
    AnalyticOnNhd ℂ (fun b => regularizedHGFun {a} {b} z) univ :=
  analyticOnNhd_regularizedConfluent_comp (differentiable_const a) differentiable_id z

/-- `𝐌(a,b,z)` is entire in `a`. -/
theorem analyticOnNhd_regularizedConfluent_a (b z : ℂ) :
    AnalyticOnNhd ℂ (fun a => regularizedHGFun {a} {b} z) univ :=
  analyticOnNhd_regularizedConfluent_comp differentiable_id (differentiable_const b) z

@[fun_prop]
theorem analyticAt_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z w : ℂ) :
    AnalyticAt ℂ (fun w => regularizedHGFun {A w} {B w} z) w :=
  analyticOnNhd_regularizedConfluent_comp hA hB z w (mem_univ w)

@[fun_prop]
theorem differentiable_regularizedConfluent_comp {A B : ℂ → ℂ} (hA : Differentiable ℂ A)
    (hB : Differentiable ℂ B) (z : ℂ) :
    Differentiable ℂ (fun w => regularizedHGFun {A w} {B w} z) :=
  fun w => (analyticAt_regularizedConfluent_comp hA hB z w).differentiableAt

/-- Off the poles of `Γ(b)`, `𝐌(a,b,z) = M(a,b,z)/Γ(b)`. -/
lemma regularizedConfluent_eq_div_Gamma {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) (z : ℂ) :
    regularizedHGFun {a} {b} z = confluentM a b z / Gamma b := by
  rw [confluentM_eq_mul_regularizedHGFun hb, mul_div_cancel_left₀ _ (Gamma_ne_zero hb)]

/-! ### Derivative -/

lemma regularizedHGFunCoeff_singleton_succ (a b : ℂ) (n : ℕ) :
    (n + 1 : ℂ) * regularizedHGFunCoeff {a} {b} (n + 1) =
      a * regularizedHGFunCoeff {a + 1} {b + 1} n := by
  rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, poch_succ_left,
    show b + ((n + 1 : ℕ) : ℂ) = b + 1 + n by push_cast; ring, Nat.factorial_succ]
  push_cast
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  field_simp

/-- At a denominator pole, the normalized ordinary Kummer function converges
along the punctured parameter neighborhood to the entire regularized function.
The puncture is essential: the totalized quotient has value zero at the pole. -/
@[dlmf 13.2.E5]
theorem tendsto_confluentM_div_Gamma_at_neg_nat (a : ℂ) (n : ℕ) (z : ℂ) :
    Tendsto (fun b : ℂ => confluentM a b z / Gamma b) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedHGFun {a} {(-(n : ℂ))} z)) := by
  have ht : Tendsto (fun b => regularizedHGFun {a} {b} z) (𝓝[≠] (-(n : ℂ)))
      (𝓝 (regularizedHGFun {a} {(-(n : ℂ))} z)) :=
    ((analyticOnNhd_regularizedConfluent_b a z) (-(n : ℂ))
      (Set.mem_univ _)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  apply ht.congr'
  filter_upwards [eventually_nhdsWithin_ne_neg_nat n] with b hb
  exact regularizedConfluent_eq_div_Gamma hb z

/-- 13.3.15 for the regularized function: `𝐌'(a,b,z) = a 𝐌(a+1,b+1,z)`, with no hypothesis
on the parameters. -/
theorem deriv_regularizedConfluent (a b z : ℂ) :
    deriv (regularizedHGFun {a} {b}) z = a * regularizedHGFun {a + 1} {b + 1} z := by
  have hd := (hasFPowerSeriesOnBall_regularizedConfluent a b).deriv_ofScalars.hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  have hs := ((hasFPowerSeriesOnBall_regularizedConfluent (a + 1) (b + 1)).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).mul_left a
  refine hd.unique ?_
  convert hs using 1
  funext n
  rw [← mul_assoc, regularizedHGFunCoeff_singleton_succ]

lemma differentiableAt_regularizedConfluent (a b z : ℂ) :
    DifferentiableAt ℂ (regularizedHGFun {a} {b}) z :=
  ((hasFPowerSeriesOnBall_regularizedConfluent a b).analyticAt_of_mem
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt

/-- 13.3.15 iterated, for the regularized function and all parameters:
`𝐌⁽ⁿ⁾(a,b,z) = (a)ₙ 𝐌(a+n,b+n,z)`. -/
theorem iteratedDeriv_regularizedConfluent (a b : ℂ) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (regularizedHGFun {a} {b}) z =
      poch a n * regularizedHGFun {a + n} {b + n} z := by
  induction n generalizing z with
  | zero => simp [iteratedDeriv_zero, poch_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, funext ih, deriv_const_mul _ (differentiableAt_regularizedConfluent _ _ _),
      deriv_regularizedConfluent, poch_succ,
      show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring,
      show b + ((n + 1 : ℕ) : ℂ) = b + n + 1 by push_cast; ring]
    ring

/-! ### Regularized contiguous relations (all parameters) -/

/-- 13.3.1 (`confluentM_contiguous_a`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_a (a b z : ℂ) :
    (b - a) * regularizedHGFun {a - 1} {b} z + (2 * a - b + z) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (b - a) * regularizedHGFun {a - 1} {b} z + (2 * a - b + z) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_a (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb]
  field_simp
  linear_combination h

/-- 13.3.2 (`confluentM_contiguous_b`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_b (a b z : ℂ) :
    regularizedHGFun {a} {b - 1} z + (1 - b - z) * regularizedHGFun {a} {b} z + z * (b - a) * regularizedHGFun {a} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => regularizedHGFun {a} {b - 1} z + (1 - b - z) * regularizedHGFun {a} {b} z + z * (b - a) * regularizedHGFun {a} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_b (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, regularizedConfluent_eq_div_Gamma hb1, hΓ1, hΓm]
  field_simp
  linear_combination h

/-- 13.3.3 (`confluentM_contiguous_a_b`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_a_b (a b z : ℂ) :
    (a - b + 1) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z + regularizedHGFun {a} {b - 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (a - b + 1) * regularizedHGFun {a} {b} z - a * regularizedHGFun {a + 1} {b} z + regularizedHGFun {a} {b - 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_a_b (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, hΓm]
  field_simp
  linear_combination h

/-- 13.3.4 (`confluentM_contiguous_shift_a`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_shift_a (a b z : ℂ) :
    regularizedHGFun {a} {b} z - regularizedHGFun {a - 1} {b} z - z * regularizedHGFun {a} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => regularizedHGFun {a} {b} z - regularizedHGFun {a - 1} {b} z - z * regularizedHGFun {a} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_shift_a (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- 13.3.5 (`confluentM_contiguous_mixed`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_mixed (a b z : ℂ) :
    (a + z) * regularizedHGFun {a} {b} z + z * (a - b) * regularizedHGFun {a} {b + 1} z - a * regularizedHGFun {a + 1} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (a + z) * regularizedHGFun {a} {b} z + z * (a - b) * regularizedHGFun {a} {b + 1} z - a * regularizedHGFun {a + 1} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_mixed (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- 13.3.6 (`confluentM_contiguous_down`) for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_down (a b z : ℂ) :
    (a - 1 + z) * regularizedHGFun {a} {b} z + (b - a) * regularizedHGFun {a - 1} {b} z - regularizedHGFun {a} {b - 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (a - 1 + z) * regularizedHGFun {a} {b} z + (b - a) * regularizedHGFun {a - 1} {b} z - regularizedHGFun {a} {b - 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_down (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, hΓm]
  field_simp
  linear_combination h

/-- `confluentM_contiguous_shift_b_succ` for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_shift_b_succ (a b z : ℂ) :
    a * regularizedHGFun {a + 1} {b + 1} z = (a - b) * regularizedHGFun {a} {b + 1} z + regularizedHGFun {a} {b} z := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => a * regularizedHGFun {a + 1} {b + 1} z)
    (g := fun b => (a - b) * regularizedHGFun {a} {b + 1} z + regularizedHGFun {a} {b} z) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_shift_b_succ (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, hΓ1]
  field_simp
  linear_combination h

/-- `confluentM_contiguous_mixed_b_pred` for the regularized function, valid for all parameters. -/
theorem regularizedConfluent_contiguous_mixed_b_pred (a b z : ℂ) :
    (b - 1) * regularizedHGFun {a} {b} z - regularizedHGFun {a} {b - 1} z + a * z * regularizedHGFun {a + 1} {b + 1} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat_sub_one (f := fun b => (b - 1) * regularizedHGFun {a} {b} z - regularizedHGFun {a} {b - 1} z + a * z * regularizedHGFun {a + 1} {b + 1} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hbm
  have hb : ∀ k : ℕ, b ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hbm 1
  have hbm0 : b - 1 ≠ 0 := by simpa using hbm 0
  have hΓm : Gamma b = (b - 1) * Gamma (b - 1) := by
    have := Gamma_add_one (b - 1) hbm0
    rwa [sub_add_cancel] at this
  have hΓm0 : Gamma (b - 1) ≠ 0 := Gamma_ne_zero hbm
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have h := confluentM_contiguous_mixed_b_pred (a := a) (z := z) hbm
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hbm, regularizedConfluent_eq_div_Gamma hb1, hΓ1, hΓm]
  field_simp
  linear_combination h

/-- 13.3.13 (`confluentM_ode_contiguous`) for the regularized function, valid for all
parameters. -/
theorem regularizedConfluent_ode_contiguous (a b z : ℂ) :
    (a + 1) * z * regularizedHGFun {a + 2} {b + 2} z + (b - z) * regularizedHGFun {a + 1} {b + 1} z -
      regularizedHGFun {a} {b} z = 0 := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => (a + 1) * z * regularizedHGFun {a + 2} {b + 2} z +
      (b - z) * regularizedHGFun {a + 1} {b + 1} z - regularizedHGFun {a} {b} z)
    (g := fun b => 0) (by intro b _; fun_prop) (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  have hb1 : ∀ k : ℕ, b + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 1
  have hb2 : ∀ k : ℕ, b + 2 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat hb 2
  have hb0 : b ≠ 0 := by simpa using hb 0
  have hb10 : b + 1 ≠ 0 := by simpa using hb1 0
  have hΓ0 : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hΓ1 : Gamma (b + 1) = b * Gamma b := Gamma_add_one b hb0
  have hΓ2 : Gamma (b + 2) = (b + 1) * Gamma (b + 1) := by
    have := Gamma_add_one (b + 1) hb10
    rwa [show b + 1 + 1 = b + 2 by ring] at this
  have h := confluentM_ode_contiguous (a := a) (z := z) hb
  simp only [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb1, regularizedConfluent_eq_div_Gamma hb2, hΓ2, hΓ1]
  field_simp
  linear_combination h

/-- Kummer's transformation 13.2.39 for the regularized function, valid for all parameters:
`𝐌(a,b,z) = e^z 𝐌(b-a,b,-z)`. -/
theorem regularizedConfluent_kummer_transform (a b z : ℂ) :
    regularizedHGFun {a} {b} z = exp z * regularizedHGFun {b - a} {b} (-z) := by
  have key := eq_of_eqOn_not_neg_nat (f := fun b => regularizedHGFun {a} {b} z)
    (g := fun b => exp z * regularizedHGFun {b - a} {b} (-z)) (by intro b _; fun_prop)
    (by intro b _; fun_prop) ?_
  · exact congrFun key b
  intro b hb
  rw [regularizedConfluent_eq_div_Gamma hb, regularizedConfluent_eq_div_Gamma hb, confluentM_kummer_transform hb]
  ring

end AAR.Confluent
