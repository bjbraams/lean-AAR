/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.IntegerCompl
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Hypergeometric.Series
public import AAR.Hypergeometric.EulerIntegral
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Group.Tannery
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.Normed.Algebra.Exponential
public import Mathlib.Analysis.Complex.RealDeriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Kummer's function `M(a,c,z) = ₁F₁(a;c;z)` (AAR §4.1)

The series is entire in `z` (AAR: the confluent limit of `₂F₁`). Mathlib's
`regularizedHGFun {a} {c}` is the regularized form `M(a,c,z)/Γ(c)`.
Tricomi's `U` uses the connection formula off the integers and parameter limits
at integers; `confluentU_zero` verifies the continuation at zero first parameter.
`confluentUOnLog` retains the logarithmic argument needed for monodromy.
-/

@[expose] public section

open Complex Filter intervalIntegral
open scoped Real Nat Topology ENNReal

noncomputable section

/-- The coefficient of `z^n` in Kummer's confluent series. -/
abbrev confluentHGCoeff (a c : ℂ) (n : ℕ) : ℂ :=
  poch a n / (poch c n * n !)

/-- Kummer's function `M(a,c,z) = ₁F₁(a;c;z)`. -/
@[dlmf 13.2.E2]
def confluentM (a c z : ℂ) : ℂ :=
  ∑' n : ℕ, poch a n / (poch c n * n !) * z ^ n

@[simp]
theorem confluentM_zero (a c : ℂ) : confluentM a c 0 = 1 := by
  unfold confluentM
  have h0 : (fun n : ℕ => poch a n / (poch c n * n !) * (0 : ℂ) ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp [pow_succ]
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- `₁F₁(a;a;z) = e^z` when `a` is not a nonpositive integer. -/
@[dlmf 13.6.E1]
theorem confluentM_self {a z : ℂ} (ha : ∀ k : ℕ, a ≠ -k) :
    confluentM a a z = exp z := by
  unfold confluentM
  have hcoeff : ∀ n : ℕ, poch a n / (poch a n * n !) * z ^ n = z ^ n / n ! := by
    intro n
    have hne := poch_ne_zero_of_not_neg_nat ha n
    field [hne]
  simp_rw [hcoeff]
  simpa [exp_eq_exp_ℂ] using (congrFun (NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)) z).symm

/-- A terminating `₁F₁(-n;c;z)` is a polynomial of degree at most `n`. -/
lemma confluentM_eq_sum_neg_nat (n : ℕ) (c z : ℂ) :
    confluentM (-(n : ℂ)) c z =
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k / (poch c k * k.factorial) * z ^ k := by
  unfold confluentM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [poch_neg_nat_eq_zero hkn]

/-- `₁F₁(0;c;z) = 1`. -/
@[dlmf 13.6.E3]
theorem confluentM_of_zero_param (c z : ℂ) : confluentM 0 c z = 1 := by
  unfold confluentM
  have h0 : (fun n : ℕ => poch 0 n / (poch c n * n !) * z ^ n) =
      fun n => if n = 0 then 1 else 0 := by
    ext n
    cases n with
    | zero => simp [poch_zero]
    | succ n => simp
  rw [h0, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

lemma regularizedHGFunCoeff_singleton (a c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {c} n = poch a n / (n ! * Gamma (c + n)) := by
  simp [regularizedHGFunCoeff, poch]

lemma regularizedHGFun_eq_tsum (a b : Multiset ℂ) (z : ℂ) :
    regularizedHGFun a b z = ∑' n : ℕ, regularizedHGFunCoeff a b n * z ^ n := by
  unfold regularizedHGFun regularizedHGFunSeries
  rw [FormalMultilinearSeries.sum]
  simp_rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

lemma regularizedHGFun_zero (a b : Multiset ℂ) :
    regularizedHGFun a b 0 = regularizedHGFunCoeff a b 0 := by
  rw [regularizedHGFun_eq_tsum]
  have h : (fun n : ℕ => regularizedHGFunCoeff a b n * (0 : ℂ) ^ n) =
      fun n => if n = 0 then regularizedHGFunCoeff a b 0 else 0 := by
    ext n
    cases n with
    | zero => simp
    | succ n => simp [pow_succ]
  rw [h, tsum_eq_single 0]
  · simp
  · intro n hn
    simp [hn]

/-- The coefficient comparison with Mathlib's regularized confluent series. -/
lemma confluentHGCoeff_eq_mul_regularizedHGFunCoeff {a c : ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    confluentHGCoeff a c n = Gamma c * regularizedHGFunCoeff {a} {c} n := by
  have hp : poch c n = Gamma (c + n) / Gamma c :=
    (Gamma_add_nat_div_Gamma_eq (n := n) c hc).symm
  have hc0 : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hcn : Gamma (c + n) ≠ 0 := Gamma_ne_zero (not_neg_nat_add_nat hc n)
  rw [confluentHGCoeff, hp, regularizedHGFunCoeff_singleton]
  field [hc0, hcn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Recover Kummer's `M` from Mathlib's regularized `₁F₁`. -/
@[dlmf 13.2.E4]
theorem confluentM_eq_mul_regularizedHGFun {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    confluentM a c z = Gamma c * regularizedHGFun {a} {c} z := by
  unfold confluentM
  simp_rw [show ∀ n : ℕ, poch a n / (poch c n * n !) =
    Gamma c * regularizedHGFunCoeff {a} {c} n from
      confluentHGCoeff_eq_mul_regularizedHGFunCoeff hc]
  rw [regularizedHGFun_eq_tsum, ← tsum_mul_left]
  exact tsum_congr fun n => by ring

/-- Kummer's series has infinite radius, by Mathlib's convergence theorem for the
regularized hypergeometric series. -/
theorem hasFPowerSeriesOnBall_confluentM {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    HasFPowerSeriesOnBall (confluentM a c)
      (FormalMultilinearSeries.ofScalars ℂ (confluentHGCoeff a c)) 0 ⊤ := by
  have hr : (regularizedHGFunSeries {a} {c}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a} {c})
      (regularizedHGFunSeries {a} {c}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {c}).sum
      (regularizedHGFunSeries {a} {c}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a} {c}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht := hs.const_smul (c := Gamma c)
  have hp : Gamma c • regularizedHGFunSeries {a} {c} =
      FormalMultilinearSeries.ofScalars ℂ (confluentHGCoeff a c) := by
    rw [regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalars_smul]
    congr 1
    funext n
    exact (confluentHGCoeff_eq_mul_regularizedHGFunCoeff hc n).symm
  have hf : Gamma c • regularizedHGFun {a} {c} = confluentM a c := by
    funext z
    exact (confluentM_eq_mul_regularizedHGFun hc).symm
  rwa [hp, hf] at ht

/-- The coefficient recurrence for the confluent hypergeometric equation. -/
lemma confluentHGCoeff_recurrence {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (n + 1 : ℂ) * (c + n) * confluentHGCoeff a c (n + 1) =
      (a + n) * confluentHGCoeff a c n := by
  have hcp := poch_ne_zero_of_not_neg_nat hc n
  have hcn : c + (n : ℂ) ≠ 0 := by
    simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
  have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simp only [confluentHGCoeff, poch_succ, Nat.factorial_succ,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field [hcp, hcn, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- Chu–Vandermonde evaluates the coefficient convolution in Kummer's transformation. -/
lemma confluentHGCoeff_kummer_convolution {a c : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      confluentHGCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial) =
      confluentHGCoeff a c n := by
  have hn : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      confluentHGCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial =
        gaussHGCoeff (-(n : ℂ)) (c - a) c k / n.factorial := by
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hk0 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hnk : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (n - k).factorial_ne_zero
    have hch : (n.choose k : ℂ) = n.factorial / (k.factorial * (n - k).factorial) := by
      apply (eq_div_iff (mul_ne_zero hk0 hnk)).2
      simpa [mul_assoc] using congrArg (Nat.cast : ℕ → ℂ)
        (Nat.choose_mul_factorial_mul_factorial hk')
    rw [gaussHGCoeff_neg_nat, hch]
    unfold confluentHGCoeff
    field [hn, hk0, hnk, poch_ne_zero_of_not_neg_nat hc k]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div]
  have hv := chu_vandermonde n (b := c - a) hc
  rw [ordinaryHypergeometric_eq_sum_neg_nat] at hv
  simp only [one_pow, mul_one, sub_sub_cancel] at hv
  rw [hv]
  unfold confluentHGCoeff
  ring

/-- Kummer's transformation `M(a,c,z) = e^z M(c-a,c,-z)` (AAR (4.1.11), p. 191).
AAR excludes nonpositive integer denominator parameters in §2.1, p. 62; that standing
restriction must be explicit for our totalized series. There is also a typographical error
in the supplied AAR printing: the right-hand denominator in (4.1.11) is printed as `a`
instead of `c`. The formula below uses the intended denominator `c`. -/
@[dlmf 13.2.E39]
theorem confluentM_kummer_transform {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) :
    confluentM a c z = exp z * confluentM (c - a) c (-z) := by
  have hf := (hasFPowerSeriesOnBall_confluentM (a := c - a) hc).hasSum_mul_pow
    (z := -z) (by simp)
  have hg : HasSum (fun n : ℕ => z ^ n / n.factorial) (exp z) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp z
  rw [mul_comm, ← hf.tsum_eq, ← hg.tsum_eq,
    tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm hf.summable.norm hg.summable.norm]
  unfold confluentM
  apply tsum_congr
  intro n
  change confluentHGCoeff a c n * z ^ n = _
  rw [← confluentHGCoeff_kummer_convolution hc n, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hp : z ^ k * z ^ (n - k) = z ^ n := by
    rw [← pow_add, Nat.add_sub_of_le hk']
  symm
  rw [neg_pow]
  calc
    _ = (confluentHGCoeff (c - a) c k * (-1 : ℂ) ^ k / (n - k).factorial) *
        (z ^ k * z ^ (n - k)) := by ring
    _ = _ := by rw [hp]

/-- The confluent hypergeometric equation
`z y'' + (c-z) y' - a y = 0` (AAR §4.1). -/
@[dlmf 13.2.E1]
theorem confluentM_ode {a c z : ℂ} (hc : ∀ k : ℕ, c ≠ -k) (hz : z ≠ 0) :
    z * iteratedDeriv 2 (confluentM a c) z + (c - z) * deriv (confluentM a c) z -
      a * confluentM a c z = 0 := by
  have h := (hasFPowerSeriesOnBall_confluentM (a := a) hc).ode_of_recurrence
    (A := 0) (B := 1) (C := a) (D := c) (fun n => ?_)
    (z := z) (by simp)
  · simpa [iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [confluentHGCoeff_recurrence hc]
    ring

/-- Differentiating the confluent equation repeatedly gives the shifted equations. -/
lemma confluent_ode_iteratedDeriv {a c : ℂ} {f : ℂ → ℂ}
    (hf : ∀ w, AnalyticAt ℂ f w)
    (hode : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (n : ℕ) (w : ℂ) :
    w * iteratedDeriv (n + 2) f w + (c + n - w) * iteratedDeriv (n + 1) f w -
      (a + n) * iteratedDeriv n f w = 0 := by
  have ha (k : ℕ) (z : ℂ) : AnalyticAt ℂ (iteratedDeriv k f) z := by
    induction k with
    | zero => simpa only [iteratedDeriv_zero] using hf z
    | succ k ih => simpa only [iteratedDeriv_succ] using ih.deriv
  have hd (k : ℕ) (z : ℂ) : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f z) z := by
    simpa only [iteratedDeriv_succ] using (ha k z).differentiableAt.hasDerivAt
  induction n generalizing w with
  | zero => simpa only [Nat.cast_zero, add_zero, iteratedDeriv_succ, iteratedDeriv_zero] using hode w
  | succ n ih =>
    have he : (id * iteratedDeriv (n + 2) f +
        ((fun _ => c + n) - id) * iteratedDeriv (n + 1) f -
        (fun z => (a + n) * iteratedDeriv n f z)) = (fun _ => 0) := funext ih
    have ht := (((hasDerivAt_id w).mul (hd (n + 2) w)).add
      (((hasDerivAt_const w (c + n)).sub (hasDerivAt_id w)).mul (hd (n + 1) w))).sub
      ((hd n w).const_mul (a + n))
    have he' := ht.deriv
    rw [he, deriv_const] at he'
    simp only [id_eq, one_mul, zero_sub, Pi.sub_apply] at he'
    push_cast
    linear_combination -he'

/-- Entire solutions of the confluent equation are determined by their value at zero
when the denominator parameter is not a nonpositive integer. -/
lemma confluent_ode_unique {a c : ℂ} {f g : ℂ → ℂ}
    (hc : ∀ k : ℕ, c ≠ -k) (hf : ∀ w, AnalyticAt ℂ f w) (hg : ∀ w, AnalyticAt ℂ g w)
    (hfeq : ∀ w, w * deriv (deriv f) w + (c - w) * deriv f w - a * f w = 0)
    (hgeq : ∀ w, w * deriv (deriv g) w + (c - w) * deriv g w - a * g w = 0)
    (hzero : f 0 = g 0) : f = g := by
  have he (n : ℕ) : iteratedDeriv n f 0 = iteratedDeriv n g 0 := by
    induction n with
    | zero => exact hzero
    | succ n ih =>
      have hfn := confluent_ode_iteratedDeriv hf hfeq n 0
      have hgn := confluent_ode_iteratedDeriv hg hgeq n 0
      have hcn : c + (n : ℂ) ≠ 0 := by simpa only [ne_eq, eq_neg_iff_add_eq_zero] using hc n
      have hm : (c + n) * (iteratedDeriv (n + 1) f 0 - iteratedDeriv (n + 1) g 0) = 0 := by
        rw [ih] at hfn
        linear_combination hfn - hgn
      exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_left hcn)
  apply AnalyticOnNhd.eq_of_eventuallyEq (fun w _ => hf w) (fun w _ => hg w) (z₀ := 0)
  have hp := (hf 0).hasFPowerSeriesAt
  have hq := (hg 0).hasFPowerSeriesAt
  simp_rw [he] at hp
  filter_upwards [hp.eventually_hasSum_sub, hq.eventually_hasSum_sub] with w hw₁ hw₂
  exact hw₁.unique hw₂

/-- The normalized Pochhammer factors have a recurrence with limit multiplier one. -/
lemma poch_div_pow_succ {b : ℂ} (hb : b ≠ 0) (n : ℕ) :
    poch b (n + 1) / b ^ (n + 1) = (poch b n / b ^ n) * (1 + (n : ℂ) / b) := by
  rw [poch_succ, pow_succ]
  field_simp

/-- Each normalized Pochhammer symbol tends to one as its parameter tends to infinity. -/
lemma tendsto_poch_div_pow (n : ℕ) :
    Tendsto (fun b : ℕ => poch (b : ℂ) n / (b : ℂ) ^ n) atTop (𝓝 1) := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    have ht := ih.mul ((tendsto_const_div_atTop_nhds_zero_nat (n : ℂ)).const_add 1)
    simp only [add_zero, mul_one] at ht
    apply ht.congr'
    filter_upwards [Filter.eventually_ne_atTop 0] with b hb
    exact (poch_div_pow_succ (Nat.cast_ne_zero.mpr hb) n).symm

/-- `(c + t)_k / t^k → 1` as the real variable `t → ∞`. -/
lemma tendsto_poch_add_div_pow (c : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => poch (c + t) k / (t : ℂ) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h0 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have : Tendsto (fun t : ℝ => ‖c + k‖ / t) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      rw [norm_div, norm_real, Real.norm_of_nonneg ht.le]
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [poch_succ, pow_succ]
    field_simp
    ring

/-- `(-N)_k / (-N)^k → 1` as the natural number `N → ∞`. -/
lemma tendsto_poch_neg_div_pow (k : ℕ) :
    Tendsto (fun N : ℕ => poch (-(N : ℂ)) k / (-(N : ℂ)) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h0 : Tendsto (fun N : ℕ => -((k : ℂ) / N)) atTop (𝓝 0) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat (k : ℂ)).neg
    have ht := ih.mul (h0.const_add 1)
    simp only [add_zero, mul_one] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with N hN
    have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    rw [poch_succ, pow_succ]
    field_simp
    ring

/-- Normalized positive Pochhammer symbols decrease as the parameter increases. -/
lemma norm_poch_div_pow_le {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) (n : ℕ) :
    ‖poch (y : ℂ) n / (y : ℂ) ^ n‖ ≤ ‖poch (x : ℂ) n / (x : ℂ) ^ n‖ := by
  have hy : 0 < y := hx.trans_le hxy
  have hnorm (t : ℝ) (ht : 0 < t) (k : ℕ) :
      ‖1 + (k : ℂ) / (t : ℂ)‖ = 1 + (k : ℝ) / t := by
    have he : (1 : ℂ) + k / (t : ℂ) = ((1 + (k : ℝ) / t : ℝ) : ℂ) := by push_cast; rfl
    rw [he, norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hy)),
      poch_div_pow_succ (ofReal_ne_zero.mpr (ne_of_gt hx)), norm_mul, norm_mul, hnorm y hy, hnorm x hx]
    exact mul_le_mul ih (add_le_add_right (div_le_div_of_nonneg_left (Nat.cast_nonneg n) hx hxy) 1)
      (by positivity) (norm_nonneg _)

/-- Rescaled Gauss coefficients separate into confluent coefficients and a normalized Pochhammer. -/
lemma gaussHGCoeff_mul_div_pow (a b c z : ℂ) (n : ℕ) :
    gaussHGCoeff a b c n * (z / b) ^ n =
      (confluentHGCoeff a c n * z ^ n) * (poch b n / b ^ n) := by
  simp only [gaussHGCoeff, confluentHGCoeff, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Confluence: `M(a,c,z) = lim_{b→∞} ₂F₁(a,b;c;z/b)`. -/
theorem tendsto_ordinaryHypergeometric_div_atTop {a c z : ℂ} :
    Tendsto (fun b : ℕ => ₂F₁ a (b : ℂ) c (z / b)) atTop (𝓝 (confluentM a c z)) := by
  obtain ⟨B, hB⟩ := exists_nat_gt ‖z‖
  have hBpos : (0 : ℝ) < B := (norm_nonneg z).trans_lt hB
  have harg : ‖z / (B : ℂ)‖ < 1 := by
    rw [norm_div, Complex.norm_natCast, div_lt_one hBpos]
    exact hB
  let f (b n : ℕ) := gaussHGCoeff a (b : ℂ) c n * (z / b) ^ n
  let bound (n : ℕ) := ‖f B n‖
  have hsum : Summable bound :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric a (B : ℂ) c).hasSum_mul_pow
      (mem_eball_one_of_norm_lt_one harg)).summable.norm
  have hlim (n : ℕ) : Tendsto (fun b => f b n) atTop (𝓝 (confluentHGCoeff a c n * z ^ n)) := by
    simpa only [f, gaussHGCoeff_mul_div_pow, mul_one] using
      (tendsto_poch_div_pow n).const_mul (confluentHGCoeff a c n * z ^ n)
  have hbound : ∀ᶠ b : ℕ in atTop, ∀ n, ‖f b n‖ ≤ bound n := by
    filter_upwards [eventually_ge_atTop B] with b hb n
    dsimp [bound, f]
    simp only [gaussHGCoeff_mul_div_pow, norm_mul]
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    simpa only [ofReal_natCast] using norm_poch_div_pow_le hBpos (Nat.cast_le.mpr hb) n
  have ht := tendsto_tsum_of_dominated_convergence hsum hlim hbound
  have he (b : ℕ) : ₂F₁ a (b : ℂ) c (z / b) = ∑' n, f b n := by
    rw [ordinaryHypergeometric_eq_tsum]
    apply tsum_congr
    intro n
    simp only [f, gaussHGCoeff, poch, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [← he, confluentM, confluentHGCoeff] using ht


/-- The connection formula for Tricomi's function at noninteger second parameter.
At integers, totalized Gamma factors do not give the continued value. -/
def confluentUConnection (a b z : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * confluentM a b z +
    Gamma (b - 1) / Gamma a * z ^ (1 - b) * confluentM (a - b + 1) (2 - b) z

/-- Tricomi's principal-branch function, with integer second parameters assigned
by limits of the connection formula along noninteger parameters.
The definition alone does not establish existence of these limits; a `Tendsto`
theorem is required when using the integer branch. -/
@[dlmf 13.2.E42]
def confluentU (a b z : ℂ) : ℂ := by
  classical
  exact if ∀ k : ℤ, b ≠ k then confluentUConnection a b z else
    Filter.limUnder (𝓝[integerComplement] b) (fun c => confluentUConnection a c z)

/-- Tricomi's function agrees with its connection formula at noninteger parameters. -/
lemma confluentU_eq_connection (a b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    confluentU a b z = confluentUConnection a b z := by
  simp [confluentU, hb]

/-- The connection formula at zero first parameter is identically one away from integers. -/
lemma confluentUConnection_zero (b z : ℂ) (hb : ∀ k : ℤ, b ≠ k) :
    confluentUConnection 0 b z = 1 := by
  have hp : ∀ k : ℕ, 1 - b ≠ -(k : ℂ) := by
    intro k hk
    apply hb ((k : ℤ) + 1)
    push_cast
    linear_combination -hk
  simp only [confluentUConnection, confluentM_of_zero_param, Gamma_zero, div_zero,
    zero_mul, add_zero, mul_one]
  rw [show (0 : ℂ) - b + 1 = 1 - b by ring, div_self (Gamma_ne_zero hp)]

/-- The connection formula at zero first parameter converges to one at every second parameter. -/
lemma tendsto_confluentUConnection_zero (b z : ℂ) :
    Tendsto (fun c => confluentUConnection 0 c z) (𝓝[integerComplement] b) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with c hc
  symm
  apply confluentUConnection_zero c z
  intro k hk
  exact hc ⟨k, hk.symm⟩

/-- Tricomi's value at zero first parameter, including integer second parameters. -/
lemma confluentU_zero (b z : ℂ) : confluentU 0 b z = 1 := by
  classical
  unfold confluentU
  split_ifs with hb
  · exact confluentUConnection_zero b z hb
  · have hd : Dense integerComplement :=
      (Set.countable_range (fun k : ℤ => (k : ℂ))).dense_compl ℂ
    have : NeBot (𝓝[integerComplement] b) :=
      mem_closure_iff_nhdsWithin_neBot.mp (hd b)
    exact (tendsto_confluentUConnection_zero b z).limUnder_eq

/-- The noninteger connection formula on the logarithmic argument plane.
The variable `w` represents a logarithm of the actual argument `exp w`. -/
def confluentUOnLog (a b w : ℂ) : ℂ :=
  Gamma (1 - b) / Gamma (a - b + 1) * confluentM a b (exp w) +
    Gamma (b - 1) / Gamma a * exp ((1 - b) * w) *
      confluentM (a - b + 1) (2 - b) (exp w)

/-- Euler's integral for Kummer's function, obtained by integrating the exponential
series against the beta weight (AAR §4.2). This is the `M` form of DLMF 13.4.1. -/
@[dlmf 13.4.E1]
lemma confluentM_eq_euler_integral {a c z : ℂ}
    (ha : 0 < a.re) (hca : 0 < (c - a).re) :
    confluentM a c z = Gamma c / (Gamma a * Gamma (c - a)) *
      ∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1) * exp (z * t) := by
  let w : ℝ → ℂ := fun t => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (c - a - 1)
  let d : ℕ → ℂ := fun n => z ^ n / n.factorial
  let F : ℕ → ℝ → ℂ := fun n t => w t * (d n * (t : ℂ) ^ n)
  have hexp (u : ℂ) : HasSum (fun n : ℕ => u ^ n / n.factorial) (exp u) := by
    simpa only [exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp u
  have hw : IntervalIntegrable w MeasureTheory.volume 0 1 := betaIntegral_convergent ha hca
  have hd : Summable (fun n => ‖d n‖) := (hexp z).summable.norm
  have hFi (n : ℕ) : IntervalIntegrable (F n) MeasureTheory.volume 0 1 :=
    hw.mul_continuousOn (by fun_prop)
  have hs := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume)
    (F := F) (f := fun t => w t * exp (z * t))
    (fun n t => ‖d n‖ * ‖w t‖) (fun n => (hFi n).def'.aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun t ht => ?_)
    (Filter.Eventually.of_forall fun t _ => hd.mul_right ‖w t‖)
    (by simp_rw [tsum_mul_right]; exact hw.norm.const_mul _)
    (Filter.Eventually.of_forall fun t _ => ?_)
  · have hterm (n : ℕ) : ∫ t : ℝ in (0 : ℝ)..1, F n t =
        betaIntegral (a + n) (c - a) / n.factorial * z ^ n := by
      rw [betaIntegral, div_eq_mul_inv, ← intervalIntegral.integral_mul_const,
        ← intervalIntegral.integral_mul_const]
      apply intervalIntegral.integral_congr_Ioo_of_le (by norm_num)
      intro t ht
      have hp : (t : ℂ) ^ (a + n - 1) = (t : ℂ) ^ (a - 1) * (t : ℂ) ^ n := by
        rw [show a + n - 1 = (a - 1) + n by ring,
          cpow_add _ _ (ofReal_ne_zero.mpr ht.1.ne'), cpow_natCast]
      dsimp [F, w, d]
      rw [hp]
      ring
    have hscaled (n : ℕ) : Gamma c / (Gamma a * Gamma (c - a)) *
        (∫ t : ℝ in (0 : ℝ)..1, F n t) = confluentHGCoeff a c n * z ^ n := by
      have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
      have he := euler_term_eq_gaussHGCoeff (a := 1) n ha hca
      simp only [poch_nat_one, div_self hf, one_mul, gaussHGCoeff] at he
      rw [hterm]
      dsimp [confluentHGCoeff]
      linear_combination (norm := (field_simp; ring)) (z ^ n / n.factorial) * he
    have hs' := hs.mul_left (Gamma c / (Gamma a * Gamma (c - a)))
    simp_rw [hscaled] at hs'
    exact hs'.tsum_eq
  · rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    have ht1 : ‖(t : ℂ)‖ ≤ 1 := by
      simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht.1] using ht.2
    calc
      ‖F n t‖ = ‖w t‖ * (‖d n‖ * ‖(t : ℂ)‖ ^ n) := by
        simp only [F, norm_mul, norm_pow]
      _ ≤ ‖w t‖ * (‖d n‖ * 1) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg _) ht1) (norm_nonneg _))
          (norm_nonneg _)
      _ = _ := by ring
  · convert (hexp (z * t)).mul_left (w t) using 1
    congr 1
    funext n
    simp only [F, d, mul_pow]
    ring

/-- Barnes's integral for `₁F₁`, AAR Theorem 4.2.1, along the upward vertical
line `s = σ + it`, with `-Re a < σ < 0`. -/
theorem confluentM_eq_barnes_integral {a c z : ℂ} {σ : ℝ}
    (haσ : -a.re < σ) (hσ : σ < 0) (hc : ∀ k : ℕ, c ≠ -k)
    (hz : z ≠ 0) (harg : |(-z).arg| < π / 2) :
    confluentM a c z =
      Gamma c / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (-(σ + I * t)) * Gamma (a + σ + I * t) /
          Gamma (c + σ + I * t) * (-z) ^ (σ + I * t) * I := by
  sorry

/-- The error function as a confluent series, AAR §4.4:
`erf z = (2z/√π) M(1/2, 3/2, -z²)`. -/
@[dlmf 13.6.E7]
def errorFn (z : ℂ) : ℂ :=
  (2 : ℂ) / (Real.sqrt π : ℂ) * z * confluentM (1 / 2) (3 / 2) (-(z ^ 2))

/-- Complementary error function `erfc z = 1 - erf z`. -/
def erfcFn (z : ℂ) : ℂ := 1 - errorFn z

theorem errorFn_zero : errorFn 0 = 0 := by simp [errorFn]

/-- The coefficient identity for the Gaussian antiderivative. -/
lemma confluentHGCoeff_half (n : ℕ) :
    (2 * n + 1 : ℂ) * confluentHGCoeff (1 / 2) (3 / 2) n = 1 / n.factorial := by
  have hp : poch (1 / 2 : ℂ) n ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (fun k hk => by
      have he := congrArg Complex.re hk
      simp at he
      have := Nat.cast_nonneg (α := ℝ) k
      linarith) n
  have hn : (2 * n + 1 : ℂ) ≠ 0 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  rw [confluentHGCoeff, poch_three_halves_eq]
  field [hp, hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- A first-order relation between the confluent series and the exponential. -/
lemma confluentM_half_add_two_mul_deriv (w : ℂ) :
    confluentM (1 / 2) (3 / 2) w +
      2 * w * deriv (confluentM (1 / 2) (3 / 2)) w = exp w := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_confluentM (a := (1 / 2 : ℂ)) hc
  have hs := (hf.hasSum_mul_pow (z := w) (by simp)).add
    ((hf.hasSum_z_mul_deriv (z := w) (by simp)).mul_left 2)
  have heq : (fun n : ℕ => confluentHGCoeff (1 / 2) (3 / 2) n * w ^ n +
      2 * ((n : ℂ) * confluentHGCoeff (1 / 2) (3 / 2) n * w ^ n)) =
      (fun n : ℕ => w ^ n / n.factorial) := by
    funext n
    calc
      _ = ((2 * n + 1 : ℂ) * confluentHGCoeff (1 / 2) (3 / 2) n) * w ^ n := by ring
      _ = _ := by rw [confluentHGCoeff_half]; ring
  rw [heq] at hs
  simpa [mul_assoc] using hs.unique (by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w)

/-- Differentiating the confluent representation gives the Gaussian. -/
lemma hasDerivAt_gaussianPrimitive (z : ℂ) :
    HasDerivAt (fun z : ℂ => z * confluentM (1 / 2) (3 / 2) (-(z ^ 2)))
      (exp (-(z ^ 2))) z := by
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -k := by
    intro k hk
    have he := congrArg Complex.re hk
    simp at he
    have := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hf := hasFPowerSeriesOnBall_confluentM (a := (1 / 2 : ℂ)) hc
  have hm := (hf.analyticAt_of_mem (y := -(z ^ 2)) (by simp)).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_id z).mul (hm.comp z (((hasDerivAt_id z).pow 2).neg))
  convert! hd using 1
  have h := confluentM_half_add_two_mul_deriv (-(z ^ 2))
  simp only [id_eq, Function.comp_apply, Pi.neg_apply, Pi.pow_apply,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, one_mul]
  linear_combination -h

/-- Integral representation `erf z = (2/√π) ∫_0^z e^{-t²} dt`. -/
@[dlmf 7.2.E1]
theorem errorFn_eq_integral (z : ℝ) :
    errorFn z =
      (2 : ℂ) / (Real.sqrt π : ℂ) *
        ∫ t : ℝ in (0 : ℝ)..z, Complex.exp (-(t : ℂ) ^ 2) := by
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ Set.uIcc (0 : ℝ) z) => (hasDerivAt_gaussianPrimitive (x : ℂ)).comp_ofReal)
    (show IntervalIntegrable (fun t : ℝ => exp (-(t : ℂ) ^ 2)) MeasureTheory.volume 0 z from
      Continuous.intervalIntegrable (by fun_prop) _ _)
  simpa [errorFn, mul_assoc] using congrArg (fun w : ℂ => (2 : ℂ) / Real.sqrt π * w) hi.symm

/-- Lower incomplete gamma via `₁F₁`, AAR §4.4:
`γ(s,z) = z^s / s · M(s, s+1, -z)`. -/
@[dlmf 13.6.E5]
def lowerIncompleteGamma (s z : ℂ) : ℂ :=
  z ^ s / s * confluentM s (s + 1) (-z)

/-- The parabolic zero-free regions of AAR Corollary 4.16.4. -/
theorem confluentM_ne_zero_of_mem_parabolicRegion {a c α : ℝ} {z : ℂ}
    (hparams : (0 < c ∧ c ≤ a ∧ α = c / a) ∨
      (1 ≤ a ∧ a ≤ c ∧ α = 1) ∨
      (0 < a ∧ a < 1 ∧ a ≤ c ∧ c < 2 * a / (1 - a) ∧
        α = (2 * a - c + c * a) / (a ^ 2 + a)))
    (hre : -α < z.re) (him : z.im ^ 2 < 4 * α * (z.re + α)) :
    confluentM a c z ≠ 0 := by
  sorry
