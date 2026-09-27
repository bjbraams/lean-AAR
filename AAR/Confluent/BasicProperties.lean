/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Hypergeometric.Continuation
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Kummer `M` and Tricomi `U`: remaining basic properties (DLMF §13.2)

Olver's regularized function `𝐌(a,b,z)` is Mathlib's `regularizedHGFun {a} {b}`.
The series `confluentM` is entire in `z` at regular denominator parameters; `confluentU`
uses the connection formula 13.2.42 and parameter limits at integer `b`.
The proved Kummer transformation currently retains a noninteger hypothesis;
extending it to the limit branch remains a separate task. Complex powers use the principal branch on the slit plane. Numerically
satisfactory pairs (13.2.24–13.2.26) are recorded as Wronskian identities on
the indicated argument sectors.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

/-- Wronskian `f g' - g f'`. -/
def wronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - g z * deriv f z

@[dlmf 13.2.E5]
theorem regularizedHGFun_of_neg_nat (a : ℂ) (n : ℕ) (z : ℂ) :
    regularizedHGFun {a} {(-(n : ℂ))} z =
      poch a (n + 1) / (n + 1).factorial * z ^ (n + 1) *
        confluentM (a + n + 1) (n + 2) z := by
  rw [regularizedHGFun_eq_tsum]
  have hs : Summable fun k : ℕ => regularizedHGFunCoeff {a} {(-(n : ℂ))} k * z ^ k := by
    have hr : (regularizedHGFunSeries {a} {(-(n : ℂ))}).radius = ⊤ :=
      radius_regularizedHGFunSeries_eq_top (by simp)
    have hp : HasFPowerSeriesOnBall (regularizedHGFun {a} {(-(n : ℂ))})
        (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff {a} {(-(n : ℂ))})) 0 ⊤ := by
      change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {(-(n : ℂ))}).sum
        (regularizedHGFunSeries {a} {(-(n : ℂ))}) 0 ⊤
      simpa only [hr] using
        (regularizedHGFunSeries {a} {(-(n : ℂ))}).hasFPowerSeriesOnBall (by rw [hr]; simp)
    exact (hp.hasSum_mul_pow (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)).summable
  rw [← hs.sum_add_tsum_nat_add (n + 1)]
  have hzero : ∀ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff {a} {(-(n : ℂ))} k * z ^ k = 0 := by
    intro k hk
    have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have : (-(n : ℂ) + k) = -((n - k : ℕ) : ℂ) := by push_cast [Nat.cast_sub hk']; ring
    rw [regularizedHGFunCoeff_singleton, this, Complex.Gamma_neg_nat_eq_zero, mul_zero, div_zero,
      zero_mul]
  rw [Finset.sum_eq_zero hzero, zero_add]
  have hpole : ∀ k : ℕ, ((n : ℂ) + 2) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.natCast_re, Complex.re_ofNat, Complex.neg_re] at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hF := (hasFPowerSeriesOnBall_confluentM (a := a + n + 1) hpole).hasSum_mul_pow
    (by simp : z ∈ Metric.eball (0 : ℂ) ⊤)
  rw [← hF.tsum_eq, ← tsum_mul_left]
  congr 1
  funext j
  have hΓ : Gamma ((n : ℂ) + 2 + j) = (ascPochhammer ℂ j).eval ((n : ℂ) + 2) * Gamma ((n : ℂ) + 2) := by
    rw [← Gamma_add_nat_div_Gamma_eq (n := j) ((n : ℂ) + 2) hpole]
    field_simp [Gamma_ne_zero hpole]
  have hΓ1 : Gamma ((n : ℂ) + 2 + j) = ((n + 1 + j).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 + j = ((n + 1 + j : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ2 : Gamma ((n : ℂ) + 2) = ((n + 1).factorial : ℂ) := by
    rw [show (n : ℂ) + 2 = ((n + 1 : ℕ) : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hΓ3 : Gamma (-(n : ℂ) + ((j + (n + 1) : ℕ) : ℂ)) = (j.factorial : ℂ) := by
    rw [show -(n : ℂ) + ((j + (n + 1) : ℕ) : ℂ) = (j : ℂ) + 1 by push_cast; ring]
    exact Complex.Gamma_nat_eq_factorial _
  have hp : (ascPochhammer ℂ j).eval ((n : ℂ) + 2) ≠ 0 := poch_ne_zero_of_not_neg_nat hpole j
  have hf1 : ((n + 1).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : ((n + 1 + j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [hΓ1, hΓ2] at hΓ
  rw [regularizedHGFunCoeff_singleton, hΓ3]
  simp only [confluentHGCoeff, poch]
  rw [add_comm j (n + 1), AAR.Hypergeometric.ascPochhammer_eval_add a,
    show a + ((n + 1 : ℕ) : ℂ) = a + n + 1 by push_cast; ring, pow_add]
  field_simp
  rw [hΓ]
  ring

/- The punctured parameter-limit theorem is proved in `AAR.Confluent.Continuation`. -/

@[dlmf 13.2.E6]
theorem tendsto_confluentU_mul_cpow_atTop (a b : ℂ) :
    Tendsto (fun x : ℝ => confluentU a b x * (x : ℂ) ^ a) atTop (𝓝 1) := by
  sorry

/-- Polynomial specialization of Tricomi U, expressed using ordinary Kummer M. -/
@[dlmf 13.2.E7]
theorem confluentU_neg_nat (m : ℕ) (b z : ℂ) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentU (-(m : ℂ)) b z =
      (-1 : ℂ) ^ m * poch b m * confluentM (-(m : ℂ)) b z := by
  sorry

@[dlmf 13.2.E7]
theorem confluentU_neg_nat_sum (m : ℕ) (b z : ℂ) :
    confluentU (-(m : ℂ)) b z =
      (-1 : ℂ) ^ m * ∑ s ∈ Finset.range (m + 1),
        (m.choose s : ℂ) * poch (b + s) (m - s) * (-z) ^ s := by
  sorry

/-- A shifted Tricomi identity with a regular denominator in ordinary Kummer M. -/
@[dlmf 13.2.E8]
theorem confluentU_shift_nat (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, 1 - a - n ≠ -k) :
    confluentU a (a + n + 1) z =
      (-1 : ℂ) ^ n * poch (1 - a - n) n / z ^ (a + n) *
        confluentM (-(n : ℂ)) (1 - a - n) z := by
  sorry

@[dlmf 13.2.E8]
theorem confluentU_shift_nat_sum (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    confluentU a (a + n + 1) z =
      z ^ (-a) * ∑ s ∈ Finset.range (n + 1),
        (n.choose s : ℂ) * poch a s * z ^ (-(s : ℂ)) := by
  sorry

@[dlmf 13.2.E9]
theorem confluentU_nat_denom (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a - n ≠ -k) :
    confluentU a (n + 1) z =
      (-1 : ℂ) ^ (n + 1) / ((n.factorial : ℂ) * Gamma (a - n)) *
        ∑' k : ℕ, poch a k / (poch (n + 1 : ℂ) k * k.factorial) * z ^ k *
          (log z + digamma (a + k) - digamma (1 + k) - digamma (n + k + 1)) +
        1 / Gamma a * ∑ k ∈ Finset.Icc 1 n,
          ((k - 1).factorial : ℂ) * poch (1 - a + k) (n - k) /
            ((n - k).factorial : ℂ) * z ^ (-(k : ℂ)) := by
  sorry

/-- Polynomial specialization at positive integer second parameter, using the continued U. -/
@[dlmf 13.2.E10]
theorem confluentU_neg_nat_nat_denom (m n : ℕ) (z : ℂ) :
    confluentU (-(m : ℂ)) (n + 1) z =
      (-1 : ℂ) ^ m * poch (n + 1 : ℂ) m * confluentM (-(m : ℂ)) (n + 1) z := by
  sorry

@[dlmf 13.2.E11]
theorem confluentU_neg_nat_shift (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    confluentU a (-(n : ℂ)) z = z ^ (n + 1 : ℂ) * confluentU (a + n + 1) (n + 2) z := by
  sorry

/-- Monodromy on the logarithmic argument plane for noninteger second parameter. -/
@[dlmf 13.2.E12]
theorem confluentU_analytic_continuation (a b z : ℂ) (m : ℤ) {w : ℂ}
    (hw : w = log z + 2 * π * I * m) (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    confluentUOnLog a b w =
      (2 * π * I * exp (-π * I * b * m) * sin (π * b * m)) /
          (Gamma (1 + a - b) * sin (π * b)) * regularizedHGFun {a} {b} z +
        exp (-2 * π * I * b * m) * confluentU a b z := by
  sorry

lemma confluentM_eq_sum_neg_nat_denom (n : ℕ) (a z : ℂ) :
    confluentM a (-(n : ℂ)) z =
      ∑ k ∈ Finset.range (n + 1),
        poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
  unfold confluentM
  refine tsum_eq_sum fun k hk => ?_
  have hkn : n < k := by
    rw [Finset.mem_range, not_lt] at hk
    exact Nat.lt_of_succ_le hk
  rw [poch_neg_nat_eq_zero hkn, zero_mul, div_zero, zero_mul]

lemma differentiableAt_confluentM (a b : ℂ) :
    DifferentiableAt ℂ (confluentM a b) 0 := by
  by_cases hb : ∀ k : ℕ, b ≠ -k
  · exact ((hasFPowerSeriesOnBall_confluentM (a := a) hb).analyticAt_of_mem
      (by simp : (0 : ℂ) ∈ Metric.eball (0 : ℂ) ⊤)).differentiableAt
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, b = -n := by
      push Not at hb
      simpa using hb
    have hfun : confluentM a b =
        fun z => ∑ k ∈ Finset.range (n + 1),
          poch a k / (poch (-(n : ℂ)) k * k.factorial) * z ^ k := by
      funext z
      rw [hn, confluentM_eq_sum_neg_nat_denom]
    rw [hfun]
    refine (Differentiable.fun_sum fun k _ => ?_).differentiableAt
    exact ((differentiable_id (𝕜 := ℂ)).pow k).const_mul _

@[dlmf 13.2.E13]
theorem isBigO_confluentM_sub_one (a b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ)) (fun z => confluentM a b z - 1) id := by
  refine (differentiableAt_confluentM a b).isBigO_sub.congr ?_ ?_
  · intro x
    simp [confluentM_zero]
  · intro x
    simp [id]

@[dlmf 13.2.E14]
theorem isBigO_confluentU_neg_nat (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => confluentU (-(n : ℂ)) b z - (-1 : ℂ) ^ n * poch b n) id := by
  sorry

@[dlmf 13.2.E15]
theorem isBigO_confluentU_neg_nat_shift (n : ℕ) (b : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU (-(n : ℂ) + b - 1) b z -
        (-1 : ℂ) ^ n * poch (2 - b) n * z ^ (1 - b))
      (fun z => z ^ (2 - b)) := by
  sorry

@[dlmf 13.2.E16]
theorem isBigO_confluentU_at_zero_re_ge_two (a b : ℂ) (hb : 2 ≤ b.re) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  sorry

@[dlmf 13.2.E17]
theorem isBigO_confluentU_at_zero_b_two (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a 2 z - 1 / Gamma a * z⁻¹)
      (fun z => log z) := by
  sorry

@[dlmf 13.2.E18]
theorem isBigO_confluentU_at_zero_re_one_to_two (a b : ℂ)
    (hb0 : 1 ≤ b.re) (hb1 : b.re < 2) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a b z - Gamma (b - 1) / Gamma a * z ^ (1 - b) -
        Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (2 - b.re : ℂ)) := by
  sorry

@[dlmf 13.2.E19]
theorem isBigO_confluentU_at_zero_b_one (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a 1 z +
        1 / Gamma a * (log z + digamma a + 2 * (Real.eulerMascheroniConstant : ℂ)))
      (fun z => z * log z) := by
  sorry

@[dlmf 13.2.E20]
theorem isBigO_confluentU_at_zero_re_zero_to_one (a b : ℂ)
    (hb0 : 0 < b.re) (hb1 : b.re < 1) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a b z - Gamma (1 - b) / Gamma (a - b + 1))
      (fun z => z ^ (1 - b.re : ℂ)) := by
  sorry

@[dlmf 13.2.E21]
theorem isBigO_confluentU_at_zero_b_zero (a : ℂ) :
    Asymptotics.IsBigO (𝓝[≠] (0 : ℂ))
      (fun z => confluentU a 0 z - 1 / Gamma (a + 1))
      (fun z => z * log z) := by
  sorry

@[dlmf 13.2.E22]
theorem isBigO_confluentU_at_zero_re_nonpos (a b : ℂ) (hb : b.re ≤ 0) :
    Asymptotics.IsBigO (𝓝 (0 : ℂ))
      (fun z => confluentU a b z - Gamma (1 - b) / Gamma (a - b + 1)) id := by
  sorry

@[dlmf 13.2.E23]
theorem tendsto_regularizedHGFun_mul_exp_neg_atTop (a b : ℂ) (ha : ∀ k : ℕ, a ≠ -k) :
    Tendsto (fun x : ℝ => regularizedHGFun {a} {b} x * Gamma a /
      (exp x * (x : ℂ) ^ (a - b))) atTop (𝓝 1) := by
  sorry

/-- Numerically satisfactory pair on `-π/2 ≤ ph z ≤ 3π/2`. -/
@[dlmf 13.2.E24]
theorem wronskian_confluentU_kummer_neg (a b : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (harg : -(π / 2) ≤ z.arg) (harg' : z.arg ≤ 3 * π / 2)
    (hb : ∀ n : ℤ, b ≠ n) :
    wronskian (confluentU a b)
      (fun w => exp w * confluentU (b - a) b (exp (-π * I) * w)) z ≠ 0 := by
  sorry

/-- Numerically satisfactory pair on `-3π/2 ≤ ph z ≤ π/2`. -/
@[dlmf 13.2.E25]
theorem wronskian_confluentU_kummer_pos (a b : ℂ) {z : ℂ}
    (hz : z ∈ slitPlane) (harg : -(3 * π / 2) ≤ z.arg) (harg' : z.arg ≤ π / 2)
    (hb : ∀ n : ℤ, b ≠ n) :
    wronskian (confluentU a b)
      (fun w => exp w * confluentU (b - a) b (exp (π * I) * w)) z ≠ 0 := by
  sorry

@[dlmf 13.2.E26]
theorem wronskian_confluentM_pair {a b z : ℂ} (hb : ∀ n : ℤ, b ≠ n)
    (hz : z ∈ slitPlane) :
    wronskian (confluentM a b)
      (fun w => w ^ (1 - b) * confluentM (a - b + 1) (2 - b) w) z ≠ 0 := by
  sorry

@[dlmf 13.2.E33]
theorem wronskian_regularizedHGFun (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ n : ℤ, b ≠ n) :
    wronskian (regularizedHGFun {a} {b})
      (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w) z =
      sin (π * b) * z ^ (-b) * exp z / π := by
  sorry

@[dlmf 13.2.E34]
theorem wronskian_regularizedHGFun_confluentU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a ≠ -k) :
    wronskian (regularizedHGFun {a} {b}) (confluentU a b) z =
      -(z ^ (-b) * exp z) / Gamma a := by
  sorry

@[dlmf 13.2.E35]
theorem wronskian_regularizedHGFun_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hba : ∀ k : ℕ, b - a ≠ -k) :
    wronskian (regularizedHGFun {a} {b})
      (fun w => exp w * confluentU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp (-(if sign then 1 else -1) * b * π * I) * z ^ (-b) * exp z / Gamma (b - a) := by
  sorry

@[dlmf 13.2.E36]
theorem wronskian_shifted_regularized_confluentU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (confluentU a b) z =
      -(z ^ (-b) * exp z) / Gamma (a - b + 1) := by
  sorry

@[dlmf 13.2.E37]
theorem wronskian_shifted_regularized_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (ha : ∀ k : ℕ, 1 - a ≠ -k) :
    wronskian (fun w => w ^ (1 - b) * regularizedHGFun {a - b + 1} {2 - b} w)
      (fun w => exp w * confluentU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      -(z ^ (-b) * exp z) / Gamma (1 - a) := by
  sorry

@[dlmf 13.2.E38]
theorem wronskian_confluentU_kummerU (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) :
    wronskian (confluentU a b)
      (fun w => exp w * confluentU (b - a) b (exp ((if sign then 1 else -1) * π * I) * w)) z =
      exp ((if sign then 1 else -1) * (a - b) * π * I) * z ^ (-b) * exp z := by
  sorry

/-- Kummer transformation for U at noninteger second parameter.
Extension to integer parameters requires the parameter-limit API. -/
@[dlmf 13.2.E40]
theorem confluentU_kummer_transform (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ k : ℤ, b ≠ k) :
    confluentU a b z = z ^ (1 - b) * confluentU (a - b + 1) (2 - b) z := by
  have hb' : ∀ k : ℤ, (2 : ℂ) - b ≠ k := by
    intro k hk
    apply hb (2 - k)
    push_cast
    linear_combination -hk
  rw [confluentU_eq_connection a b z hb,
    confluentU_eq_connection (a - b + 1) (2 - b) z hb']
  unfold confluentUConnection
  have hz0 := slitPlane_ne_zero hz
  have h1 : (1 : ℂ) - (2 - b) = b - 1 := by ring
  have h2 : (a - b + 1 : ℂ) - (2 - b) + 1 = a := by ring
  have h3 : (2 - b : ℂ) - 1 = 1 - b := by ring
  have h4 : (1 : ℂ) - (2 - b) = b - 1 := h1
  have h5 : (2 : ℂ) - (2 - b) = b := by ring
  have hpow : z ^ (1 - b) * z ^ (b - 1) = 1 := by
    rw [← cpow_add _ _ hz0]
    ring_nf
    simp
  simp only [h1, h2, h3, h5]
  rw [mul_add]
  have hswap :
      z ^ (1 - b) * (Gamma (1 - b) / Gamma (a - b + 1) * z ^ (b - 1) * confluentM a b z) =
        Gamma (1 - b) / Gamma (a - b + 1) * confluentM a b z := by
    calc
      _ = (z ^ (1 - b) * z ^ (b - 1)) *
            (Gamma (1 - b) / Gamma (a - b + 1) * confluentM a b z) := by ring
      _ = _ := by rw [hpow, one_mul]
  rw [hswap]
  ring

@[dlmf 13.2.E41]
theorem confluentM_eq_confluentU_connection (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (sign : Bool) (hb : ∀ k : ℕ, b ≠ -k) :
    confluentM a b z / Gamma b =
      exp (-(if sign then 1 else -1) * a * π * I) / Gamma (b - a) * confluentU a b z +
        exp ((if sign then 1 else -1) * (b - a) * π * I) / Gamma a *
          exp z * confluentU (b - a) b (exp ((if sign then 1 else -1) * π * I) * z) := by
  sorry

@[dlmf 13.2.E43]
theorem confluentM_eq_confluentU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (hb : ∀ k : ℕ, b ≠ -k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma b * Gamma (a - b + 1)) * confluentM (b - a) b z =
      exp (b * π * I) * confluentU a b (exp (π * I) * z) -
        exp (-b * π * I) * confluentU a b (exp (-π * I) * z) := by
  sorry

@[dlmf 13.2.E44]
theorem confluentU_jump (a b : ℂ) {z : ℂ} (hz : z ∈ slitPlane)
    (ha : ∀ k : ℕ, a ≠ -k) (hab : ∀ k : ℕ, a - b + 1 ≠ -k) :
    2 * π * I * exp (-z) / (Gamma a * Gamma (a - b + 1)) * confluentU (b - a) b z =
      exp (a * π * I) * confluentU a b (exp (π * I) * z) -
        exp (-a * π * I) * confluentU a b (exp (-π * I) * z) := by
  sorry

end AAR.Confluent
