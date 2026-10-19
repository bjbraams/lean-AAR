/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module
public import AAR.Confluent.ParameterDerivatives

/-!
# The analytic part of the integer-parameter Tricomi expansion

The logarithmic expansion separates into `log z` times a regularized Kummer function and
an ordinary power series. Parameter differentiation proves convergence of that series;
its analyticity at zero then supplies the small-argument remainder estimates.
-/

@[expose] public section
open Complex Filter Set FormalMultilinearSeries AAR.Hypergeometric
open scoped Real Nat Topology ENNReal
noncomputable section
set_option autoImplicit false
namespace AAR.Confluent

/-- Coefficients of the analytic part of the integer-parameter logarithmic expansion. -/
def tricomiLogSeriesCoeff (a : ℂ) (n k : ℕ) : ℂ :=
  poch a k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹ *
    (digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))

/-- The analytic part that accompanies `log z` in the integer-parameter U expansion. -/
def tricomiLogSeries (a : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' k : ℕ, tricomiLogSeriesCoeff a n k * z ^ k

/-- Parameter differentiation gives absolute convergence of the analytic logarithmic part. -/
theorem summable_tricomiLogSeries (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    Summable (fun k : ℕ => tricomiLogSeriesCoeff a n k * z ^ k) := by
  have h := (tricomi_numerator_nat_series a n hz ha).1.sub
    ((summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_right (log z))
  refine h.congr fun k => ?_
  dsimp only [tricomiLogSeriesCoeff]
  ring

/-- The ordinary power series part is analytic at zero. -/
theorem analyticAt_tricomiLogSeries (a : ℂ) (n : ℕ)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    AnalyticAt ℂ (tricomiLogSeries a n) 0 := by
  let p := ofScalars ℂ (tricomiLogSeriesCoeff a n)
  have hs := (summable_tricomiLogSeries a n (z := 2) (by norm_num) ha).norm
  have hr : (2 : ENNReal) ≤ p.radius := by
    apply p.le_radius_of_summable_norm (r := 2)
    simpa only [p, ofScalars_norm, norm_mul, norm_pow, Complex.norm_ofNat,
      NNReal.coe_ofNat] using hs
  have hp := p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 2) hr)
  have heq : p.sum = tricomiLogSeries a n := by
    funext z
    simp only [p, FormalMultilinearSeries.sum, ofScalars_apply_eq, smul_eq_mul, tricomiLogSeries]
  rw [heq] at hp
  exact hp.analyticAt

/-- Constant term of the analytic logarithmic part. -/
theorem tricomiLogSeries_zero (a : ℂ) (n : ℕ) :
    tricomiLogSeries a n 0 = (Gamma ((n : ℂ) + 1))⁻¹ *
      (digamma a - digamma 1 - digamma ((n : ℂ) + 1)) := by
  unfold tricomiLogSeries
  rw [tsum_eq_single 0]
  · simp [tricomiLogSeriesCoeff, poch_zero]
  · intro k hk
    simp [zero_pow hk]

/-- Separation of the logarithm from the convergent integer-parameter series. -/
theorem tricomi_log_series_split (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : ∀ k : ℕ, a - n ≠ -(k : ℂ)) :
    (∑' k : ℕ, (poch a k * z ^ k / k.factorial * (Gamma ((n : ℂ) + 1 + k))⁻¹) *
      (log z + digamma (a + k) - digamma (k + 1) - digamma ((n : ℂ) + 1 + k))) =
      log z * regularizedHGFun {a} {(n : ℂ) + 1} z + tricomiLogSeries a n z := by
  have hM := (summable_regularizedConfluent_term a ((n : ℂ) + 1) z).mul_left (log z)
  have hT := summable_tricomiLogSeries a n hz ha
  rw [regularizedConfluent_eq_tsum, tricomiLogSeries, ← tsum_mul_left, ← hM.tsum_add hT]
  refine tsum_congr fun k => ?_
  dsimp only [tricomiLogSeriesCoeff]
  ring

end AAR.Confluent
