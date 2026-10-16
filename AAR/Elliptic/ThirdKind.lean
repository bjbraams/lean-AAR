/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Elliptic.Jacobi

/-!
# The elliptic integral of the third kind (Temme (12.17), DLMF §19.2)

For `n < 1` and `m < 1` the integrand `(1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2}` is continuous, so
`Π(n; φ|m) = ∫₀^φ (1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2} dθ` needs no principal value. It is odd and
quasi-periodic, `Π(n; φ+π|m) = Π(n; φ|m) + 2Π(n|m)`, and `Π(0; φ|m) = F(φ|m)`. At `m = 0` it is
elementary: with `c = √(1-n)`,
`Π(n; φ|0) = (φ - arctan((1-c) sin φ cos φ/(cos²φ + c sin²φ)))/c`, which is `arctan(c tan φ)/c` on
`(-π/2, π/2)` but is smooth on all of `ℝ`. In particular `Π(n|0) = π/(2√(1-n))`.
-/

@[expose] public section

open Real Set Filter
open scoped Topology

noncomputable section

namespace AAR.Elliptic

/-- The integrand `(1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2}` of the third kind. -/
def piIntegrand (n m θ : ℝ) : ℝ := (1 - n * sin θ ^ 2)⁻¹ * (1 - m * sin θ ^ 2) ^ (-(1 / 2) : ℝ)

/-- Legendre's incomplete integral of the third kind
`Π(n; φ|m) = ∫₀^φ (1 - n sin²θ)⁻¹ (1 - m sin²θ)^{-1/2} dθ` (DLMF 19.2.7, Temme (12.17)),
used here for `n < 1`, `m < 1` where no principal value is needed. -/
@[dlmf 19.2.E7]
def ellipticPi (n φ m : ℝ) : ℝ := ∫ θ in (0 : ℝ)..φ, piIntegrand n m θ

/-- The complete integral of the third kind `Π(n|m) = Π(n; π/2|m)` (DLMF 19.2.7). -/
def ellipticPiComplete (n m : ℝ) : ℝ := ellipticPi n (π / 2) m

/-- For `n, m < 1` the integrand of the third kind is continuous. -/
lemma continuous_piIntegrand {n m : ℝ} (hn : n < 1) (hm : m < 1) :
    Continuous (piIntegrand n m) :=
  ((by fun_prop : Continuous fun θ : ℝ => 1 - n * sin θ ^ 2).inv₀
    fun θ => (one_sub_mul_sin_sq_pos hn θ).ne').mul (continuous_one_sub_mul_sin_sq_rpow hm _)

/-- The integrand is symmetric about `π/2`. -/
lemma piIntegrand_pi_sub (n m θ : ℝ) : piIntegrand n m (π - θ) = piIntegrand n m θ := by
  simp [piIntegrand, sin_pi_sub]

/-- The integrand is `π`-periodic. -/
lemma piIntegrand_add_pi (n m θ : ℝ) : piIntegrand n m (θ + π) = piIntegrand n m θ := by
  simp [piIntegrand, sin_add_pi]

/-- The integrand is even. -/
lemma piIntegrand_neg (n m θ : ℝ) : piIntegrand n m (-θ) = piIntegrand n m θ := by
  simp [piIntegrand, sin_neg]

/-- `Π(0; φ|m) = F(φ|m)`. -/
theorem ellipticPi_zero_left (φ m : ℝ) : ellipticPi 0 φ m = ellipticF φ m := by
  simp [ellipticPi, piIntegrand, ellipticF]

/-- `∂Π/∂φ = (1 - n sin²φ)⁻¹ (1 - m sin²φ)^{-1/2}`. -/
theorem hasDerivAt_ellipticPi {n m : ℝ} (hn : n < 1) (hm : m < 1) (φ : ℝ) :
    HasDerivAt (fun φ => ellipticPi n φ m) (piIntegrand n m φ) φ :=
  intervalIntegral.integral_hasDerivAt_right
    ((continuous_piIntegrand hn hm).intervalIntegrable _ _)
    ((continuous_piIntegrand hn hm).stronglyMeasurableAtFilter _ _)
    (continuous_piIntegrand hn hm).continuousAt

/-- `Π(n; -φ|m) = -Π(n; φ|m)`. -/
theorem ellipticPi_neg (n φ m : ℝ) : ellipticPi n (-φ) m = -ellipticPi n φ m := by
  have h : ∫ θ in (0 : ℝ)..(-φ), piIntegrand n m θ =
      ∫ θ in (0 : ℝ)..(-φ), piIntegrand n m (-θ) := by simp only [piIntegrand_neg]
  rw [ellipticPi, ellipticPi, h, intervalIntegral.integral_comp_neg (piIntegrand n m), neg_neg,
    neg_zero, intervalIntegral.integral_symm]

/-- `Π(n; φ + π|m) = Π(n; φ|m) + 2Π(n|m)` (DLMF §19.2(ii)). -/
theorem ellipticPi_add_pi {n m : ℝ} (hn : n < 1) (hm : m < 1) (φ : ℝ) :
    ellipticPi n (φ + π) m = ellipticPi n φ m + 2 * ellipticPiComplete n m := by
  have hc := continuous_piIntegrand hn hm
  have hper : ∫ θ in (0 : ℝ)..π, piIntegrand n m θ =
      2 * ∫ θ in (0 : ℝ)..(π / 2), piIntegrand n m θ := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have h := intervalIntegral.integral_comp_sub_left (piIntegrand n m) (a := 0) (b := π / 2) π
    simp only [piIntegrand_pi_sub, sub_zero, show π - π / 2 = π / 2 by ring] at h
    rw [← h]; ring
  unfold ellipticPi ellipticPiComplete ellipticPi
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π)
    (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hper]
  have h := intervalIntegral.integral_comp_add_right (piIntegrand n m) (a := 0) (b := φ) π
  simp only [piIntegrand_add_pi, zero_add] at h
  rw [← h, add_comm]

/-- A smooth antiderivative of `(cos²φ + c² sin²φ)⁻¹`, equal to `arctan(c tan φ)/c` on
`(-π/2, π/2)`. -/
def piZeroPrimitive (c φ : ℝ) : ℝ :=
  (φ - arctan ((1 - c) * sin φ * cos φ / (cos φ ^ 2 + c * sin φ ^ 2))) / c

/-- `cos²φ + c sin²φ > 0` for `c > 0`. -/
lemma cos_sq_add_mul_sin_sq_pos {c : ℝ} (hc : 0 < c) (φ : ℝ) : 0 < cos φ ^ 2 + c * sin φ ^ 2 := by
  rcases eq_or_ne (sin φ) 0 with h | h
  · have := sin_sq_add_cos_sq φ; rw [h] at this; nlinarith
  · have : 0 < sin φ ^ 2 := by positivity
    nlinarith [sq_nonneg (cos φ)]

/-- The primitive has derivative `(cos²φ + c² sin²φ)⁻¹` on all of `ℝ`. -/
lemma hasDerivAt_piZeroPrimitive {c : ℝ} (hc : 0 < c) (φ : ℝ) :
    HasDerivAt (piZeroPrimitive c) (1 / (cos φ ^ 2 + c ^ 2 * sin φ ^ 2)) φ := by
  have hD := cos_sq_add_mul_sin_sq_pos hc φ
  have hD2 := cos_sq_add_mul_sin_sq_pos (pow_pos hc 2) φ
  have hu : HasDerivAt (fun φ => (1 - c) * sin φ * cos φ / (cos φ ^ 2 + c * sin φ ^ 2))
      (((1 - c) * (cos φ * cos φ + sin φ * -sin φ) * (cos φ ^ 2 + c * sin φ ^ 2) -
        (1 - c) * sin φ * cos φ * (2 * cos φ * -sin φ + c * (2 * sin φ * cos φ))) /
          (cos φ ^ 2 + c * sin φ ^ 2) ^ 2) φ := by
    have h1 := (((hasDerivAt_sin φ).const_mul (1 - c)).mul (hasDerivAt_cos φ))
    have h2 := ((hasDerivAt_cos φ).pow 2).add (((hasDerivAt_sin φ).pow 2).const_mul c)
    convert h1.div h2 hD.ne' using 1
    simp; ring
  have h := ((hasDerivAt_id φ).sub hu.arctan).div_const c
  refine h.congr_deriv ?_
  have hsc := sin_sq_add_cos_sq φ
  field_simp
  linear_combination (c * (cos φ ^ 2 + sin φ ^ 2) * (c ^ 2 * sin φ ^ 2 + cos φ ^ 2)) * hsc

/-- Closed form at `m = 0`: `Π(n; φ|0) = (φ - arctan((1-c) sin φ cos φ/(cos²φ + c sin²φ)))/c`
with `c = √(1-n)`; on `(-π/2, π/2)` this is `arctan(c tan φ)/c`. -/
theorem ellipticPi_zero_right {n : ℝ} (hn : n < 1) (φ : ℝ) :
    ellipticPi n φ 0 = piZeroPrimitive (√(1 - n)) φ := by
  set c := √(1 - n) with hcdef
  have hc : 0 < c := sqrt_pos.mpr (by linarith)
  have hc2 : c ^ 2 = 1 - n := sq_sqrt (by linarith)
  have hderiv : ∀ θ ∈ uIcc 0 φ, HasDerivAt (piZeroPrimitive c) (piIntegrand n 0 θ) θ := by
    intro θ _
    refine (hasDerivAt_piZeroPrimitive hc θ).congr_deriv ?_
    have := sin_sq_add_cos_sq θ
    simp only [piIntegrand, zero_mul, sub_zero, one_rpow, mul_one, hc2, one_div]
    congr 1
    linarith
  rw [ellipticPi, intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_piIntegrand hn (by norm_num)).intervalIntegrable _ _)]
  simp [piZeroPrimitive]

/-- `Π(n|0) = π/(2√(1-n))` for `n < 1`. -/
theorem ellipticPiComplete_zero_right {n : ℝ} (hn : n < 1) :
    ellipticPiComplete n 0 = π / (2 * √(1 - n)) := by
  rw [ellipticPiComplete, ellipticPi_zero_right hn, piZeroPrimitive]
  simp
  ring

end AAR.Elliptic

end
