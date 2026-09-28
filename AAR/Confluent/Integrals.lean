/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import AAR.Bessel.Basic
public import AAR.Bessel.Modified
public import AAR.Hypergeometric.EulerIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integrals (DLMF §§13.10, 13.23)

Indefinite integrals are stated as derivative identities. Laplace, Mellin, and
Bessel transforms use real half-lines. Hankel-loop formulas 13.10.8–13.10.9 and
13.23.6–13.23.7, and the inversion pair 13.23.13–13.23.14, are deferred.
-/

@[expose] public section

open Complex Filter MeasureTheory FormalMultilinearSeries
open scoped Real Topology ENNReal

noncomputable section

namespace AAR.Confluent

@[dlmf 13.10.E1]
theorem deriv_regularizedHGFun_shift {a b z : ℂ} (ha : a ≠ 1) :
    deriv (regularizedHGFun {a - 1} {b - 1}) z = (a - 1) * regularizedHGFun {a} {b} z := by
  have hr : (regularizedHGFunSeries {a - 1} {b - 1}).radius = ⊤ :=
    radius_regularizedHGFunSeries_eq_top (by simp)
  have hs : HasFPowerSeriesOnBall (regularizedHGFun {a - 1} {b - 1})
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤ := by
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a - 1} {b - 1}).sum
      (regularizedHGFunSeries {a - 1} {b - 1}) 0 ⊤
    simpa only [hr] using (regularizedHGFunSeries {a - 1} {b - 1}).hasFPowerSeriesOnBall
      (by rw [hr]; simp)
  have ht : HasFPowerSeriesOnBall (regularizedHGFun {a} {b})
      (regularizedHGFunSeries {a} {b}) 0 ⊤ := by
    have hr' : (regularizedHGFunSeries {a} {b}).radius = ⊤ :=
      radius_regularizedHGFunSeries_eq_top (by simp)
    change HasFPowerSeriesOnBall (regularizedHGFunSeries {a} {b}).sum
      (regularizedHGFunSeries {a} {b}) 0 ⊤
    simpa only [hr'] using (regularizedHGFunSeries {a} {b}).hasFPowerSeriesOnBall
      (by rw [hr']; simp)
  have hcoeff (n : ℕ) :
      (n + 1 : ℂ) * regularizedHGFunCoeff {a - 1} {b - 1} (n + 1) =
        (a - 1) * regularizedHGFunCoeff {a} {b} n := by
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rw [regularizedHGFunCoeff_singleton, regularizedHGFunCoeff_singleton, poch_succ_left]
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    rw [show (b - 1) + (n + 1) = b + n by ring,
      show a - 1 + 1 = a by ring]
    field [hn, Nat.cast_ne_zero.mpr n.factorial_ne_zero]
  have hd := hs.deriv_ofScalars.hasSum_mul_pow (z := z) (by simp)
  have he := (ht.hasSum_mul_pow (z := z) (by simp)).mul_left (a - 1)
  simp_rw [hcoeff] at hd
  simp only [mul_assoc] at hd he
  exact hd.unique he

/-- Derivative of Tricomi U with shifted parameters. `U` is not complex-differentiable on the cut,
so `z` is restricted to the slit plane. -/
@[dlmf 13.10.E2]
theorem deriv_confluentU_shift {a b z : ℂ} (ha : a ≠ 1) (hz : z ∈ slitPlane) :
    deriv (confluentU (a - 1) (b - 1)) z = -(a - 1) * confluentU a b z := by
  sorry

@[dlmf 13.10.E3]
theorem laplace_regularizedHGFun {a b c k z : ℂ}
    (hb : 0 < b.re) (hz : z.re > k.re) (hz0 : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} (k * t) =
      Gamma b * z ^ (-b) * regularizedGaussHGFun a b c (k / z) := by
  sorry

@[dlmf 13.10.E4]
theorem laplace_regularizedHGFun_self {a b z : ℂ} (hb : 0 < b.re) (hz : 1 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {b} t =
      z ^ (-b) * (1 - z⁻¹) ^ (-a) := by
  sorry

@[dlmf 13.10.E5]
theorem mellin_regularizedHGFun_exp {a b c : ℂ}
    (hb : 0 < b.re) (h : b.re < (c - a).re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1) * regularizedHGFun {a} {c} t =
      Gamma b * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) := by
  sorry

/-- A Gaussian-weighted Laplace transform of `𝐌`; it converges for `0 < Re z`. -/
@[dlmf 13.10.E6]
theorem gauss_regularizedHGFun {a b z : ℂ} (hb : (1 / 2 : ℝ) < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t - (t : ℂ) ^ 2) * (t : ℂ) ^ (2 * b - 2) *
          regularizedHGFun {a} {b} ((t : ℂ) ^ 2) =
      (1 / 2) * (π : ℂ) ^ (-(1 / 2 : ℂ)) * Gamma (b - 1 / 2) *
        confluentU (b - 1 / 2) (a + 1 / 2) (z ^ 2 / 4) := by
  sorry

/-- The Laplace transform of Tricomi U; it converges for `0 < Re z`. -/
@[dlmf 13.10.E7]
theorem laplace_confluentU {a b c z : ℂ}
    (hb : 0 < b.re) (hbc : (c - 1).re < b.re) (hz : 0 < z.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-z * t) * (t : ℂ) ^ (b - 1) * confluentU a c t =
      Gamma b * Gamma (b - c + 1) * z ^ (-b) *
        regularizedGaussHGFun a b (a + b - c + 1) (1 - z⁻¹) := by
  sorry

@[dlmf 13.10.E10]
theorem mellin_regularizedHGFun {a b lam : ℂ} (hlam : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * regularizedHGFun {a} {b} (-t) =
      Gamma lam * Gamma (a - lam) / (Gamma a * Gamma (b - lam)) := by
  sorry

@[dlmf 13.10.E11]
theorem mellin_confluentU {a b lam : ℂ}
    (hlam0 : (b - 1).re < lam.re) (hlam1 : 0 < lam.re) (ha : lam.re < a.re) :
    ∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ (lam - 1) * confluentU a b t =
      Gamma lam * Gamma (a - lam) * Gamma (lam - b + 1) / (Gamma a * Gamma (a - b + 1)) := by
  sorry

/-- A cosine transform of `𝐌`. For `a ≤ 1/2` the integral converges only conditionally,
which Lean's integral does not capture, so `1/2 < a` is required. -/
@[dlmf 13.10.E12]
theorem cosine_regularizedHGFun {a b x : ℝ} (hx : 0 < x) (ha : 1 / 2 < a) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * regularizedHGFun {(a : ℂ)} {(b : ℂ)} (-(t : ℂ) ^ 2) =
      (Real.sqrt π : ℂ) / (2 * Gamma (a : ℂ)) * (x : ℂ) ^ (2 * (a : ℂ) - 1) *
        exp (-(x : ℂ) ^ 2) *
        confluentU (b - 1 / 2) (a + 1 / 2) (x ^ 2) := by
  sorry

/-- A Hankel-type transform of `𝐌`, for real `x > 0`. For non-real `x` the Bessel kernel grows like
`exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required for
Lean's integral. -/
@[dlmf 13.10.E13]
theorem bessel_regularizedHGFun {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hb : 0 < b.re) (hν : 2 * a.re < ν.re + 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (b - 1 - ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (-a + ν / 2) * exp (-x) * regularizedHGFun {ν - b + 1} {ν - a + 1} x := by
  sorry

/-- A Hankel-type transform of `𝐌` in terms of U, for real `x > 0`. For non-real `x` the Bessel
kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable,
as required for Lean's integral. -/
@[dlmf 13.10.E14]
theorem bessel_regularizedHGFun_U {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (b - a).re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * regularizedHGFun {a} {b} t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      x ^ (ν / 2) * exp (-x) / Gamma (b - a) * confluentU a (a - b + ν + 2) x := by
  sorry

/-- A Hankel-type transform of Tricomi U, for real `x > 0`. For non-real `x` the Bessel kernel grows
like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as required
for Lean's integral. -/
@[dlmf 13.10.E15]
theorem bessel_confluentU {a b ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * a.re - 3 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        (t : ℂ) ^ (ν / 2) * confluentU a b t * besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) / Gamma a * x ^ (ν / 2) * confluentU (ν - b + 2) (ν - a + 2) x := by
  sorry

@[dlmf 13.10.E16]
theorem bessel_confluentU_M {a b ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (b - 2).re < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ)) * (t : ℂ) ^ (ν / 2) * confluentU a b t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - b + 2) * x ^ (ν / 2) * exp (-x) *
        regularizedHGFun {a} {a - b + ν + 2} x := by
  sorry

@[dlmf 13.23.E1]
theorem laplace_whittakerM {κ μ ν z : ℂ}
    (h : 0 < μ.re + ν.re + 1 / 2) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t =
      Gamma (μ + ν + 1 / 2) / (z + 1 / 2) ^ (μ + ν + 1 / 2) *
        ₂F₁ (1 / 2 + μ - κ) (1 / 2 + μ + ν) (1 + 2 * μ) (1 / (z + 1 / 2)) := by
  sorry

@[dlmf 13.23.E2]
theorem laplace_whittakerM_closed {κ μ z : ℂ}
    (hμ : -1 / 2 < μ.re) (hz : 1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (μ - 1 / 2) * whittakerM κ μ t =
      Gamma (2 * μ + 1) * (z + 1 / 2) ^ (-κ - μ - 1 / 2) *
        (z - 1 / 2) ^ (κ - μ - 1 / 2) := by
  sorry

@[dlmf 13.23.E3]
theorem mellin_whittakerM {κ μ ν : ℂ}
    (h0 : -1 / 2 - μ.re < ν.re) (h1 : ν.re < κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-(t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerM κ μ t /
        Gamma (1 + 2 * μ) =
      Gamma (μ + ν + 1 / 2) * Gamma (κ - ν) /
        (Gamma (1 / 2 + μ + κ) * Gamma (1 / 2 + μ - ν)) := by
  sorry

@[dlmf 13.23.E4]
theorem laplace_whittakerW {κ μ ν z : ℂ}
    (h : |μ.re| < ν.re + 1 / 2) (hz : -1 / 2 < z.re) :
    ∫ t : ℝ in Set.Ioi 0, exp (-z * t) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) *
        regularizedGaussHGFun (1 / 2 - μ + ν) (1 / 2 + μ + ν) (ν - κ + 1) (1 / 2 - z) := by
  sorry

@[dlmf 13.23.E5]
theorem mellin_whittakerW {κ μ ν : ℂ}
    (h0 : |μ.re| - 1 / 2 < ν.re) (h1 : ν.re < -κ.re) :
    ∫ t : ℝ in Set.Ioi 0, exp ((t : ℂ) / 2) * (t : ℂ) ^ (ν - 1) * whittakerW κ μ t =
      Gamma (1 / 2 + μ + ν) * Gamma (1 / 2 - μ + ν) * Gamma (-κ - ν) /
        (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) := by
  sorry

/-- A cosine transform of Whittaker M. For `κ + μ ≤ 0` the integral converges only
conditionally, which Lean's integral does not capture, so `0 < κ + μ` is required. -/
@[dlmf 13.23.E8]
theorem cosine_whittakerM {κ μ x : ℝ} (hx : 0 < x)
    (h : 0 < (κ + μ : ℂ).re) :
    ∫ t : ℝ in Set.Ioi 0,
        Complex.cos (2 * x * t) * exp (-(t : ℂ) ^ 2 / 2) *
          (t : ℂ) ^ (-(2 * (μ : ℂ) + 1)) *
          whittakerM κ μ ((t : ℂ) ^ 2) / Gamma (1 + 2 * (μ : ℂ)) =
      (Real.sqrt π : ℂ) * exp (-(x : ℂ) ^ 2 / 2) * (x : ℂ) ^ ((μ : ℂ) + κ - 1) /
        (2 * Gamma (1 / 2 + (μ : ℂ) + κ)) *
        whittakerW (κ / 2 - 3 * μ / 2) (κ / 2 + μ / 2) (x ^ 2) := by
  sorry

/-- A Hankel-type transform of Whittaker M, for real `x > 0`. For non-real `x` the Bessel kernel
grows like `exp (c √t)`; the parameter bound makes the integrand absolutely integrable, as
required for Lean's integral. -/
@[dlmf 13.23.E9]
theorem bessel_whittakerM {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hμ : -1 / 2 < μ.re) (hμ' : μ.re < κ.re + ν.re / 2 - 1 / 4) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ (μ - (ν + 1) / 2) * whittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (1 + 2 * μ) / Gamma (1 / 2 - μ + κ + ν) * exp (-x / 2) *
        x ^ ((κ - μ - 3 / 2) / 2) *
        whittakerM ((κ + 3 * μ - ν + 1 / 2) / 2) ((κ - μ + ν - 1 / 2) / 2) x := by
  sorry

/-- A Hankel-type transform of Whittaker M in terms of W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E10]
theorem bessel_whittakerM_W {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : -1 < ν.re) (hν1 : ν.re < 2 * (κ + μ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerM κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) / Gamma (1 + 2 * μ) =
      exp (-x / 2) * x ^ ((κ + μ - 3 / 2) / 2) / Gamma (1 / 2 + μ + κ) *
        whittakerW ((κ - 3 * μ + ν + 1 / 2) / 2) ((κ + μ - ν - 1 / 2) / 2) x := by
  sorry

/-- A Hankel-type transform of `e^{t/2}` times Whittaker W, for real `x > 0`. For non-real `x` the
Bessel kernel grows like `exp (c √t)`; the parameter bound makes the integrand absolutely
integrable, as required for Lean's integral. -/
@[dlmf 13.23.E11]
theorem bessel_whittakerW {κ μ ν x : ℂ} (hx : 0 < x.re) (hxi : x.im = 0)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) (hν2 : ν.re < 2 * (μ - κ).re - 1 / 2) :
    ∫ t : ℝ in Set.Ioi 0,
        exp ((t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) / Gamma (1 / 2 + μ - κ) * exp (x / 2) *
        x ^ ((μ - κ - 3 / 2) / 2) *
        whittakerW ((κ + 3 * μ - ν - 1 / 2) / 2) ((κ - μ + ν + 1 / 2) / 2) x := by
  sorry

@[dlmf 13.23.E12]
theorem bessel_whittakerW_M {κ μ ν x : ℂ} (hx : 0 < x.re)
    (hν0 : (2 * μ.re - 1) < ν.re) (hν1 : -1 < ν.re) :
    ∫ t : ℝ in Set.Ioi 0,
        exp (-(t : ℂ) / 2) * (t : ℂ) ^ ((ν - 1) / 2 - μ) * whittakerW κ μ t *
          besselJ ν (2 * (x * t) ^ (1 / 2 : ℂ)) =
      Gamma (ν - 2 * μ + 1) / Gamma (3 / 2 - μ - κ + ν) * exp (-x / 2) *
        x ^ ((μ + κ - 3 / 2) / 2) *
        whittakerM ((κ - 3 * μ + ν + 1 / 2) / 2) ((ν - μ - κ + 1 / 2) / 2) x := by
  sorry

end AAR.Confluent
