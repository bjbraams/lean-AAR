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
public import AAR.Hypergeometric.ArgumentContinuation
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Integral representations (DLMF §§13.4, 13.16)

Gauss kernels use cut-plane continuation, since their arguments range over the
negative ray. Argument bounds explicitly exclude zero where needed.

Euler, Laplace, Bessel, and vertical Barnes integrals are acquired on real
intervals or vertical lines. Hankel-loop and Pochhammer-double-loop formulas
13.4.9–13.4.15 are deferred pending a contour API, matching Chapter 15.
The `M` form of 13.4.1 is already `confluentM_eq_euler_integral` in `Basic`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology ENNReal

noncomputable section

namespace AAR.Confluent

@[dlmf 13.4.E1]
theorem regularized_euler_integral {a b z : ℂ} (ha : 0 < a.re) (hba : 0 < (b - a).re) :
    regularizedHGFun {a} {b} z =
      1 / (Gamma a * Gamma (b - a)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) := by
  have hb : ∀ k : ℕ, b ≠ -k := not_neg_nat_of_re_pos (by
    have h : b.re = a.re + (b - a).re := by simp [sub_re]
    linarith)
  have hG : Gamma b ≠ 0 := Gamma_ne_zero hb
  have hM := confluentM_eq_euler_integral (a := a) (c := b) (z := z) ha hba
  rw [confluentM_eq_mul_regularizedHGFun hb] at hM
  apply mul_left_cancel₀ hG
  rw [hM]
  have hinter :
      (∫ t : ℝ in (0 : ℝ)..1,
        (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) * exp (z * t)) =
      ∫ t : ℝ in (0 : ℝ)..1,
        exp (z * t) * (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - a - 1) :=
    intervalIntegral.integral_congr fun t _ => by ring
  rw [hinter]
  simp [div_eq_mul_inv, one_div, mul_assoc]

@[dlmf 13.4.E2]
theorem regularized_parameter_integral {a b c z : ℂ}
    (hc : 0 < c.re) (hbc : 0 < (b - c).re) :
    regularizedHGFun {a} {b} z =
      1 / Gamma (b - c) *
        ∫ t : ℝ in (0 : ℝ)..1,
          regularizedHGFun {a} {c} (z * t) * (t : ℂ) ^ (c - 1) *
            (1 - (t : ℂ)) ^ (b - c - 1) := by
  sorry

@[dlmf 13.4.E3]
theorem regularized_bessel_integral {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    regularizedHGFun {a} {b} (-z) =
      z ^ ((1 - b) / 2) / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) * besselJ (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.4.E4]
theorem confluentU_laplace {a b z : ℂ} (ha : 0 < a.re) (hz : 0 < z.re) :
    confluentU a b z =
      1 / Gamma a *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (a - 1) * (1 + (t : ℂ)) ^ (b - a - 1) := by
  sorry

@[dlmf 13.4.E5]
theorem confluentU_stieltjes {a b z : ℂ} (hz : z ∈ slitPlane)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    confluentU a b z =
      z ^ (1 - a) / (Gamma a * Gamma (1 + a - b)) *
        ∫ t : ℝ in Set.Ioi 0,
          confluentU (b - a) b t * exp (-(t : ℂ)) * (t : ℂ) ^ (a - 1) /
            ((t : ℂ) + z) := by
  sorry

@[dlmf 13.4.E6]
theorem confluentU_stieltjes_regularized {a b z : ℂ} (n : ℕ) (hz : z ∈ slitPlane)
    (hn0 : -b.re < n) (hn1 : (n : ℝ) < 1 + (a - b).re) :
    confluentU a b z =
      (-1 : ℂ) ^ n * z ^ (1 - b - n) / Gamma (1 + a - b) *
        ∫ t : ℝ in Set.Ioi 0,
          regularizedHGFun {b - a} {b} t * exp (-(t : ℂ)) * (t : ℂ) ^ (b + n - 1) /
            ((t : ℂ) + z) := by
  sorry

/-- A Bessel-K integral for Tricomi U, away from `z = 0` where the totalized values of both
sides differ. -/
@[dlmf 13.4.E7]
theorem confluentU_integral_besselK {a b z : ℂ} (hz : 0 ≤ z.re) (hz0 : z ≠ 0)
    (ha : (b - 1).re < a.re) (ha0 : 0 < a.re) :
    confluentU a b z =
      2 * z ^ ((1 - b) / 2) / (Gamma a * Gamma (a - b + 1)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (a - b / 2 - 1 / 2) *
            besselK (b - 1) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.4.E8]
theorem confluentU_gauss {a b c z : ℂ} (ha : 0 < c.re) (hz : 0 < z.re) :
    confluentU a b z =
      z ^ (c - a) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.gaussHGCut a (a - b + 1) c (-(t : ℂ)) := by
  sorry

/-- Vertical Mellin–Barnes line; the factor `i` from `dt` is included. -/
@[dlmf 13.4.E16]
theorem regularized_barnes_integral {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hσ : σ < 0) :
    regularizedHGFun {a} {b} (-(x : ℂ)) =
      1 / (2 * π * I * Gamma a) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (-(σ + I * t)) /
          Gamma (b + σ + I * t) * (x : ℂ) ^ (σ + I * t) * I := by
  sorry

@[dlmf 13.4.E17]
theorem confluentU_barnes {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (ha : 0 < a.re + σ) (hab : 0 < (1 + a - b).re + σ) (hσ : σ < 0) :
    confluentU a b x =
      (x : ℂ) ^ (-a) / (2 * π * I) *
        ∫ t : ℝ, Gamma (a + σ + I * t) * Gamma (1 + a - b + σ + I * t) *
          Gamma (-(σ + I * t)) / (Gamma a * Gamma (1 + a - b)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

@[dlmf 13.4.E18]
theorem confluentU_barnes_exp {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hb : 0 < (b - 1).re + σ) (hσ : 0 < σ) :
    confluentU a b x =
      (x : ℂ) ^ (1 - b) * exp x / (2 * π * I) *
        ∫ t : ℝ, Gamma (b - 1 + σ + I * t) * Gamma (σ + I * t) /
          Gamma (a + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

@[dlmf 13.16.E1]
theorem whittakerM_euler {κ μ z : ℂ}
    (hμ : 0 < μ.re + 1 / 2 - |κ.re|) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 + μ + κ)) *
        ∫ t : ℝ in (-1 : ℝ)..1,
          exp (z * t / 2) * (1 + (t : ℂ)) ^ (μ - 1 / 2 - κ) *
            (1 - (t : ℂ)) ^ (μ - 1 / 2 + κ) := by
  sorry

@[dlmf 13.16.E2]
theorem whittakerM_parameter_integral {κ μ lam z : ℂ}
    (hμ : lam.re < μ.re + 1 / 2) (hlam : 0 < lam.re) (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (1 + 2 * μ) * z ^ lam / (Gamma (1 + 2 * μ - 2 * lam) * Gamma (2 * lam)) *
        ∫ t : ℝ in (0 : ℝ)..1,
          whittakerM (κ - lam) (μ - lam) (z * t) * exp (z * (t - 1) / 2) *
            (t : ℂ) ^ (μ - lam - 1 / 2) * (1 - (t : ℂ)) ^ (2 * lam - 1) := by
  sorry

@[dlmf 13.16.E3]
theorem whittakerM_integral_besselJ {κ μ z : ℂ} (hκ : 0 < (κ + μ).re + 1 / 2)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (z / 2) / Gamma (1 / 2 + μ + κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (κ - 1 / 2) *
            besselJ (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E4]
theorem whittakerM_integral_besselI {κ μ z : ℂ} (hκ : (κ - μ).re - 1 / 2 < 0)
    (hz : z ∈ slitPlane) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      z ^ (1 / 2 : ℂ) * exp (-z / 2) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselI (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E5]
theorem whittakerW_laplace {κ μ z : ℂ} (hμ : κ.re < μ.re + 1 / 2)
    (hz : 0 < z.re) :
    whittakerW κ μ z =
      z ^ (μ + 1 / 2) * (2 : ℂ) ^ (-(2 * μ)) / Gamma (1 / 2 + μ - κ) *
        ∫ t : ℝ in Set.Ioi 1,
          exp (-z * t / 2) * ((t : ℂ) - 1) ^ (μ - 1 / 2 - κ) *
            ((t : ℂ) + 1) ^ (μ - 1 / 2 + κ) := by
  sorry

@[dlmf 13.16.E6]
theorem whittakerW_stieltjes {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : (2 * μ.re) < (1 / 2 + μ - κ).re) (hκ0 : 0 < (1 / 2 + μ - κ).re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + 1) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          whittakerW (-κ) μ t * exp (-(t : ℂ) / 2) * (t : ℂ) ^ (-κ - 1) /
            ((t : ℂ) + z) := by
  sorry

/-- A Bessel-K integral for Whittaker W, away from `z = 0` where the totalized values of both
sides differ. -/
@[dlmf 13.16.E8]
theorem whittakerW_integral_besselK {κ μ z : ℂ} (hκ : 0 < (μ - κ).re + 1 / 2)
    (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    whittakerW κ μ z =
      2 * z ^ (1 / 2 : ℂ) * exp (-z / 2) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-(t : ℂ)) * (t : ℂ) ^ (-κ - 1 / 2) *
            besselK (2 * μ) (2 * (z * t) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.16.E9]
theorem whittakerW_gauss {κ μ c z : ℂ} (hc : 0 < c.re) (hz : 0 < z.re) :
    whittakerW κ μ z =
      exp (-z / 2) * z ^ (κ + c) *
        ∫ t : ℝ in Set.Ioi 0,
          exp (-z * t) * (t : ℂ) ^ (c - 1) *
            AAR.Hypergeometric.gaussHGCut (1 / 2 + μ - κ) (1 / 2 - μ - κ) c (-(t : ℂ)) := by
  sorry

@[dlmf 13.16.E11]
theorem whittakerW_barnes {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ)
    (hκ : κ.re + σ < 0) :
    whittakerW κ μ x =
      exp (-(x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) *
          Gamma (-κ - (σ + I * t)) /
          (Gamma (1 / 2 + μ - κ) * Gamma (1 / 2 - μ - κ)) *
          (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

@[dlmf 13.16.E12]
theorem whittakerW_barnes_exp {κ μ : ℂ} {x σ : ℝ} (hx : 0 < x)
    (hμ : 0 < (1 / 2 + μ).re + σ) (hμ' : 0 < (1 / 2 - μ).re + σ) (hσ : 0 < σ) :
    whittakerW κ μ x =
      exp ((x : ℂ) / 2) / (2 * π * I) *
        ∫ t : ℝ, Gamma (1 / 2 + μ + σ + I * t) * Gamma (1 / 2 - μ + σ + I * t) /
          Gamma (1 - κ + σ + I * t) * (x : ℂ) ^ (-(σ + I * t)) * I := by
  sorry

end AAR.Confluent
