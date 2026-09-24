/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Continued fractions (DLMF §§13.5, 13.17)

Partial numerators follow DLMF 13.5.2, 13.5.4, 13.17.2, and 13.17.4.
Convergence is acquired on a convenient real domain, matching the Chapter 15
restriction of meromorphic continued fractions.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

/-- Coefficients `u_n` in DLMF 13.5.2. Stream index `k` is DLMF's `n = k+1`. -/
def kummerMContFractCoeff (a b : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    (a - b - m) / ((b + 2 * m) * (b + 2 * m + 1))
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    (a + m) / ((b + 2 * m - 1) * (b + 2 * m))

@[dlmf 13.5.E2]
def kummerMContinuedFraction (a b z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨kummerMContFractCoeff a b k * z, 1⟩

/-- Coefficients `v_n` in DLMF 13.5.4. -/
def kummerUContFractCoeff (a b : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    a + m
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    a - b + m + 1

@[dlmf 13.5.E4]
def kummerUContinuedFraction (a b z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨kummerUContFractCoeff a b k / z, 1⟩

@[dlmf 13.5.E1]
theorem kummerM_continued_fraction_limit {a b x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hba : a < b) (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (kummerMContinuedFraction a b x).convs atTop
      (𝓝 (confluentM a b x / confluentM (a + 1) (b + 1) x)) := by
  sorry

@[dlmf 13.5.E3]
theorem kummerU_continued_fraction_limit {a b x : ℝ} (ha : 0 < a) (hb : 1 < b)
    (hx : 0 < x) :
    Tendsto (kummerUContinuedFraction a b x).convs atTop
      (𝓝 (confluentU a b x / confluentU a (b - 1) x)) := by
  sorry

/-- Coefficients `u_n` in DLMF 13.17.2. -/
def whittakerMContFractCoeff (κ μ : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    (-(1 / 2 + μ + κ + m) / ((2 * μ + 2 * m + 1) * (2 * μ + 2 * m + 2)))
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    (1 / 2 + μ - κ + m) / ((2 * μ + 2 * m) * (2 * μ + 2 * m + 1))

@[dlmf 13.17.E2]
def whittakerMContinuedFraction (κ μ z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨whittakerMContFractCoeff κ μ k * z, 1⟩

/-- Coefficients `v_n` in DLMF 13.17.4. -/
def whittakerWContFractCoeff (κ μ : ℂ) (k : ℕ) : ℂ :=
  if (k + 1) % 2 = 1 then
    let m : ℂ := (k / 2 : ℕ)
    1 / 2 + μ - κ + m
  else
    let m : ℂ := ((k + 1) / 2 : ℕ)
    1 / 2 - μ - κ + m

@[dlmf 13.17.E4]
def whittakerWContinuedFraction (κ μ z : ℂ) : GenContFract ℂ where
  h := 1
  s := Stream'.Seq.ofStream fun k => ⟨whittakerWContFractCoeff κ μ k / z, 1⟩

@[dlmf 13.17.E1]
theorem whittakerM_continued_fraction_limit {κ μ x : ℝ} (hμ : 0 < μ)
    (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (whittakerMContinuedFraction κ μ x).convs atTop
      (𝓝 (Real.sqrt x * whittakerM κ μ x / whittakerM (κ - 1 / 2) (μ + 1 / 2) x)) := by
  sorry

@[dlmf 13.17.E3]
theorem whittakerW_continued_fraction_limit {κ μ x : ℝ} (hμ : 0 < μ) (hx : 0 < x) :
    Tendsto (whittakerWContinuedFraction κ μ x).convs atTop
      (𝓝 (whittakerW κ μ x / (Real.sqrt x * whittakerW (κ - 1 / 2) (μ - 1 / 2) x))) := by
  sorry

end AAR.Confluent
