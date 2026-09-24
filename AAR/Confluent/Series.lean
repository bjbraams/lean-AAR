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
public import Mathlib.Analysis.Complex.Trigonometric

/-!
# Series expansions (DLMF §§13.11, 13.24)

Bessel-function expansions of `M` and `M_{κ,μ}`. The generating function 13.11.4
for the coefficients `A_s` and 13.24.3 for `p_s^{(μ)}` are included.
-/

@[expose] public section

open Complex
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

@[dlmf 13.11.E1]
theorem confluentM_besselI_series {a b z : ℂ}
    (ha : ∀ k : ℕ, a + 1 / 2 ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    confluentM a b z =
      Gamma (a - 1 / 2) * exp (z / 2) * (z / 4) ^ (1 / 2 - a) *
        ∑' s : ℕ, poch (2 * a - 1) s * poch (2 * a - b) s / (poch b s * s.factorial) *
          (a - 1 / 2 + s) * besselI (a - 1 / 2 + s) (z / 2) := by
  sorry

@[dlmf 13.11.E2]
theorem confluentM_besselI_series_complement {a b z : ℂ}
    (hab : ∀ k : ℕ, b - a + 1 / 2 ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) (hz : z ∈ slitPlane) :
    confluentM a b z =
      Gamma (b - a - 1 / 2) * exp (z / 2) * (z / 4) ^ (a - b + 1 / 2) *
        ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * b - 2 * a - 1) s * poch (b - 2 * a) s *
          (b - a - 1 / 2 + s) / (poch b s * s.factorial) *
          besselI (b - a - 1 / 2 + s) (z / 2) := by
  sorry

/-- Coefficients `A_s` in DLMF 13.11.3–13.11.4. -/
@[dlmf 13.11.E4]
def besselExpansionCoeff (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => 0
  | 2 => b / 2
  | n + 3 =>
    ((n + 1 + b) * besselExpansionCoeff a b (n + 1) +
      (2 * a - b) * besselExpansionCoeff a b n) / (n + 3 : ℂ)

@[dlmf 13.11.E3]
theorem regularizedHGFun_besselJ_series {a b z : ℂ} (hz : z ∈ slitPlane)
    (hba : 0 ≤ (b - 2 * a).re) :
    regularizedHGFun {a} {b} z =
      exp (z / 2) * ∑' s : ℕ, besselExpansionCoeff a b s *
        (b - 2 * a) ^ ((1 - b - s) / 2) * (z / 2) ^ ((1 - b + s) / 2) *
          besselJ (b - 1 + s) ((2 * z * (b - 2 * a)) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 13.24.E1]
theorem whittakerM_besselI_series {κ μ z : ℂ}
    (hμ : ∀ k : ℕ, 2 * μ ≠ -k - 1) (hκ : ∀ k : ℕ, κ + μ ≠ -k - 1)
    (hz : z ∈ slitPlane) :
    whittakerM κ μ z =
      Gamma (κ + μ) * (2 : ℂ) ^ (2 * κ + 2 * μ) * z ^ (1 / 2 - κ) *
        ∑' s : ℕ, (-1 : ℂ) ^ s * poch (2 * κ + 2 * μ) s * poch (2 * κ) s /
          (poch (1 + 2 * μ) s * s.factorial) * (κ + μ + s) *
          besselI (κ + μ + s) (z / 2) := by
  sorry

/-- Generating function for `p_s^{(μ)}(z)` in DLMF 13.24.3. -/
@[dlmf 13.24.E3]
def whittakerBesselGenerating (μ z t : ℂ) : ℂ :=
  if t = 0 then 1
  else exp (-z / 2 * (cosh t / sinh t - t⁻¹)) * (t / sinh t) ^ (1 - 2 * μ)

@[dlmf 13.24.E3]
def whittakerBesselCoeff (μ z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (whittakerBesselGenerating μ z) 0 / s.factorial * (-z) ^ s

@[dlmf 13.24.E3]
theorem whittakerBesselCoeff_hasSum {μ z t : ℂ} (ht : t ≠ 0) (hz : z ≠ 0)
    (hsmall : ‖t‖ < 1) :
    HasSum (fun s : ℕ => whittakerBesselCoeff μ z s * (-t / z) ^ s)
      (exp (-z / 2 * (cosh t / sinh t - 1 / t)) * (t / sinh t) ^ (1 - 2 * μ)) := by
  sorry

@[dlmf 13.24.E2]
theorem whittakerM_besselJ_series {κ μ z : ℂ} (hz : z ∈ slitPlane)
    (hκ : 0 < κ.re) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    whittakerM κ μ z / Gamma (1 + 2 * μ) =
      (2 : ℂ) ^ (2 * μ) * z ^ (μ + 1 / 2) *
        ∑' s : ℕ, whittakerBesselCoeff μ z s *
          (2 * (κ * z) ^ (1 / 2 : ℂ)) ^ (-(2 * μ + s)) *
          besselJ (2 * μ + s) (2 * (κ * z) ^ (1 / 2 : ℂ)) := by
  sorry

end AAR.Confluent
