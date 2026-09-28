/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Zeros (DLMF §§13.9, 13.22)

`p(a,b)` and `n(a,b)` count positive zeros of `M(a,b,x)` and of
`M(a,b,x)` in the left half-plane after Kummer's transformation, respectively.
`T(a,b)` and `P(a,b)` count zeros of `U(a,b,x)` on `(0,∞)`. Bessel-zero
expansions 13.9.8 and 13.22.1 are deferred pending indexed Bessel zeros.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

/-- Positive real zeros of `M(a,b,·)`. -/
def confluentMPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ confluentM a b x = 0}

/-- Positive real zeros of `U(a,b,·)`. -/
def confluentUPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ confluentU a b x = 0}

@[dlmf 13.9.E1]
theorem confluentM_posZeros_neg_a {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (confluentMPosZeros a b).encard = Int.toNat ⌈-a⌉ := by
  sorry

@[dlmf 13.9.E2]
theorem confluentM_posZeros_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (confluentMPosZeros a b).encard = 0 := by
  sorry

@[dlmf 13.9.E3]
theorem confluentM_posZeros_one {a b : ℝ} (ha : 0 ≤ a) (hb0 : -1 < b) (hb1 : b < 0) :
    (confluentMPosZeros a b).encard = 1 := by
  sorry

@[dlmf 13.9.E4]
theorem confluentM_posZeros_b_le_neg_one {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ -1)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (confluentMPosZeros a b).encard =
      Int.toNat (⌊-(b / 2)⌋ - ⌊-((b + 1) / 2)⌋) := by
  sorry

@[dlmf 13.9.E5]
theorem confluentM_posZeros_ceil {a b : ℝ} (h : ⌈-a⌉ ≥ ⌈-b⌉) (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (confluentMPosZeros a b).encard = Int.toNat (⌈-a⌉ - ⌈-b⌉) := by
  sorry

@[dlmf 13.9.E6]
theorem confluentM_posZeros_ceil_swap {a b : ℝ} (h : ⌈-b⌉ > ⌈-a⌉) (ha : 0 < ⌈-a⌉)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (confluentMPosZeros a b).encard = Int.toNat ((⌈-b⌉ - ⌈-a⌉) % 2) := by
  sorry

@[dlmf 13.9.E7]
theorem confluentM_negZeros_eq {a b : ℝ} (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    {x : ℝ | x < 0 ∧ confluentM a b x = 0}.encard =
      (confluentMPosZeros (b - a) b).encard := by
  sorry

@[dlmf 13.9.E9]
theorem confluentM_large_zeros (a b : ℂ) (sign : Bool) (ha : ∀ k : ℕ, a ≠ -k)
    (hba : ∀ k : ℕ, b - a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ r : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => r n -
          ((if sign then 1 else -1) * (2 * n + a) * π * I +
            log (-Gamma a / Gamma (b - a) *
              ((if sign then 1 else -1) * 2 * n * π * I) ^ (b - 2 * a))))
        (fun n : ℕ => (n : ℂ)⁻¹ * log n) ∧
      ∀ᶠ n : ℕ in atTop, confluentM a b (r n) = 0 := by
  sorry

@[dlmf 13.9.E10]
theorem confluentM_zeros_in_a (b z : ℂ) (hz : z ≠ 0) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + π ^ 2 / (4 * z) * ((n : ℂ) ^ 2 + (b - 3 / 2) * n) +
          1 / (16 * z) * ((b - 3 / 2) ^ 2 * π ^ 2 + 4 / 3 * z ^ 2 -
            8 * b * (z - 1) - 4 * b ^ 2 - 3))
        (fun n : ℕ => (n : ℂ)⁻¹) ∧
      ∀ᶠ n : ℕ in atTop, confluentM (α n) b z = 0 := by
  sorry

@[dlmf 13.9.E11]
theorem confluentU_posZeros_gamma_pos {a b : ℝ}
    (h : 0 < Real.Gamma a * Real.Gamma (a - b + 1)) :
    (confluentUPosZeros a b).encard = Int.toNat (⌊-a⌋ + 1) := by
  sorry

@[dlmf 13.9.E12]
theorem confluentU_posZeros_gamma_neg {a b : ℝ}
    (h : Real.Gamma a * Real.Gamma (a - b + 1) < 0) :
    (confluentUPosZeros a b).encard = Int.toNat ⌊-a⌋ := by
  sorry

@[dlmf 13.9.E13]
theorem confluentU_posZeros_none {a b : ℝ} (ha : 0 ≤ a) :
    (confluentUPosZeros a b).encard = 0 := by
  sorry

/- DLMF 13.9.14 (count of zeros of `U(a,b,·)` on the negative axis) was removed from the
formalization: with the principal-branch `confluentU` the stated count is false, since `U` is
complex-valued and bounded away from zero on the negative axis in tested cases where the
count is positive. See `STATEMENT_AUDIT_2026-09-27.md`. -/

@[dlmf 13.9.E15]
theorem confluentU_negZeros_none {a b : ℝ} (h : a + 1 ≥ b) :
    {x : ℝ | x < 0 ∧ confluentU a b (x : ℂ) = 0}.encard = 0 := by
  sorry

@[dlmf 13.9.E16]
theorem confluentU_zeros_in_a (b z : ℂ) (hz : z ∈ slitPlane) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + n + 2 / π * (z * n) ^ (1 / 2 : ℂ) + 2 * z / π ^ 2 -
          b / 2 - 1 / 4)
        (fun n : ℕ => (n : ℂ)⁻¹ ^ (1 / 2 : ℂ)) ∧
      ∀ᶠ n : ℕ in atTop, confluentU (α n) b z = 0 := by
  sorry

end AAR.Confluent
