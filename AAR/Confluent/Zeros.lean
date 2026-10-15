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

/-- The boundary case omitted by the positive-zero formulas: `M(0,b,x) = 1`. -/
theorem confluentM_posZeros_zero (b : ℝ) : (confluentMPosZeros 0 b).encard = 0 := by
  simp [confluentMPosZeros, confluentM_of_zero_param]

/- The old 13.9.3–4 statements were false at `a = 0`; 13.9.5 omitted `a,b < 0`. -/
@[dlmf 13.9.E1]
theorem confluentM_posZeros_neg_a {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (confluentMPosZeros a b).encard = Int.toNat ⌈-a⌉ := by
  sorry

/-- Kummer's series has positive real part for nonnegative real numerator and
positive real argument, including its totalized denominator value at zero. -/
lemma confluentM_re_pos_of_nonneg {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 < x) : 0 < (confluentM a b x).re := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · have h : confluentM (a : ℂ) 0 x = 1 := by
      unfold confluentM
      rw [tsum_eq_single 0]
      · simp [poch_zero]
      · intro n hn
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp only [Nat.succ_eq_add_one, poch_zero_succ, zero_mul, div_zero]
    simp [h]
  · have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb)
    have hs := (hasFPowerSeriesOnBall_confluentM (a := (a : ℂ)) hb').hasSum_mul_pow
      (z := (x : ℂ)) (by simp)
    have hr := Complex.hasSum_re hs
    let t : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
      ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n
    have ht : ∀ n : ℕ, (confluentHGCoeff (a : ℂ) b n * (x : ℂ) ^ n).re = t n := by
      intro n
      simp [t, confluentHGCoeff, poch_ofReal, ← ofReal_natCast, ← ofReal_mul,
        ← ofReal_div, ← ofReal_pow]
    simp only [ht] at hr
    have hnonneg : ∀ n, 0 ≤ t n := fun n => mul_nonneg
      (div_nonneg (poch_eval_nonneg ha n)
        (mul_nonneg (poch_eval_nonneg hb.le n) (Nat.cast_nonneg _)))
      (pow_nonneg hx.le n)
    have hle := hr.summable.sum_le_tsum ({0} : Finset ℕ) (fun n _ => hnonneg n)
    have h0 : t 0 = 1 := by simp [t]
    rw [Finset.sum_singleton, h0, hr.tsum_eq] at hle
    linarith

@[dlmf 13.9.E2]
theorem confluentM_posZeros_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (confluentMPosZeros a b).encard = 0 := by
  rw [Set.encard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hzero⟩
  have hp := confluentM_re_pos_of_nonneg ha hb hx
  rw [hzero] at hp
  simp at hp

@[dlmf 13.9.E3]
theorem confluentM_posZeros_one {a b : ℝ} (ha : 0 < a) (hb0 : -1 < b) (hb1 : b < 0) :
    (confluentMPosZeros a b).encard = 1 := by
  sorry

@[dlmf 13.9.E4]
theorem confluentM_posZeros_b_le_neg_one {a b : ℝ} (ha : 0 < a) (hb : b ≤ -1)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (confluentMPosZeros a b).encard =
      Int.toNat (⌊-(b / 2)⌋ - ⌊-((b + 1) / 2)⌋) := by
  sorry

@[dlmf 13.9.E5]
theorem confluentM_posZeros_ceil {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : ⌈-a⌉ ≥ ⌈-b⌉) (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
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
  have hb : ∀ k : ℕ, (b : ℂ) ≠ -k := fun k hk => hbi k (by exact_mod_cast hk)
  have hz (x : ℝ) : confluentM a b x = 0 ↔ confluentM (b - a) b (-x) = 0 := by
    rw [confluentM_kummer_transform hb, mul_eq_zero]
    simp [Complex.exp_ne_zero]
  have heq : {x : ℝ | x < 0 ∧ confluentM a b x = 0} =
      (fun x : ℝ => -x) ⁻¹' confluentMPosZeros (b - a) b := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, confluentMPosZeros, neg_pos, hz, ofReal_sub, ofReal_neg]
  rw [heq]
  exact Set.encard_preimage_of_bijective (Equiv.neg ℝ).bijective _

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
