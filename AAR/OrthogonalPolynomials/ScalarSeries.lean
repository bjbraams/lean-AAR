/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import Mathlib.Analysis.Analytic.OfScalars

/-!
# Scalar power series helpers

Mathlib's uniqueness of formal multilinear series identifies scalar coefficients
from their sums on a disk. Its shifted-series API supplies multiplication by monomials.
-/

@[expose] public section
open Complex Filter
open scoped Nat Topology
noncomputable section
namespace AAR.OrthogonalPolynomials

/-- Recover a scalar power series from its sums on the unit disk. -/
lemma scalarSeries_unique {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    (hd : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => d n * z ^ n) (f z)) : c = d := by
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => e n * z ^ n) (f z)) :
      HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ e) 0
        ((1 / 2 : NNReal) : ENNReal) := by
    refine ⟨?_, by norm_num, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using
        (he (1 / 2) (by norm_num)).summable.norm
    · intro z hz
      have hzNN : ‖z‖₊ < (1 / 2 : NNReal) := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < (1 / 2 : ℝ) := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- Multiplication of a power series by a monomial inserts a zero prefix. -/
lemma hasSum_scalar_shift {c : ℕ → ℂ} {z u : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u) (k : ℕ) :
    HasSum (fun n => (if k ≤ n then c (n - k) else 0) * z ^ n) (z ^ k * u) := by
  apply (hasSum_nat_add_iff' k).mp
  have hzero : ∑ n ∈ Finset.range k, (if k ≤ n then c (n - k) else 0) * z ^ n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [show ¬k ≤ n by have := Finset.mem_range.mp hn; omega]
  rw [hzero, sub_zero]
  convert hc.mul_left (z ^ k) using 1
  funext n
  simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
  ring

end AAR.OrthogonalPolynomials
