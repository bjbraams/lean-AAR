/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import AAR.Gamma.Polygamma
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin–Barnes and related integrals; sums (DLMF §§5.13, 5.16)

Vertical-line integrals are acquired with a real parameter `t` in place of the
source's `c±i∞` contour, on the indicated real-part strips. The inversion
contour 5.13.1 is restricted to positive real `z`. Parametrizing `s = σ + it`
converts the factor `1/(2πi) ds` into `1/(2π) dt`.
The alternating trigamma sum 5.16.1 has closed-form partial sums, and its limit
uses the odd part of `ζ(2)`.
-/

@[expose] public section

open Complex MeasureTheory Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

@[dlmf 5.13.E1]
theorem mellin_barnes_beta {a b : ℂ} {x σ : ℝ}
    (hx : 0 < x) (hab : 0 < (a + b).re) (hσa : -a.re < σ) (hσb : σ < b.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (σ + I * t + a) * Complex.Gamma (b - (σ + I * t)) *
          (x : ℂ) ^ (-(σ + I * t)) =
      Complex.Gamma (a + b) * (x : ℂ) ^ a / (1 + (x : ℂ)) ^ (a + b) := by
  sorry

@[dlmf 5.13.E2]
theorem mellin_barnes_norm_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hbπ : b < π / 2) :
    (1 / (2 * π)) * ∫ t : ℝ,
        ‖Complex.Gamma (a + I * t)‖ ^ 2 * Real.exp ((2 * b - π) * t) =
      Real.Gamma (2 * a) / (2 * Real.sin b) ^ (2 * a) := by
  sorry

@[dlmf 5.13.E3]
theorem mellin_barnes_four {a b c d : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (1 / (2 * π)) * ∫ t : ℝ,
        Complex.Gamma (a + I * t) * Complex.Gamma (b + I * t) *
          Complex.Gamma (c - I * t) * Complex.Gamma (d - I * t) =
      Complex.Gamma (a + c) * Complex.Gamma (a + d) * Complex.Gamma (b + c) *
        Complex.Gamma (b + d) / Complex.Gamma (a + b + c + d) := by
  sorry

@[dlmf 5.13.E4]
theorem mellin_barnes_inv_four {a b c d : ℂ}
    (h : 3 < (a + b + c + d).re) :
    ∫ t : ℝ, 1 /
        (Complex.Gamma (a + t) * Complex.Gamma (b + t) *
          Complex.Gamma (c - t) * Complex.Gamma (d - t)) =
      Complex.Gamma (a + b + c + d - 3) /
        (Complex.Gamma (a + c - 1) * Complex.Gamma (a + d - 1) *
          Complex.Gamma (b + c - 1) * Complex.Gamma (b + d - 1)) := by
  sorry

@[dlmf 5.13.E5]
theorem mellin_barnes_selberg {a : Fin 4 → ℂ} (ha : ∀ k, 0 < (a k).re) :
    (1 / (4 * π)) * ∫ t : ℝ,
        (∏ k : Fin 4, Complex.Gamma (a k + I * t) * Complex.Gamma (a k - I * t)) /
          (Complex.Gamma (2 * I * t) * Complex.Gamma (-2 * I * t)) =
      (∏ j : Fin 4, ∏ k : Fin 4, if j.val < k.val then Complex.Gamma (a j + a k) else 1) /
        Complex.Gamma (∑ k : Fin 4, a k) := by
  sorry

/-- `∑ 1/(2j+1)² = π²/8`. -/
lemma hasSum_one_div_odd_sq :
    HasSum (fun j : ℕ => (1 : ℝ) / (2 * j + 1) ^ 2) (π ^ 2 / 8) := by
  set f : ℕ → ℝ := fun n => 1 / (n : ℝ) ^ 2 with hf
  have h : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have he : HasSum (fun j : ℕ => f (2 * j)) (π ^ 2 / 24) := by
    have := h.div_const 4
    rw [show π ^ 2 / 6 / 4 = π ^ 2 / 24 by ring] at this
    refine this.congr_fun fun j => ?_
    simp only [hf]; push_cast
    rcases eq_or_ne j 0 with rfl | hj
    · simp
    · have : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      field_simp; ring
  have hinj : Function.Injective fun j : ℕ => 2 * j + 1 := fun a b h => by
    simp only at h; omega
  have ho : HasSum (fun j : ℕ => f (2 * j + 1)) (∑' j : ℕ, f (2 * j + 1)) :=
    (h.summable.comp_injective hinj).hasSum
  have hval := h.unique (HasSum.even_add_odd (f := f) he ho)
  have ho' : ∑' j : ℕ, f (2 * j + 1) = π ^ 2 / 8 := by linarith
  rw [ho'] at ho
  refine ho.congr_fun fun j => ?_
  simp only [hf]; push_cast; ring

/-- Tail of the trigamma series. -/
lemma tendsto_trigamma_nat_add_one : Tendsto (fun k : ℕ => Real.trigamma (k + 1)) atTop (𝓝 0) := by
  have hs : Summable fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2 := by
    have := (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
    simpa [one_div] using this
  refine (tendsto_sum_nat_add fun n : ℕ => ((n : ℝ) + 1)⁻¹ ^ 2).congr fun k => ?_
  rw [Real.trigamma_eq_tsum (by positivity)]
  congr 1; funext n; push_cast; ring_nf


/-- Consecutive trigamma values differ by `1/(k+1)²`. -/
lemma trigamma_succ_sub (k : ℕ) :
    Real.trigamma ((k : ℝ) + 1) - Real.trigamma (((k + 1 : ℕ) : ℝ) + 1) =
      1 / ((k : ℝ) + 1) ^ 2 := by
  have h := trigamma_add_one (x := (k : ℝ) + 1) (by positivity)
  push_cast
  rw [h]; field_simp; ring

/-- Even partial sums of the alternating trigamma series. -/
lemma sum_alternating_trigamma_even (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [show 2 * (M + 1) = 2 * M + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    have hd := trigamma_succ_sub (2 * M)
    have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have e2 : (-1 : ℝ) ^ (2 * M + 1 + 1) = 1 := by rw [pow_succ, e1]; norm_num
    rw [e1, e2]
    push_cast at hd ⊢
    linear_combination -hd

/-- Odd partial sums of the alternating trigamma series. -/
lemma sum_alternating_trigamma_odd (M : ℕ) :
    ∑ k ∈ Finset.range (2 * M + 1), (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2 - Real.trigamma ((2 * M : ℕ) + 1) := by
  rw [Finset.sum_range_succ, sum_alternating_trigamma_even]
  have e1 : (-1 : ℝ) ^ (2 * M + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
  rw [e1]; push_cast; ring

/-- The alternating trigamma series. It converges only conditionally, so it is stated with
ordered partial sums; Lean's unordered `tsum` of the series would be `0`. -/
@[dlmf 5.16.E1]
theorem sum_alternating_trigamma :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1))
      Filter.atTop (nhds (-π ^ 2 / 8)) := by
  set A : ℕ → ℝ := fun M => ∑ j ∈ Finset.range M, (1 : ℝ) / (2 * j + 1) ^ 2
  set E : ℕ → ℝ := fun N => if Even N then 0 else Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)
  have hform : ∀ N, ∑ k ∈ Finset.range N, (-1 : ℝ) ^ (k + 1) * Real.trigamma (k + 1) =
      -A (N / 2) - E N := by
    intro N
    obtain ⟨M, rfl | rfl⟩ := Nat.even_or_odd' N
    · rw [sum_alternating_trigamma_even]
      simp [A, E, show 2 * M / 2 = M by omega]
    · rw [sum_alternating_trigamma_odd]
      simp [A, E, show (2 * M + 1) / 2 = M by omega, Nat.not_even_bit1]
  simp_rw [hform]
  have hA : Tendsto (fun N => A (N / 2)) atTop (𝓝 (π ^ 2 / 8)) :=
    hasSum_one_div_odd_sq.tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop two_ne_zero)
  have hT : Tendsto (fun N : ℕ => Real.trigamma (((N - 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_trigamma_nat_add_one.comp (tendsto_sub_atTop_nat 1)
  have hE : Tendsto E atTop (𝓝 0) := by
    refine squeeze_zero (fun N => ?_) (fun N => ?_) hT
    · simp only [E]; split_ifs
      · exact le_rfl
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
    · simp only [E]; split_ifs
      · rw [Real.trigamma_eq_tsum (by positivity)]; positivity
      · exact le_rfl
  have := (hA.neg).sub hE
  simpa [neg_div] using this

@[dlmf 5.16.E2]
theorem sum_trigamma_div :
    ∑' k : ℕ, (1 / (k + 1 : ℝ)) * Real.trigamma (k + 2) = (riemannZeta 3).re := by
  sorry

end AAR.Gamma
