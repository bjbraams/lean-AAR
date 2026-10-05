/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Differential
public import AAR.OrthogonalPolynomials.GegenbauerSeries

/-!
# Bounds, positive sums, zeros, and leading asymptotics

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

@[dlmf 18.14.E1]
theorem jacobi_bound_at_one {α β x : ℝ} (hαβ : β ≤ α) (hβ : -1 < β) (hα : -1 / 2 ≤ α) (hx : |x| ≤ 1) (n : ℕ) :
    ‖jacobiP α β n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  sorry

@[dlmf 18.14.E2]
theorem jacobi_bound_at_neg_one {α β x : ℝ} (hαβ : α ≤ β) (hα : -1 < α) (hβ : -1 / 2 ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    ‖jacobiP α β n x‖ ≤ (poch (β + 1) n).re / n.factorial := by
  sorry

@[dlmf 18.14.E3]
theorem jacobi_bernstein_bound {α β x : ℝ} (hα : α ∈ Set.Icc (-1 / 2) (1 / 2))
    (hβ : β ∈ Set.Icc (-1 / 2) (1 / 2)) (hx : |x| ≤ 1) (n : ℕ) :
    ((1 - x) / 2) ^ (α / 2 + 1 / 4) * ((1 + x) / 2) ^ (β / 2 + 1 / 4) * ‖jacobiP α β n x‖ ≤
      Real.Gamma (max α β + n + 1) / (Real.sqrt Real.pi * n.factorial *
        (n + (α + β + 1) / 2) ^ (max α β + 1 / 2)) := by
  sorry

/-- Pochhammer symbols of a positive real are positive reals. -/
lemma exists_poch_ofReal_eq {r : ℝ} (hr : 0 < r) (k : ℕ) :
    ∃ s : ℝ, 0 < s ∧ poch (r : ℂ) k = s := by
  induction k with
  | zero => exact ⟨1, one_pos, by simp [poch_zero]⟩
  | succ k ih =>
    obtain ⟨s, hs, hk⟩ := ih
    refine ⟨s * (r + k), by positivity, ?_⟩
    rw [poch_succ, hk]; push_cast; ring

@[dlmf 18.14.E4]
theorem gegenbauer_bound_at_one {lam x : ℝ} (hlam : 0 < lam) (hx : |x| ≤ 1) (n : ℕ) :
    ‖gegenbauer lam n x‖ ≤ (poch (2 * lam) n).re / n.factorial := by
  have hl : -1 / 2 < (lam : ℂ).re := by simp; linarith
  set θ := Real.arccos x
  have hcx : (x : ℂ) = cos (θ : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2]
  -- the coefficients of the trigonometric sum are positive reals
  have hc : ∀ k ≤ n, ∃ c : ℝ, 0 < c ∧ poch (lam : ℂ) k * poch (lam : ℂ) (n - k) /
      ((k.factorial : ℂ) * (n - k).factorial) = c := by
    intro k _
    obtain ⟨s, hs, h1⟩ := exists_poch_ofReal_eq hlam k
    obtain ⟨t, ht, h2⟩ := exists_poch_ofReal_eq hlam (n - k)
    refine ⟨s * t / (k.factorial * (n - k).factorial), by positivity, ?_⟩
    rw [h1, h2]; push_cast; ring
  choose! c hcpos hceq using hc
  have hone := gegenbauer_cos_sum hl n 0
  simp only [Complex.cos_zero, mul_zero] at hone
  have hval : gegenbauer (lam : ℂ) n 1 = poch (2 * (lam : ℂ)) n / n.factorial := by
    simp [gegenbauer]
  rw [hcx, gegenbauer_cos_sum hl n θ]
  calc ‖∑ k ∈ Finset.range (n + 1), poch (lam : ℂ) k * poch (lam : ℂ) (n - k) /
          ((k.factorial : ℂ) * (n - k).factorial) * cos (((n : ℂ) - 2 * k) * θ)‖
      ≤ ∑ k ∈ Finset.range (n + 1), c k := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
        have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [hceq k hkn, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hcpos k hkn).le]
        have : ‖cos (((n : ℂ) - 2 * k) * θ)‖ ≤ 1 := by
          rw [show ((n : ℂ) - 2 * k) * θ = (((n : ℝ) - 2 * k) * θ : ℝ) by push_cast; ring,
            ← Complex.ofReal_cos, Complex.norm_real, Real.norm_eq_abs]
          exact Real.abs_cos_le_one _
        nlinarith [hcpos k hkn]
    _ = (poch (2 * (lam : ℂ)) n).re / n.factorial := by
        have h := congrArg Complex.re (hone.symm.trans hval)
        rw [Finset.sum_congr rfl fun k hk => by
          rw [hceq k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)), mul_one]] at h
        rw [← Complex.ofReal_sum, Complex.ofReal_re] at h
        rw [h]
        simp

@[dlmf 18.14.E5]
theorem gegenbauer_even_bound {lam x : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam < 0) (hx : |x| ≤ 1) (n : ℕ) :
    ‖gegenbauer lam (2 * n) x‖ ≤ ‖poch lam n / (n.factorial : ℂ)‖ := by
  sorry

@[dlmf 18.14.E6]
theorem gegenbauer_odd_bound {lam x : ℝ} (hlam : -1 / 2 < lam) (hlam0 : lam < 0) (hx : |x| ≤ 1) (n : ℕ) :
    ‖gegenbauer lam (2 * n + 1) x‖ < -2 * (poch lam (n + 1)).re /
      (Real.sqrt ((2 * n + 1) * (2 * lam + 2 * n + 1)) * n.factorial) := by
  sorry

@[dlmf 18.14.E7]
theorem gegenbauer_bernstein_bound {lam x : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) (hx : |x| ≤ 1) (n : ℕ) :
    (n + lam) ^ (1 - lam) * (1 - x ^ 2) ^ (lam / 2) * ‖gegenbauer lam n x‖ <
      (2 : ℝ) ^ (1 - lam) / Real.Gamma lam := by
  sorry

@[dlmf 18.14.E8]
theorem laguerre_bound {α x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) (n : ℕ) :
    Real.exp (-x / 2) * ‖laguerre α n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  sorry

@[dlmf 18.14.E9]
theorem hermitePhys_bound (n : ℕ) (x : ℝ) :
    Real.exp (-(x ^ 2) / 2) * |aeval x (hermitePhys n)| ≤ Real.sqrt (2 ^ n * n.factorial) := by
  sorry

@[dlmf 18.14.E11]
theorem jacobi_turan {α β x : ℝ} (hα : -1 < α) (hαβ : α ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    (jacobiP α β (n + 1) x / jacobiP α β (n + 1) 1).re ^ 2 ≥
      (jacobiP α β n x / jacobiP α β n 1).re * (jacobiP α β (n + 2) x / jacobiP α β (n + 2) 1).re := by
  sorry

@[dlmf 18.14.E12]
theorem laguerre_turan {α x : ℝ} (hα : 0 ≤ α) (hx : 0 ≤ x) (n : ℕ) :
    (laguerre α (n + 1) x).re ^ 2 ≥ (laguerre α n x).re * (laguerre α (n + 2) x).re := by
  sorry

@[dlmf 18.14.E13]
theorem hermitePhys_turan (n : ℕ) (x : ℝ) :
    (aeval x (hermitePhys (n + 1)) : ℝ) ^ 2 ≥ aeval x (hermitePhys n) * aeval x (hermitePhys (n + 2)) := by
  set H : ℕ → ℝ := fun k => (aeval x (hermitePhys k) : ℝ) with hH
  have hrec : ∀ k : ℕ, H (k + 2) = 2 * x * H (k + 1) - 2 * (k + 1) * H k := by
    intro k
    simp only [hH]
    rw [hermitePhys_recurrence k]
    simp only [map_sub, map_mul, map_add, aeval_X, map_ofNat, map_natCast, map_one]
  have hD : ∀ n : ℕ, H (n + 1 + 1) ^ 2 - H (n + 1) * H (n + 1 + 2) =
      2 * (n + 1) * (H (n + 1) ^ 2 - H n * H (n + 2)) + 2 * H (n + 1) ^ 2 := by
    intro n
    have h1 := hrec n
    have h2 := hrec (n + 1)
    push_cast at h2
    rw [show n + 1 + 2 = n + 1 + 1 + 1 by ring] at h2 ⊢
    rw [show n + 2 = n + 1 + 1 by ring] at h1 ⊢
    linear_combination (H (n + 1 + 1)) * h1 - H (n + 1) * h2
  have key : ∀ n : ℕ, 0 ≤ H (n + 1) ^ 2 - H n * H (n + 2) := by
    intro n
    induction n with
    | zero =>
      simp only [hH, Nat.zero_add, hermitePhys_one, hermitePhys_two, hermitePhys_zero, map_sub,
        map_mul, map_pow, aeval_X, map_ofNat, map_one]
      nlinarith
    | succ n ih =>
      rw [hD n]
      have h1 : (0 : ℝ) ≤ 2 * (n + 1) := by positivity
      have h2 : (0 : ℝ) ≤ 2 * H (n + 1) ^ 2 := by positivity
      exact add_nonneg (mul_nonneg h1 ih) h2
  have := key n
  change 0 ≤ H (n + 1) ^ 2 - H n * H (n + 2) at this
  show H (n + 1) ^ 2 ≥ H n * H (n + 2)
  linarith

@[dlmf 18.14.E25]
theorem jacobi_positive_weighted_sum {α β lam x : ℝ} (hα : -1 < α) (hβ : -1 / 2 ≤ β)
    (hlam : 0 ≤ lam) (hαβ : lam ≤ α + β) (hx : -1 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), poch (lam + 1) (n - m) / (n - m).factorial *
      (poch (lam + 1) m / m.factorial) * jacobiP α β m x / jacobiP β α m 1).re := by
  sorry

@[dlmf 18.14.E26]
theorem jacobi_positive_sum {α β x : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hparams : (0 ≤ α + β ∧ -1 / 2 ≤ β) ∨ (-2 ≤ α + β ∧ 0 ≤ β)) (hx : -1 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), jacobiP α β m x / jacobiP β α m 1).re := by
  sorry

@[dlmf 18.14.E27]
theorem laguerre_positive_weighted_sum {β lam x : ℝ} (hβ : -1 / 2 ≤ β) (hlam : -1 / 2 ≤ lam) (hx : 0 ≤ x) (n : ℕ) :
    0 ≤ (∑ m ∈ Finset.range (n + 1), poch (lam + 1) (n - m) / (n - m).factorial *
      (poch (lam + 1) m / m.factorial) * (-1 : ℂ) ^ m * laguerre β m x / laguerre β m 0).re := by
  sorry

@[dlmf 18.16.i]
theorem jacobi_zeros {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, x i ∈ Set.Ioo (-1) 1) ∧
      ∀ z : ℂ, jacobiP α β n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  sorry

@[dlmf 18.16.iv]
theorem laguerre_zeros {α : ℝ} (hα : -1 < α) (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, 0 < x i) ∧
      ∀ z : ℂ, laguerre α n z = 0 ↔ ∃ i, z = (x i : ℂ) := by
  sorry

@[dlmf 18.16.E16]
theorem hermitePhys_zeros (n : ℕ) :
    ∃ x : Fin n → ℝ, StrictMono x ∧ (∀ i, |x i| < Real.sqrt (2 * n + 1)) ∧
      ∀ z : ℂ, (aeval z (hermitePhys n) : ℂ) = 0 ↔ ∃ i, z = (x i : ℂ) := by
  sorry

@[dlmf 18.15.E4_5]
theorem jacobi_darboux_asymptotic {α β θ : ℝ} (hα : -1 < α) (hβ : -1 < β)
    (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun n : ℕ => Real.sqrt n * (Real.sin (θ / 2)) ^ (α + 1 / 2) *
      (Real.cos (θ / 2)) ^ (β + 1 / 2) * (jacobiP α β n (Real.cos θ)).re -
      Real.cos ((n + (α + β + 1) / 2) * θ - (α + 1 / 2) * Real.pi / 2) / Real.sqrt Real.pi) atTop (𝓝 0) := by
  sorry


@[dlmf 18.14.E3_5]
theorem jacobi_weighted_bound {α β x : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hx : |x| ≤ 1) (n : ℕ) :
    ((1 + x) / 2) ^ (β / 2) * ‖jacobiP α β n x‖ ≤ (poch (α + 1) n).re / n.factorial := by
  sorry


@[dlmf 18.16.E12]
theorem laguerre_zero_lower_bound {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : laguerre α n x = 0) :
    ((n : ℝ) - 1 - Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 ≤ (n + 2) * x := by
  sorry


@[dlmf 18.16.E13]
theorem laguerre_zero_upper_bound {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n) {x : ℝ}
    (hx : laguerre α n x = 0) :
    ((n : ℝ) - 1 + Real.sqrt (n ^ 2 + (n + 2) * (α + 1))) ^ 2 - 1 ≥ (n + 2) * x := by
  sorry


/-- Discriminant expressed through a complete root list. The identities below
assume positive degree; this avoids conventions for the discriminant of a constant. -/
@[dlmf 18.2.E20]
def rootDiscriminant {n : ℕ} (leading : ℝ) (x : Fin n → ℝ) : ℝ :=
  leading ^ (2 * (n : ℤ) - 2) * ∏ i : Fin n, ∏ j : Fin n,
    if i < j then (x i - x j) ^ 2 else 1

@[dlmf 18.16.E19]
theorem jacobi_discriminant {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hinj : Function.Injective x) (hroot : ∀ i, jacobiP α β n (x i) = 0) :
    rootDiscriminant ((poch (n + α + β + 1) n).re / (2 ^ n * n.factorial)) x =
      (2 : ℝ)⁻¹ ^ (n * (n - 1)) * ∏ j ∈ Finset.Icc 1 n,
        (j : ℝ) ^ ((j : ℤ) - 2 * n + 2) * (j + α) ^ (j - 1) * (j + β) ^ (j - 1) *
          (n + j + α + β) ^ (n - j) := by
  sorry

@[dlmf 18.16.E20]
theorem laguerre_discriminant {α : ℝ} (hα : -1 < α) {n : ℕ} (hn : 0 < n)
    (x : Fin n → ℝ) (hinj : Function.Injective x) (hroot : ∀ i, laguerre α n (x i) = 0) :
    rootDiscriminant ((-1 : ℝ) ^ n / n.factorial) x =
      ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ ((j : ℤ) - 2 * n + 2) * (j + α) ^ (j - 1) := by
  sorry

@[dlmf 18.16.E21]
theorem hermitePhys_discriminant {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ) (hinj : Function.Injective x)
    (hroot : ∀ i, (aeval (x i) (hermitePhys n) : ℝ) = 0) :
    rootDiscriminant (2 ^ n) x = (2 : ℝ) ^ (3 * n * (n - 1) / 2) *
      ∏ j ∈ Finset.Icc 1 n, (j : ℝ) ^ j := by
  sorry


end AAR.OrthogonalPolynomials
