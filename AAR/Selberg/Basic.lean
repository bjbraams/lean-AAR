/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Hypergeometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The Selberg and Aomoto integrals (AAR §§8.1–8.4)

Mathlib has the Selberg *sieve*, not Selberg's integral. The `n = 1` case is the Beta
integral already in Mathlib (`Complex.betaIntegral`).
-/

@[expose] public section

open Complex MeasureTheory intervalIntegral
open scoped Real

noncomputable section

/-- The Selberg integrand on `[0,1]^n` (AAR §8.1). -/
def selbergIntegrand (n : ℕ) (a b c : ℂ) (t : Fin n → ℝ) : ℂ :=
  (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * (1 - (t i : ℂ)) ^ (b - 1)) *
    ∏ i : Fin n, ∏ j : Fin n,
      if i.val < j.val then ((abs (t i - t j) : ℝ) : ℂ) ^ (2 * c) else 1

/-- Selberg's integral, AAR Theorem 8.1.1. Indexed so that `j : Fin n` corresponds to
the factor with shift `j · c`. -/
@[dlmf 5.14.E4]
theorem selberg_integral {n : ℕ} {a b c : ℂ} (hn : 0 < n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < 1 + n * c.re)
    (hca : 0 < a.re + (n - 1 : ℕ) * c.re)
    (hcb : 0 < b.re + (n - 1 : ℕ) * c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t =
      ∏ j : Fin n,
        Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
          (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) := by
  sorry

/-- The `n = 1` case is the Beta integral (independent of `c`). -/
@[dlmf 5.12.E1]
theorem selberg_integral_one {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    ∫ t : ℝ in (0 : ℝ)..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) =
      Gamma a * Gamma b / Gamma (a + b) := by
  have hG : Gamma (a + b) ≠ 0 :=
    Gamma_ne_zero_of_re_pos (by simp [add_re]; linarith)
  change betaIntegral a b = _
  rw [eq_div_iff_mul_eq hG, mul_comm, Gamma_mul_Gamma_eq_betaIntegral ha hb]

/-- Aomoto's extension (AAR §8.1, §8.3): inserting `∏_{i=1}^m t_i`. -/
@[dlmf 5.14.E4]
theorem aomoto_integral {n m : ℕ} {a b c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) 1,
        selbergIntegrand n a b c t * ∏ i : Fin m, (t (Fin.castLE hm i) : ℂ) =
      (∏ j : Fin m, (a + (n - 1 - j : ℕ) * c) / (a + b + (2 * n - 2 - j : ℕ) * c)) *
        ∏ j : Fin n,
          Gamma (a + (j : ℕ) * c) * Gamma (b + (j : ℕ) * c) * Gamma (1 + ((j : ℕ) + 1) * c) /
            (Gamma (a + b + (n + j - 1 : ℕ) * c) * Gamma (1 + c)) := by
  sorry
