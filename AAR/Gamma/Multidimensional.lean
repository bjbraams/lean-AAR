/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Selberg.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Multidimensional integrals (DLMF §5.14)

The Selberg/Aomoto identities 5.14.4 are already in `AAR.Selberg.Basic`.
Dirichlet's simplex integrals and the remaining Hermite/circular ensembles are
recorded here. `Δ` is the Vandermonde product 5.14.3.
-/

@[expose] public section

open Complex MeasureTheory
open scoped Real

noncomputable section

namespace AAR.Gamma

/-- Vandermonde product, DLMF 5.14.3. -/
@[dlmf 5.14.E3]
def vandermonde {n : ℕ} (t : Fin n → ℝ) : ℝ :=
  ∏ i : Fin n, ∏ j : Fin n, if i.val < j.val then t i - t j else 1

@[dlmf 5.14.E1]
theorem dirichlet_simplex {n : ℕ} (z : Fin n → ℂ) (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        ∏ i : Fin n, (t i : ℂ) ^ (z i - 1) =
      (∏ i : Fin n, Complex.Gamma (z i)) / Complex.Gamma (1 + ∑ i, z i) := by
  sorry

@[dlmf 5.14.E2]
theorem dirichlet_simplex_full {n : ℕ} (z : Fin (n + 1) → ℂ)
    (hz : ∀ i, 0 < (z i).re) :
    ∫ t : Fin n → ℝ in
        (Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ)) ∩ {t | ∑ i, t i ≤ 1},
        (1 - ∑ i, (t i : ℂ)) ^ (z ⟨n, Nat.lt_succ_self n⟩ - 1) *
          ∏ i : Fin n, (t i : ℂ) ^ (z i.castSucc - 1) =
      (∏ i : Fin (n + 1), Complex.Gamma (z i)) / Complex.Gamma (∑ i, z i) := by
  sorry

@[dlmf 5.14.E5]
theorem selberg_laguerre {n m : ℕ} {a c : ℂ} (hm : m ≤ n)
    (ha : 0 < a.re) (hc : 0 < c.re) :
    ∫ t : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Ioi (0 : ℝ),
        (∏ i : Fin m, (t (Fin.castLE hm i) : ℂ)) *
          (∏ i : Fin n, (t i : ℂ) ^ (a - 1) * Complex.exp (-(t i : ℂ))) *
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) =
      (∏ k : Fin m, (a + (n - 1 - k : ℕ) * c)) *
        (∏ k : Fin n, Complex.Gamma (a + (n - 1 - k : ℕ) * c) *
          Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  sorry

@[dlmf 5.14.E6]
theorem selberg_hermite {n : ℕ} {c : ℂ} (hc : (-1 / n : ℝ) < c.re) :
    (1 / (2 * π : ℂ) ^ (n / 2 : ℂ)) *
        ∫ t : Fin n → ℝ,
          ((|vandermonde t| : ℝ) : ℂ) ^ (2 * c) *
            ∏ k : Fin n, Complex.exp (-(t k : ℂ) ^ 2 / 2) =
      (∏ k : Fin n, Complex.Gamma (1 + ((k : ℕ) + 1) * c)) /
        Complex.Gamma (1 + c) ^ n := by
  sorry

@[dlmf 5.14.E7]
theorem selberg_circular {n : ℕ} {b : ℂ} (hb : (-1 / n : ℝ) < b.re) :
    (1 / (2 * π : ℂ) ^ (n : ℂ)) *
        ∫ θ : Fin n → ℝ in Set.pi Set.univ fun _ => Set.Icc (-π) π,
          ∏ j : Fin n, ∏ k : Fin n,
            (if j.val < k.val then
              (‖Complex.exp (I * θ j) - Complex.exp (I * θ k)‖ : ℂ) ^ (2 * b)
            else 1) =
      Complex.Gamma (1 + b * n) / Complex.Gamma (1 + b) ^ n := by
  sorry

end AAR.Gamma
