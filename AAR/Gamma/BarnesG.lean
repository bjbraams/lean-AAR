/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Basic
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Barnes G-function (DLMF §5.17)

The Weierstrass product 5.17.3 is taken as the definition of `G(z+1)`.
-/

@[expose] public section

open Complex Filter MeasureTheory intervalIntegral
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Weierstrass factors in DLMF 5.17.3. -/
def barnesGTerm (z : ℂ) (k : ℕ) : ℂ :=
  let n : ℂ := k + 1
  (1 + z / n) ^ n * Complex.exp (-z + z ^ 2 / (2 * n))

/-- Barnes `G(z+1)` via the Weierstrass product. -/
@[dlmf 5.17.E3]
def barnesGSucc (z : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (z / 2) *
    Complex.exp (-(z * (z + 1) / 2) - (Real.eulerMascheroniConstant : ℂ) * z ^ 2 / 2) *
      ∏' k : ℕ, barnesGTerm z k

/-- Barnes `G(z) = G((z-1)+1)`. -/
def barnesG (z : ℂ) : ℂ := barnesGSucc (z - 1)

@[dlmf 5.17.E1]
theorem barnesG_one : barnesG 1 = 1 := by
  unfold barnesG
  rw [sub_self]
  have hterm : ∀ k : ℕ, barnesGTerm 0 k = 1 := by
    intro k
    unfold barnesGTerm
    simp [one_cpow, Complex.exp_zero]
  unfold barnesGSucc
  simp [hterm, cpow_zero, Complex.exp_zero, tprod_one]

@[dlmf 5.17.E1]
theorem barnesG_add_one (z : ℂ) :
    barnesG (z + 1) = Complex.Gamma z * barnesG z := by
  sorry

@[dlmf 5.17.E2]
theorem barnesG_nat (n : ℕ) (hn : 2 ≤ n) :
    barnesG n = ∏ k ∈ Finset.Icc 1 (n - 2), (k.factorial : ℂ) := by
  sorry

@[dlmf 5.17.E4]
theorem log_barnesGSucc {x : ℝ} (hx : 0 < x) :
    Complex.log (barnesGSucc x) =
      (1 / 2 : ℂ) * x * Complex.log (2 * π) - (1 / 2 : ℂ) * x * (x + 1) +
        x * Complex.log (Complex.Gamma (x + 1)) -
        ∫ t : ℝ in (0 : ℝ)..x, Complex.log (Complex.Gamma (t + 1)) := by
  sorry

/-- Glaisher–Kinkelin constant, via the first closed form for `C` in 5.17.7. -/
@[dlmf 5.17.E6]
def glaisherKinkelin : ℝ :=
  Real.exp ((Real.eulerMascheroniConstant + Real.log (2 * π)) / 12 -
    (deriv riemannZeta 2).re / (2 * π ^ 2))

@[dlmf 5.17.E7]
theorem glaisherKinkelin_eq_zeta_neg_one :
    Real.log glaisherKinkelin = 1 / 12 - (deriv riemannZeta (-1)).re := by
  sorry

@[dlmf 5.17.E5]
theorem log_barnesG_asymptotic {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (barnesGSucc (t + x)).re -
        ((1 / 4) * (t + x) ^ 2 + (t + x) * Real.log (Real.Gamma (t + x + 1)) -
          ((1 / 2) * (t + x) * (t + x + 1) + 1 / 12) * Real.log (t + x) -
          Real.log glaisherKinkelin))
      (fun t : ℝ => (t : ℝ) ^ (-(1 : ℝ))) := by
  sorry

end AAR.Gamma
