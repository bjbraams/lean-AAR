/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Jacobi's theta functions in DLMF normalization (Temme §12.3.2, DLMF §20.2)

Mathlib's `jacobiTheta₂ z τ = ∑ₙ exp(2πinz + πin²τ)` is `θ₃(πz|τ)`. We define `θ₁, …, θ₄` with
the DLMF argument convention (`q = e^{iπτ}`, period `π` in `z`) and derive their series,
periodicity, parity and the quasi-periodicity of `θ₃`, together with Jacobi's imaginary
transformation of `θ₃(0|τ)`, from Mathlib's results for `jacobiTheta₂`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

namespace AAR.Elliptic

/-- `θ₃(z|τ) = ∑ₙ q^{n²} e^{2inz}`, `q = e^{iπτ}` (DLMF 20.2.3), via Mathlib's `jacobiTheta₂`. -/
def thetaThree (z τ : ℂ) : ℂ := jacobiTheta₂ (z / π) τ

/-- `θ₄(z|τ) = θ₃(z + π/2|τ) = ∑ₙ (-1)ⁿ q^{n²} e^{2inz}` (DLMF 20.2.4). -/
def thetaFour (z τ : ℂ) : ℂ := thetaThree (z + π / 2) τ

/-- `θ₂(z|τ) = q^{1/4} e^{iz} θ₃(z + πτ/2|τ) = ∑ₙ q^{(n+1/2)²} e^{(2n+1)iz}` (DLMF 20.2.2). -/
def thetaTwo (z τ : ℂ) : ℂ := cexp (π * I * τ / 4 + I * z) * thetaThree (z + π * τ / 2) τ

/-- `θ₁(z|τ) = -θ₂(z + π/2|τ)` (DLMF §20.2). -/
def thetaOne (z τ : ℂ) : ℂ := -thetaTwo (z + π / 2) τ

/-- `(π : ℂ) ≠ 0`. -/
lemma pi_ne_zero' : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero

/-- The series for `θ₃` (DLMF 20.2.3). -/
@[dlmf 20.2.E3]
theorem thetaThree_eq_tsum (z τ : ℂ) :
    thetaThree z τ = ∑' n : ℤ, cexp (π * I * n ^ 2 * τ + 2 * I * n * z) := by
  rw [thetaThree, jacobiTheta₂]
  refine tsum_congr fun n => ?_
  rw [jacobiTheta₂_term]
  congr 1
  field_simp [pi_ne_zero']
  ring

/-- The series for `θ₄` (DLMF 20.2.4). -/
@[dlmf 20.2.E4]
theorem thetaFour_eq_tsum (z τ : ℂ) :
    thetaFour z τ = ∑' n : ℤ, (-1 : ℂ) ^ n * cexp (π * I * n ^ 2 * τ + 2 * I * n * z) := by
  rw [thetaFour, thetaThree_eq_tsum]
  refine tsum_congr fun n => ?_
  rw [← exp_pi_mul_I, ← exp_int_mul, ← exp_add]
  congr 1
  ring

/-- `θ₃(z + π|τ) = θ₃(z|τ)`. -/
theorem thetaThree_add_pi (z τ : ℂ) : thetaThree (z + π) τ = thetaThree z τ := by
  rw [thetaThree, thetaThree, add_div, div_self pi_ne_zero', jacobiTheta₂_add_left]

/-- `θ₃` is even. -/
theorem thetaThree_neg (z τ : ℂ) : thetaThree (-z) τ = thetaThree z τ := by
  rw [thetaThree, thetaThree, neg_div, jacobiTheta₂_neg_left]

/-- Quasi-periodicity `θ₃(z + πτ|τ) = q⁻¹ e^{-2iz} θ₃(z|τ)` (Temme §12.3.2). -/
theorem thetaThree_add_pi_mul (z τ : ℂ) :
    thetaThree (z + π * τ) τ = cexp (-(π * I * τ) - 2 * I * z) * thetaThree z τ := by
  rw [thetaThree, thetaThree, add_div, mul_div_cancel_left₀ _ pi_ne_zero',
    jacobiTheta₂_add_left']
  congr 2
  field_simp [pi_ne_zero']
  ring

/-- `θ₃(z - πτ|τ) = q⁻¹ e^{2iz} θ₃(z|τ)`. -/
theorem thetaThree_sub_pi_mul (z τ : ℂ) :
    thetaThree (z - π * τ) τ = cexp (-(π * I * τ) + 2 * I * z) * thetaThree z τ := by
  have h := thetaThree_add_pi_mul (z - π * τ) τ
  rw [sub_add_cancel] at h
  rw [h, ← mul_assoc, ← exp_add]
  ring_nf
  rw [exp_zero, one_mul]

/-- `θ₄(z + π|τ) = θ₄(z|τ)`. -/
theorem thetaFour_add_pi (z τ : ℂ) : thetaFour (z + π) τ = thetaFour z τ := by
  rw [thetaFour, thetaFour, show z + π + π / 2 = z + π / 2 + π by ring, thetaThree_add_pi]

/-- `θ₄` is even. -/
theorem thetaFour_neg (z τ : ℂ) : thetaFour (-z) τ = thetaFour z τ := by
  rw [thetaFour, thetaFour, ← thetaThree_neg, show -(-z + π / 2) = z - π / 2 by ring,
    ← thetaThree_add_pi (z - π / 2)]
  ring_nf

/-- `θ₂(z + π|τ) = -θ₂(z|τ)`. -/
theorem thetaTwo_add_pi (z τ : ℂ) : thetaTwo (z + π) τ = -thetaTwo z τ := by
  rw [thetaTwo, thetaTwo, show z + π + π * τ / 2 = z + π * τ / 2 + π by ring, thetaThree_add_pi,
    show π * I * τ / 4 + I * (z + π) = (π * I * τ / 4 + I * z) + π * I by ring, exp_add,
    exp_pi_mul_I]
  ring

/-- `θ₂` is even. -/
theorem thetaTwo_neg (z τ : ℂ) : thetaTwo (-z) τ = thetaTwo z τ := by
  rw [thetaTwo, thetaTwo, ← thetaThree_neg (-z + π * τ / 2),
    show -(-z + π * τ / 2) = (z + π * τ / 2) - π * τ by ring, thetaThree_sub_pi_mul,
    ← mul_assoc, ← exp_add]
  congr 2
  ring

/-- `θ₁(z + π|τ) = -θ₁(z|τ)`. -/
theorem thetaOne_add_pi (z τ : ℂ) : thetaOne (z + π) τ = -thetaOne z τ := by
  rw [thetaOne, thetaOne, show z + π + π / 2 = z + π / 2 + π by ring, thetaTwo_add_pi]

/-- `θ₁` is odd. -/
theorem thetaOne_neg (z τ : ℂ) : thetaOne (-z) τ = -thetaOne z τ := by
  rw [thetaOne, thetaOne, ← thetaTwo_neg, show -(-z + π / 2) = (z - π / 2) by ring,
    show z + π / 2 = (z - π / 2) + π by ring, thetaTwo_add_pi, neg_neg]

/-- Jacobi's imaginary transformation at `z = 0`: `θ₃(0|-1/τ) = (-iτ)^{1/2} θ₃(0|τ)`. -/
theorem thetaThree_zero_neg_inv {τ : ℂ} (hτ : τ ≠ 0) :
    thetaThree 0 (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * thetaThree 0 τ := by
  have h := jacobiTheta₂_functional_equation 0 τ
  simp only [zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
    exp_zero, mul_one] at h
  have hne : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ))
  rw [thetaThree, thetaThree, zero_div, h]
  field_simp

end AAR.Elliptic
