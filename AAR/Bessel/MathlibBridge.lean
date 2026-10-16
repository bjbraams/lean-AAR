/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Bessel.Basic
public import Mathlib.Analysis.SpecialFunctions.Bessel

/-!
# Bridge to Mathlib's `Complex.besselJ`

Mathlib defines `Complex.besselJ a x = (x/2)^a * ₀F̃₁(a+1; -(x/2)²)` with the same regularized
series as the project's root-namespace `besselJ`. This file proves the two agree and transfers
Mathlib's integer-order results: parity, entireness and the value at the origin.

This file deliberately does not `open Complex`, since `besselJ` would then be ambiguous.
-/

@[expose] public section

noncomputable section

/-- The project's `J_ν` is Mathlib's `Complex.besselJ`. -/
theorem besselJ_eq_complex_besselJ (ν z : ℂ) : besselJ ν z = Complex.besselJ ν z := by
  rw [besselJ, Complex.besselJ, Multiset.empty_eq_zero, div_pow]
  norm_num

/-- Parity at integer order: `J_n(-z) = (-1)^n J_n(z)` (DLMF 10.11.1). -/
@[dlmf 10.11.E1]
theorem besselJ_int_neg_arg (n : ℤ) (z : ℂ) : besselJ n (-z) = (-1) ^ n * besselJ n z := by
  simp only [besselJ_eq_complex_besselJ, Complex.besselJ_int_neg]

/-- At integer order `J_n` is entire. -/
theorem analyticAt_besselJ_int (n : ℤ) (z : ℂ) : AnalyticAt ℂ (besselJ n) z := by
  have h : besselJ (n : ℂ) = Complex.besselJ n := funext (besselJ_eq_complex_besselJ n)
  rw [h]
  exact Complex.analyticAt_besselJ_int n z

/-- The value at the origin: `J_0(0) = 1` and `J_ν(0) = 0` for `ν ≠ 0`. -/
theorem besselJ_zero_arg (ν : ℂ) : besselJ ν 0 = if ν = 0 then 1 else 0 := by
  rw [besselJ_eq_complex_besselJ, Complex.besselJ_zero]
