/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric

/-!
# DLMF Chapter 13 results already in Mathlib 4.35.0-rc2

The following statement excerpts are deliberately commented out: the declarations
belong to Mathlib. Variables implicit in the excerpts retain their upstream context.
DLMF tags are included in the commented excerpts; Mathlib’s cross-reference
attribute cannot modify documentation on imported declarations.

Mathlib does not define named Kummer `M`, Tricomi `U`, or Whittaker `M_{κ,μ}`,
`W_{κ,μ}`. Olver's regularized `𝐌(a,b,z)` is `regularizedHGFun {a} {b}`.
-/

public section

/- Already in Mathlib: `regularizedHGFun {a} {b}` is Olver's `𝐌(a,b,z)`.
@[dlmf 13.2.E3]
def regularizedHGFun {a b : ℂ} : ℂ → ℂ
-/
-- Mathlib: Complex.regularizedHGFun

/- Already in Mathlib: the series coefficients of `𝐌`.
@[dlmf 13.2.E3]
theorem regularizedHGFunCoeff_singleton (a b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {a} {b} n = poch a n / (n ! * Gamma (b + n))
-/
-- Mathlib: Complex.regularizedHGFunCoeff; project: regularizedHGFunCoeff_singleton

/- Already in Mathlib: infinite radius of the regularized confluent series.
@[dlmf 13.2.E3]
theorem radius_regularizedHGFunSeries_eq_top {a b : ℂ} :
    (regularizedHGFunSeries {a} {b}).radius = ⊤
-/
-- Mathlib: radius_regularizedHGFunSeries_eq_top (p ≤ q, here p = q = 1)

/- Already in Mathlib: `M(a,b,z) = Γ(b) 𝐌(a,b,z)` at regular `b`, recovered locally.
@[dlmf 13.2.E4]
-/
-- Project: kummerM_eq_mul_regularizedHGFun

/- Already in Mathlib: the generalized series includes `{}_2F_0`.
@[dlmf 13.6.E21]
-/
-- Mathlib: regularizedHGFun {a, a - b + 1} ∅ is the regularized `{}_2F_0`

/- Already in Mathlib: Gaussian `{}_2F_1`, used in 13.10.3, 13.10.7, 13.23.1, 13.23.4.
@[dlmf 13.10.E3]
-/
-- Mathlib: Complex.ordinaryHypergeometric / regularizedGaussHGFun
