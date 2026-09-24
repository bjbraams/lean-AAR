/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# DLMF Chapter 5 results already in Mathlib 4.35.0-rc2

The following statement excerpts are deliberately commented out: the declarations
belong to Mathlib. Variables implicit in the excerpts retain their upstream context.
DLMF tags are included in the commented excerpts; Mathlib’s cross-reference
attribute cannot modify documentation on imported declarations.
-/

public section

/- Already in Mathlib: Euler's integral.
@[dlmf 5.2.E1]
theorem Gamma_eq_integral {s : ℂ} (hs : 0 < s.re) :
    Gamma s = ∫ t : ℝ in Set.Ioi 0, exp (-t) * (t : ℂ) ^ (s - 1)
-/
-- Mathlib: Complex.Gamma_eq_integral, Real.Gamma_eq_integral

/- Already in Mathlib: digamma as logarithmic derivative.
@[dlmf 5.2.E2]
def digamma : ℂ → ℂ := logDeriv Gamma
-/
-- Mathlib: Complex.digamma; project real form: Real.digamma

/- Already in Mathlib: Euler–Mascheroni constant.
@[dlmf 5.2.E3]
def eulerMascheroniConstant : ℝ
-/
-- Mathlib: Real.eulerMascheroniConstant

/- Already in Mathlib: `(a)_n = Γ(a+n)/Γ(a)` at regular `a`.
@[dlmf 5.2.E5]
theorem Gamma_add_nat_div_Gamma_eq {n : ℕ} (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Gamma (z + n) / Gamma z = (ascPochhammer ℂ n).eval z
-/
-- Mathlib: Complex.Gamma_add_nat_div_Gamma_eq

/- Already in Mathlib: `Γ(1) = 1` and `Γ(n+1) = n!`.
@[dlmf 5.4.E1]
theorem Gamma_one : Gamma 1 = 1
theorem Gamma_nat_eq_factorial (n : ℕ) : Gamma (n + 1) = n !
-/
-- Mathlib: Complex.Gamma_one, Complex.Gamma_nat_eq_factorial (and real analogues)

/- Already in Mathlib: `Γ(1/2) = √π`.
@[dlmf 5.4.E6]
theorem Gamma_one_half_eq : Gamma (1 / 2) = √π
-/
-- Mathlib: Complex.Gamma_one_half_eq, Real.Gamma_one_half_eq

/- Already in Mathlib: `ψ(1) = -γ`.
@[dlmf 5.4.E12]
theorem digamma_one : digamma 1 = -eulerMascheroniConstant
-/
-- Mathlib: Complex.digamma_one; project: Real.digamma_one

/- Already in Mathlib: recurrence.
@[dlmf 5.5.E1]
theorem Gamma_add_one (s : ℂ) (h : s ≠ 0) : Gamma (s + 1) = s * Gamma s
-/
-- Mathlib: Complex.Gamma_add_one, Real.Gamma_add_one

/- Already in Mathlib: digamma recurrence.
@[dlmf 5.5.E2]
theorem digamma_apply_add_one (s : ℂ) (hs : ∀ m : ℕ, s ≠ -m) :
    digamma (s + 1) = digamma s + s⁻¹
-/
-- Mathlib: Complex.digamma_apply_add_one; project: Real.digamma_add_one

/- Already in Mathlib: Euler reflection.
@[dlmf 5.5.E3]
theorem Gamma_mul_Gamma_one_sub (z : ℂ) :
    Gamma z * Gamma (1 - z) = π / sin (π * z)
-/
-- Mathlib: Complex.Gamma_mul_Gamma_one_sub, Real.Gamma_mul_Gamma_one_sub

/- Already in Mathlib: digamma reflection.
@[dlmf 5.5.E4]
theorem digamma_one_sub (s : ℂ) :
    digamma (1 - s) = digamma s + π * cot (π * s)
-/
-- Mathlib: Complex.digamma_one_sub (equivalent form)

/- Already in Mathlib: Legendre duplication.
@[dlmf 5.5.E5]
theorem Gamma_mul_Gamma_add_half (s : ℂ) :
    Gamma s * Gamma (s + 1 / 2) = Gamma (2 * s) * 2 ^ (1 - 2 * s) * √π
-/
-- Mathlib: Complex.Gamma_mul_Gamma_add_half (equivalent to the DLMF form)

/- Already in Mathlib: digamma duplication.
@[dlmf 5.5.E8]
theorem digamma_two_mul (s : ℂ) :
    digamma (2 * s) = (1 / 2) * (digamma s + digamma (s + 1 / 2)) + log 2
-/
-- Mathlib: Complex.digamma_two_mul; project real rearrangement: digamma_add_digamma_add_half

/- Already in Mathlib: Gauss's product/limit.
@[dlmf 5.8.E1]
theorem GammaSeq_tendsto_Gamma (s : ℂ) :
    Tendsto (fun n : ℕ => GammaSeq s n) atTop (𝓝 (Gamma s))
-/
-- Mathlib: Complex.GammaSeq_tendsto_Gamma, Real.GammaSeq_tendsto_Gamma

/- Already in Mathlib: Beta integral and Gamma quotient.
@[dlmf 5.12.E1]
def betaIntegral (u v : ℂ) : ℂ
theorem Gamma_mul_Gamma_eq_betaIntegral {s t : ℂ} (hs : 0 < re s) (ht : 0 < re t) :
    Gamma s * Gamma t = Gamma (s + t) * betaIntegral s t
-/
-- Mathlib: Complex.betaIntegral, Complex.Gamma_mul_Gamma_eq_betaIntegral
-- Project: selberg_integral_one
