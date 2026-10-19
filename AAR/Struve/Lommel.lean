/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Basic

/-!
# Lommel functions and parameter continuation

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel

/-- lommelA. -/
@[dlmf 11.9.E4]
def lommelA (μ ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, ((μ+2*j+1)^2-ν^2)

/-- Nonexceptional parameters of the small Lommel function. -/
def LommelRegular (μ ν : ℂ) : Prop :=
  ∀ n : ℕ, μ-ν ≠ -(2*n+1) ∧ μ+ν ≠ -(2*n+1)

/-- lommelS. -/
@[dlmf 11.9.E3]
def lommelS (μ ν z : ℂ) : ℂ :=
  z^(μ+1) * ∑' k : ℕ, (-1)^k*z^(2*k)/lommelA μ ν (k+1)

/-- lommelCapitalRegular. -/
@[dlmf 11.9.E5]
def lommelCapitalRegular (μ ν z : ℂ) : ℂ :=
  lommelS μ ν z + 2^(μ-1)*Gamma ((μ+ν+1)/2)*Gamma ((μ-ν+1)/2)*(sin ((μ-ν)*π/2)*besselJ ν z-cos ((μ-ν)*π/2)*besselY ν z)

/-- Removable parameter continuation of the capital Lommel function, including exceptional parameters. -/
def lommelCapital (μ ν z : ℂ) : ℂ :=
  limUnder (𝓝[≠] μ) (fun m => lommelCapitalRegular m ν z)

/-- lommelCapital regular. -/
@[dlmf 11.9.E5]
theorem lommelCapital_regular {μ ν z : ℂ} (h : LommelRegular μ ν) (hz : z ∈ slitPlane) :
    lommelCapital μ ν z = lommelCapitalRegular μ ν z := by
  sorry

/-- Existence of the limiting definition at exceptional parameters. -/
theorem lommelCapital_parameter_limit (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    Tendsto (fun m => lommelCapitalRegular m ν z) (𝓝[≠] μ) (𝓝 (lommelCapital μ ν z)) := by
  sorry

/-- hasSum lommelS. -/
@[dlmf 11.9.E3]
theorem hasSum_lommelS {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => z^(μ+1)*(-1)^k*z^(2*k)/lommelA μ ν (k+1)) (lommelS μ ν z) := by
  sorry

/-- lommelA poch. -/
@[dlmf 11.9.E4]
theorem lommelA_poch (μ ν : ℂ) (k : ℕ) :
    lommelA μ ν k = 4^k*poch ((μ-ν+1)/2) k*poch ((μ+ν+1)/2) k := by
  induction k with
  | zero => simp [lommelA, poch_zero]
  | succ k ih =>
    have h : lommelA μ ν (k+1) = lommelA μ ν k*((μ+2*k+1)^2-ν^2) := by
      simp [lommelA, Finset.prod_range_succ]
    rw [h, ih, poch_succ, poch_succ, pow_succ]
    push_cast
    ring

/-- lommelS ode. -/
@[dlmf 11.9.E1]
theorem lommelS_ode {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv 2 (lommelS μ ν) z+deriv (lommelS μ ν) z/z+(1-ν^2/z^2)*lommelS μ ν z = z^(μ-1) := by
  sorry

/-- lommelS neg order. -/
@[dlmf 11.9.E6]
theorem lommelS_neg_order {μ ν : ℂ} (h : LommelRegular μ ν) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelS μ (-ν) z = lommelS μ ν z := by
  have h (k : ℕ) : lommelA μ (-ν) k=lommelA μ ν k := by simp [lommelA]
  simp only [lommelS, h]

/-- lommelCapital ode. -/
@[dlmf 11.9.E1]
theorem lommelCapital_ode (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    iteratedDeriv 2 (lommelCapital μ ν) z+deriv (lommelCapital μ ν) z/z+(1-ν^2/z^2)*lommelCapital μ ν z = z^(μ-1) := by
  sorry

/-- lommelCapital neg order. -/
@[dlmf 11.9.E6]
theorem lommelCapital_neg_order (μ ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapital μ (-ν) z = lommelCapital μ ν z := by
  sorry

/-- lommel general solution. -/
@[dlmf 11.9.E2]
theorem lommel_general_solution {μ ν : ℂ} (h : LommelRegular μ ν) (f : ℂ → ℂ) :
    (AnalyticOnNhd ℂ f slitPlane ∧ ∀ z ∈ slitPlane, iteratedDeriv 2 f z+deriv f z/z+(1-ν^2/z^2)*f z=z^(μ-1)) ↔ ∃ A B : ℂ, ∀ z ∈ slitPlane, f z=lommelS μ ν z+A*besselJ ν z+B*besselY ν z := by
  sorry

/-- lommelS bessel series 7. -/
@[dlmf 11.9.E7]
theorem lommelS_bessel_series_7 {μ ν : ℂ} (h : ∀ n : ℕ, μ-ν ≠ -(n+1) ∧ μ+ν ≠ -(n+1)) (hm : ∀ n : ℕ, μ ≠ -(n+1)) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2^(μ+1)*(2*k+μ+1)*Gamma (k+μ+1)/((k.factorial:ℂ)*(2*k+μ-ν+1)*(2*k+μ+ν+1))*besselJ (2*k+μ+1) z) (lommelS μ ν z) := by
  sorry

/-- lommelS bessel series 8. -/
@[dlmf 11.9.E8]
theorem lommelS_bessel_series_8 {μ ν : ℂ} (h : ∀ n : ℕ, μ-ν ≠ -(n+1) ∧ μ+ν ≠ -(n+1)) (hm : ∀ n : ℕ, μ ≠ -(n+1)) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2^((μ+ν-1)/2)*Gamma ((μ+ν+1)/2)*z^((μ+1-ν)/2)*(z/2)^k/((k.factorial:ℂ)*(2*k+μ-ν+1))*besselJ (k+(μ+ν+1)/2) z) (lommelS μ ν z) := by
  sorry

/-- lommelCapital asymptotic. -/
@[dlmf 11.9.E9]
theorem lommelCapital_asymptotic (μ ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => lommelCapital μ ν z-z^(μ-1)*∑ k ∈ Finset.range N, (-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ))) =O[sector (π-δ)] (fun z : ℂ => z^(μ-1-2*N)) := by
  sorry

/-- lommelCapital terminates. -/
@[dlmf 11.9.E9]
theorem lommelCapital_terminates {μ ν : ℂ} (n : ℕ) (h : μ+ν=2*n+1 ∨ μ-ν=2*n+1) {z : ℂ} (hz : z ∈ slitPlane) :
    lommelCapital μ ν z = z^(μ-1)*∑ k ∈ Finset.range (n+1), (-1)^k*lommelA (-μ) ν k*z^(-(2*k:ℤ)) := by
  sorry

end AAR.Struve
