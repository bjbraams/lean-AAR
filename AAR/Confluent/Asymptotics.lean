/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Whittaker
public import AAR.Hypergeometric.Asymptotics
public import AAR.Gamma.Asymptotics
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Asymptotic expansions (DLMF §§13.7, 13.8, 13.19)

Poincaré expansions are stated along the positive real axis and, for regularized M,
on closed upper-half-plane sectors as the norm tends to infinity. Tricomi remainder
statements include an error bound or an asymptotic order, rather than an arbitrary
additive error. Remainder-region machinery 13.7.5–13.7.9 and 13.7.11–13.7.13, uniform
parabolic-cylinder/Bessel approximations 13.8.4–13.8.16, and the uniform
turning-point expansions of §§13.20–13.21 (Airy/Bessel with `envAi`/`envJ`)
are deferred.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Confluent

@[dlmf 13.7.E1]
theorem regularizedHGFun_poincare_real (a b : ℂ) (n : ℕ) (ha : ∀ k : ℕ, a ≠ -k) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => regularizedHGFun {a} {b} x -
        exp x * (x : ℂ) ^ (a - b) / Gamma a *
          ∑ s ∈ Finset.range n, poch (1 - a) s * poch (b - a) s / s.factorial *
            (x : ℂ) ^ (-(s : ℂ)))
      (fun x : ℝ => exp x * (x : ℂ) ^ (a - b - n)) := by
  sorry

/-- Two-term-family Poincaré expansion in closed upper-half-plane sectors.
The filter sends the norm to infinity; the bound contains both the exponential
and algebraic remainder scales. It is not a local boundedness assertion. -/
@[dlmf 13.7.E2]
theorem regularizedHGFun_poincare_sector (a b : ℂ) (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π / 2)
    (ha : ∀ k : ℕ, a ≠ -k) (hba : ∀ k : ℕ, b - a ≠ -k) :
    Asymptotics.IsBigO
      (Filter.comap (fun z : ℂ => ‖z‖) atTop ⊓
        Filter.principal {z : ℂ | δ ≤ z.arg ∧ z.arg ≤ π - δ})
      (fun z => regularizedHGFun {a} {b} z -
        (exp z * z ^ (a - b) / Gamma a *
          ∑ s ∈ Finset.range n, poch (1 - a) s * poch (b - a) s / s.factorial *
            z ^ (-(s : ℂ)) +
         exp (π * I * a) * z ^ (-a) / Gamma (b - a) *
          ∑ s ∈ Finset.range n, poch a s * poch (a - b + 1) s / s.factorial *
            (-z) ^ (-(s : ℂ))))
      (fun z => ‖exp z * z ^ (a - b - n)‖ + ‖z ^ (-a - n)‖) := by
  sorry

@[dlmf 13.7.E3]
theorem confluentU_poincare (a b : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => confluentU a b x -
        (x : ℂ) ^ (-a) * ∑ s ∈ Finset.range n,
          poch a s * poch (a - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => (x : ℂ) ^ (-a - n)) := by
  sorry

/-- For positive real `a` and `b ≤ a + 1`, the positive-ray Tricomi
truncation error is bounded by the magnitude of the first omitted term. -/
@[dlmf 13.7.E4]
theorem confluentU_poincare_finite {a b x : ℝ} (ha : 0 < a) (hb : b ≤ a + 1)
    (hx : 0 < x) (n : ℕ) :
    ‖confluentU a b x -
      (x : ℂ) ^ (-(a : ℂ)) * ∑ s ∈ Finset.range n,
        poch (a : ℂ) s * poch ((a : ℂ) - b + 1) s / s.factorial *
          (-(x : ℂ)) ^ (-(s : ℂ))‖ ≤
      ‖(x : ℂ) ^ (-(a : ℂ) - n) *
        poch (a : ℂ) n * poch ((a : ℂ) - b + 1) n / n.factorial‖ := by
  sorry

/-- A positive-ray remainder function with the stated order of decay.
This gives an actual asymptotic bound, not just an arbitrary additive error.
It does not yet assert the exponentially improved expansion of DLMF 13.7.10. -/
@[dlmf 13.7.E4]
theorem confluentU_poincare_remainder (a b : ℂ) (n : ℕ) :
    ∃ R : ℝ → ℂ,
      (∀ x : ℝ, 0 < x → confluentU a b x =
        (x : ℂ) ^ (-a) * ∑ s ∈ Finset.range n,
          poch a s * poch (a - b + 1) s / s.factorial * (-(x : ℂ)) ^ (-(s : ℂ)) + R x) ∧
      Asymptotics.IsBigO atTop R (fun x : ℝ => (x : ℂ) ^ (-a - n)) := by
  sorry

@[dlmf 13.8.E1]
theorem confluentM_large_b (a z : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => confluentM a b z -
        ∑ s ∈ Finset.range n, poch a s / (poch (b : ℂ) s * s.factorial) * z ^ s)
      (fun b : ℝ => ((b : ℂ)⁻¹) ^ n) := by
  sorry

/-- Analytic normalization of the generating function in 13.8.3.
The former product of singular powers assigned zero at the removable point. -/
@[dlmf 13.8.E3]
def largeBGenerating (a z t : ℂ) : ℂ :=
  AAR.Hypergeometric.expSubOneDiv t ^ (a - 1) * exp (t + z * (1 - exp (-t)))

@[dlmf 13.8.E3]
def largeBCoeff (a z : ℂ) (s : ℕ) : ℂ :=
  iteratedDeriv s (largeBGenerating a z) 0 / s.factorial

@[simp]
theorem largeBCoeff_zero (a z : ℂ) : largeBCoeff a z 0 = 1 := by
  simp [largeBCoeff, largeBGenerating, AAR.Hypergeometric.expSubOneDiv]

/- The Gamma ratio grows like b^a, so the absolute remainder is O(b^(-n)). -/
@[dlmf 13.8.E2]
theorem confluentM_large_b_poincare (a z : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => confluentM a b z -
        Gamma (b : ℂ) / Gamma ((b : ℂ) - a) *
          ∑ s ∈ Finset.range n, poch a s * largeBCoeff a z s * (b : ℂ) ^ (-(s : ℂ) - a))
      (fun b : ℝ => (b : ℂ) ^ (-(n : ℂ))) := by
  sorry

@[dlmf 13.8.E6]
theorem confluentM_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => confluentM a b b -
        (Real.sqrt π : ℂ) * (b / 2 : ℂ) ^ (a / 2) *
          (1 / Gamma ((a + 1) / 2) + (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (a / 2 - 1)) := by
  sorry

@[dlmf 13.8.E7]
theorem confluentU_transition (a : ℂ) :
    Asymptotics.IsBigO atTop
      (fun b : ℝ => confluentU a b b -
        (Real.sqrt π : ℂ) * (2 * b : ℂ) ^ (-(a / 2)) *
          (1 / Gamma ((a + 1) / 2) - (a + 1) * (8 / b : ℂ) ^ (1 / 2 : ℂ) / (3 * Gamma (a / 2))))
      (fun b : ℝ => (b : ℂ) ^ (-(a / 2) - 1)) := by
  sorry

/- DLMF uses scaled Gamma in M, ordinary Gamma in U, and a relative error in U.
The parameter ray is real and positive, as in the source statement. -/
@[dlmf 13.8.E17]
theorem confluentM_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => confluentM a (a / ν) z -
        exp (ν * z) * AAR.Gamma.scaledGamma (a / ν : ℂ) / AAR.Gamma.scaledGamma (a : ℂ) *
          (1 + (1 - ν) * (1 + 6 * ν ^ 2 * z ^ 2) / (12 * a)))
      (fun a : ℝ => (a : ℂ)⁻¹ ^ 2) := by
  sorry

@[dlmf 13.8.E18]
theorem confluentU_large_a_b (ν : ℝ) (z : ℂ) (hν : 0 < ν) (hν1 : ν < 1)
    (hz : 0 < z.re) :
    Asymptotics.IsBigO atTop
      (fun a : ℝ => confluentU a (a / ν + 1) z -
        z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) * Gamma (a / ν : ℂ) / Gamma (a : ℂ) *
          (1 + ν * z * (1 - ν) * (2 - ν * z) / (2 * a)))
      (fun a : ℝ => z ^ (-(a / ν : ℂ)) * exp ((1 - ν) * z) *
        Gamma (a / ν : ℂ) / Gamma (a : ℂ) * (a : ℂ)⁻¹ ^ 2) := by
  sorry

@[dlmf 13.19.E1]
theorem whittakerM_poincare_real (κ μ : ℂ) (n : ℕ)
    (hκ : ∀ k : ℕ, μ - κ ≠ -1 / 2 - k) (hμ : ∀ k : ℕ, 1 + 2 * μ ≠ -k) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerM κ μ x -
        Gamma (1 + 2 * μ) / Gamma (1 / 2 + μ - κ) * exp (x / 2) * (x : ℂ) ^ (-κ) *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 - μ + κ) s * poch (1 / 2 + μ + κ) s / s.factorial *
              (x : ℂ) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (x / 2) * (x : ℂ) ^ (-κ - n)) := by
  sorry

@[dlmf 13.19.E3]
theorem whittakerW_poincare (κ μ : ℂ) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun x : ℝ => whittakerW κ μ x -
        exp (-x / 2) * (x : ℂ) ^ κ *
          ∑ s ∈ Finset.range n,
            poch (1 / 2 + μ - κ) s * poch (1 / 2 - μ - κ) s / s.factorial *
              (-(x : ℂ)) ^ (-(s : ℂ)))
      (fun x : ℝ => exp (-x / 2) * (x : ℂ) ^ (κ - n)) := by
  sorry

end AAR.Confluent
