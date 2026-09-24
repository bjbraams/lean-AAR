/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Basic
public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Continued fractions (DLMF §15.7)

All three coefficient sequences use Mathlib's `GenContFract` and `convs`;
the general continued-fraction machinery is not duplicated.
Convergence is acquired on the common real domain `0 < a,b < c`, `0 < x < 1/2`.
This avoids poles and exceptional terminating fractions. The larger complex
domains in DLMF need a meromorphic/projective formulation at denominator zeros.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

/-- Gauss's continued fraction, with DLMF's subtraction absorbed into the
partial numerators. Mathlib's stream index `k` corresponds to DLMF's `k+1`. -/
@[dlmf 15.7.E2]
def gaussContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := ((k + 1) / 2 : ℕ)
    ⟨-(if (k + 1)%2 = 1 then (a + n) * (c - b + n) else (b + n) * (c - a + n)) * z,
      c + (k + 1 : ℕ)⟩

/-- The second expansion of the same quotient. -/
@[dlmf 15.7.E4]
def contiguousContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c + (b - a + 1) * z
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := (k + 1 : ℕ)
    ⟨-(b + n) * (c - a + n) * z, c + n + (b - a + n + 1) * z⟩

/-- The continued fraction associated with the derivative quotient. -/
@[dlmf 15.7.E6]
def derivativeContinuedFraction (a b c z : ℂ) : GenContFract ℂ where
  h := c - (a + b + 1) * z
  s := Stream'.Seq.ofStream fun k =>
    let n : ℂ := (k + 1 : ℕ)
    ⟨(a + n) * (b + n) * z * (1 - z), c + n - (a + b + 2 * n + 1) * z⟩

@[dlmf 15.7.E1]
theorem gauss_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (gaussContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ))) := by
  sorry

@[dlmf 15.7.E3]
theorem contiguous_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (contiguousContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun a (b + 1) (c + 1) (x : ℂ))) := by
  sorry

@[dlmf 15.7.E5]
theorem derivative_continued_fraction_limit {a b c x : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hca : a < c) (hcb : b < c) (hx : 0 < x) (hx1 : x < 1 / 2) :
    Tendsto (derivativeContinuedFraction a b c x).convs atTop
      (𝓝 (regularizedGaussHGFun a b c (x : ℂ) / regularizedGaussHGFun (a + 1) (b + 1) (c + 1) (x : ℂ))) := by
  sorry

end AAR.Hypergeometric
