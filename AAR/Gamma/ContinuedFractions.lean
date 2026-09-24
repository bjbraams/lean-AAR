/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Basic
public import Mathlib.Algebra.ContinuedFractions.Basic

/-!
# Continued fractions (DLMF §5.10)

The Stieltjes-type continued fraction for Binet's function. The source lists
explicit partial numerators `a_0,…,a_6`; those values are recorded below. The
limit is acquired on `(1,∞)`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Partial numerators `a_k` in DLMF 5.10.1, with the seven tabulated values. -/
@[dlmf 5.10.E1]
def logGammaContFractCoeff : ℕ → ℂ
  | 0 => 1 / 12
  | 1 => 1 / 30
  | 2 => 53 / 210
  | 3 => 195 / 371
  | 4 => 22999 / 22737
  | 5 => 29944523 / 19733142
  | 6 => 109352241009 / 48264275462
  | _ => 0

@[dlmf 5.10.E1]
def logGammaContinuedFraction (z : ℂ) : GenContFract ℂ where
  h := 0
  s := Stream'.Seq.ofStream fun k => ⟨logGammaContFractCoeff k, z⟩

/-- Binet's function, the left-hand side of 5.10.1. -/
@[dlmf 5.10.E1]
def logGammaBinet (x : ℝ) : ℝ :=
  Real.log (Real.Gamma x) + x - (x - 1 / 2) * Real.log x - (1 / 2) * Real.log (2 * π)

@[dlmf 5.10.E1]
theorem logGamma_continued_fraction_limit {x : ℝ} (hx : 1 < x) :
    Tendsto (logGammaContinuedFraction x).convs atTop (𝓝 (logGammaBinet x : ℂ)) := by
  sorry

end AAR.Gamma
