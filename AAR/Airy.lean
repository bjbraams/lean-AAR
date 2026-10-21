/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Basic
public import AAR.Airy.Bessel
public import AAR.Airy.Framework
public import AAR.Airy.Equation
public import AAR.Airy.IntegralRepresentations
public import AAR.Airy.Relations
public import AAR.Airy.Asymptotics
public import AAR.Airy.ModulusTools
public import AAR.Airy.ModulusPhase
public import AAR.Airy.Zeros
public import AAR.Airy.Scorer
public import AAR.Airy.ScorerAsymptotics
public import AAR.Airy.IntegralTools
public import AAR.Airy.Integrals
public import AAR.Airy.Products
public import AAR.Airy.Generalized
public import AAR.Airy.GeneralizedContours
public import AAR.Airy.Incomplete

/-!
# Airy functions (DLMF Chapter 9; Beals–Wong §9.9)

Mathlib has no Airy functions. This area defines `Ai` and `Bi` as entire functions through
their Maclaurin series (`AAR.Airy.Basic`), proves Airy's equation, the initial values, the
Wronskian, uniqueness of solutions from initial data, the rotation identities with cube roots
of unity and real-valuedness on `ℝ`; and relates them to Bessel functions of order `±1/3` on the
real line, with the leading large-`x` behaviour and positivity on `[0, ∞)` (`AAR.Airy.Bessel`).

The remaining modules acquire DLMF §§9.2 and 9.4–9.14, including Scorer, generalized and
incomplete Airy functions. The initial acquisition admits all new statements; existing
proofs are preserved. Oscillatory integrals include convergence limits, continued Bessel
arguments retain logarithmic coordinates, and asymptotic expansions use finite remainders.
The equation-by-equation inventory and source-domain qualifications are in
`AiryAcquisition.md` at the project root.
-/
