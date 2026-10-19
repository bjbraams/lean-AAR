/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.EulerHalfLine
public import AAR.Hypergeometric.Boundary
public import AAR.Hypergeometric.AnalyticProperties
public import AAR.Hypergeometric.Asymptotics
public import AAR.Hypergeometric.Basic
public import AAR.Hypergeometric.ConnectionFormulas
public import AAR.Hypergeometric.Contiguous
public import AAR.Hypergeometric.ContinuedFractions
public import AAR.Hypergeometric.Continuation
public import AAR.Hypergeometric.ArgumentContinuation
public import AAR.Hypergeometric.Derivatives
public import AAR.Hypergeometric.DiffEq
public import AAR.Hypergeometric.Elementary
public import AAR.Hypergeometric.EulerIntegral
public import AAR.Hypergeometric.FurtherTransformations
public import AAR.Hypergeometric.Identities
public import AAR.Hypergeometric.IntegralRepresentations
public import AAR.Hypergeometric.Kummer
public import AAR.Hypergeometric.Riemann
public import AAR.Hypergeometric.Solutions
public import AAR.Hypergeometric.Transformations
public import AAR.Hypergeometric.BarnesAux
public import AAR.Hypergeometric.Generalized
public import AAR.Hypergeometric.LoopIntegral
public import AAR.Hypergeometric.Saalschutz
public import AAR.Hypergeometric.FiniteConvolution
public import AAR.Hypergeometric.GeneralizedCalculus
public import AAR.Hypergeometric.GeneralizedIntegral
public import AAR.Hypergeometric.Clausen
public import AAR.Hypergeometric.SpecialCases

/-!
# The hypergeometric function (AAR Chapters 2 and 3; DLMF Chapter 15)

Mathlib already supplies the Gaussian series `₂F₁` (`ordinaryHypergeometric`), its radius of
convergence, the regularized generalized series, and the binomial series
`(1+x)^a`. The imported modules record AAR Chapter 2–3 identities and suitable statements
from DLMF §§15.2, 15.4–15.8, and 15.10–15.12 that are absent from Mathlib.
Each statement taken from the DLMF records its equation number in a `@[dlmf]`
attribute. Many newly acquired statements are admitted and remain proof obligations.

From Duverney, *An Introduction to Hypergeometric Functions*, Chapters 3–4 (all proved):
Pfaff–Saalschütz (`Saalschutz`); the derivative, contiguous relation, uniqueness of power-series
solutions and Euler–Pochhammer integral of the general `ₚFq` (`GeneralizedCalculus`,
`GeneralizedIntegral`); Clausen's formula with Euler's `arcsin²` series and
`π² = 18 ∑ 1/(n² C(2n,n))` (`Clausen`); and `Si` as a `₁F₂` (`SpecialCases`).
-/
