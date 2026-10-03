/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.Regularized
public import AAR.Confluent.BasicProperties
public import AAR.Confluent.Whittaker
public import AAR.Confluent.Recurrence
public import AAR.Confluent.IntegralRepresentations
public import AAR.Confluent.ContinuedFractions
public import AAR.Confluent.Relations
public import AAR.Confluent.Asymptotics
public import AAR.Confluent.Zeros
public import AAR.Confluent.Integrals
public import AAR.Confluent.Series
public import AAR.Confluent.ProductsAddition
public import AAR.Confluent.MathlibCoverage
public import AAR.Confluent.Continuation

/-!
# Confluent hypergeometric functions (AAR Chapter 4, §§4.1–4.4; DLMF Chapter 13)

Mathlib has the regularized generalized hypergeometric series, including the `p = q`
case of infinite radius, but not the named Kummer function `M(a,c,z) = ₁F₁(a;c;z)`,
Tricomi's `U(a,b,z)`, nor Whittaker's `M_{κ,μ}` and `W_{κ,μ}`. Bessel functions are
in `AAR.Bessel`.

The additional modules collect DLMF Chapter 13 statements from §§13.2–13.26.
Applications (§§13.27–13.28) and computation (§§13.29–13.32) are excluded, as is
notation §13.1. Each statement taken from the DLMF records its equation number in a
`@[dlmf]` attribute. Many newly acquired statements are admitted and remain proof
obligations.
-/
