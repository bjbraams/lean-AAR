/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Basic
public import AAR.Gamma.Digamma
public import AAR.Gamma.Dirichlet
public import AAR.Gamma.GaussDigamma
public import AAR.Gamma.IntegralRep
public import AAR.Gamma.Kummer
public import AAR.Gamma.Multiplication
public import AAR.Gamma.Stirling
public import AAR.Gamma.Pochhammer
public import AAR.Gamma.SpecialValues
public import AAR.Gamma.Inequalities
public import AAR.Gamma.SeriesExpansions
public import AAR.Gamma.Products
public import AAR.Gamma.IntegralRepresentations
public import AAR.Gamma.ContinuedFractions
public import AAR.Gamma.Asymptotics
public import AAR.Gamma.BetaFunction
public import AAR.Gamma.Integrals
public import AAR.Gamma.Polygamma
public import AAR.Gamma.Multidimensional
public import AAR.Gamma.BarnesG
public import AAR.Gamma.QGamma
public import AAR.Gamma.MathlibCoverage

/-!
# The Gamma and Beta functions (AAR Chapter 1; DLMF Chapter 5)

Mathlib supplies Euler's integral, the recurrence, factorial values, reflection,
Legendre duplication, the Beta integral, Gauss's product, and the complex digamma
function. The modules below record AAR Chapter 1 identities and suitable statements
from DLMF §§5.2 and 5.4–5.18 that are absent from Mathlib.

Graphics §5.3, applications §§5.19–5.20, and computation §§5.21–5.24 are excluded.
Each statement taken from the DLMF records its equation number in a `@[dlmf]`
attribute. Many newly acquired statements are admitted and remain proof obligations.
-/
