/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.General
public import AAR.OrthogonalPolynomials.Classical
public import AAR.OrthogonalPolynomials.Topics
public import AAR.OrthogonalPolynomials.MathlibCoverage
public import AAR.OrthogonalPolynomials.GeneralIdentities
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.OrthogonalPolynomials.Differential
public import AAR.OrthogonalPolynomials.Limits
public import AAR.OrthogonalPolynomials.Integrals
public import AAR.OrthogonalPolynomials.Series
public import AAR.OrthogonalPolynomials.BoundsZeros
public import AAR.OrthogonalPolynomials.ContinuedFractions
public import AAR.OrthogonalPolynomials.Hahn
public import AAR.OrthogonalPolynomials.Wilson
public import AAR.OrthogonalPolynomials.QFamilies
public import AAR.OrthogonalPolynomials.Associated
public import AAR.OrthogonalPolynomials.UnitCircle
public import AAR.OrthogonalPolynomials.Multivariate

/-!
# Orthogonal polynomials (AAR Chapters 5–7)

Mathlib already has Chebyshev polynomials `T,U,C,S` (including `T_n(cos θ) = cos(nθ)`,
orthogonality of `T` on `[-1,1]` with weight `(1-x²)^{-1/2}`, Chebyshev–Gauss quadrature, and
extrema), the probabilists' Hermite polynomials, and the shifted Legendre polynomials. The
modules below record the remaining AAR Chapters 5–7 material: general orthogonal polynomial
theory, the classical families (physicists' Hermite, Laguerre, Jacobi, Gegenbauer), and the
Chapter 7 topics (connection coefficients, Turán, Apéry's theorem).

The additional modules collect DLMF Chapter 18 statements, with an equation-by-equation
inventory and explicit scope notes in `OrthogonalPolynomials/DLMFCoverage.md`.
-/
