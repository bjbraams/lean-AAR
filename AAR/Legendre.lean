/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated
public import AAR.Legendre.SpecialValues
public import AAR.Legendre.Connections
public import AAR.Legendre.AssociatedRecurrences
public import AAR.Legendre.Hypergeometric
public import AAR.Legendre.IntegralRepresentations
public import AAR.Legendre.Integrals
public import AAR.Legendre.Series
public import AAR.Legendre.Singularities
public import AAR.Legendre.IntegerTheory
public import AAR.Legendre.Toroidal
public import AAR.Legendre.Conical
public import AAR.Legendre.UniformCoordinates
public import AAR.Legendre.Uniform
public import AAR.Legendre.ConicalAsymptotics
public import AAR.Legendre.Sums
public import AAR.Legendre.Zeros
public import AAR.Legendre.Continuation
public import AAR.Legendre.Harmonics
public import AAR.Legendre.RelatedFunctions
public import AAR.Legendre.Primitives
public import AAR.Legendre.LocalTheory
public import AAR.Legendre.SourceChecks
public import AAR.Legendre.ParameterLimits
public import AAR.Legendre.Basic
public import AAR.Legendre.Ferrers
public import AAR.Legendre.Integer
public import AAR.Legendre.Laplace
public import AAR.Legendre.Neumann
public import AAR.Legendre.Recurrences
public import AAR.Legendre.SecondKind

/-!
# Legendre and related functions (Temme Chapter 8; DLMF Chapter 14)

The original seven modules retain their proved degree-only P/Q and Ferrers P
APIs. The additional modules acquire associated P/Q, regularized Olver Q,
Ferrers Q, parameter derivatives, integrals, series, uniform approximations,
toroidal and conical functions, continuation by ODE transport and normalized
spherical harmonics. Their remaining `sorry` declarations are admissions.

Mathlib's shifted Legendre Rodrigues formula is referenced in IntegerTheory;
its normalization bridge already exists in OrthogonalPolynomials.Classical.
`DLMF111214Acquisition.md` records every equation, source counterexamples,
remaining domain extensions and the current proof and axiom audits.
-/
