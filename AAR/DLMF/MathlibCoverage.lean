/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# DLMF Chapters 6–8 results already in Mathlib

The comments below are source pointers, deliberately not duplicate local theorems.
The pinned Mathlib has neither named exponential/error/Fresnel functions nor complex
incomplete Gamma/Beta continuations. Its `Complex.partialGamma` does cover the
positive-real-argument lower incomplete Gamma integral. The real error/inverse
functions imported by the project belong to TauCeti, including the declaration
`Real.erfInv` in TauCeti's source; the namespace alone does not identify ownership.

* DLMF 8.2.1 on real X≥0: `Complex.partialGamma` is the defining interval integral.
  See Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean. The local complex-argument
  continuation and its bridge remain separate obligations.
* DLMF 8.8.1 on real X≥0 and Re a>0: `Complex.partialGamma_add_one` in the same file.
  The existing project recurrence extends its parameter and argument coverage.
* DLMF 8.17.3: `Complex.betaIntegral_eq_Gamma_mul_div` in
  Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean, for positive real parts.
  The defining complete Beta integral is `Complex.betaIntegral`; no local proof
  of the displayed Gamma quotient is introduced.
* DLMF 7.7.6, b=c=x=0: `integral_gaussian_complex_Ioi` in
  Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean.
  Its full-line counterpart is `integral_gaussian_complex`.

The alternative notations of §8.1 are aliases for existing functions: Prym's
P_z(a), Q_z(a) mean `AAR.Confluent.lowerIncGamma a z`, `upperIncGamma a z`;
(a,z)! and [a,z]! shift that parameter to a+1. B(a,b,x), I(a,b,x) name the
incomplete Beta functions, and Luke's generalized trigonometric parameter is
1-a. These notational aliases do not introduce new mathematical functions.

The former equation 8.18.13 was retired in DLMF 1.1.8; its slot now points to
5.11.3. The scaled Gamma definition is recorded in `gammaScaled`, and the
project's proved logarithmic Stirling expansion is in AAR/Gamma/Asymptotics.lean.
-/
