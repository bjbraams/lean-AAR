/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.NumberTheory.EulerPolynomials
public import ToMathlib.Analysis.EulerMaclaurin
public import ToMathlib.Analysis.BooleSummation
public import ToMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import ToMathlib.Analysis.Asymptotics.Watson
public import ToMathlib.Analysis.Integral.Laplace

/-!
# Supporting results for Mathlib

General results used by the special-function library but not specific to it, written in
the namespaces of the Mathlib APIs they extend. These modules import Mathlib only.

* `ToMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and Euler numbers.
* `ToMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin summation formula with remainder.
* `ToMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `ToMathlib.Analysis.Asymptotics.AsymptoticExpansion`: Poincaré asymptotic expansions.
* `ToMathlib.Analysis.Asymptotics.Watson`: Watson's lemma for Laplace transforms.
* `ToMathlib.Analysis.Integral.Laplace`: quantitative Laplace asymptotics with a quadratic
  phase (a copy of the `lean-codes` module of the same path).
-/
