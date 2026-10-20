/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.NumberTheory.EulerPolynomials
public import ToMathlib.NumberTheory.EulerNumbers
public import ToMathlib.NumberTheory.BernoulliTaylor
public import ToMathlib.Analysis.SpecialFunctions.Trigonometric.PartialFractions
public import ToMathlib.Analysis.EulerMaclaurin
public import ToMathlib.Analysis.BooleSummation
public import ToMathlib.Analysis.Asymptotics.AsymptoticExpansion
public import ToMathlib.Analysis.Asymptotics.Watson
public import ToMathlib.Analysis.Integral.Laplace
public import ToMathlib.Analysis.Complex.Carlson
public import ToMathlib.Analysis.Complex.FactorialSeries
public import ToMathlib.Analysis.Complex.ParametricHolomorphy
public import ToMathlib.Analysis.Complex.SegmentPrimitive
public import ToMathlib.Analysis.ODE.SturmComparison
public import ToMathlib.Analysis.ODE.SoninePolya
public import ToMathlib.Analysis.ODE.Volterra

/-!
# Supporting results for Mathlib

General results used by the special-function library but not specific to it, written in
the namespaces of the Mathlib APIs they extend. These modules import Mathlib only.

* `ToMathlib.Analysis.Complex.SegmentPrimitive`: straight-segment primitives and their derivatives.
* `ToMathlib.Analysis.Complex.FactorialSeries`: convergence and entireness of sparse factorial series.
* `ToMathlib.Analysis.Complex.ParametricHolomorphy`: holomorphy of dominated parametric series and
  integrals in finite-dimensional complex parameters, and the continuous Osgood lemma.
* `ToMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and Euler numbers.
* `ToMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin summation formula with remainder.
* `ToMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `ToMathlib.Analysis.Asymptotics.AsymptoticExpansion`: Poincaré asymptotic expansions.
* `ToMathlib.Analysis.Asymptotics.Watson`: Watson's lemma for Laplace transforms.
* `ToMathlib.Analysis.Integral.Laplace`: quantitative Laplace asymptotics with a quadratic
  phase (a copy of the `lean-codes` module of the same path).
* `ToMathlib.Analysis.ODE.SturmComparison`: Sturm's comparison and separation theorems for
  `(p y')' + q y = 0`.
* `ToMathlib.Analysis.ODE.SoninePolya`: the Sonine–Pólya theorem on relative maxima.
* `ToMathlib.Analysis.ODE.Volterra`: the Volterra integral equation and Gronwall-type
  perturbation estimate for `u'' + ω² u = g u`.
-/
