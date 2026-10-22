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
public import ToMathlib.Analysis.Asymptotics.WatsonRotated
public import ToMathlib.Analysis.Asymptotics.AsymptoticInversion
public import ToMathlib.Analysis.Asymptotics.StationaryPhase
public import ToMathlib.Analysis.Integral.Laplace
public import ToMathlib.Analysis.Integral.Improper
public import ToMathlib.Analysis.Complex.Carlson
public import ToMathlib.Analysis.Complex.FactorialSeries
public import ToMathlib.Analysis.Complex.ParametricHolomorphy
public import ToMathlib.Analysis.Complex.SegmentPrimitive
public import ToMathlib.Analysis.Complex.StarPrimitive
public import ToMathlib.Analysis.Complex.BarnesResidue
public import ToMathlib.Analysis.Complex.ZeroLocalization
public import ToMathlib.Analysis.ContinuedFraction.Convergence
public import ToMathlib.Analysis.SpecificLimits.Pincherle
public import ToMathlib.Analysis.ODE.SturmComparison
public import ToMathlib.Analysis.ODE.PowerSeriesUniqueness
public import ToMathlib.Analysis.ODE.SoninePolya
public import ToMathlib.Analysis.ODE.Volterra
public import ToMathlib.Analysis.ODE.LiouvilleGreenVolterra
public import ToMathlib.Analysis.ODE.LiouvilleGreen
public import ToMathlib.Analysis.ODE.LiouvilleGreenReal
public import ToMathlib.Analysis.ODE.LiouvilleGreenExpansion
public import ToMathlib.Analysis.ODE.LiouvilleGreenComparison
public import ToMathlib.Analysis.ODE.LiouvilleGreenFinite
public import ToMathlib.Topology.Order.ZeroEnumeration
public import ToMathlib.Analysis.Calculus.DoubleZeroSqrt
public import ToMathlib.Analysis.Complex.MellinBarnesSeries
public import ToMathlib.Analysis.Complex.LagrangeBurmann
public import ToMathlib.Analysis.Integral.PrincipalValue
public import ToMathlib.Analysis.ODE.SturmCount
public import ToMathlib.Analysis.ODE.SturmDeformation
public import ToMathlib.Analysis.Asymptotics.StieltjesRemainder
public import ToMathlib.Analysis.Calculus.InverseSeries

/-!
# Supporting results for Mathlib

General results used by the special-function library but not specific to it, written in
the namespaces of the Mathlib APIs they extend. These modules import Mathlib only.

* `ToMathlib.Analysis.Complex.SegmentPrimitive`: straight-segment primitives and their derivatives.
* `ToMathlib.Analysis.Complex.StarPrimitive`: primitives of holomorphic functions on star-convex
  open sets.
* `ToMathlib.Analysis.Complex.BarnesResidue`: shifting a vertical-line integral across a simple
  pole (one-pole residue theorem on a strip).
* `ToMathlib.Analysis.Complex.ZeroLocalization`: existence and uniqueness of a zero near an
  approximate zero (contraction form of Newton–Kantorovich), with a filter version.
* `ToMathlib.Analysis.ContinuedFraction.Convergence`: convergence of generalized continued fractions
  through three-term recurrences (Pincherle, a ratio criterion, bracketing for positive elements).
* `ToMathlib.Analysis.SpecificLimits.Pincherle`: divergence of sums with ratio limit outside the unit
  disc, and convergence of a continued fraction from a backward solution with such a ratio limit.
* `ToMathlib.Analysis.Complex.FactorialSeries`: convergence and entireness of sparse factorial series.
* `ToMathlib.Analysis.Complex.ParametricHolomorphy`: holomorphy of dominated parametric series and
  integrals in finite-dimensional complex parameters, and the continuous Osgood lemma.
* `ToMathlib.Topology.Order.ZeroEnumeration`: unique zeros of strictly monotone functions and the
  enumeration of zeros separated by a sequence of points.
* `ToMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and Euler numbers.
* `ToMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin summation formula with remainder.
* `ToMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `ToMathlib.Analysis.Asymptotics.AsymptoticExpansion`: Poincaré asymptotic expansions.
* `ToMathlib.Analysis.Asymptotics.Watson`: Watson's lemma for Laplace transforms.
* `ToMathlib.Analysis.Asymptotics.StationaryPhase`: oscillatory integrals with a cubic stationary
  point at an endpoint.
* `ToMathlib.Analysis.Asymptotics.WatsonRotated`: rotation of Laplace rays, Watson's lemma along
  rotated rays, and gluing of asymptotic expansions on overlapping sectors.
* `ToMathlib.Analysis.Integral.Laplace`: quantitative Laplace asymptotics with a quadratic
  phase (a copy of the `lean-codes` module of the same path).
* `ToMathlib.Analysis.ODE.SturmComparison`: Sturm's comparison and separation theorems for
  `(p y')' + q y = 0`.
* `ToMathlib.Analysis.ODE.PowerSeriesUniqueness`: uniqueness for second-order linear ODEs
  (analytic, via the Taylor recurrence; real-variable, via Gronwall) and 2×2 linear systems.
* `ToMathlib.Analysis.ODE.SoninePolya`: the Sonine–Pólya theorem on relative maxima.
* `ToMathlib.Analysis.ODE.Volterra`: the Volterra integral equation and Gronwall-type
  perturbation estimate for `u'' + ω² u = g u`.
-/
