/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Bessel.Asymptotics
public import AAR.Bessel.Basic
public import AAR.Bessel.BesselIntegral
public import AAR.Bessel.Elementary
public import AAR.Bessel.KIntegrals
public import AAR.Bessel.KIntegralRep
public import AAR.Bessel.IntegralTransforms
public import AAR.Bessel.LaplaceTransform
public import AAR.Bessel.LargeOrder
public import AAR.Bessel.Lommel
public import AAR.Bessel.Modified
public import AAR.Bessel.NeumannSeries
public import AAR.Bessel.ProductIntegral
public import AAR.Bessel.Schlafli
public import AAR.Bessel.SecondKind
public import AAR.Bessel.SturmZeros
public import AAR.Bessel.Theorems
public import AAR.Bessel.YIntegralRep
public import AAR.Bessel.YSchlafli
public import AAR.Bessel.WeberSeries
public import AAR.Bessel.Zeros
public import AAR.Bessel.MathlibCoverage

/-!
# Bessel functions (AAR Chapter 4, §§4.5–4.15; DLMF Chapter 10)

`J_ν` is Mathlib's `Complex.besselJ`, used directly; `besselJ_eq_regularized` gives its
regularized `₀F₁` series form, and Mathlib supplies parity at integer order (DLMF 10.11.1),
analyticity, entireness at integer order and the value at `0`. This cluster defines `Y_ν`,
`I_ν`, `K_ν` and the Hankel functions. It proves differential equations, recurrences,
Wronskians, half-integer values, Poisson's, Sonine's, Bessel's and Lommel's integrals, the
generating function, Hankel's large-argument expansions and the existence of infinitely many real
zeros.

The integer-order values of `Y` and `K` are parameter limits (`Filter.limUnder`). These limits
exist at every nonzero argument, are jointly continuous in order and argument
(`continuousAt_besselY`, `continuousAt_besselK`), and satisfy the recurrences and differential
equations for all orders. `WeberSeries` gives `Y_{-n} = (-1)ⁿ Y_n`, `Y_n` as an order derivative
of `J_ν`, the logarithmic series of `Y_n` (DLMF 10.8.1–10.8.2), the general solution
`A J_ν + B Y_ν` of Bessel's equation, the product formula 10.8.3 and the Jacobi–Anger cosine and
sine series. The values at zero supplied by the totalized definitions must not be
interpreted as finite limits of the classical singular functions.

The remaining admitted results are Gegenbauer's addition theorem (DLMF 10.23.8) and Nicholson's
integral (10.9.30). Their
stated domains agree with DLMF; in particular, no radius ordering is needed in 10.23.8 for `J`.
-/
