/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Bessel.Basic
public import AAR.Bessel.Modified
public import AAR.Bessel.Theorems

/-!
# Bessel functions (AAR Chapter 4, §§4.5–4.15)

Mathlib now defines `Complex.besselJ` via the same regularized `₀F₁` series as the
project's `besselJ` (with `-(z/2)^2` in place of `-z^2/4`). This cluster also defines
`Y_ν`, `I_ν`, and `K_ν` and proves differential equations, recurrences, half-integer
values, Poisson's and Sonine's integrals, and the absolutely convergent generating function.

The remaining admitted results are Gegenbauer's addition theorem (DLMF 10.23.8),
Nicholson's integral (10.9.30), infinitely many positive zeros, and monotonicity of the first positive zero (10.21). Their stated domains
agree with DLMF; in particular, no radius ordering is needed in 10.23.8 for `J`.

The integer-order definitions of `Y` and `K` use `Filter.limUnder`. Existence of
these parameter limits at nonzero arguments remains to be proved; the current
ODE theorems for `Y` and `K` therefore cover only noninteger orders. The values at
zero supplied by the totalized definitions must not be interpreted as finite
limits of the classical singular functions. Sonine's integral (10.22.51) is proved
by termwise integration and Gamma moments. Nicholson's integral and the zero theorems
require further integral representations or oscillation/comparison theory.
-/
