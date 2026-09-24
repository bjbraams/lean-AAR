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

Mathlib has Bessel's inequality and Bessel potential spaces, but not the cylinder functions
`J_ν`, `Y_ν`, `I_ν`, `K_ν`. The regularized generalized hypergeometric series supplies the
`₀F₁` series used in the definitions of `J` and `I`.
-/
