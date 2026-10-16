/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Constants.BBP
public import AAR.Constants.Catalan
public import AAR.Constants.Dirichlet

/-!
# Elementary constants and series (Duverney §§2.5, 8.4)

* `AAR.Constants.Dirichlet`: `∑ (-1)^i/(i+1) = ln 2` (as a limit of partial sums), Dirichlet's
  `η(s) = (1 - 2^{1-s}) ζ(s)` and `λ(s) = (1 - 2^{-s}) ζ(s)` for `Re s > 1`, and `ζ(s) → 1`.
* `AAR.Constants.Catalan`: Catalan's constant `G`, with `ψ'(1/4) = π² + 8G` and
  `ψ'(3/4) = π² - 8G`.
* `AAR.Constants.BBP`: the Bailey–Borwein–Plouffe formula for `π`, BBP-type series for `ln 2`,
  `ln 3`, `ln 5`, and Gauss's Machin-like formula.

There are no admissions.
-/
