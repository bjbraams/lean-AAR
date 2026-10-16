/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Basic
public import AAR.Legendre.Ferrers
public import AAR.Legendre.Integer
public import AAR.Legendre.Laplace
public import AAR.Legendre.Neumann
public import AAR.Legendre.Recurrences
public import AAR.Legendre.SecondKind

/-!
# Legendre functions (Temme Chapter 8; DLMF Chapter 14)

Mathlib has no Legendre functions; the project's Legendre polynomials `legendreP` live in
`AAR.OrthogonalPolynomials`. This area defines, through the continuation `gaussHGCut` of `₂F₁` to
the cut plane, the Legendre functions `P_ν` (analytic off `(-∞, -1]`) and `Q_ν` (analytic off
`(-∞, 1]`) for complex degree, and the Ferrers functions `𝖯^μ_ν` on `(-1, 1)`.

Proved: the differential equations 14.2.1–14.2.2, `P_ν(1) = 1`, `P_{-ν-1} = P_ν` (14.9.5),
`P_n = legendreP n`, `P_ν(0)` (14.5.1), the recurrence 14.10.3 and the derivative relation,
`Q₀(z) = ½ log((z+1)/(z-1))`, `𝖯^m_ν = (-1)ᵐ (1-x²)^{m/2} P_ν⁽ᵐ⁾` (14.6.1), and Laplace's
first integral `P_ν(x) = π⁻¹ ∫₀^π (x + √(x²-1) cos φ)^ν dφ` for `x ≥ 1`. There are no
admissions.
-/
