/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Upstream
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.Harmonic.ZetaAsymp
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues

/-!
# DLMF Chapters 4, 24 and 25: central results already in Mathlib

Checked `dlmf_upstream` pointers for central identities of DLMF Chapter 4 (elementary
functions), Chapter 24 (Bernoulli polynomials) and Chapter 25 (zeta functions) that Mathlib
proves without a `@[dlmf]` tag. This is a selection, not an inventory. Chapter 5 pointers are
in `DLMF.Gamma.MathlibCoverage`.

Conventions. `Complex.log` is the principal branch with `Complex.arg ∈ (-π, π]` and
`log 0 = 0`; `Complex.tan` is `sin / cos` with Mathlib's `x / 0 = 0`. Mathlib's `bernoulli n`
are DLMF's `B_n` (`B_1 = -1/2`); `bernoulli' n` has `B'_1 = +1/2`. `Polynomial.bernoulli n` is
DLMF's `B_n(x)` over `ℚ`, and `bernoulliFun n` its real evaluation. Mathlib's `hurwitzZeta a s`
takes `a : ℝ/ℤ`.

Items already tagged with `@[dlmf]` in Mathlib get no pointer: 4.14.1, 4.14.2, 4.14.4, 4.14.7,
4.28.1, 4.28.2, 4.28.4, 4.34.1, 4.34.2, 4.35.11, 4.35.26 and 4.35.27.

Two printed DLMF domains include a boundary where the principal-branch identity fails, so the
Mathlib statements below are recorded as special cases: in 4.8.2 at `ph z₁ + ph z₂ = -π`
(for `z₁ = z₂ = -i`, `ln(z₁z₂) = iπ` but `ln z₁ + ln z₂ = -iπ`), and in 4.8.9 at `Im z = -π`
(for `z = -iπ`, `ln(exp z) = iπ`).
-/

/-! ### Chapter 4: logarithm, exponential and powers -/

dlmf_upstream 4.2.E5 Complex.log
  "exact: ln z = ln|z| + i ph z with -π < ph z ≤ π, z ≠ 0; Mathlib's log 0 = 0 is totalized"
dlmf_upstream 4.2.E19 NormedSpace.expSeries_div_hasSum_exp
  "partial: Σ zⁿ/n! sums to NormedSpace.exp z, which is Complex.exp by Complex.exp_eq_exp_ℂ"
dlmf_upstream 4.2.E19 Complex.exp_eq_exp_ℂ
  "partial: Complex.exp is the exponential series NormedSpace.exp"
dlmf_upstream 4.2.E20 Complex.exp_periodic "exact: exp is 2πi-periodic"
dlmf_upstream 4.2.E21 Complex.exp_neg "exact"
dlmf_upstream 4.2.E22 Complex.norm_exp "exact"
dlmf_upstream 4.2.E24 Complex.exp_eq_exp_re_mul_sin_add_cos "exact: x = Re z, y = Im z"
dlmf_upstream 4.2.E28 Complex.cpow_def
  "exact: z ≠ 0, principal branch; Mathlib sets 0^0 = 1 and 0^a = 0 for a ≠ 0"

dlmf_upstream 4.5.E1 Real.log_lt_sub_one_of_pos
  "partial: right inequality ln(1+x) < x, in the form ln y < y - 1 for y = 1 + x > 0, y ≠ 1"
dlmf_upstream 4.5.E4 Real.log_le_sub_one_of_pos "exact: x > 0"
dlmf_upstream 4.5.E8 Real.add_one_lt_exp "exact: x ≠ 0 (equality at x = 0)"

dlmf_upstream 4.8.E2 Complex.log_mul
  "special case: z₁, z₂ ≠ 0 and -π < ph z₁ + ph z₂ ≤ π; the printed bound -π fails for the \
  principal branch (Complex.log_mul_eq_add_log_iff is the iff)"
dlmf_upstream 4.8.E9 Complex.log_exp
  "special case: -π < Im z ≤ π; the printed bound Im z = -π fails for the principal branch"
dlmf_upstream 4.8.E10 Complex.exp_log "partial: exp(ln z) = z for z ≠ 0"
dlmf_upstream 4.8.E13 Real.log_rpow "exact: a > 0, real x"
dlmf_upstream 4.8.E14 Complex.cpow_add "exact: a ≠ 0, principal powers"
dlmf_upstream 4.8.E16 Complex.exp_add "exact"

/-! ### Chapter 4: trigonometric and hyperbolic functions -/

dlmf_upstream 4.14.E3 Complex.exp_mul_I "partial: upper sign, cos z + i sin z = e^{iz}"
dlmf_upstream 4.14.E8 Complex.sin_add_int_mul_two_pi "exact: k ∈ ℤ"
dlmf_upstream 4.14.E9 Complex.cos_add_int_mul_two_pi "exact: k ∈ ℤ"
dlmf_upstream 4.14.E10 Complex.tan_add_int_mul_pi
  "exact: k ∈ ℤ; Mathlib's tan is 0 at the poles, where the identity also holds"

dlmf_upstream 4.21.E2 Complex.sin_add "partial: upper sign"
dlmf_upstream 4.21.E2 Complex.sin_sub "partial: lower sign"
dlmf_upstream 4.21.E3 Complex.cos_add "partial: upper sign"
dlmf_upstream 4.21.E3 Complex.cos_sub "partial: lower sign"
dlmf_upstream 4.21.E12 Complex.sin_sq_add_cos_sq "exact"
dlmf_upstream 4.21.E24 Complex.sin_neg "exact"
dlmf_upstream 4.21.E25 Complex.cos_neg "exact"
dlmf_upstream 4.21.E26 Complex.tan_neg "exact"
dlmf_upstream 4.21.E27 Complex.sin_two_mul "partial: first equality sin 2z = 2 sin z cos z"
dlmf_upstream 4.21.E28 Complex.cos_two_mul "partial: first equality cos 2z = 2cos²z - 1"
dlmf_upstream 4.21.E28 Complex.cos_two_mul' "partial: third equality cos 2z = cos²z - sin²z"
dlmf_upstream 4.21.E30 Complex.sin_three_mul "exact"
dlmf_upstream 4.21.E31 Complex.cos_three_mul "exact"
dlmf_upstream 4.21.E34 Complex.cos_add_sin_mul_I_pow "special case: n ∈ ℕ (DLMF: n ∈ ℤ)"
dlmf_upstream 4.21.E37 Complex.sin_eq "exact: x = Re z, y = Im z"
dlmf_upstream 4.21.E38 Complex.cos_eq "exact: x = Re z, y = Im z"

dlmf_upstream 4.35.E1 Complex.sinh_add "partial: upper sign"
dlmf_upstream 4.35.E1 Complex.sinh_sub "partial: lower sign"
dlmf_upstream 4.35.E2 Complex.cosh_add "partial: upper sign"
dlmf_upstream 4.35.E2 Complex.cosh_sub "partial: lower sign"
dlmf_upstream 4.35.E23 Complex.sinh_neg "exact"
dlmf_upstream 4.35.E24 Complex.cosh_neg "exact"
dlmf_upstream 4.35.E25 Complex.tanh_neg "exact"
dlmf_upstream 4.35.E29 Complex.sinh_three_mul "exact"
dlmf_upstream 4.35.E30 Complex.cosh_three_mul "exact"

/-! ### Chapter 24: Bernoulli numbers and polynomials -/

dlmf_upstream 24.2.E2 bernoulli_eq_zero_of_odd "partial: first relation B_{2n+1} = 0, n ≥ 1"
dlmf_upstream 24.2.E3 Polynomial.bernoulli_generating_function
  "different convention: identity of formal power series over a ℚ-algebra, \
  (Σ B_n(t) Xⁿ/n!)(e^X - 1) = X e^{tX}; no convergence statement for |t| < 2π"
dlmf_upstream 24.2.E4 Polynomial.bernoulli_eval_zero "exact"
dlmf_upstream 24.2.E5 Polynomial.bernoulli "exact: definition, in ℚ[X]"
dlmf_upstream 24.4.E1 Polynomial.bernoulli_comp_one_add_X
  "exact: as the polynomial identity B_n(1+X) = B_n(X) + n X^{n-1} in ℚ[X]"
dlmf_upstream 24.4.E3 Polynomial.bernoulli_comp_one_sub_X
  "exact: as the polynomial identity B_n(1-X) = (-1)ⁿ B_n(X) in ℚ[X]"
dlmf_upstream 24.4.E7 Polynomial.sum_range_pow_eq_bernoulli_sub
  "exact: n ≥ 1, as (n+1) Σ_{k=0}^{m} kⁿ = B_{n+1}(m+1) - B_{n+1}; for n = 0 Mathlib's sum \
  includes 0⁰ = 1, while the printed sum from k = 1 is off by one"
dlmf_upstream 24.4.E18 bernoulliFun_mul "exact: real x, m ≥ 1"
dlmf_upstream 24.4.E25 Polynomial.bernoulli_eval_zero "partial: B_n(0) = B_n"
dlmf_upstream 24.4.E25 Polynomial.bernoulli_eval_one
  "different convention: B_n(1) = bernoulli' n, Mathlib's B'_n = (-1)ⁿ B_n"
dlmf_upstream 24.4.E27 bernoulliFun_eval_half "exact: in the form (2/2ⁿ - 1) B_n"
dlmf_upstream 24.4.E34 Polynomial.derivative_bernoulli "exact: as polynomials over ℚ"
dlmf_upstream 24.8.E1 hasSum_one_div_nat_pow_mul_cos
  "exact: n ≥ 1, 0 ≤ x ≤ 1, as the sum of the cosine series"
dlmf_upstream 24.8.E2 hasSum_one_div_nat_pow_mul_sin
  "special case: n ≥ 1, 0 ≤ x ≤ 1 (DLMF also allows n = 0 for 0 < x < 1)"
dlmf_upstream 24.8.E3 hasSum_one_div_pow_mul_fourier_mul_bernoulliFun
  "special case: n ≥ 2, 0 ≤ x ≤ 1 (DLMF also allows n = 1 for 0 < x < 1); the k = 0 term is \
  Mathlib's 1/0 = 0"
dlmf_upstream 24.13.E1 antideriv_bernoulliFun "exact: real t, as HasDerivAt of B_{n+1}(t)/(n+1)"
dlmf_upstream 24.13.E2 integral_bernoulliFun_eq_zero "special case: x = 0, n ≥ 1"

/-! ### Chapter 25: Riemann and Hurwitz zeta functions -/

dlmf_upstream 25.2.E1 zeta_eq_tsum_one_div_nat_cpow
  "exact: Re s > 1 (the n = 0 term is Mathlib's 0^s = 0)"
dlmf_upstream 25.2.i riemannZeta_residue_one "partial: the simple pole at s = 1 has residue 1"
dlmf_upstream 25.2.i differentiableAt_riemannZeta
  "partial: ζ is holomorphic on ℂ \\ {1}; Mathlib's value at s = 1 is totalized"
dlmf_upstream 25.2.E4 tendsto_riemannZeta_sub_one_div
  "partial: constant term γ₀ = γ of the Laurent expansion at s = 1"
dlmf_upstream 25.2.E11 riemannZeta_eulerProduct_tprod "exact: Re s > 1"
dlmf_upstream 25.4.E1 riemannZeta_one_sub
  "exact: s ∉ {1, 0, -1, -2, …}, where every factor is defined"
dlmf_upstream 25.4.E3 completedRiemannZeta_one_sub
  "different convention: Λ(s) = π^{-s/2} Γ(s/2) ζ(s), without the factor s(s-1)/2 of ξ(s)"
dlmf_upstream 25.6.E1 riemannZeta_zero "partial: ζ(0) = -1/2"
dlmf_upstream 25.6.E1 riemannZeta_two "partial: ζ(2) = π²/6"
dlmf_upstream 25.6.E2 riemannZeta_two_mul_nat
  "exact: n ≥ 1, with (-1)^{n+1} B_{2n} in place of |B_{2n}| (equal by 24.2.2)"
dlmf_upstream 25.6.E3 riemannZeta_neg_nat_eq_bernoulli
  "stronger: ζ(-n) = (-1)ⁿ B_{n+1}/(n+1), valid also for n = 0"
dlmf_upstream 25.11.E1 HurwitzZeta.hasSum_hurwitzZeta_of_one_lt_re
  "special case: real 0 ≤ a ≤ 1, Re s > 1; Mathlib's a lives in ℝ/ℤ and the a = 0 series \
  (n = 0 term 0^{-s} = 0) is ζ(s, 1)"
dlmf_upstream 25.11.E2 HurwitzZeta.hurwitzZeta_zero
  "different convention: Mathlib's parameter is a mod 1, so a = 1 is hurwitzZeta 0"
