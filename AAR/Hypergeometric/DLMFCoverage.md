# DLMF Chapter 15 acquisition inventory

Reviewed against the live [NIST DLMF Chapter 15](https://dlmf.nist.gov/15) on
2026-09-16 and the project's local Mathlib **v4.34.0** sources. The project has since moved to Mathlib v4.35.0-rc2; this inventory was not re-reviewed against it.
This inventory covers every numbered equation in the requested sections
15.2, 15.4, 15.5, 15.6, 15.7, 15.8, 15.10, 15.11, and 15.12.
The other sections were not acquired.

Of the 169 numbered equations, 143 now have tagged project declarations (including
definitions and specializations). Three further entries use existing Mathlib
definitions/results, one is a deferred sector-boundary definition, and 22 require
additional continuation, contour, or special-function infrastructure.

## What was added

**125 new theorem statements and 24 supporting definitions in 11 modules.**
The acquisition initially proved two elementary Riemann-equation identities and
admitted 123 statements. A subsequent proof pass proved 15 more statements, so
**108 acquired statements remain admitted**. Together with the project's earlier
46 admissions, there are now **154 proof obligations**, **116** in this chapter.
See [the proof progress report](../../PROOF_PROGRESS_HYPERGEOMETRIC_2026-09-16.md).
Every acquired mathematical result carries Mathlib's `@[dlmf ...]` cross-reference
attribute. Existing results were tagged instead of copied. Statements/definitions
already supplied by Mathlib are identified in comments and below, without duplicate
project declarations. Multiple DLMF equations sometimes specialize the same theorem.

## Interpretation and domain restrictions

Mathlib's `ordinaryHypergeometric` and `regularizedGaussHGFun` are **series sums**,
not the globally analytically continued DLMF functions. In particular, a divergent
series is totalized, and a conditionally convergent ordered series is not an
unconditionally summable family. Consequently:

- Nonterminating arguments, including transformed arguments, lie in their series
  disks, except where absolute convergence at the boundary is explicitly assumed.
- Conditional convergence uses limits of finite sums in their natural order.
  This matters particularly for 15.4.E27 at −1.
- Ordinary denominator parameters and numerator Gamma factors avoid their poles.
  Regularized formulas retain singular denominator parameters where appropriate.
- Complex powers use principal branches. Slit-plane and upper-half-plane
  hypotheses specify branches when derivatives or connection phases need them.
- Some formulas are acquired on convenient real subdomains: trigonometric
  evaluations, continued fractions, Barnes integrals, cubic connections, and
  asymptotics. These are explicitly restricted forms of the source statements.
- The quotient formulas 15.4.E2, E5, E9, E10, E15, E16 are multiplied through by
  elementary denominators to include removable points. Their values at vanishing
  denominators are not asserted by dividing by zero.
- 15.2.E5 and E6 have distinct parameter-limit interpretations; both are recorded.
  The diagonal limit is not silently identified with the terminating polynomial.
- Riemann's P-symbol denotes a solution space. `riemannSolutions` implements that
  interpretation; the Möbius covariance theorem currently treats finite triples
  whose images remain finite. The reduction to the normalized equation is also
  recorded. A full classification of regular singularities on the Riemann sphere
  requires further definitions.

“Deferred” below means that the equation was reviewed but no formal theorem was
introduced because the required function/branch/continuation API is absent.
These are future coverage gaps, not claims that the DLMF equations are false.
No AAR source statement was changed and no new source error is asserted here.

## Mathlib coverage beyond the numbered series definitions

In `Mathlib/Analysis/SpecialFunctions/OrdinaryHypergeometric.lean`:

- `ordinaryHypergeometric_zero` gives the value at zero.
- `ordinaryHypergeometricSeries_symm` gives numerator symmetry.
- `ordinaryHypergeometricSeries_radius_eq_one` gives the nonterminating radius.
- `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂` give terminating radii.
  Mathlib also has `ordinaryHypergeometric_radius_top_of_neg_nat₃` for its
  totalized negative-denominator series; that last convention is not an assertion
  about the unrestricted DLMF continuation at a denominator pole.

In `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean`:

- `regularizedGaussHGFun_symm` gives numerator symmetry.
- The coefficient, normalization, and radius results are reused.

The boundary-convergence results and entire parameter dependence in unnumbered
15.2(i)–(ii) have project declarations in `Basic` and `AnalyticProperties`.
The continued fractions use Mathlib's `GenContFract` and `convs`; the Bessel
asymptotic uses our existing `besselI` and Mathlib's `Real.arcosh`.

## Equation-by-equation index

Names introduced by this acquisition live in `AAR.Hypergeometric`.
Existing names generally live in the root namespace. “New” includes admitted
theorems and the supporting function definitions, as distinguished in the source.

### [§15.2](https://dlmf.nist.gov/15.2)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.2.E1](https://dlmf.nist.gov/15.2.E1) | Mathlib: `ordinaryHypergeometric_eq_tsum`, with coefficients `ordinaryHypergeometricSeries_apply_eq`. The Gamma form follows from the existing Gamma/Pochhammer identities. |
| [15.2.E2](https://dlmf.nist.gov/15.2.E2) | Mathlib: `regularizedGaussHGFun`, `coeff_regularizedGaussHGFunSeries`, `ordinaryHypergeometric_div_Gamma_eq`. |
| [15.2.E3](https://dlmf.nist.gov/15.2.E3) | Deferred: boundary values on both sides of the cut require an analytically continued function and one-sided boundary-value definitions. |
| [15.2.E3_5](https://dlmf.nist.gov/15.2.E3_5) | New: [`regularized_at_neg_nat`](AnalyticProperties.lean); New: [`tendsto_regularized_at_neg_nat`](AnalyticProperties.lean) |
| [15.2.E4](https://dlmf.nist.gov/15.2.E4) | Existing: [`ordinaryHypergeometric_eq_sum_neg_nat`](Basic.lean) |
| [15.2.E5](https://dlmf.nist.gov/15.2.E5) | New: [`terminating_iterated_parameter_limit`](AnalyticProperties.lean) |
| [15.2.E6](https://dlmf.nist.gov/15.2.E6) | New: [`diagonal_parameter_limit`](AnalyticProperties.lean) |

### [§15.4](https://dlmf.nist.gov/15.4)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.4.E1](https://dlmf.nist.gov/15.4.E1) | Existing: [`log_one_add_eq_ordinaryHypergeometric`](Basic.lean) |
| [15.4.E2](https://dlmf.nist.gov/15.4.E2) | Proved: [`log_ratio`](Elementary.lean) |
| [15.4.E3](https://dlmf.nist.gov/15.4.E3) | Existing: [`arctan_eq_ordinaryHypergeometric`](Basic.lean) |
| [15.4.E4](https://dlmf.nist.gov/15.4.E4) | Existing: [`arcsin_eq_ordinaryHypergeometric`](DiffEq.lean) |
| [15.4.E5](https://dlmf.nist.gov/15.4.E5) | New: [`log_add_sqrt`](Elementary.lean) |
| [15.4.E6](https://dlmf.nist.gov/15.4.E6) | Existing: [`ordinaryHypergeometric_eq_one_sub_neg_cpow`](Basic.lean) |
| [15.4.E7](https://dlmf.nist.gov/15.4.E7) | New: [`even_binomial`](Elementary.lean) |
| [15.4.E8](https://dlmf.nist.gov/15.4.E8) | New: [`tan_cos`](Elementary.lean) |
| [15.4.E9](https://dlmf.nist.gov/15.4.E9) | New: [`odd_binomial`](Elementary.lean) |
| [15.4.E10](https://dlmf.nist.gov/15.4.E10) | New: [`tan_sin`](Elementary.lean) |
| [15.4.E11](https://dlmf.nist.gov/15.4.E11) | New: [`opposite_parameters_sqrt`](Elementary.lean) |
| [15.4.E12](https://dlmf.nist.gov/15.4.E12) | New: [`sin_sq_cos`](Elementary.lean) |
| [15.4.E13](https://dlmf.nist.gov/15.4.E13) | New: [`complementary_parameters_sqrt`](Elementary.lean) |
| [15.4.E14](https://dlmf.nist.gov/15.4.E14) | New: [`sin_sq_cos_quotient`](Elementary.lean) |
| [15.4.E15](https://dlmf.nist.gov/15.4.E15) | New: [`complementary_parameters_odd_sqrt`](Elementary.lean) |
| [15.4.E16](https://dlmf.nist.gov/15.4.E16) | New: [`sin_sq_sin`](Elementary.lean) |
| [15.4.E17](https://dlmf.nist.gov/15.4.E17) | New: [`quadratic_binomial`](Elementary.lean) |
| [15.4.E18](https://dlmf.nist.gov/15.4.E18) | New: [`quadratic_binomial_derivative`](Elementary.lean) |
| [15.4.E19](https://dlmf.nist.gov/15.4.E19) | Proved: [`successor_binomial`](Elementary.lean) |
| [15.4.E20](https://dlmf.nist.gov/15.4.E20) | Existing: [`gauss_summation`](EulerIntegral.lean) |
| [15.4.E21](https://dlmf.nist.gov/15.4.E21) | New: [`zero_balanced_limit`](AnalyticProperties.lean) |
| [15.4.E22](https://dlmf.nist.gov/15.4.E22) | New: [`imaginary_excess_limit`](AnalyticProperties.lean) |
| [15.4.E23](https://dlmf.nist.gov/15.4.E23) | Existing: [`tendsto_ordinaryHypergeometric_nhdsWithin_one`](Basic.lean) |
| [15.4.E24](https://dlmf.nist.gov/15.4.E24) | Existing: [`chu_vandermonde`](EulerIntegral.lean) |
| [15.4.E25](https://dlmf.nist.gov/15.4.E25) | Existing: [`dougall_bilateral`](Identities.lean) |
| [15.4.E26](https://dlmf.nist.gov/15.4.E26) | Existing: [`kummer_theorem`](Identities.lean) |
| [15.4.E27](https://dlmf.nist.gov/15.4.E27) | New: [`half_argument_digamma`](Elementary.lean); New: [`alternating_digamma`](Elementary.lean) |
| [15.4.E28](https://dlmf.nist.gov/15.4.E28) | New: [`gauss_second_summation`](Elementary.lean) |
| [15.4.E29](https://dlmf.nist.gov/15.4.E29) | New: [`gauss_second_summation_contiguous`](Elementary.lean) |
| [15.4.E30](https://dlmf.nist.gov/15.4.E30) | New: [`bailey_summation`](Elementary.lean) |
| [15.4.E31](https://dlmf.nist.gov/15.4.E31) | New: [`value_neg_one_third`](Elementary.lean) |
| [15.4.E32](https://dlmf.nist.gov/15.4.E32) | New: [`value_one_ninth`](Elementary.lean) |
| [15.4.E33](https://dlmf.nist.gov/15.4.E33) | New: [`value_sixth_root`](Elementary.lean) |
| [15.4.E34](https://dlmf.nist.gov/15.4.E34) | New: [`value_sixth_root_contiguous`](Elementary.lean) |

### [§15.5](https://dlmf.nist.gov/15.5)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.5.E1](https://dlmf.nist.gov/15.5.E1) | Existing: [`hasDerivAt_ordinaryHypergeometric`](DiffEq.lean); Existing: [`deriv_ordinaryHypergeometric`](DiffEq.lean) |
| [15.5.E2](https://dlmf.nist.gov/15.5.E2) | Proved: [`iteratedDeriv_hypergeometric`](Derivatives.lean) |
| [15.5.E3](https://dlmf.nist.gov/15.5.E3) | Proved: [`iterate_mulDerivMul`](Derivatives.lean) |
| [15.5.E4](https://dlmf.nist.gov/15.5.E4) | Proved: [`iteratedDeriv_mul_cpow`](Derivatives.lean) |
| [15.5.E5](https://dlmf.nist.gov/15.5.E5) | New: [`iterate_mulDerivMul_euler`](Derivatives.lean) |
| [15.5.E6](https://dlmf.nist.gov/15.5.E6) | New: [`iteratedDeriv_euler`](Derivatives.lean) |
| [15.5.E7](https://dlmf.nist.gov/15.5.E7) | New: [`iterate_oneSubMulDerivMul`](Derivatives.lean) |
| [15.5.E8](https://dlmf.nist.gov/15.5.E8) | New: [`iterate_oneSubMulDerivMul_cpow`](Derivatives.lean) |
| [15.5.E9](https://dlmf.nist.gov/15.5.E9) | New: [`iteratedDeriv_two_cpow`](Derivatives.lean) |
| [15.5.E10](https://dlmf.nist.gov/15.5.E10) | New: [`iterate_mulDerivMul_eq`](Derivatives.lean) |
| [15.5.E11](https://dlmf.nist.gov/15.5.E11) | Existing: [`contiguous_a`](Contiguous.lean) |
| [15.5.E12](https://dlmf.nist.gov/15.5.E12) | Proved: [`contiguous_ab`](Derivatives.lean) |
| [15.5.E13](https://dlmf.nist.gov/15.5.E13) | Proved: [`contiguous_a_b_pred`](Derivatives.lean) |
| [15.5.E14](https://dlmf.nist.gov/15.5.E14) | Proved: [`contiguous_a_c_succ`](Derivatives.lean) |
| [15.5.E15](https://dlmf.nist.gov/15.5.E15) | Proved: [`contiguous_a_succ_c_pred`](Derivatives.lean) |
| [15.5.E16](https://dlmf.nist.gov/15.5.E16) | Proved: [`contiguous_a_pred_c_succ`](Derivatives.lean) |
| [15.5.E16_5](https://dlmf.nist.gov/15.5.E16_5) | Existing: [`contiguous_shift_b`](Contiguous.lean) |
| [15.5.E17](https://dlmf.nist.gov/15.5.E17) | Proved: [`contiguous_a_pred_c_pred`](Derivatives.lean) |
| [15.5.E18](https://dlmf.nist.gov/15.5.E18) | Proved: [`contiguous_c_three`](Derivatives.lean) |
| [15.5.E19](https://dlmf.nist.gov/15.5.E19) | Proved: [`contiguous_diagonal`](Derivatives.lean) |
| [15.5.E20](https://dlmf.nist.gov/15.5.E20) | Existing: [`ordinaryHypergeometric_mul_one_sub_mul_deriv_eq`](Contiguous.lean) |
| [15.5.E21](https://dlmf.nist.gov/15.5.E21) | Proved: [`deriv_contiguous_c_succ`](Derivatives.lean) |

### [§15.6](https://dlmf.nist.gov/15.6)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.6.E1](https://dlmf.nist.gov/15.6.E1) | Existing: [`ordinaryHypergeometric_eq_integral`](EulerIntegral.lean) |
| [15.6.E2](https://dlmf.nist.gov/15.6.E2) | Deferred: a loop/Pochhammer contour with continuously lifted logarithms is needed. Integrating principal powers around an ordinary closed path would give a different formula. |
| [15.6.E2_5](https://dlmf.nist.gov/15.6.E2_5) | New: [`integral_Ioi`](IntegralRepresentations.lean) |
| [15.6.E3](https://dlmf.nist.gov/15.6.E3) | Deferred: a loop/Pochhammer contour with continuously lifted logarithms is needed. Integrating principal powers around an ordinary closed path would give a different formula. |
| [15.6.E4](https://dlmf.nist.gov/15.6.E4) | Deferred: a loop/Pochhammer contour with continuously lifted logarithms is needed. Integrating principal powers around an ordinary closed path would give a different formula. |
| [15.6.E5](https://dlmf.nist.gov/15.6.E5) | Deferred: a loop/Pochhammer contour with continuously lifted logarithms is needed. Integrating principal powers around an ordinary closed path would give a different formula. |
| [15.6.E6](https://dlmf.nist.gov/15.6.E6) | New: [`barnes_integral`](IntegralRepresentations.lean) |
| [15.6.E7](https://dlmf.nist.gov/15.6.E7) | New: [`barnes_integral_one_sub`](IntegralRepresentations.lean) |
| [15.6.E8](https://dlmf.nist.gov/15.6.E8) | New: [`fractional_integral`](IntegralRepresentations.lean) |
| [15.6.E9](https://dlmf.nist.gov/15.6.E9) | New: [`product_integral`](IntegralRepresentations.lean) |

### [§15.7](https://dlmf.nist.gov/15.7)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.7.E1](https://dlmf.nist.gov/15.7.E1) | New: [`gauss_continued_fraction_limit`](ContinuedFractions.lean) |
| [15.7.E2](https://dlmf.nist.gov/15.7.E2) | New: [`gaussContinuedFraction`](ContinuedFractions.lean) |
| [15.7.E3](https://dlmf.nist.gov/15.7.E3) | New: [`contiguous_continued_fraction_limit`](ContinuedFractions.lean) |
| [15.7.E4](https://dlmf.nist.gov/15.7.E4) | New: [`contiguousContinuedFraction`](ContinuedFractions.lean) |
| [15.7.E5](https://dlmf.nist.gov/15.7.E5) | New: [`derivative_continued_fraction_limit`](ContinuedFractions.lean) |
| [15.7.E6](https://dlmf.nist.gov/15.7.E6) | New: [`derivativeContinuedFraction`](ContinuedFractions.lean) |

### [§15.8](https://dlmf.nist.gov/15.8)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.8.E1](https://dlmf.nist.gov/15.8.E1) | New: [`regularized_euler`](FurtherTransformations.lean); New: [`regularized_pfaff`](FurtherTransformations.lean); Existing: [`pfaff_transformation`](Transformations.lean); Existing: [`euler_transformation`](Transformations.lean); Existing: [`pfaff_transformation_symm`](Transformations.lean) |
| [15.8.E2](https://dlmf.nist.gov/15.8.E2) | Deferred: the left side requires analytic continuation for `|z| > 1`; the original and reciprocal series disks have no open overlap. E8 additionally prescribes logarithmic limiting values. |
| [15.8.E3](https://dlmf.nist.gov/15.8.E3) | New: [`regularized_connection_one_div_one_sub`](FurtherTransformations.lean) |
| [15.8.E4](https://dlmf.nist.gov/15.8.E4) | New: [`regularized_connection_one_sub`](FurtherTransformations.lean) |
| [15.8.E5](https://dlmf.nist.gov/15.8.E5) | New: [`regularized_connection_one_sub_inv`](FurtherTransformations.lean) |
| [15.8.E6](https://dlmf.nist.gov/15.8.E6) | New: [`terminating_inverse`](FurtherTransformations.lean); New: [`terminating_inverse_one_sub`](FurtherTransformations.lean) |
| [15.8.E7](https://dlmf.nist.gov/15.8.E7) | New: [`terminating_one_sub`](FurtherTransformations.lean); New: [`terminating_one_sub_inv`](FurtherTransformations.lean) |
| [15.8.E8](https://dlmf.nist.gov/15.8.E8) | Deferred: the left side requires analytic continuation for `|z| > 1`; the original and reciprocal series disks have no open overlap. E8 additionally prescribes logarithmic limiting values. |
| [15.8.E9](https://dlmf.nist.gov/15.8.E9) | New: [`logarithmic_connection_one_div_one_sub`](ConnectionFormulas.lean) |
| [15.8.E10](https://dlmf.nist.gov/15.8.E10) | New: [`logarithmic_connection_one_sub`](ConnectionFormulas.lean) |
| [15.8.E11](https://dlmf.nist.gov/15.8.E11) | New: [`logarithmic_connection_one_sub_inv`](ConnectionFormulas.lean) |
| [15.8.E12](https://dlmf.nist.gov/15.8.E12) | General case / specialization: [`regularized_euler`](FurtherTransformations.lean) |
| [15.8.E13](https://dlmf.nist.gov/15.8.E13) | New: [`quadratic_double_denominator`](FurtherTransformations.lean) |
| [15.8.E14](https://dlmf.nist.gov/15.8.E14) | New: [`quadratic_double_denominator_one_sub`](FurtherTransformations.lean) |
| [15.8.E15](https://dlmf.nist.gov/15.8.E15) | New: [`quadratic_well_poised_plus`](FurtherTransformations.lean) |
| [15.8.E16](https://dlmf.nist.gov/15.8.E16) | New: [`quadratic_well_poised_minus`](FurtherTransformations.lean) |
| [15.8.E17](https://dlmf.nist.gov/15.8.E17) | New: [`quadratic_half_sum`](FurtherTransformations.lean) |
| [15.8.E18](https://dlmf.nist.gov/15.8.E18) | Existing: [`kummer_quadratic`](Transformations.lean); Existing: [`gauss_quadratic`](Transformations.lean) |
| [15.8.E19](https://dlmf.nist.gov/15.8.E19) | New: [`quadratic_complementary`](FurtherTransformations.lean) |
| [15.8.E20](https://dlmf.nist.gov/15.8.E20) | New: [`quadratic_complementary_four_mul`](FurtherTransformations.lean) |
| [15.8.E21](https://dlmf.nist.gov/15.8.E21) | New: [`quadratic_sqrt`](FurtherTransformations.lean) |
| [15.8.E22](https://dlmf.nist.gov/15.8.E22) | New: [`quadratic_inverse_sqrt`](FurtherTransformations.lean) |
| [15.8.E23](https://dlmf.nist.gov/15.8.E23) | New: [`quadratic_inverse_sqrt_complementary`](FurtherTransformations.lean) |
| [15.8.E24](https://dlmf.nist.gov/15.8.E24) | New: [`quadratic_connection_well_poised`](ConnectionFormulas.lean) |
| [15.8.E25](https://dlmf.nist.gov/15.8.E25) | New: [`quadratic_connection_half_sum`](ConnectionFormulas.lean) |
| [15.8.E26](https://dlmf.nist.gov/15.8.E26) | New: [`quadratic_connection_complementary`](ConnectionFormulas.lean) |
| [15.8.E27](https://dlmf.nist.gov/15.8.E27) | New: [`quadratic_even_connection`](ConnectionFormulas.lean) |
| [15.8.E28](https://dlmf.nist.gov/15.8.E28) | New: [`quadratic_odd_connection`](ConnectionFormulas.lean) |
| [15.8.E29](https://dlmf.nist.gov/15.8.E29) | General case / specialization: [`quadratic_sqrt`](FurtherTransformations.lean) |
| [15.8.E30](https://dlmf.nist.gov/15.8.E30) | General case / specialization: [`quadratic_double_denominator`](FurtherTransformations.lean); General case / specialization: [`quadratic_well_poised_plus`](FurtherTransformations.lean) |
| [15.8.E31](https://dlmf.nist.gov/15.8.E31) | New: [`cubic_transformation`](FurtherTransformations.lean) |
| [15.8.E32](https://dlmf.nist.gov/15.8.E32) | New: [`cubic_connection`](ConnectionFormulas.lean) |
| [15.8.E33](https://dlmf.nist.gov/15.8.E33) | New: [`ramanujan_cubic`](FurtherTransformations.lean) |

### [§15.10](https://dlmf.nist.gov/15.10)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.10.E1](https://dlmf.nist.gov/15.10.E1) | Existing: [`ordinaryHypergeometric_ode`](DiffEq.lean); New: [`gaussOperator`](Solutions.lean) |
| [15.10.E2](https://dlmf.nist.gov/15.10.E2) | New: [`zeroSecond`](Solutions.lean); New: [`zero_second_ode`](Solutions.lean) |
| [15.10.E3](https://dlmf.nist.gov/15.10.E3) | New: [`zero_wronskian`](Solutions.lean) |
| [15.10.E4](https://dlmf.nist.gov/15.10.E4) | New: [`oneFirst`](Solutions.lean); New: [`oneSecond`](Solutions.lean); Proved: [`one_first_ode`](Solutions.lean); New: [`one_second_ode`](Solutions.lean) |
| [15.10.E5](https://dlmf.nist.gov/15.10.E5) | New: [`one_wronskian`](Solutions.lean) |
| [15.10.E6](https://dlmf.nist.gov/15.10.E6) | New: [`infinityFirst`](Solutions.lean); New: [`infinity_first_ode`](Solutions.lean) |
| [15.10.E7](https://dlmf.nist.gov/15.10.E7) | New: [`infinity_wronskian`](Solutions.lean) |
| [15.10.E8](https://dlmf.nist.gov/15.10.E8) | New: [`logarithmicSecond`](Solutions.lean); New: [`logarithmic_second_fundamental`](Solutions.lean) |
| [15.10.E9](https://dlmf.nist.gov/15.10.E9) | New: [`logarithmicSecondTerminating`](Solutions.lean); New: [`logarithmic_second_terminating_fundamental`](Solutions.lean) |
| [15.10.E10](https://dlmf.nist.gov/15.10.E10) | New: [`logarithmicSecondBothTerminating`](Solutions.lean); New: [`logarithmic_second_both_terminating_fundamental`](Solutions.lean) |
| [15.10.E11](https://dlmf.nist.gov/15.10.E11) | General case / specialization: [`regularized_euler`](FurtherTransformations.lean); General case / specialization: [`regularized_pfaff`](FurtherTransformations.lean); General case / specialization: [`euler_transformation`](Transformations.lean); General case / specialization: [`pfaff_transformation`](Transformations.lean); General case / specialization: [`pfaff_transformation_symm`](Transformations.lean) |
| [15.10.E12](https://dlmf.nist.gov/15.10.E12) | New: [`zero_second_representations`](Kummer.lean) |
| [15.10.E13](https://dlmf.nist.gov/15.10.E13) | New: [`one_first_representations`](Kummer.lean) |
| [15.10.E14](https://dlmf.nist.gov/15.10.E14) | New: [`one_second_representations`](Kummer.lean) |
| [15.10.E15](https://dlmf.nist.gov/15.10.E15) | New: [`kummerFive`](Kummer.lean); New: [`kummerFiveLeft`](Kummer.lean); New: [`kummer_five_representations`](Kummer.lean) |
| [15.10.E16](https://dlmf.nist.gov/15.10.E16) | New: [`kummerSix`](Kummer.lean); New: [`kummerSixLeft`](Kummer.lean); New: [`kummer_six_representations`](Kummer.lean) |
| [15.10.E17](https://dlmf.nist.gov/15.10.E17) | New: [`one_first_connection_zero`](Solutions.lean) |
| [15.10.E18](https://dlmf.nist.gov/15.10.E18) | New: [`one_second_connection_zero`](Solutions.lean) |
| [15.10.E19](https://dlmf.nist.gov/15.10.E19) | New: [`kummer_five_left_connection_zero`](Kummer.lean) |
| [15.10.E20](https://dlmf.nist.gov/15.10.E20) | New: [`kummer_six_left_connection_zero`](Kummer.lean) |
| [15.10.E21](https://dlmf.nist.gov/15.10.E21) | New: [`zero_first_connection_one`](Solutions.lean) |
| [15.10.E22](https://dlmf.nist.gov/15.10.E22) | New: [`zero_second_connection_one`](Solutions.lean) |
| [15.10.E23](https://dlmf.nist.gov/15.10.E23) | New: [`kummer_five_connection_one`](Kummer.lean) |
| [15.10.E24](https://dlmf.nist.gov/15.10.E24) | New: [`kummer_six_connection_one`](Kummer.lean) |
| [15.10.E25](https://dlmf.nist.gov/15.10.E25) | New: [`zero_first_connection_left`](Kummer.lean) |
| [15.10.E26](https://dlmf.nist.gov/15.10.E26) | New: [`zero_second_connection_left`](Kummer.lean) |
| [15.10.E27](https://dlmf.nist.gov/15.10.E27) | New: [`one_first_connection_infinity`](Kummer.lean) |
| [15.10.E28](https://dlmf.nist.gov/15.10.E28) | New: [`one_second_connection_infinity`](Kummer.lean) |
| [15.10.E29](https://dlmf.nist.gov/15.10.E29) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E30](https://dlmf.nist.gov/15.10.E30) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E31](https://dlmf.nist.gov/15.10.E31) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E32](https://dlmf.nist.gov/15.10.E32) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E33](https://dlmf.nist.gov/15.10.E33) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E34](https://dlmf.nist.gov/15.10.E34) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E35](https://dlmf.nist.gov/15.10.E35) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |
| [15.10.E36](https://dlmf.nist.gov/15.10.E36) | Deferred: this connection mixes all three centers. The local charts used here have no common open domain for all terms; global continuation is required. |

### [§15.11](https://dlmf.nist.gov/15.11)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.11.E1](https://dlmf.nist.gov/15.11.E1) | New: [`riemannOperator`](Riemann.lean) |
| [15.11.E2](https://dlmf.nist.gov/15.11.E2) | New: [`gauss_fuchs_relation`](Riemann.lean) |
| [15.11.E3](https://dlmf.nist.gov/15.11.E3) | New: [`riemannSolutions`](Riemann.lean) |
| [15.11.E4](https://dlmf.nist.gov/15.11.E4) | New: [`riemannNormalOperator_gauss`](Riemann.lean) |
| [15.11.E5](https://dlmf.nist.gov/15.11.E5) | New: [`riemann_mobius_covariance`](Riemann.lean) |
| [15.11.E6](https://dlmf.nist.gov/15.11.E6) | New: [`riemann_mobius_covariance`](Riemann.lean) |
| [15.11.E7](https://dlmf.nist.gov/15.11.E7) | New: [`riemann_hypergeometric_solution`](Riemann.lean) |
| [15.11.E8](https://dlmf.nist.gov/15.11.E8) | New: [`riemann_gauge_shift`](Riemann.lean) |

### [§15.12](https://dlmf.nist.gov/15.12)

| Equation | Project declaration or disposition |
| --- | --- |
| [15.12.E1](https://dlmf.nist.gov/15.12.E1) | Auxiliary sector-boundary definition. The larger complex-parameter sectors are deferred; the acquired expansions use the positive real direction. |
| [15.12.E2](https://dlmf.nist.gov/15.12.E2) | New: [`large_denominator_expansion`](Asymptotics.lean) |
| [15.12.E3](https://dlmf.nist.gov/15.12.E3) | New: [`large_denominator_shift_expansion`](Asymptotics.lean) |
| [15.12.E4](https://dlmf.nist.gov/15.12.E4) | New: [`largeDenominatorGenerating`](Asymptotics.lean); New: [`largeDenominatorCoeff`](Asymptotics.lean); New: [`large_denominator_generating_hasSum`](Asymptotics.lean) |
| [15.12.E5](https://dlmf.nist.gov/15.12.E5) | New: [`large_opposite_parameters_bessel`](Asymptotics.lean) |
| [15.12.E6](https://dlmf.nist.gov/15.12.E6) | Mathlib: `Real.arcosh`, used directly in `large_opposite_parameters_bessel`; no duplicate definition. |
| [15.12.E7](https://dlmf.nist.gov/15.12.E7) | Deferred: parabolic-cylinder function and the continuously chosen turning-point variable are not yet defined in the project. |
| [15.12.E8](https://dlmf.nist.gov/15.12.E8) | Deferred: parabolic-cylinder function and the continuously chosen turning-point variable are not yet defined in the project. |
| [15.12.E9](https://dlmf.nist.gov/15.12.E9) | Deferred: Airy functions and the continuous turning-point branches/coefficient functions are not yet defined in the project. |
| [15.12.E10](https://dlmf.nist.gov/15.12.E10) | Deferred: Airy functions and the continuous turning-point branches/coefficient functions are not yet defined in the project. |
| [15.12.E11](https://dlmf.nist.gov/15.12.E11) | Deferred: Airy functions and the continuous turning-point branches/coefficient functions are not yet defined in the project. |
| [15.12.E12](https://dlmf.nist.gov/15.12.E12) | Deferred: Airy functions and the continuous turning-point branches/coefficient functions are not yet defined in the project. |
| [15.12.E13](https://dlmf.nist.gov/15.12.E13) | Deferred: Airy functions and the continuous turning-point branches/coefficient functions are not yet defined in the project. |

## Proof and validation status

New proved theorems:

- `AAR.Hypergeometric.gauss_fuchs_relation`.
- `AAR.Hypergeometric.riemannNormalOperator_gauss`.

The subsequent proof pass also proved the following acquired statements:

- `log_ratio`.
- `successor_binomial`.
- `iteratedDeriv_hypergeometric`.
- `iterate_mulDerivMul`.
- `iteratedDeriv_mul_cpow`.
- `contiguous_ab`.
- `contiguous_a_b_pred`.
- `contiguous_a_c_succ`.
- `contiguous_a_succ_c_pred`.
- `contiguous_a_pred_c_succ`.
- `contiguous_a_pred_c_pred`.
- `contiguous_c_three`.
- `contiguous_diagonal`.
- `deriv_contiguous_c_succ`.
- `one_first_ode`.

All other acquired theorem statements remain admitted. The existing derivative identity
`ordinaryHypergeometric_mul_one_sub_mul_deriv_eq` already proves 15.5.E20; it was
tagged and no duplicate theorem was retained.

Validation performed:

- Root `lake build > /tmp/AAR-build.log 2>&1` after every batch of Lean edits;
  the final build passed all 3770 jobs.
- Direct `lake env lean` checks passed for all 16 changed Lean files.
- `git diff --check`, plus independent whitespace checks because these working
  project files are currently untracked by Git.
- Admission inventory and checks that existing theorem statements/proofs were
  preserved apart from added cross-reference attributes.
- Independent numerical transcription checks at 40-digit precision for selected
  Kummer phases/chart overlaps, the cubic connection, all three logarithmic ODE
  solutions, and all three continued fractions. Relative residuals were below
  `2e-38`. These checks are not formal proofs of the admitted statements.

### Remaining admissions by file

| File | Admissions |
| --- | ---: |
| `AAR/Bailey.lean` | 4 |
| `AAR/Bessel/Modified.lean` | 1 |
| `AAR/Bessel/Theorems.lean` | 5 |
| `AAR/Confluent/Basic.lean` | 2 |
| `AAR/Hypergeometric/AnalyticProperties.lean` | 9 |
| `AAR/Hypergeometric/Asymptotics.lean` | 4 |
| `AAR/Hypergeometric/Basic.lean` | 1 |
| `AAR/Hypergeometric/ConnectionFormulas.lean` | 9 |
| `AAR/Hypergeometric/ContinuedFractions.lean` | 3 |
| `AAR/Hypergeometric/Derivatives.lean` | 6 |
| `AAR/Hypergeometric/Elementary.lean` | 22 |
| `AAR/Hypergeometric/EulerIntegral.lean` | 1 |
| `AAR/Hypergeometric/FurtherTransformations.lean` | 21 |
| `AAR/Hypergeometric/Identities.lean` | 4 |
| `AAR/Hypergeometric/IntegralRepresentations.lean` | 5 |
| `AAR/Hypergeometric/Kummer.lean` | 13 |
| `AAR/Hypergeometric/Riemann.lean` | 3 |
| `AAR/Hypergeometric/Solutions.lean` | 13 |
| `AAR/Hypergeometric/Transformations.lean` | 2 |
| `AAR/OrthogonalPolynomials/Classical.lean` | 1 |
| `AAR/OrthogonalPolynomials/General.lean` | 2 |
| `AAR/OrthogonalPolynomials/Topics.lean` | 4 |
| `AAR/Partitions.lean` | 3 |
| `AAR/QSeries/Identities.lean` | 3 |
| `AAR/Selberg/Applications.lean` | 5 |
| `AAR/Selberg/Basic.lean` | 2 |
| `AAR/SphericalHarmonics/Basic.lean` | 1 |
| `AAR/SphericalHarmonics/Theorems.lean` | 5 |
| **Total** | **154** |
