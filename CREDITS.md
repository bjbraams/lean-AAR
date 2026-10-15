# Credits and related upstream work

The project formalizes material from Andrews, Askey and Roy, *Special Functions*
(1999), and the NIST Digital Library of Mathematical Functions, using Mathlib.
Existing module copyright and authorship notices remain authoritative.

## `ToMathlib` layer (2026-10-15)

`ToMathlib/Analysis/Integral/Laplace.lean` is an unmodified copy of the module of the same
path in the companion project `lean-codes`. The Euler polynomials build on the Mathlib
contributors' `Polynomial.bernoulli` API and follow its recursive style; Euler–Maclaurin uses
`bernoulliFun` and its derivative from `Mathlib.NumberTheory.ZetaValues`, and both summation
formulas use Mathlib's interval integration by parts. Watson's lemma uses the Gamma integral
`Real.integral_rpow_mul_exp_neg_mul_Ioi` and `isLittleO_rpow_exp_pos_mul_atTop`. The proof
routes follow Temme, *Special Functions*, §§1.1–1.2 and Theorem 2.4.

## Gamma pass from Temme (2026-10-15)

The proof routes for the Binet formulas, Prym's and the Cauchy–Saalschütz
representations, and Stirling's series with remainder follow N. M. Temme,
*Special Functions: An Introduction to the Classical Functions of Mathematical
Physics* (Wiley, 1996), §§3.2, 3.4 and 3.6. The `coth` partial fractions use the
Mathlib contributors' `cot_series_rep'` in
`Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent`; the zeta values use
`hasSum_zeta_nat` in `Mathlib.NumberTheory.ZetaValues`; Stirling's constant uses the
project's `tendsto_Gamma_nat_div_stirlingGamma`, built on Mathlib's `Stirling`.
No upstream theorem is admitted or copied.

## Legendre and Chebyshev pass from Temme (2026-10-15)

The proof routes follow Temme, *Special Functions*, §§6.8–6.9. The Chebyshev convergence theorem
uses Mathlib's `has_pointwise_sum_fourier_series_of_summable` and `fourierCoeff_eq_intervalIntegral`
(`Mathlib.Analysis.Fourier.AddCircle`), the Chebyshev measure and
`integral_measureT_eq_integral_cos` (`Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev`),
and the coefficient decay uses `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`. The
Laplace–Heine formula uses `integral_gaussian_complex_Ioi` and
`Complex.tendsto_one_add_pow_exp_of_tendsto`. Example 6.3 uses the project's
`chebyshevT_generating_function`.

## Confluent pass from Temme (2026-10-15)

The proof routes for the asymptotic expansions of the confluent functions and their special
cases follow N. M. Temme, *Special Functions* (Wiley, 1996), §§7.1–7.3. The binomial series
uses Mathlib's `Complex.one_add_cpow_hasFPowerSeriesAt_zero` and
`HasFPowerSeriesAt.isBigO_sub_partialSum_pow`. The regularized contiguous relations are the
project's existing ones in `AAR.Confluent.Continuation`. The incomplete Gamma bridge reuses
TauCeti's `TauCeti.ofReal_lowerIncompleteGamma_eq_partialGamma`
(`TauCeti.Analysis.SpecialFunctions.IncompleteGamma`), and `Si(x) → π/2` is TauCeti's
`TauCeti.Contour.tendsto_integral_sinc_atTop`
(`TauCeti.Analysis.Contour.WorkedExamples.HalfDisc.SineIntegral`). Euler's constant enters
`E₁` through the project's `AAR.Gamma.eulerMascheroni_eq_integral_inv_one_add`.

## Further local proofs (2026-10-08)

The Whittaker M denominator-pole limit and the `q`-Gegenbauer classical limit
reuse the project's proved regularized Kummer continuity/pole formulas and finite
`q`-Pochhammer and Gegenbauer coefficient identities. The two Laguerre fractional
integrals reuse its Kummer parameter integral, Laguerre addition, and moments.
Their adapters use the Mathlib contributors' Gamma/Pochhammer relation in
`Mathlib.Analysis.SpecialFunctions.Gamma.Basic`, affine interval substitution,
and measure-preserving translation. No new upstream theorem is admitted or copied;
the compiled axiom audit verifies all four proofs and their two supporting lemmas.

## Next priority proofs (2026-10-08)

The Rodrigues proofs reuse the project's weighted Jacobi and Laguerre derivative
identities and the Mathlib contributors' iterated derivative and scalar-restriction
APIs in `Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas`. Legendre norms reuse local
Jacobi orthogonality and Legendre recurrence. The unweighted Laguerre convolution
uses local Laguerre derivative identities and Mathlib's interval integration by parts.
The Jacobi fractional integral reuses the proved regularized Gauss fractional integral;
the power moment helper scales Mathlib's Beta integral.

The regularized Kummer Laplace self-transform uses Mathlib's
`hasSum_integral_of_summable_integral_norm`, the project's regularized Gauss
summability and binomial series, and its proved complex Gamma moments. The closed
Whittaker M transform reuses that self-transform with Mathlib's principal-logarithm
API. Tricomi kernel convergence uses Mathlib's Gamma integrability and a finite
binomial majorant; its shifted-parameter case reuses local Kummer transformation and
Gamma moments. The compiled audit checks all seven completed admissions and five
supporting lemmas without admitted dependencies.

## Open priority continuation (2026-10-08)

The weighted Laguerre convolution uses the Mathlib contributors' Beta integral,
Gamma/Pochhammer relation, polynomial coefficient formulas for `(X + 1)^n`, and
additive-homomorphism finite-sum API. Jacobi norms use the project's weighted
Jacobi derivative with Mathlib's endpoint power continuity and interval FTC;
Gegenbauer orthogonality then uses the proved symmetric Jacobi family and
Mathlib's Gamma duplication formula. The underlying upstream modules are
`Mathlib.Analysis.SpecialFunctions.Gamma.Beta`,
`Mathlib.Algebra.Polynomial.Coeff`, `Mathlib.Algebra.Polynomial.Monic`, and
`Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.

The general Kummer transform in its absolute series region uses Mathlib's
summable-integral-norm exchange and the project's regularized Gauss summability,
cut-plane comparison, and complex Gamma moments. The finite shifted Tricomi
Laplace family uses the project's proved shifted Tricomi sum with Mathlib's
binomial expansion and Gamma integrability. The existing Kummer self-transform
and Tricomi shift-one proofs now specialize these broader lemmas. No new upstream
admission is used; the compiled audit checks all three closed admissions, their
supporting lemmas, and the refactored special cases.

## Full half-plane Kummer transform (2026-10-08)

The Kummer ray bound uses the Mathlib contributors' reciprocal Gamma recurrence
in `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`, interval-integral norm bounds,
and FTC. Parameter lowering extends the project's proved Euler representation
to arbitrary complex parameters. Finite Gamma majorants justify holomorphic
Laplace dependence using `hasDerivAt_integral_of_dominated_loc_of_deriv_le` from
`Mathlib.Analysis.Calculus.ParametricIntegral`. Analytic uniqueness extends the
project's series-region transform to the full half-plane, retaining the Gauss
cut-plane continuation and singular denominator parameters.

Tricomi integral parameter continuity uses Mathlib's `continuousAt_of_dominated`
from `Mathlib.MeasureTheory.Integral.Bochner.Basic`, the proved kernel
integrability, and the project's continued `U` parameter continuity. This also
provides a proved reduction of the general representation to noninteger second
parameters; that initial identification remains open. The compiled audit checks
the completed Kummer transform and all eight new public supporting proofs without
any dependency on admitted results. No new TauCeti result is adopted in this pass.

## Tricomi and Whittaker Laplace representations (2026-10-08)

The Gauss confluence proof uses the Mathlib contributors' dominated convergence
theorem for series. Tricomi's integral limit uses their real Bernoulli inequality
from `Mathlib.Analysis.Convex.SpecificFunctions.Basic`, complex exponential
approximation, and dominated convergence for integrals. Its majorant is integrable
by the **Tau Ceti contributors'**
`integrableOn_rpow_mul_one_add_rpow` in
[TauCeti.Analysis.SpecialFunctions.Beta](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean).
The affected module header and point of use also credit this reuse.

The connection limit reuses the project's proved Gauss connection formula and
Gamma-ratio asymptotic. Mathlib's dominated differentiation and analytic
uniqueness extend the argument region; the project's proved parameter continuity
then supplies integer second parameters. Whittaker W uses Mathlib's affine
integral substitution and principal complex powers. The compiled axiom audit
checks both completed representations, the public supporting lemmas, the shifted
special cases, and the Gauss, Gamma, and TauCeti foundations without admitted
dependencies.

## Tricomi Mellin transform (2026-10-08)

The proof reuses the project's proved Tricomi Laplace representation and complex
Gamma and Beta integrals. Absolute convergence uses the Mathlib contributors'
`Real.integral_rpow_mul_exp_neg_mul_Ioi` and Gamma integrability, together with
the **Tau Ceti contributors'** `integrableOn_rpow_mul_one_add_rpow` from
[TauCeti.Analysis.SpecialFunctions.Beta](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean).
Mathlib's `integrable_prod_iff'` and `integral_integral_swap` in
`Mathlib.MeasureTheory.Integral.Prod` justify the integral exchange. The affected
module header and helper docstring credit the reuse. The compiled axiom audit
checks the transform, its new absolute-integrability theorem, and all three
special-function integral foundations without admitted dependencies.

## TauCeti

TauCeti is available as a dependency at revision
`a780c7ad6beb23f60a17351a492d177878020ad5`. The source headers of the modules below
credit **The Tau Ceti contributors**, under the Apache 2.0 license.

The [reuse review and implementation](TauCetiReview.md) records six adopted uses.
Three existing proofs now call TauCeti, new bridges connect the real restrictions
of the complex error functions, and three admissions (two Hermite Fourier
identities and compact-support Parseval) have been replaced by checked proofs.
The affected module headers also credit the imported work.

- [Hermite orthogonality](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Orthogonality.lean):
  `integral_hermite_mul_hermite_mul_gaussian`, now used for AAR's
  probabilists’ Hermite orthogonality proof.
- [Polynomial Gaussian integrability](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Probability/Distributions/Gaussian/PolynomialMemLp.lean):
  `integrable_eval_mul_exp_neg_sq`, now used for the matching AAR helper.
- [Beta integrals](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Beta.lean):
  `integral_rpow_mul_one_sub_rpow`, now used for AAR's real beta integral.
- [Error function](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Erf.lean):
  the real `erf` and `erfc` APIs, identified with AAR's complex functions on real inputs.
- [Hermite Fourier transform](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/SpecialFunctions/Hermite/Function/Fourier/Basic.lean):
  `fourier_twoPiHermiteFunction` supplies the upstream eigenfunction theorem for
  the now-proved `hermitePhys_fourier_eigenfunction` and `hermite_fourier_eigenfunction`.
  Local adapters account for the Fourier phase, dilation and polynomial normalization.
- [Polynomial completeness](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/PolynomialCompleteness.lean)
  and [weighted orthogonal bases](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/Analysis/InnerProductSpace/WeightedOrthogonalBasis.lean):
  the completeness and basis construction used to prove
  `orthogonal_polynomials_parseval` and `compact_support_L2_expansion`, followed
  by Mathlib’s Hilbert-basis Parseval and expansion identities.

- [Hermite parity](https://github.com/TauCetiProject/TauCeti/blob/a780c7ad6beb23f60a17351a492d177878020ad5/TauCeti/RingTheory/Polynomial/Hermite/Derivative.lean):
  `Polynomial.hermite_aeval_neg`, and the Gaussian integrability
  `integrable_aeval_mul_gaussian` from the Hermite orthogonality module above. Both are
  used for the now-proved `hermite_even_cosine_transform` and `hermite_odd_sine_transform`
  in [Integrals.lean](AAR/OrthogonalPolynomials/Integrals.lean). The product cosine
  and sine transforms reuse these single-polynomial transforms and Gaussian
  integrability. The Hermite convolution uses the polynomial Gaussian integrability
  adaptation listed above.

Related real incomplete-gamma, Dirichlet and multivariate-Gamma developments are
not replacements for AAR's general complex statements. Adoption should retain
attribution in the affected module headers and at the point of use.
