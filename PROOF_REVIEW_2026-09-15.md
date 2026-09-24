# Proof review — 2026-09-15

## Scope and results

Seven focused proof passes have reduced the original 80 explicit `sorry` occurrences to
58. The seventh pass proved the confluence limit and the Bessel–Kummer relation.
Bessel and Confluent remain the first priorities. This is not a complete audit of every
existing proof or source attribution.

### Seventh pass — confluence and the Bessel–Kummer relation

Consulted [AAR Chapter 4](References/AAR1999Chapter04.pdf) using local OCR.
The rescaling and confluence argument appears in §4.1, pp. 188–189 (PDF pages 2–3).
Kummer's second transformation is (4.1.12), p. 191, with proof guidance on p. 192
(PDF pages 5–6); it gives the Bessel representation (4.5.3), p. 200.

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `tendsto_ordinaryHypergeometric_div_atTop` | Separate each rescaled Gauss term into a confluent term and `(b)_n / b^n`. Prove the latter tends to one and decreases for positive real `b`; dominate by a fixed convergent Gauss series and apply Mathlib's Tannery theorem. | No `sorryAx` |
| `besselJ_eq_confluentM` | Prove Kummer's second transformation using the confluent equation and uniqueness of entire solutions with a fixed value at zero. Substitute `2iz` and cancel the exponential and Gamma factors. | No `sorryAx` |

The confluence proof keeps the original unrestricted complex parameters `a, c, z`.
In particular, it covers nonpositive integer `c` under the project's terminating-series
convention. Choosing a natural `B > ‖z‖` supplies a summable majorant for every `b ≥ B`.
This also handles `z = 0` and avoids any dependence on the exceptional initial value `b = 0`.

The new `confluent_ode_iteratedDeriv` and `confluent_ode_unique` establish uniqueness
at the regular singular point directly. Differentiating the equation gives
`(c+n) f^(n+1)(0) = (a+n) f^n(0)`; the existing exclusion of nonpositive integer `c`
makes each coefficient nonzero. Equal derivatives give equal Taylor series, and the
analytic identity theorem extends equality to the complex plane.

The helper `confluentM_eq_exp_mul_regularized0F1` formalizes Kummer's second
transformation itself. The Bessel–Kummer result retains both existing parameter
hypotheses and remains valid for every complex `z`, including zero and the branch cut;
it requires no new restriction on `z`.

Both formerly admitted theorems, Kummer's second transformation, the uniqueness lemma,
and the majorant lemma were audited with `#print axioms`. Only `propext`,
`Classical.choice`, and `Quot.sound` occur. Existing theorem statements and assumptions
were compared against snapshots and are unchanged. No axioms were introduced and no
additional false or suspected-false statement was identified. Audit commands were removed.

### Sixth pass — Bessel equations and recurrences

Consulted [AAR Chapter 4](References/AAR1999Chapter04.pdf), using local OCR:

- §4.5, pp. 199–200 (PDF pages 13–14): the `₀F₁` series solution of Bessel's
  equation, and the construction of `Y` from orders `ν` and `-ν`.
- §4.6, p. 202 (PDF page 16): differentiation identities (4.6.1)–(4.6.2) and
  the resulting order recurrences (4.6.5)–(4.6.6).
- §4.12, pp. 222–223 (PDF pages 36–37): the modified equation, the positive-sign
  series for `I`, and the linear combination defining `K`.

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `besselJ_ode` | Obtain the regularized `₀F₁` equation from its coefficient recurrence, then differentiate the principal-power prefactor and quadratic substitution. | No `sorryAx` |
| `besselY_ode` | Use analyticity and linearity on the two `J` solutions of opposite orders. | No `sorryAx` |
| `besselI_ode` | Specialize the same series calculation to the positive quadratic argument. | No `sorryAx` |
| `besselK_ode` | Use analyticity and linearity on the two `I` solutions of opposite orders. | No `sorryAx` |
| `besselJ_add_sub` | Combine the contiguous relation for regularized `₀F₁` with the principal-power shift identities. | No `sorryAx` |
| `two_deriv_besselJ` | Differentiate the series and use the adjacent-order recurrence. | No `sorryAx` |

The key coefficient identity uses Mathlib's reciprocal Gamma recurrence, which is valid
also at Gamma poles. Consequently the regularized `₀F₁` differential equation,
derivative, and contiguous relation require no exclusions on the parameter. The `J`
and `I` equations cover every complex order. The `Y` and `K` equations retain their
existing noninteger-order hypotheses; the integer-order limits were not needed here.
The algebraic order recurrence retains its full domain `z ≠ 0`, including the branch
cut, while derivative statements retain the slit-plane hypothesis.

New helpers include `hasFPowerSeriesOnBall_regularized0F1`, `regularized0F1_ode`,
`deriv_regularized0F1`, `regularized0F1_contiguous`, `besselSeries_ode`,
`analyticAt_besselJ`, `analyticAt_besselI`, and `hasDerivAt_besselJ`.
The common equation has a sign parameter so the ordinary and modified calculations
share the same proof.

All six theorems and three central helpers were checked with `#print axioms`;
only `propext`, `Classical.choice`, and `Quot.sound` occur. Temporary audit commands
were removed. Existing theorem statements and assumptions were compared against the
pre-edit snapshots and are unchanged. No axioms were introduced, and no additional
false or suspected-false statement was identified. The three Confluent admissions
remain open; no Confluent theorem was changed in this pass.

### Fifth pass — guided by the AAR source

Read [AAR Chapter 5](References/AAR1999Chapter05.pdf), printed pp. 244–246
(PDF pages 5–7), using local OCR because the mathematical pages are scans.
Theorem 5.2.2 and Remark 5.2.1 give the recurrence argument; Theorem 5.2.4 and
Remark 5.2.2 give the normalized and unnormalized Christoffel–Darboux formulas.
The code comments now cite these precise locations, correcting the old §5.6 label
on Christoffel–Darboux.

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `three_term_recurrence` | Follow AAR: expand `X * p (n + 1)` in the degree-ordered basis, then integrate against lower-degree basis polynomials to eliminate their coefficients. | No `sorryAx` |
| `christoffel_darboux` | Implement AAR's cancellation using symmetry of the multiplication coefficients divided by squared norms. The interior double sum cancels; the boundary coefficient is the ratio of leading coefficients. | No `sorryAx` |

The new `IsOrthogonalPolynomials` helpers reuse Mathlib's `Polynomial.Sequence.basis`.
They establish finite expansions with degree bounds, square integrability of every
polynomial, integrability of polynomial products, and the integral formula for basis
coordinates. These results also prepare the remaining quadrature and zeros proofs.

Positive squared norms imply that every basis polynomial is nonzero, including `p 0`;
natural degree zero alone would not suffice. The recurrence includes `n = 0` (an empty
lower-degree sum), and Christoffel–Darboux includes `n = 1`. Leading coefficients and
squared norms are proved nonzero before division. The original assumptions and theorem
statements are unchanged. No new false or suspected-false statement was identified.

The two theorems and four integrability/coordinate helpers were checked with
`#print axioms`; only `propext`, `Classical.choice`, and `Quot.sound` occur.
Temporary audit commands were removed afterward. No axioms were introduced.

### Fourth pass

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `euler_transformation` | Prove the integral substitution `t = (1-u)/(1-zu)` for real `0 ≤ z < 1`, then use the analytic identity theorem to extend to the complex unit disk. | No `sorryAx` |
| `jacobiP_orthogonal` | Use the Gauss differential equation and a weighted Wronskian on `[0,1]`, then make the affine substitution back to `[-1,1]`. | No `sorryAx` |

The real substitution keeps the bases of all complex powers positive in the open
integration interval; multiplication and division of those powers are justified
explicitly. Analytic continuation uses the sequence `1/(n+1)` accumulating at zero.

The Jacobi proof establishes integrability of the weighted product and continuity of
the boundary primitive. Its boundary values vanish under the existing assumptions
`α, β > -1`, and the distinct eigenvalues yield orthogonality. The terminating Gauss
series are proved analytic everywhere, including both endpoints. Degree zero and both
orderings of the two distinct degrees are covered.

Both theorems and their real/shifted helper results were checked with `#print axioms`:
only `propext`, `Classical.choice`, and `Quot.sound` occur. No statements or assumptions
changed, no axioms were introduced, and no additional false or suspected-false statement
was identified. Temporary audit commands were removed after the check.

### Third pass

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `confluentM_kummer_transform` | Evaluate the Cauchy product of the exponential and confluent series using Chu–Vandermonde. Absolute convergence justifies the product formula. | No `sorryAx` |
| `laguerre_orthogonal` | Compute the moments against monomials by Gamma integration and Chu–Vandermonde, then expand the lower-degree Laguerre polynomial. | No `sorryAx` |

The stronger helper `integral_laguerre_mul_monomial` computes every moment:
`∫ L_n^(α)(x) x^k x^α exp(-x) dx = Γ(α+k+1) (-k)_n / n!`.
`integrable_laguerre_mul_monomial` separately establishes integrability, so the
vanishing argument does not rely on the totalized integral of a nonintegrable function.
The proofs cover degree zero and both orderings of the two distinct degrees.

These two theorems and both moment helpers were checked with `#print axioms` during
a Lake build; only `propext`, `Classical.choice`, and `Quot.sound` occur.
No statements or assumptions changed, no axioms were introduced, and no additional
false or suspected-false statement was identified. The full remaining inventory is
below; unproved results were left in place.

### Second pass

| Theorem | Proof | Dependency audit |
| --- | --- | --- |
| `ordinaryHypergeometric_eq_integral` | Integrate the binomial series term by term, dominated by an integrable beta weight times a summable sequence; identify the integrals using the existing beta/Gamma coefficient lemma. | No `sorryAx` |
| `pfaff_transformation` | Substitute `t ↦ 1 - t` in Euler's integral. Positive real parts of both factors justify multiplication of principal complex powers. | No `sorryAx` |
| `completeEllipticK_eq_integral` | Substitute `t = sin² θ` in Euler's integral and evaluate the Gamma prefactor. The monotone substitution theorem accommodates endpoint singularities. | No `sorryAx` |
| `laguerre_generating_function` | Prove absolute convergence of the double series using a nonnegative binomial/exponential majorant, then regroup by total degree and apply the existing terminating-sum formula. | No `sorryAx` |

The previous pass's `pfaff_transformation_symm` now also has no `sorryAx` dependency,
because the original Pfaff transformation is proved. All five declarations were audited
with `#print axioms` in a successful Lake build; each lists only `propext`,
`Classical.choice`, and `Quot.sound`. Temporary audit commands were removed afterward.

The Laguerre proof includes `t = 0` and `x = 0` without additional hypotheses.
No theorem statements or assumptions were changed, and no new axioms were introduced.
No additional false or suspected-false statement was identified in this pass; this does
not certify all remaining statements. Earlier review documents were preserved.

### First pass

- `eval_U_eq_gegenbauer`: match Taylor coefficients at one using Mathlib's Chebyshev
  derivative recurrence and the Gauss coefficient recurrence, including degree zero.
- `whittakerM_ode`: differentiate the prefactor and use the confluent equation.
- `whittakerW_ode`: combine the two analytic M solutions by linearity.
- `pfaff_transformation_symm`: swap numerator parameters in Pfaff's transformation.
  Its then-remaining admitted dependency was resolved in the second pass.

## Remaining priority work

### First priorities: Bessel and Confluent

- Bessel: half-integer evaluations, Poisson's and Sonine's integrals, generating and
  addition formulas, Nicholson's integral, and the three results about zeros.
  The Bessel–Kummer relation, differential equations, analyticity, and adjacent-order
  recurrences are now proved. Half-integer evaluations and Poisson's integral are
  natural next targets using this infrastructure.
- Confluent: Barnes's integral and the parabolic zero-free region remain open.
  The confluence limit and Kummer's second transformation are now proved.
  Barnes's integral and the zero-free theorem still need further analytic infrastructure.
- `AAR/Confluent/Whittaker.lean` remains free of `sorry`s.

### Other remaining work

- Gauss summation still needs the unit-circle convergence/boundary argument and
  treatment of the full stated parameter domain. The Euler integral is now available
  without admitted dependencies.
- Both quadratic transformations remain unproved, as do Kummer/Dixon/Whipple/Dougall
  summation identities. Euler's transformation is now proved.
- General orthogonal polynomial results still open: Favard, quadrature, zeros, and
  Parseval. The three-term recurrence and Christoffel–Darboux are now proved, with
  polynomial-basis and integration infrastructure available. For later orthogonal
  polynomial work, quadrature is a natural next target: the statement already supplies
  distinct roots, and polynomial division and Lagrange interpolation can be combined with the new low-degree orthogonality lemma.
- Jacobi completeness and the Chapter 7 results remain open. Jacobi completeness is
  now the only remaining `sorry` in `AAR/OrthogonalPolynomials/Classical.lean`; both
  Laguerre and Jacobi orthogonality are proved.

## Validation of the seventh pass

All commands ran from the Lake root. The intentional `.lake` symlink was preserved,
and neither the Lean toolchain nor the Mathlib revision was changed.

- `lake build > /tmp/AAR-build.log 2>&1`: passed (3680 jobs).
- `lake env lean AAR/Bessel/Basic.lean`: passed.
- `lake env lean AAR/Confluent/Basic.lean`: passed.
- `git diff --check`: passed. Because the source files were already untracked,
  whitespace checks against snapshots taken before this pass were also run.
- `rg -n '\bsorry\b' AAR`: 58 remaining occurrences, listed below.

Warnings in the changed Lean files concern their remaining admitted declarations and
the pre-existing unused `hz` argument in `confluentM_ode`.
No temporary Lean experiment files were retained. No commits were made.

## Complete remaining inventory

### AAR/Bailey.lean

- `rogers_ramanujan_first` — line 31
- `rogers_ramanujan_second` — line 39
- `bailey_lemma` — line 62
- `watson_transformation` — line 77

### AAR/Bessel/Basic.lean

- `besselJ_half` — line 267
- `besselJ_neg_half` — line 273

### AAR/Bessel/Modified.lean

- `nicholson_integral` — line 119

### AAR/Bessel/Theorems.lean

- `besselJ_eq_poisson_integral` — line 51
- `besselJ_generating_function` — line 57
- `besselJ_addition` — line 68
- `sonine_integral` — line 75
- `besselJ_infinite_zeros` — line 80
- `besselJ_zeros_simple` — line 86
- `besselJ_first_positive_zero_strictMono` — line 91

### AAR/Confluent/Basic.lean

- `confluentM_eq_barnes_integral` — line 386
- `confluentM_ne_zero_of_mem_parabolicRegion` — line 483

### AAR/Hypergeometric/Basic.lean

- `ordinaryHypergeometric_summable_of_mem_sphere` — line 320
- `tendsto_ordinaryHypergeometric_nhdsWithin_one` — line 328

### AAR/Hypergeometric/EulerIntegral.lean

- `gauss_summation` — line 157

### AAR/Hypergeometric/Identities.lean

- `kummer_theorem` — line 37
- `dixon_sum` — line 52
- `whipple_7F6` — line 70
- `dougall_bilateral` — line 81

### AAR/Hypergeometric/Transformations.lean

- `kummer_quadratic` — line 228
- `gauss_quadratic` — line 236

### AAR/OrthogonalPolynomials/Classical.lean

- `jacobiP_complete` — line 888

### AAR/OrthogonalPolynomials/General.lean

- `favard` — line 232
- `gauss_quadrature` — line 244
- `orthogonal_polynomials_roots` — line 250
- `orthogonal_polynomials_parseval` — line 338

### AAR/OrthogonalPolynomials/Topics.lean

- `jacobiP_connection` — line 38
- `turan_legendre` — line 45
- `turan_gegenbauer` — line 54
- `vietoris_inequality` — line 61
- `gegenbauer_cesaro_nonneg` — line 67
- `irrational_riemannZeta_three` — line 71

### AAR/Partitions.lean

- `ramanujan_mod_five` — line 46
- `ramanujan_mod_seven` — line 50
- `ramanujan_mod_eleven` — line 54

### AAR/QSeries/Identities.lean

- `jacobi_triple_product` — line 35
- `jacobiTheta_eq_qPochhammer` — line 43
- `ramanujan_1psi1` — line 67
- `heine_transformation` — line 82
- `q_beta_integral` — line 101

### AAR/QSeries/Pochhammer.lean

- `q_binomial_theorem` — line 157

### AAR/Selberg/Applications.lean

- `jacobiP_discriminant` — line 43
- `siegel_inequality` — line 65
- `nearly_poised_3F2` — line 103
- `hasse_davenport` — line 111
- `selberg_finite_field` — line 138

### AAR/Selberg/Basic.lean

- `selberg_integral` — line 46
- `aomoto_integral` — line 68

### AAR/SphericalHarmonics/Basic.lean

- `harmonicHomogeneous_orthogonal` — line 96

### AAR/SphericalHarmonics/Theorems.lean

- `spherical_addition` — line 41
- `funk_hecke` — line 53
- `gegenbauer_addition` — line 68
- `poissonKernelBall_reproduces` — line 86
- `su2_covers_so3` — line 104
