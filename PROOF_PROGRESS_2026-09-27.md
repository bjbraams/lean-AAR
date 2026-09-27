**lean-AAR: statement repairs and initial proof development — 27 September 2026**

This pass implements repairs from [the review](REVIEW_2026-09-27.md) and completes its first five proof priorities. It also proves three statements involved in the repairs. There are **646 admissions remaining, down from 654**. Fifteen existing Lean files were changed; no project Lean file was added. No dependency pins, build-directory settings, or shared `.lake` symlinks were changed. Existing deletions of older documentation were preserved, and no commit was made.

**Proofs completed**

The following eight previously admitted declarations now have proofs:

| Declaration | File | Result |
| --- | --- | --- |
| `AAR.Gamma.inv_Gamma_hasSum` | [Gamma/SeriesExpansions.lean](AAR/Gamma/SeriesExpansions.lean) | Reciprocal Gamma Taylor series. A new `hasSum_invGammaCoeff` proves convergence for every complex argument; the old disk-restricted theorem remains as a compatibility wrapper. |
| `AAR.OrthogonalPolynomials.hermitePhys_integral` | [OrthogonalPolynomials/Integrals.lean](AAR/OrthogonalPolynomials/Integrals.lean) | Hermite interval antiderivative, using the polynomial derivative and FTC. |
| `AAR.OrthogonalPolynomials.hermitePhys_weighted_integral` | Same file | Gaussian-weighted Hermite interval antiderivative. |
| `AAR.OrthogonalPolynomials.jacobi_weighted_integral` | Same file | Weighted Jacobi antiderivative on an interval contained in `(-1,1)`. |
| `AAR.OrthogonalPolynomials.laguerre_norm` | Same file | Squared norm from the finite polynomial expansion and already proved monomial moments. |
| `AAR.Confluent.confluentU_of_zero_param` | [Confluent/Relations.lean](AAR/Confluent/Relations.lean) | `U(0,b,z) = 1`, including integer `b`, using the repaired definition and a proved parameter limit. |
| `AAR.Confluent.tendsto_confluentM_div_Gamma_at_neg_nat` | [Confluent/Continuation.lean](AAR/Confluent/Continuation.lean) | The corrected punctured parameter limit of normalized Kummer M. Moved here from `BasicProperties.lean` to use parameter analyticity without an import cycle. |
| `AAR.Confluent.whittakerM_continuation` | [Confluent/Whittaker.lean](AAR/Confluent/Whittaker.lean) | Full-turn monodromy on the logarithmic argument plane, for every integer winding number. |

New supporting lemmas include `confluentU_eq_connection`, `confluentUConnection_zero`, `tendsto_confluentUConnection_zero`, `confluentU_zero`, `whittakerW_eq_connection`, and `whittakerW_half_zero`. The last establishes the formerly broken value

`whittakerW (1 / 2) 0 z = exp (-z / 2) * z ^ (1 / 2 : ℂ)`.

The first five proof targets retain their original statements. Their zero-degree and reversed-interval cases are included; no positivity condition on the Hermite interval endpoint was added.

**Gamma repairs**

- `polygamma_multiplication` now requires positive derivative order `0 < n`. The order-zero digamma formula requires a logarithmic correction. [DLMF 5.15.7](https://dlmf.nist.gov/5.15#E7)
- `qGamma_mono_right` now requires `x < 2` as well as `1 < x`. This removes the impossible strict inequality at `x = 2`. [DLMF 5.18.9](https://dlmf.nist.gov/5.18#E9)
- `Gamma_ratio_norm_le` now has real shifts `a,b`, assumptions `0 ≤ a` and `1 ≤ b - a`, and a complex argument with `0 < z.re`. Its bound is `‖z‖ ^ (-(b-a))`. The adjacent `norm_Gamma_bound` now also requires `0 ≤ z.re`. [DLMF 5.6.8–9](https://dlmf.nist.gov/5.6#E8)
- `digamma_half_diff` now sums paired adjacent terms, `1/(2k+z) - 1/(2k+1+z)`. This gives an absolutely convergent series rather than treating an alternating harmonic series as an unordered `tsum`.
- `stirlingG` and `stirlingRatioG` now define every coefficient by Bernoulli-number and Bernoulli-polynomial recurrences. Higher coefficients are no longer arbitrarily zero. The corresponding asymptotic theorems remain admitted.
- `Gamma_ratio_three` retains the parameter-dependent factor `t^(a+b-c)` in its remainder scale; previously even the zeroth-order bound could have the wrong growth rate.

The coefficient repairs were checked on `stirlingG 1 = 1/12`, `stirlingG 2 = 1/288`, and `stirlingRatioG 3 0 2 = 2`. The last specifically addresses the Gamma-ratio counterexample in the review.

**Confluent definitions, limits, and branches**

`confluentUConnection` now names the raw Gamma-prefactor connection formula. `confluentU` uses that formula at noninteger second parameters and a `Filter.limUnder` along noninteger parameters at integer second parameters. `whittakerW` is defined through this U function, avoiding its former independent, degenerate Gamma formula.

**The general limit-existence theorem is still missing.** A `limUnder` definition alone does not establish analytic continuation. This pass proves existence and the value for first parameter zero, and proves agreement with the raw formula at noninteger second parameter. General existence on the slit plane, continuity in the parameters, and transfer of identities to integer parameters remain substantive follow-up work. Thus the defining totalization and the concrete counterexample have been repaired, but the full integer-parameter analytic API is not complete.

To retain honest, admission-free proofs after this definition change, the proved `confluentU_kummer_transform` and its `confluentU_upperIncompleteGamma` consequence now require noninteger parameter; `whittakerW_even_mu` now requires noninteger twice-order and an argument in the slit plane. Their intended extensions through the new limits remain to be proved. `whittakerW_ode` retains its existing statement and proof, now using the proved generic connection formula locally.

The new definitions `confluentUOnLog`, `whittakerMOnLog`, and `whittakerWOnLog` take a logarithmic argument. Continuation statements now shift that argument by integer multiples of `2πi`; they no longer attempt to encode winding solely by multiplying a complex number by one. The W connection formula on the logarithmic plane is explicitly restricted to noninteger twice-order in its continuation theorem.

Both normalized M parameter-limit statements now use punctured neighborhoods. The Kummer limit is proved; the Whittaker limit remains admitted. Ordinary-M formulas involving shifted denominator parameters gained the necessary pole exclusions, including:

- `confluentU_neg_nat` and `confluentU_shift_nat`;
- `confluentM_lowerIncompleteGamma`, `confluentU_laguerre`, `confluentU_charlier`, and `whittakerW_laguerre`;
- `whittakerM_exp_neg`;
- `iteratedDeriv_exp_mul_whittakerM` and `iteratedDeriv_exp_neg_whittakerM`.

The Charlier identity additionally requires a nonzero scale. `whittakerM_neg_argument` requires a regular ordinary-M denominator. `confluentU_eq_twoFzero` now states the terminating polynomial case: a generic divergent `₂F₀` cannot be interpreted as an ordinary power-series sum. These are intentional statement/API changes, not newly completed proofs.

**Incomplete formulations repaired or removed**

- `regularizedHGFun_poincare_sector` now describes an expansion as the norm tends to infinity on closed upper-half-plane sectors, with both exponential and algebraic terms and their remainder scales. The previous statement was only local boundedness at a fixed point. This is a genuine, still-admitted sector theorem, with an explicit positive angular margin. [DLMF 13.7.2](https://dlmf.nist.gov/13.7#E2)
- `confluentU_poincare_finite` now bounds the error by the magnitude of the first omitted term under positive-real-parameter hypotheses. `confluentU_poincare_remainder` now supplies a remainder function together with its asymptotic order. Neither can be proved merely by naming an arbitrary difference. The latter no longer claims the exponentially improved content of DLMF 13.7.10.
- The reflexive `jacobiP_matrix_coefficient` placeholder was removed and replaced by an explicit documentation TODO. No representation-theoretic result was lost, and none is claimed to have been proved.
- `dyson_constant_term` was renamed `factorial_sum_div_prod_factorial`, preserving its valid proof while accurately describing its content. The Laurent-polynomial constant-term theorem is still unimplemented.

New declarations and repaired statements received formal docstrings; affected module summaries were updated. This was not a project-wide documentation or naming cleanup.

**Remaining admissions and next work**

| Area | Remaining admissions |
| --- | ---: |
| Gamma | 76 |
| Hypergeometric | 102 |
| Confluent | 206 |
| Bessel | 6 |
| Orthogonal polynomials | 233 |
| Q-series | 3 |
| Selberg | 7 |
| Spherical harmonics | 6 |
| Partitions | 3 |
| Bailey | 4 |
| **Total** | **646** |

The repaired Gamma inequalities, multiplication formula, paired digamma series, and asymptotic statements remain admitted. The eight proofs listed above account for the entire reduction; removing the reflexive placeholder did not reduce the admission count. No new `sorry` declaration was introduced.

The next finite-algebra targets remain `laguerre_negative_integer_parameter` and `besselPolynomial_eq_laguerre`, followed by the fixed-degree Hahn-family limits. The next general orthogonal-polynomial targets are `symmetric_measure_parity` and `hankelDeterminant_pos`. Gauss summation remains a separate, larger analytic task. The U limit-existence API should now be treated as an explicit foundational priority alongside that queue.

The remainder of the 646-statement backlog has not received a complete mathematical correctness audit; in particular, further branch-sensitive identities need scrutiny. This pass does not assert that every remaining admitted statement is true.

**Validation**

| Check | Result |
| --- | --- |
| `lake build > /tmp/AAR-build.log 2>&1`, run from the Lake root after each batch of Lean edits | Final build passed, 3,866 jobs. Remaining admission warnings are expected. |
| `lake env lean f.lean` for each changed Lean file | All 15 files passed individually. |
| Environment audit using `Lean.collectAxioms` | All 1,681 explicit declarations matched to the environment; all 845 completed theorem/lemma declarations are free of `sorryAx`, including transitive dependencies. All 190 explicit definitions/abbreviations are free of `sorryAx` as well. |
| Comment-aware source inventory and `rg -n '\bsorry\b' --glob '*.lean' AAR AAR.lean Main.lean` | 646 actual admissions. The raw text search also includes a comment containing the word. |
| Reciprocal-Gamma, Hermite, Jacobi, Laguerre, Whittaker, and coefficient probes | Passed against the pinned Lean/Mathlib before or alongside integration. |
| `git diff --check` | Passed. |
| Source/dependency/configuration preservation | Changes are limited to the 15 listed implementation files and this progress report; pre-existing documentation deletions and the earlier review were preserved. No explicit axioms or admitted definitions were introduced. |

The changed implementation files are the seven Confluent modules `Basic`, `BasicProperties`,
`Continuation`, `Whittaker`, `Relations`, `Recurrence`, and `Asymptotics`; the five Gamma modules
`Polygamma`, `QGamma`, `Inequalities`, `SeriesExpansions`, and `Asymptotics`;
`OrthogonalPolynomials/Integrals.lean`; `Selberg/Applications.lean`; and
`SphericalHarmonics/Theorems.lean`.


