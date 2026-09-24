# Proof progress — 2026-09-15

This pass reduced the actual starting inventory from **53 to 50** explicit `sorry`
occurrences. The older review's count of 58 predates proofs already present when this
pass began.

## Theorems proved

| Theorem | Proof |
| --- | --- |
| `ordinaryHypergeometric_summable_of_mem_sphere` | Separate terminating parameter cases. For the other cases, Euler's Gamma approximants give the normalized coefficient limit; comparison with a convergent p-series proves absolute convergence on the unit circle. |
| `besselJ_eq_poisson_integral` | Prove Euler's integral for Kummer's function by dominated termwise integration of the exponential series. Combine the existing Bessel–Kummer identity with the substitution `t = 2u - 1` and Gamma duplication. |
| `besselJ_zeros_simple` | Reduce a hypothetical double Bessel zero to a double zero of regularized `₀F₁`. Its contiguous relation forces all derivatives to vanish; analytic uniqueness contradicts its nonzero value at zero. |

New supporting lemmas are `GammaSeq_eq_poch`, `tendsto_gaussHGCoeff_div_cpow`,
`confluentM_eq_euler_integral`, and `regularized0F1_deriv_ne_zero`.

The convergence proof includes nonpositive integer numerator and denominator parameters
under the project's totalized coefficient definition. The integral proof uses equality
on the open integration interval, avoiding endpoint power identities at singularities.
The zero proof establishes nonzero prefactors and Gamma values before cancellation.

## Validation

All commands ran from the Lake root.

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3682 jobs.
- `lake env lean AAR/Hypergeometric/Basic.lean`: passed.
- `lake env lean AAR/Confluent/Basic.lean`: passed.
- `lake env lean AAR/Bessel/Theorems.lean`: passed.
- `git diff --check`: passed. Since the Lean files were already untracked, comparisons
  against pre-edit snapshots were also checked and reported no whitespace errors.
- `rg -n '\bsorry\b' AAR`: 50 occurrences; complete inventory below.
- A Lake build with `#print axioms` checked all three formerly admitted theorems and
  the normalized coefficient limit, Kummer integral, and regularized-series zero helper.
  Each depends only on `propext`, `Classical.choice`, and `Quot.sound`; none depends
  on `sorryAx`. The temporary audit commands were removed before the final build.
- Existing declaration signatures were compared against pre-edit snapshots and are unchanged.

No axioms were introduced, and no theorem assumptions were changed. No additional
false or suspected-false theorem was identified; this is not a full statement audit.
The remaining warnings in edited files concern admitted results, the existing unused
`hz` in `confluentM_ode`, and the now-unused `hx` in Poisson's integral. That hypothesis
was retained to preserve the original statement.

The `.lake` symlink, toolchain, and Mathlib revision were preserved. No temporary Lean
files remain and no commits were made.

## Remaining admissions

### AAR/Bailey.lean

- `rogers_ramanujan_first` — line 31
- `rogers_ramanujan_second` — line 39
- `bailey_lemma` — line 62
- `watson_transformation` — line 77

### AAR/Bessel/Modified.lean

- `nicholson_integral` — line 119

### AAR/Bessel/Theorems.lean

- `besselJ_generating_function` — line 117
- `besselJ_addition` — line 128
- `sonine_integral` — line 135
- `besselJ_infinite_zeros` — line 140
- `besselJ_first_positive_zero_strictMono` — line 207

### AAR/Confluent/Basic.lean

- `confluentM_eq_barnes_integral` — line 450
- `confluentM_ne_zero_of_mem_parabolicRegion` — line 547

### AAR/Hypergeometric/Basic.lean

- `tendsto_ordinaryHypergeometric_nhdsWithin_one` — line 400

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

- `favard` — line 268
- `orthogonal_polynomials_parseval` — line 713

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

