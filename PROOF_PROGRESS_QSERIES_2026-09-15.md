# Q-series proof progress — 2026-09-15

This continuation reduced explicit admissions from **50 to 48**.

## Theorems proved

- `heine_transformation`: expand the quotient of shifted infinite products with the
  proved q-binomial theorem. Bound the double series by the product of two absolutely
  summable q-binomial series, interchange its sums, and apply the q-binomial theorem
  again. The proof includes `q = 0` and `z = 0`, as permitted by the original hypotheses.
- `q_beta_integral`: rewrite Jackson's integral as a q-binomial series using the product
  splitting formulas. Positive real `q` justifies the complex-power identities;
  `Re a, Re b > 0` ensures the infinite-product denominators are nonzero. The product
  evaluation reduces to the defining q-Gamma quotient.

Both proofs are in `AAR/QSeries/Identities.lean`. Existing theorem signatures and
assumptions are unchanged, and no axioms were introduced.

## Validation

All commands ran from the Lake root.

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3682 jobs.
- `lake env lean AAR/QSeries/Identities.lean`: passed.
- `lake env lean AAR/Selberg/Applications.lean`: passed.
- `git diff --check`: passed. The files were already untracked, so whitespace checks
  against pre-edit snapshots were also run; no whitespace errors were reported.
- `rg -n '\bsorry\b' AAR`: 48 occurrences, listed below.
- A Lake build with `#print axioms` audited both newly proved identities. Each depends only on `propext`,
  `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.
  Audit commands were removed before the final build.

The edited files only warn about their remaining admitted declarations. The intentional
`.lake` symlink, Lean toolchain, and Mathlib revision were preserved. No temporary Lean
files remain, and no commits were made.

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

- `jacobi_triple_product` — line 36
- `jacobiTheta_eq_qPochhammer` — line 44
- `ramanujan_1psi1` — line 68

### AAR/Selberg/Applications.lean

- `jacobiP_discriminant` — line 44
- `siegel_inequality` — line 66
- `nearly_poised_3F2` — line 113
- `hasse_davenport` — line 125
- `selberg_finite_field` — line 152

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

