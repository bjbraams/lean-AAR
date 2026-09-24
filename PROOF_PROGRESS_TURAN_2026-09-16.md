# Turán proof progress — 2026-09-16

Explicit admissions decreased from **48 to 46**.

## Theorems proved

In `AAR/OrthogonalPolynomials/Topics.lean`:

- `turan_gegenbauer`: Turán's inequality for Gegenbauer polynomials normalized at one,
  for every positive real parameter, positive degree, and real argument in `[-1,1]`.
- `turan_legendre`: the Legendre specialization at parameter `1/2`.

The proof first derives the normalized three-term recurrence directly from the terminating
hypergeometric coefficients. If `G_n` denotes the normalized polynomial's real part and
`D_n = G_n² - G_{n-1} G_{n+1}`, the recurrence gives

`(n + 2λ) D_n = (n - 1) D_{n-1} + G_n² + G_{n-1}² - 2x G_n G_{n-1}`.

The last three terms equal `(G_n - x G_{n-1})² + (1-x²) G_{n-1}²`, so induction
proves nonnegativity, including both endpoints. The degree-one case is checked separately.

Reusable lemmas added:

- `gegenbauer_div_at_one`
- `gegenbauer_normalized_recurrence`
- `gegenbauer_normalized_one`
- `legendreP_eq_normalized_gegenbauer`
- `legendreP_one`
- `legendreP_recurrence`

## Assumptions and source issues

All existing theorem statements and assumptions are unchanged. No new false statements
or source errors were identified in this proof cluster. No axioms were introduced.

## Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3682 jobs.
- `lake env lean AAR/OrthogonalPolynomials/Topics.lean`: passed; only the four remaining
  admitted declarations in that file produce warnings.
- `git diff --check`: passed. Because the file is untracked, its changes were also checked
  against the pre-edit snapshot; no whitespace errors were found.
- `rg -n '\bsorry\b' AAR`: 46 remaining occurrences.
- A build with `#print axioms` checked both Turán inequalities and both recurrence lemmas.
  All four depend only on `propext`, `Classical.choice`, and `Quot.sound`; none uses `sorryAx`.
  The audit commands were removed before the final build.
- Every existing theorem signature in the edited file was compared with the pre-edit
  snapshot and is unchanged.

The `.lake` symlink, toolchain, and dependencies were preserved. No temporary Lean files
were created, and no commits were made.

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
- `vietoris_inequality` — line 232
- `gegenbauer_cesaro_nonneg` — line 238
- `irrational_riemannZeta_three` — line 242

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
