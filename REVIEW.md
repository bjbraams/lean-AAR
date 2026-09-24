# AAR Lean review — 2026-09-14

The initial pass inventoried the unfinished declarations and inspected their formulations against the
local Mathlib checkout. It is not a complete audit of every proof or a page-by-page comparison
with the book. Several unfinished statements need correction before proof work is worthwhile.
No toolchain, dependency, or Lake topology changes were made. No commits were made.

The five counterexamples have since been checked against AAR and their source declarations
corrected. See [SOURCE_REVIEW.md](SOURCE_REVIEW.md) for the page references, the printed
Kummer typo, corrected domains, and validation of the replacements.

**Proof progress**

The initial pass decreased explicit `sorry` occurrences in `AAR/` from 99 to 92.
The source-correction follow-up proved `qGamma_add_one`, bringing the count to 91.
The differential-equation pass removed three more, bringing the count to 88.
The formulation-review pass proved two results and reopened the corrected Favard theorem,
bringing the current count to **87**.

| Declaration | Result |
| --- | --- |
| `harmonicHomogeneousDim_three` | Proved using Mathlib's binomial symmetry and Pascal identities, including degrees zero and one. |
| `aeval_hermitePhys_eq_hermite` | Proved by induction, differentiating the scaling identity to relate the two polynomial recurrences. |
| `deriv_gaussian_eq_hermitePhys` | Adapted Mathlib's `Polynomial.deriv_gaussian_eq_hermite_mul_gaussian` to the physicists' normalization. |
| `qGamma_one` | Proved after correcting its hypothesis to `‖q‖ < 1`. |
| `dyson_constant_term` | Proved the stated factorial-ratio identity from `Nat.multinomial_spec`, including the empty index type. This does **not** prove Dyson's constant-term theorem. |
| `favard` | The initial zero-measure proof covered only the weak formulation. The formulation-review pass restored positivity and the initial recurrence; the genuine theorem now awaits proof. |
| `jacobiP_matrix_coefficient` | Proved by reflexivity; documented that the statement does **not** express a matrix-coefficient theorem. |

The additional lemma `qPochhammerInf_ne_zero` applies Mathlib's
`tprod_one_add_ne_zero_of_summable` to a geometrically summable perturbation of one.
Comments identify the Mathlib results used in the short adaptations.

**Source-correction follow-up**

The original counterexample module has been removed after checking its five cases against
the book. The repaired declarations are `qGamma_one`, `qGamma_add_one`,
`confluentM_kummer_transform`, `spherical_addition`, and `siegel_inequality`.
See [SOURCE_REVIEW.md](SOURCE_REVIEW.md) for all changed assumptions and the distinction
between transcription errors, implicit domain conventions, and the typo in AAR (4.1.11).
The corrected Kummer, spherical-addition, and general Siegel proofs still contain `sorry`.

**Hypergeometric differential-equation follow-up**

Proved `hasDerivAt_ordinaryHypergeometric`, `ordinaryHypergeometric_ode`, and
`confluentM_ode`. The existing consequence `deriv_ordinaryHypergeometric` now also has
no dependency on an unfinished proof. No statements or assumptions changed, and no new
false statements were found in this cluster.

The new `AAR/Hypergeometric/Series.lean` specializes Mathlib's analytic differentiation
machinery to scalar power series and derives a second-order differential equation from
a coefficient recurrence. The Gauss expansion includes terminating numerator parameters;
the confluent expansion uses Mathlib's entire regularized hypergeometric series. Comments
identify direct adaptations of existing Mathlib results.

The original nonzero-point hypotheses in the ODE statements are preserved, although the
proofs also work at zero. Lean consequently reports unused-variable warnings for these
hypotheses (and the redundant exclusion of one in the Gauss unit disk).

**Source-level findings addressed**

Every row of the former formulation-findings table has now been checked against the supplied
AAR scans and addressed. See [FORMULATION_REVIEW.md](FORMULATION_REVIEW.md) for the
source-by-source record, precise changed assumptions, renamed declarations, and related
corrections found in those clusters.

The corrections include the Gamma factors, hypergeometric transformations and sums,
Barnes contour, confluent parabolic zero-free regions, branch domains, orthogonal-polynomial
hypotheses and normalizations, actual Jacobi completeness, surface measure, Selberg/Aomoto
formulas, the finite-field character sum, and bilateral q-indices. The existing hypergeometric
polynomial definitions are retained on their explicitly documented regular-parameter domains;
no extension at exceptional parameters is claimed.

Two additional source deficiencies are noted in Lean: the extra cosine around the Euclidean
inner product in AAR's Poisson kernel on p. 463, and the missing sufficient character-order
hypothesis in the finite-field treatment on pp. 431–438. The earlier printed Kummer typo
remains noted. Ordinary Lean transcription history is kept in the review reports.

Proved `besselI_eq_besselJ` on its corrected domain and `errorFn_eq_integral`, with reusable
Gaussian-series lemmas. None of these proofs depends on `sorryAx`. Favard's former trivial
proof no longer applies after restoring the correct formulation, so that obligation is open.
Other corrected targets remain unfinished; a source check is not a proof.

The previously identified vacuous Dyson and matrix-coefficient formulations in the first
proof-progress table are separate outstanding formalization tasks. This pass does not certify
all remaining assertions by omission. The Gamma files still contain no explicit `sorry`.

**Suggested next proof clusters**

The repaired orthogonal-polynomial hypotheses now provide sound targets for the recurrence,
quadrature, root, and Parseval proofs. Other useful clusters are terminating hypergeometric
summation, Euler/Pfaff transformations, and integral representations. Mathlib supplies the
regularized series, analytic machinery, polynomial differentiation, and Beta/Gamma infrastructure.
The seven unfinished classical-polynomial results can also build on the two Hermite proofs.

**Validation**

The latest pass passed a full build (3678 jobs), all 17 edited files individually, whitespace
checks, and axiom audits. Details are in [FORMULATION_REVIEW.md](FORMULATION_REVIEW.md).
The following records the earlier differential-equation pass:

The initial pass passed the full build, per-file Lean checks, whitespace checks, and axiom
audits of all new proofs. Validation of the source corrections is recorded in
[SOURCE_REVIEW.md](SOURCE_REVIEW.md). The differential-equation pass also passed:

- `lake build` from the Lake root (3676 jobs).
- `lake env lean` for `AAR/Hypergeometric/Series.lean`, `AAR/Hypergeometric/DiffEq.lean`,
  and `AAR/Confluent/Basic.lean`.
- `git diff --check` and a direct whitespace check of all files changed in this pass
  (the repository sources are untracked).
- `#print axioms` for the three completed theorems, `deriv_ordinaryHypergeometric`,
  `HasFPowerSeriesOnBall.deriv_ofScalars`, `HasFPowerSeriesOnBall.ode_of_recurrence`,
  and `hasFPowerSeriesOnBall_confluentM`: only `propext`, `Classical.choice`, and
  `Quot.sound`, with no `sorryAx` dependencies.
- At the end of that pass, `rg -n '\bsorry\b' AAR`: 88 occurrences. No `sorry` remains in the Gauss
  differential-equation file or the new scalar-series file. The confluent file retains
  five, listed below.

No `Scratch.lean` remains, and the intentional `.lake` symlink is unchanged.

**Remaining `sorry` inventory (87 occurrences)**

| File and line | Declaration |
| --- | --- |
| `AAR/Bailey.lean:31` | `rogers_ramanujan_first` |
| `AAR/Bailey.lean:39` | `rogers_ramanujan_second` |
| `AAR/Bailey.lean:62` | `bailey_lemma` |
| `AAR/Bailey.lean:77` | `watson_transformation` |
| `AAR/Bessel/Basic.lean:68` | `besselJ_ode` |
| `AAR/Bessel/Basic.lean:74` | `besselY_ode` |
| `AAR/Bessel/Basic.lean:80` | `besselJ_half` |
| `AAR/Bessel/Basic.lean:86` | `besselJ_neg_half` |
| `AAR/Bessel/Basic.lean:95` | `besselJ_eq_confluentM` |
| `AAR/Bessel/Modified.lean:78` | `besselI_ode` |
| `AAR/Bessel/Modified.lean:84` | `besselK_ode` |
| `AAR/Bessel/Modified.lean:92` | `nicholson_integral` |
| `AAR/Bessel/Theorems.lean:29` | `besselJ_add_sub` |
| `AAR/Bessel/Theorems.lean:35` | `two_deriv_besselJ` |
| `AAR/Bessel/Theorems.lean:45` | `besselJ_eq_poisson_integral` |
| `AAR/Bessel/Theorems.lean:51` | `besselJ_generating_function` |
| `AAR/Bessel/Theorems.lean:62` | `besselJ_addition` |
| `AAR/Bessel/Theorems.lean:69` | `sonine_integral` |
| `AAR/Bessel/Theorems.lean:74` | `besselJ_infinite_zeros` |
| `AAR/Bessel/Theorems.lean:80` | `besselJ_zeros_simple` |
| `AAR/Bessel/Theorems.lean:85` | `besselJ_first_positive_zero_strictMono` |
| `AAR/Confluent/Basic.lean:174` | `confluentM_kummer_transform` |
| `AAR/Confluent/Basic.lean:192` | `tendsto_ordinaryHypergeometric_div_atTop` |
| `AAR/Confluent/Basic.lean:203` | `confluentM_eq_barnes_integral` |
| `AAR/Confluent/Basic.lean:300` | `confluentM_ne_zero_of_mem_parabolicRegion` |
| `AAR/Confluent/Whittaker.lean:43` | `whittakerM_ode` |
| `AAR/Confluent/Whittaker.lean:51` | `whittakerW_ode` |
| `AAR/Hypergeometric/Basic.lean:272` | `arcsin_eq_ordinaryHypergeometric` |
| `AAR/Hypergeometric/Basic.lean:278` | `ordinaryHypergeometric_summable_of_mem_sphere` |
| `AAR/Hypergeometric/Basic.lean:286` | `tendsto_ordinaryHypergeometric_nhdsWithin_one` |
| `AAR/Hypergeometric/Contiguous.lean:32` | `contiguous_shift_b` |
| `AAR/Hypergeometric/Contiguous.lean:39` | `contiguous_a` |
| `AAR/Hypergeometric/Contiguous.lean:45` | `contiguous_c` |
| `AAR/Hypergeometric/EulerIntegral.lean:40` | `ordinaryHypergeometric_eq_integral` |
| `AAR/Hypergeometric/EulerIntegral.lean:48` | `gauss_summation` |
| `AAR/Hypergeometric/EulerIntegral.lean:54` | `chu_vandermonde` |
| `AAR/Hypergeometric/Identities.lean:36` | `kummer_theorem` |
| `AAR/Hypergeometric/Identities.lean:51` | `dixon_sum` |
| `AAR/Hypergeometric/Identities.lean:69` | `whipple_7F6` |
| `AAR/Hypergeometric/Identities.lean:80` | `dougall_bilateral` |
| `AAR/Hypergeometric/Identities.lean:94` | `completeEllipticK_eq_integral` |
| `AAR/Hypergeometric/Transformations.lean:31` | `pfaff_transformation` |
| `AAR/Hypergeometric/Transformations.lean:39` | `euler_transformation` |
| `AAR/Hypergeometric/Transformations.lean:46` | `pfaff_transformation_symm` |
| `AAR/Hypergeometric/Transformations.lean:53` | `kummer_quadratic` |
| `AAR/Hypergeometric/Transformations.lean:61` | `gauss_quadratic` |
| `AAR/OrthogonalPolynomials/Classical.lean:109` | `hermitePhys_generating_function` |
| `AAR/OrthogonalPolynomials/Classical.lean:126` | `laguerre_orthogonal` |
| `AAR/OrthogonalPolynomials/Classical.lean:134` | `laguerre_generating_function` |
| `AAR/OrthogonalPolynomials/Classical.lean:157` | `aeval_shiftedLegendre_eq_legendreP` |
| `AAR/OrthogonalPolynomials/Classical.lean:165` | `jacobiP_orthogonal` |
| `AAR/OrthogonalPolynomials/Classical.lean:182` | `eval_U_eq_gegenbauer` |
| `AAR/OrthogonalPolynomials/Classical.lean:208` | `jacobiP_complete` |
| `AAR/OrthogonalPolynomials/General.lean:47` | `three_term_recurrence` |
| `AAR/OrthogonalPolynomials/General.lean:60` | `favard` |
| `AAR/OrthogonalPolynomials/General.lean:72` | `gauss_quadrature` |
| `AAR/OrthogonalPolynomials/General.lean:78` | `orthogonal_polynomials_roots` |
| `AAR/OrthogonalPolynomials/General.lean:91` | `christoffel_darboux` |
| `AAR/OrthogonalPolynomials/General.lean:101` | `orthogonal_polynomials_parseval` |
| `AAR/OrthogonalPolynomials/Topics.lean:38` | `jacobiP_connection` |
| `AAR/OrthogonalPolynomials/Topics.lean:45` | `turan_legendre` |
| `AAR/OrthogonalPolynomials/Topics.lean:54` | `turan_gegenbauer` |
| `AAR/OrthogonalPolynomials/Topics.lean:61` | `vietoris_inequality` |
| `AAR/OrthogonalPolynomials/Topics.lean:67` | `gegenbauer_cesaro_nonneg` |
| `AAR/OrthogonalPolynomials/Topics.lean:71` | `irrational_riemannZeta_three` |
| `AAR/Partitions.lean:46` | `ramanujan_mod_five` |
| `AAR/Partitions.lean:50` | `ramanujan_mod_seven` |
| `AAR/Partitions.lean:54` | `ramanujan_mod_eleven` |
| `AAR/QSeries/Identities.lean:35` | `jacobi_triple_product` |
| `AAR/QSeries/Identities.lean:43` | `jacobiTheta_eq_qPochhammer` |
| `AAR/QSeries/Identities.lean:67` | `ramanujan_1psi1` |
| `AAR/QSeries/Identities.lean:82` | `heine_transformation` |
| `AAR/QSeries/Identities.lean:101` | `q_beta_integral` |
| `AAR/QSeries/Pochhammer.lean:111` | `q_binomial_theorem` |
| `AAR/Selberg/Applications.lean:43` | `jacobiP_discriminant` |
| `AAR/Selberg/Applications.lean:65` | `siegel_inequality` |
| `AAR/Selberg/Applications.lean:103` | `nearly_poised_3F2` |
| `AAR/Selberg/Applications.lean:111` | `hasse_davenport` |
| `AAR/Selberg/Applications.lean:138` | `selberg_finite_field` |
| `AAR/Selberg/Basic.lean:46` | `selberg_integral` |
| `AAR/Selberg/Basic.lean:68` | `aomoto_integral` |
| `AAR/SphericalHarmonics/Basic.lean:96` | `harmonicHomogeneous_orthogonal` |
| `AAR/SphericalHarmonics/Theorems.lean:41` | `spherical_addition` |
| `AAR/SphericalHarmonics/Theorems.lean:53` | `funk_hecke` |
| `AAR/SphericalHarmonics/Theorems.lean:68` | `gegenbauer_addition` |
| `AAR/SphericalHarmonics/Theorems.lean:86` | `poissonKernelBall_reproduces` |
| `AAR/SphericalHarmonics/Theorems.lean:104` | `su2_covers_so3` |
