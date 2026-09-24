# Orthogonal-polynomial proof progress — 2026-09-16, second pass

## Outcome

Replaced **17 more `sorry`s** with Lean proofs. Orthogonal-polynomial admissions decreased from **304 to 287**, and the project total decreased from **452 to 435**. No theorem statement or assumption changed, no new admission was added, and no theorem was found or suspected to be false during this pass.

This follows the [first 30-proof pass](PROOF_PROGRESS_ORTHOGONAL_2026-09-16.md). The DLMF attributes on the completed statements are preserved.

## Proved theorems

### [Differential.lean](AAR/OrthogonalPolynomials/Differential.lean)

- `jacobi_differential_equation`
- `gegenbauer_differential_equation`
- `legendre_differential_equation`
- `laguerre_differential_equation`
- `jacobi_derivative`
- `gegenbauer_derivative`
- `laguerre_derivative`

### [ContinuedFractions.lean](AAR/OrthogonalPolynomials/ContinuedFractions.lean)

- `chebyshevT_continued_fraction`
- `chebyshevU_continued_fraction`
- `legendre_continued_fraction`
- `hermitePhys_continued_fraction`

### [Wilson.lean](AAR/OrthogonalPolynomials/Wilson.lean)

- `wilson_hypergeometric`
- `continuousDualHahn_hypergeometric`
- `racah_hypergeometric`
- `dualHahn_hypergeometric`
- `dualHahn_hahn_duality`
- `racah_duality`

## Proof structure

- The Jacobi, Gegenbauer, and Legendre differential equations follow from the entire terminating Gauss series and its coefficient recurrence. The Laguerre differential equation follows from the confluent hypergeometric series recurrence, including at zero.
- New derivative helpers for terminating Gauss series and regular confluent hypergeometric series establish the Jacobi, Gegenbauer, and Laguerre derivative identities, with Pochhammer and factorial factors simplified explicitly.
- The four continued-fraction identities use Mathlib's convergent-denominator recurrence and induction, matching the existing polynomial recurrences.
- The Wilson-class representations follow from finite product identities for paired Pochhammer factors. A shared finite-series `HasSum` lemma in `Hahn.lean` proves the dual-Hahn/Hahn and Racah dualities by exchanging terminating upper parameters. It handles degree zero and totalized singular denominators.

## Remaining admissions

| Changed module | Before | After |
| --- | ---: | ---: |
| [Hahn.lean](AAR/OrthogonalPolynomials/Hahn.lean) | 33 | 33 |
| [Differential.lean](AAR/OrthogonalPolynomials/Differential.lean) | 26 | 19 |
| [ContinuedFractions.lean](AAR/OrthogonalPolynomials/ContinuedFractions.lean) | 5 | 1 |
| [Wilson.lean](AAR/OrthogonalPolynomials/Wilson.lean) | 15 | 9 |

The other orthogonal-polynomial modules retain 225 admissions. No other chapter was changed. The remaining Laguerre continued fraction depends on the still-admitted Laguerre recurrence; it was set aside while other proofs proceeded. The [DLMF coverage checklist](AAR/OrthogonalPolynomials/DLMFCoverage.md) records the remaining acquired statements throughout the chapter.

Remaining admitted declarations in the four edited modules:

### Hahn.lean

- `hahn_orthogonal`
- `krawtchouk_orthogonality`
- `meixner_orthogonality`
- `charlier_orthogonality`
- `continuousHahn_orthogonal`
- `meixnerPollaczek_orthogonality`
- `hahn_difference_equation`
- `krawtchouk_difference_equation`
- `meixner_difference_equation`
- `charlier_difference_equation`
- `hahn_forward_difference`
- `krawtchouk_forward_difference`
- `meixner_forward_difference`
- `charlier_forward_difference`
- `meixnerPollaczek_recurrence`
- `meixnerPollaczek_central_difference`
- `krawtchouk_generating_function`
- `meixner_generating_function`
- `charlier_generating_function`
- `meixnerPollaczek_generating_function`
- `hahn_limit_krawtchouk`
- `hahn_limit_jacobi`
- `krawtchouk_limit_charlier`
- `meixner_limit_charlier`
- `charlier_limit_hermite`
- `hahn_limit_meixner`
- `meixner_limit_laguerre`
- `meixnerPollaczek_limit_laguerre`
- `meixnerPollaczek_limit_hermite`
- `continuousHahn_difference_equation`
- `meixnerPollaczek_difference_equation`
- `continuousHahn_central_difference`
- `continuousHahn_generating_function`

### Differential.lean

- `jacobi_recurrence`
- `gegenbauer_recurrence`
- `laguerre_recurrence`
- `jacobi_contiguous_sub`
- `jacobi_contiguous_add`
- `jacobi_raise_beta`
- `jacobi_raise_degree_beta`
- `gegenbauer_raise_parameter`
- `gegenbauer_raise_parameter_sq`
- `chebyshevV_contiguous`
- `chebyshevV_mul_one_add`
- `laguerre_raise_parameter`
- `laguerre_mul_argument`
- `jacobi_lowering_derivative`
- `jacobi_raising_derivative`
- `jacobi_weighted_derivative`
- `gegenbauer_weighted_derivative`
- `chebyshevU_weighted_derivative`
- `laguerre_weighted_derivative`

### ContinuedFractions.lean

- `laguerre_continued_fraction`

### Wilson.lean

- `wilson_orthogonal`
- `continuousDualHahn_orthogonality`
- `wilson_limit_continuousDualHahn`
- `racah_limit_dualHahn`
- `racah_limit_hahn`
- `wilson_central_difference`
- `continuousDualHahn_central_difference`
- `wilson_generating_function`
- `continuousDualHahn_generating_function`

## Validation

- `#print axioms` checked all 17 newly completed theorems during a root build. Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`. Temporary audit commands were removed. The audit output is preserved at `/tmp/aar-proof-op2-axioms.txt`.
- `lake build > /tmp/AAR-build.log 2>&1`: passed after removing audit commands, 3792 jobs.
- `lake env lean AAR/OrthogonalPolynomials/<file>.lean`: passed separately for `Differential`, `ContinuedFractions`, `Wilson`, and `Hahn`. Expected admission and unused-hypothesis warnings remain.
- `git diff --check`: passed. Since these working files are untracked, snapshot comparisons and a separate trailing-whitespace check were also used; they passed.
- `rg -n '\bsorry\b' AAR/OrthogonalPolynomials --glob '*.lean'`: 287 remaining admissions; the listing is saved in `/tmp/aar-proof-op2-remaining.txt`. Across `AAR`, 435 remain.
- All original theorem headers were compared with the pre-edit snapshots and preserved. The other orthogonal-polynomial Lean files are byte-for-byte unchanged. `Scratch.lean` is absent.
- The existing `.lake` symlink and toolchain were preserved. No commits were made.
