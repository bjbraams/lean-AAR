# Orthogonal-polynomial proof progress — 2026-09-16

## Outcome

Replaced **30 `sorry`s** with Lean proofs in five modules. Orthogonal-polynomial admissions decreased from **334 to 304**; the project total decreased from **482 to 452**. No theorem statement or assumption changed, no new admission was added, and no theorem was found or suspected to be false during this proof pass.

The proofs establish kernel reproduction and annihilation, the diagonal Christoffel–Darboux formula, the corrected telescoping sum of recurrence coefficients, finite-family dualities, Hermite derivatives/recurrences/differential equations, the Jacobi finite sum, special values, and polynomial symmetries.

The sign correction previously recorded for DLMF 18.2.11_1 is now backed by a completed Lean proof (`sum_recurrenceDiagonal`).

## Proved theorems

### [Hahn.lean](AAR/OrthogonalPolynomials/Hahn.lean)

- `krawtchouk_duality`
- `meixner_duality`
- `charlier_duality`

### [Differential.lean](AAR/OrthogonalPolynomials/Differential.lean)

- `hermitePhys_differential_equation`
- `hermite_differential_equation`
- `hermitePhys_recurrence`
- `hermite_recurrence`
- `hermitePhys_derivative`
- `hermite_derivative`
- `hermitePhys_weighted_derivative`
- `hermite_weighted_derivative`

### [Explicit.lean](AAR/OrthogonalPolynomials/Explicit.lean)

- `jacobi_finite_sum`
- `laguerre_at_zero`
- `jacobi_at_one`
- `gegenbauer_at_one`
- `hermitePhys_reflection`
- `chebyshevV_at_one`
- `chebyshevW_at_one`
- `legendre_eq_gegenbauer`

### [GeneralIdentities.lean](AAR/OrthogonalPolynomials/GeneralIdentities.lean)

- `integral_product`
- `recurrenceDiagonal_eq_integral`
- `sum_recurrenceDiagonal`
- `kernel_reproduces`
- `christoffel_darboux_diagonal`
- `kernel_difference`
- `monic_squaredNorm_ratio`
- `kernel_annihilates`

### [Associated.lean](AAR/OrthogonalPolynomials/Associated.lean)

- `reverseBesselPolynomial_eq`
- `pollaczek_reflection`
- `pollaczek_eq_associatedMeixnerPollaczek`

## Proof structure

- Kernel integration reduces to a finite sum of orthogonal coordinates, using the existing polynomial basis and integrability lemmas. The diagonal Christoffel–Darboux formula follows by differentiating a polynomial identity; no limit theorem is admitted.
- The recurrence-coefficient sum follows from the next-to-leading coefficients of polynomial basis expansions and telescoping, including the degree-zero base case.
- A terminating-sum cutoff lemma proves duality uniformly, including zero indices and singular lower parameters. Existing degree-bound hypotheses on `krawtchouk_duality` were preserved.
- Hermite derivative formulas follow by induction from the defining differential recurrences. The three-term recurrences, differential equations, and weighted derivatives then follow algebraically.
- The Jacobi finite sum follows from the terminating Gauss series and Pochhammer identities. Polynomial composition proves Hermite reflection; the Bessel reversal and Pollaczek identities use finite sums and recurrences.

## Remaining admissions

| Changed module | Before | After |
| --- | ---: | ---: |
| [Hahn.lean](AAR/OrthogonalPolynomials/Hahn.lean) | 36 | 33 |
| [Differential.lean](AAR/OrthogonalPolynomials/Differential.lean) | 34 | 26 |
| [Explicit.lean](AAR/OrthogonalPolynomials/Explicit.lean) | 34 | 26 |
| [GeneralIdentities.lean](AAR/OrthogonalPolynomials/GeneralIdentities.lean) | 16 | 8 |
| [Associated.lean](AAR/OrthogonalPolynomials/Associated.lean) | 21 | 18 |

The other orthogonal-polynomial modules retain 193 admissions. No other chapter was changed. The [DLMF coverage checklist](AAR/OrthogonalPolynomials/DLMFCoverage.md) records the remaining acquired statements.

Remaining admitted declarations in the five edited modules:

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

- `jacobi_differential_equation`
- `gegenbauer_differential_equation`
- `legendre_differential_equation`
- `laguerre_differential_equation`
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
- `jacobi_derivative`
- `jacobi_lowering_derivative`
- `jacobi_raising_derivative`
- `gegenbauer_derivative`
- `laguerre_derivative`
- `jacobi_weighted_derivative`
- `gegenbauer_weighted_derivative`
- `chebyshevU_weighted_derivative`
- `laguerre_weighted_derivative`

### Explicit.lean

- `chebyshevV_cos`
- `chebyshevW_cos`
- `jacobi_binomial_sum`
- `gegenbauer_finite_sum`
- `gegenbauer_cos_sum`
- `chebyshevT_hypergeometric`
- `hermitePhys_finite_sum`
- `jacobi_reflection`
- `jacobi_symmetric_even_at_zero`
- `gegenbauer_reflection`
- `gegenbauer_even_at_zero`
- `hermitePhys_even_at_zero`
- `chebyshevV_reflection`
- `chebyshevW_reflection`
- `chebyshevT_eq_jacobi`
- `jacobi_quadratic_even`
- `jacobi_quadratic_odd`
- `gegenbauer_quadratic_even`
- `gegenbauer_quadratic_odd`
- `chebyshevU_quadratic`
- `chebyshevT_quadratic`
- `hermitePhys_even_eq_laguerre`
- `hermitePhys_odd_eq_laguerre`
- `chebyshevT_discrete_orthogonality`
- `chebyshevT_finite_sum`
- `chebyshevU_finite_sum`

### GeneralIdentities.lean

- `hankelDeterminant_pos`
- `zeros_interlace`
- `symmetric_measure_parity`
- `kernel_polynomials_orthogonal`
- `monic_moment_determinant`
- `monic_diagonal_moment_determinant`
- `monic_offdiagonal_moment_determinant`
- `compact_support_L2_expansion`

### Associated.lean

- `associatedPollaczek_limit_laguerre`
- `associatedPollaczek_limit_hermite`
- `besselPolynomial_eq_laguerre`
- `besselPolynomial_recurrence`
- `besselPolynomial_differential_equation`
- `besselPolynomial_finite_orthogonality`
- `jacobi_limit_besselPolynomial`
- `pollaczek_finite_sum`
- `pollaczek_generating_function`
- `pollaczek_eq_gegenbauer`
- `pollaczek_eq_meixnerPollaczek`
- `laguerre_negative_integer_parameter`
- `exceptionalLaguerre_orthogonality`
- `exceptionalLaguerre_differential_equation`
- `exceptionalHermite_orthonormal`
- `pollaczek_orthogonality`
- `morsePolynomialFunction_ode`
- `morsePolynomialFunction_orthogonality`

## Validation

- `#print axioms` checked all 30 newly completed theorems during a root build. Every result depends only on `propext`, `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`. Temporary audit commands were removed. The audit output is preserved at `/tmp/aar-proof-op-axioms.txt`.
- `lake build > /tmp/AAR-build.log 2>&1`: passed after removing audit commands, 3788 jobs.
- `lake env lean AAR/OrthogonalPolynomials/<file>.lean`: passed separately for `Hahn`, `Differential`, `Explicit`, `GeneralIdentities`, and `Associated`.
- `git diff --check`: passed. Since these working files are untracked, snapshot comparisons and a separate trailing-whitespace check were also used; they passed.
- `rg -n '\bsorry\b' AAR/OrthogonalPolynomials --glob '*.lean'`: 304 remaining admissions; the listing is saved in `/tmp/aar-proof-op-remaining.txt`. Across `AAR`, 452 remain.
- All original theorem headers were compared with the pre-edit snapshots and preserved. The other orthogonal-polynomial Lean files are byte-for-byte unchanged. `Scratch.lean` is absent.
- The existing `.lake` symlink and toolchain were preserved. No commits were made.
