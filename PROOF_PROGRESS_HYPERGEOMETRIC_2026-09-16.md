# Hypergeometric proof progress — 2026-09-16

## Result

Removed **15 admissions**. The hypergeometric chapter went from **131 to 116**
`sorry` proof obligations; the project total went from **169 to 154**.
No theorem statements or assumptions changed. No theorem was found or suspected
to be false during this pass. Existing DLMF cross-reference attributes remain.

## Theorems proved

All names below are in `AAR.Hypergeometric`.

| Theorem | DLMF |
| --- | --- |
| [`log_ratio`](AAR/Hypergeometric/Elementary.lean) | [15.4.E2](https://dlmf.nist.gov/15.4.E2) |
| [`successor_binomial`](AAR/Hypergeometric/Elementary.lean) | [15.4.E19](https://dlmf.nist.gov/15.4.E19) |
| [`iteratedDeriv_hypergeometric`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E2](https://dlmf.nist.gov/15.5.E2) |
| [`iterate_mulDerivMul`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E3](https://dlmf.nist.gov/15.5.E3) |
| [`iteratedDeriv_mul_cpow`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E4](https://dlmf.nist.gov/15.5.E4) |
| [`contiguous_ab`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E12](https://dlmf.nist.gov/15.5.E12) |
| [`contiguous_a_b_pred`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E13](https://dlmf.nist.gov/15.5.E13) |
| [`contiguous_a_c_succ`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E14](https://dlmf.nist.gov/15.5.E14) |
| [`contiguous_a_succ_c_pred`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E15](https://dlmf.nist.gov/15.5.E15) |
| [`contiguous_a_pred_c_succ`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E16](https://dlmf.nist.gov/15.5.E16) |
| [`contiguous_a_pred_c_pred`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E17](https://dlmf.nist.gov/15.5.E17) |
| [`contiguous_c_three`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E18](https://dlmf.nist.gov/15.5.E18) |
| [`contiguous_diagonal`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E19](https://dlmf.nist.gov/15.5.E19) |
| [`deriv_contiguous_c_succ`](AAR/Hypergeometric/Derivatives.lean) | [15.5.E21](https://dlmf.nist.gov/15.5.E21) |
| [`one_first_ode`](AAR/Hypergeometric/Solutions.lean) | [15.10.E4](https://dlmf.nist.gov/15.10.E4) |

## Proof structure

- The nth derivative follows by induction, using equality on a neighborhood,
  the proved first derivative, and Pochhammer recurrences.
- The two weighted differentiation identities use principal complex powers on
  the slit plane. The lowering identity derives intermediate denominator
  exclusions from the existing hypothesis on the final shifted parameter.
- All nine remaining contiguous relations in `Derivatives.lean` are now proved.
  Most are algebraic combinations of previously proved relations. A coefficient
  identity establishes the denominator-shift derivative relation; the diagonal
  relation then follows without dividing by either numerator parameter.
- The logarithmic evaluation follows by substituting `-i z` in the existing
  arctangent identity. The successor-binomial evaluation combines the binomial
  specialization with a contiguous relation.
- The local solution around 1 satisfies the Gauss equation by the substitution
  `z ↦ 1-z`. A private coefficient-based helper also handles the regular point
  zero, so the statement needs no additional exclusion at `z = 1`.

## Validation

- Root `lake build > /tmp/AAR-build.log 2>&1` passed after the final changes.
- `lake env lean` passed for `Derivatives.lean`, `Elementary.lean`, and
  `Solutions.lean`.
- An additional build printed the axioms of all 15 theorems: each depends only
  on `propext`, `Classical.choice`, and `Quot.sound`; **none uses `sorryAx`**.
  The temporary audit module was removed, followed by another root build.
- `git diff --check` and explicit whitespace checks passed. Independent
  comparison against pre-edit snapshots confirmed unchanged theorem statements
  and preservation of the other project files. This is necessary because the
  working Lean files are currently untracked by Git.
- `rg -n '\bsorry\b' AAR --glob '*.lean'` was run; the counts above count proof
  admissions, excluding mentions of the word in documentation.

## Remaining hypergeometric admissions

The remaining six in `Derivatives.lean` are `iterate_mulDerivMul_euler`,
`iteratedDeriv_euler`, `iterate_oneSubMulDerivMul`,
`iterate_oneSubMulDerivMul_cpow`, `iteratedDeriv_two_cpow`, and
`iterate_mulDerivMul_eq`. The other remaining obligations include summations,
parameter limits, integrals, continued fractions, transformations, local solutions,
Wronskians, and asymptotics. The equation-level index remains in
[DLMFCoverage.md](AAR/Hypergeometric/DLMFCoverage.md).

| File | Remaining admissions |
| --- | ---: |
| `AnalyticProperties.lean` | 9 |
| `Asymptotics.lean` | 4 |
| `Basic.lean` | 1 |
| `ConnectionFormulas.lean` | 9 |
| `ContinuedFractions.lean` | 3 |
| `Derivatives.lean` | 6 |
| `Elementary.lean` | 22 |
| `EulerIntegral.lean` | 1 |
| `FurtherTransformations.lean` | 21 |
| `Identities.lean` | 4 |
| `IntegralRepresentations.lean` | 5 |
| `Kummer.lean` | 13 |
| `Riemann.lean` | 3 |
| `Solutions.lean` | 13 |
| `Transformations.lean` | 2 |
| **Hypergeometric total** | **116** |
