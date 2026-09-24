# DLMF Chapter 13 acquisition inventory

Reviewed against the live [NIST DLMF Chapter 13](https://dlmf.nist.gov/13) on
2026-09-17 (Version 1.2.8, release 2026-09-15) and the project's local Mathlib
**v4.34.0** sources.

This inventory covers numbered equations in §§13.2–13.26. Notation §13.1,
applications §§13.27–13.28, and computation §§13.29–13.32 were not acquired.
Graphics are excluded.

## What was added

New modules under `AAR/Confluent/` record tagged statements for Kummer `M`,
Tricomi `U`, and Whittaker `M_{κ,μ}`, `W_{κ,μ}`. Tricomi's function is defined
by the connection formula [13.2.42](https://dlmf.nist.gov/13.2.E42). Olver's
regularized `𝐌` is Mathlib's `regularizedHGFun {a} {b}` and is not duplicated.
Existing project theorems were tagged rather than copied. Statements already
supplied by Mathlib are identified in [MathlibCoverage.lean](MathlibCoverage.lean)
and below, without duplicate project declarations.

Newly acquired identities are admitted (`sorry`) unless they were already proved
in `Basic.lean` or `Whittaker.lean`. No AAR source statement was changed.

## Interpretation and domain restrictions

- `confluentM` is the totalized series. Nonpositive integer denominators are
  excluded by standing hypotheses `∀ k : ℕ, b ≠ -k`, matching AAR §2.1.
- `confluentU` is the Gamma connection formula, polar at integer `b`. Integer-`b`
  logarithmic cases are recorded as limits or explicit series.
- Complex powers use principal branches. Slit-plane hypotheses specify those
  branches. Several formulas are acquired on convenient real rays (`x > 0`) or
  real parameter ranges; those are restricted forms of the source statements.
- Continued fractions use Mathlib `GenContFract` on a real subdomain, as in
  DLMF Chapter 15.
- Remainders use Mathlib `Asymptotics.IsBigO`. Leading terms also appear as
  `Tendsto` statements.

“Deferred” means the equation was reviewed but no formal theorem was introduced
because the required function, contour, or turning-point API is absent.

## Mathlib coverage

In `Mathlib/Analysis/SpecialFunctions/RegularizedHypergeometric.lean`:

- `regularizedHGFun {a} {b}` is Olver's `𝐌(a,b,z)` ([13.2.3](https://dlmf.nist.gov/13.2.E3)).
- Infinite radius for `p ≤ q` includes the confluent case.
- Empty-denominator series supplies `{}_2F_0` in [13.6.21](https://dlmf.nist.gov/13.6.E21).

Mathlib has no named Kummer `M`, Tricomi `U`, Whittaker pair, incomplete gamma,
or error function. Project definitions `errorFn`, `lowerIncompleteGamma`,
`erfcFn`, and `GammaInc` are used in §13.6 and §13.18.

## Existing tagged project results

| Equation | Existing declaration |
| --- | --- |
| 13.2.E1 | `confluentM_ode` |
| 13.2.E2 | `confluentM` |
| 13.2.E4 | `confluentM_eq_mul_regularizedHGFun` |
| 13.2.E39 | `confluentM_kummer_transform` |
| 13.3.E15 | `deriv_confluentM_regular` in `OrthogonalPolynomials/Differential.lean`; restated in `Recurrence.lean` |
| 13.4.E1 | `confluentM_eq_euler_integral` (the `M` form); regularized form in `IntegralRepresentations.lean` |
| 13.6.E1 | `confluentM_self` |
| 13.6.E3 | `confluentM_of_zero_param`; `U` form in `Relations.lean` |
| 13.6.E5 | `lowerIncompleteGamma` |
| 13.6.E7 | `errorFn` |
| 13.14.E1 | `whittakerM_ode`, `whittakerW_ode` |
| 13.14.E2 | `whittakerM` |
| 13.14.E33 | `whittakerW` |

## Deferred infrastructure

| Equations | Reason |
| --- | --- |
| 13.2.E27–E32 | Integer-`b` second-kind logarithmic tables; generic case is 13.2.E9 |
| 13.4.E9–E15, 13.10.E8–E9, 13.16.E10, 13.23.E6–E7 | Hankel, Pochhammer, and loop contours |
| 13.7.E5–E9, 13.7.E11–E13 | Remainder-region constants `R₁,R₂,R₃`, `χ(n)`, incomplete-gamma remainder |
| 13.8.E4–E5, 13.8.E8–E16 | Uniform parabolic-cylinder / Bessel / `envJ` approximations |
| 13.6.E11, 13.18.E10 | Airy function not in the project API |
| 13.6.E12–E15, 13.18.E11–E13 | Parabolic cylinder `U(a,z)` (DLMF Chapter 12) |
| 13.6(vii) Coulomb | Coulomb wave functions (DLMF Chapter 33) |
| 13.9.E8, 13.22.E1 | Indexed Bessel zeros `j_{ν,r}` |
| 13.20, 13.21 | Uniform Airy/Bessel turning-point expansions in `μ` and `κ` |
| 13.23.E13–E14 | Mellin inversion pair for a general transform `f` |

## Equation-by-equation index (summary)

Names introduced here live in `AAR.Confluent` except the existing root-namespace
definitions in `Basic.lean` and `Whittaker.lean`.

### Kummer functions

| Section | Tagged / numbered | Notes |
| --- | ---: | --- |
| [13.2](https://dlmf.nist.gov/13.2) | 40 / 44 | E3 is Mathlib. E27–E32 deferred as the integer table. E24–E26 as Wronskian nonvanishing. |
| [13.3](https://dlmf.nist.gov/13.3) | 29 / 29 | Contiguous relations, derivatives, operator identity. |
| [13.4](https://dlmf.nist.gov/13.4) | 12 / 18 | E9–E15 contours deferred. Barnes vertical lines acquired. |
| [13.5](https://dlmf.nist.gov/13.5) | 4 / 4 | Real-domain continued fractions. |
| [13.6](https://dlmf.nist.gov/13.6) | 16 / 23 | Airy, parabolic cylinder, Coulomb deferred. |
| [13.7](https://dlmf.nist.gov/13.7) | 5 / 13 | Poincaré expansions; remainder regions deferred. |
| [13.8](https://dlmf.nist.gov/13.8) | 6 / 18 | Large-`b` series and transition; uniform Bessel deferred. |
| [13.9](https://dlmf.nist.gov/13.9) | 14 / 16 | Zero counts and large-zero asymptotics; Bessel-zero expansion deferred. |
| [13.10](https://dlmf.nist.gov/13.10) | 14 / 16 | Loop integrals deferred. |
| [13.11](https://dlmf.nist.gov/13.11) | 4 / 4 | Bessel series and coefficient recurrence. |
| [13.12](https://dlmf.nist.gov/13.12) | 1 / 1 | Product identity. |
| [13.13](https://dlmf.nist.gov/13.13) | 12 / 12 | Addition theorems. |

### Whittaker functions

| Section | Tagged / numbered | Notes |
| --- | ---: | --- |
| [13.14](https://dlmf.nist.gov/13.14) | 24 / 35 | Definitions, connections, Wronskians, leading limits. Logarithmic integer-order tables and some `z→0` cases overlap 13.2. |
| [13.15](https://dlmf.nist.gov/13.15) | 26 / 26 | Contiguous relations and derivatives. |
| [13.16](https://dlmf.nist.gov/13.16) | 10 / 12 | Real-line integrals; one Barnes contour deferred. |
| [13.17](https://dlmf.nist.gov/13.17) | 4 / 4 | Real-domain continued fractions. |
| [13.18](https://dlmf.nist.gov/13.18) | 12 / 17 | Airy and parabolic cylinder deferred. |
| [13.19](https://dlmf.nist.gov/13.19) | 2 / 3 | Poincaré expansions on the positive ray; sector form 13.19.2 recorded via 13.7.2 analogue. |
| [13.20](https://dlmf.nist.gov/13.20) | 0 / 19 | Deferred: uniform Airy/Bessel in `μ`. |
| [13.21](https://dlmf.nist.gov/13.21) | 0 / 25 | Deferred: uniform Airy/Bessel in `κ`. |
| [13.22](https://dlmf.nist.gov/13.22) | 0 / 1 | Deferred: Bessel-zero expansion. |
| [13.23](https://dlmf.nist.gov/13.23) | 10 / 14 | Loops and inversion pair deferred. |
| [13.24](https://dlmf.nist.gov/13.24) | 3 / 3 | Bessel series and generating function. |
| [13.25](https://dlmf.nist.gov/13.25) | 1 / 1 | Product identity. |
| [13.26](https://dlmf.nist.gov/13.26) | 12 / 12 | Addition theorems. |

## Modules

| Module | Theorems | Definitions | Current `sorry`s |
| --- | ---: | ---: | ---: |
| [Basic.lean](Basic.lean) | 29 | 5 | 2 (pre-existing Barnes integral and parabolic zero-free region) |
| [BasicProperties.lean](BasicProperties.lean) | 35 | 1 | 35 |
| [Whittaker.lean](Whittaker.lean) | 23 | 2 | 19 |
| [Recurrence.lean](Recurrence.lean) | 55 | 1 | 55 |
| [IntegralRepresentations.lean](IntegralRepresentations.lean) | 21 | 0 | 21 |
| [ContinuedFractions.lean](ContinuedFractions.lean) | 4 | 8 | 4 |
| [Relations.lean](Relations.lean) | 30 | 2 | 30 |
| [Asymptotics.lean](Asymptotics.lean) | 13 | 2 | 13 |
| [Zeros.lean](Zeros.lean) | 15 | 2 | 15 |
| [Integrals.lean](Integrals.lean) | 24 | 0 | 24 |
| [Series.lean](Series.lean) | 6 | 3 | 6 |
| [ProductsAddition.lean](ProductsAddition.lean) | 26 | 0 | 26 |
| [MathlibCoverage.lean](MathlibCoverage.lean) | 0 | 0 | 0 |

The acquisition introduced Tricomi's `U` and complementary error/incomplete-gamma helpers, together with about 250 tagged statements. All new identities are admitted except the previously proved theorems in `Basic` and `Whittaker`.
