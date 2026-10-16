# Special Functions following Andrews, Askey, and Roy (1999)

A Lean 4 formalization of AAR.

## Organization

The library follows the chapter arrangement of AAR, supplemented by related material from
the NIST Digital Library of Mathematical Functions (DLMF). Its aim is to fill gaps in
Mathlib's coverage of special functions, not to reproduce either source sequentially. Each
umbrella module `AAR/<Area>.lean` describes what Mathlib already provides and what the
area adds. Statements taken from the DLMF record their equation numbers with Mathlib's
`@[dlmf]` cross-reference attribute.

| Area | AAR chapters | DLMF chapters | Submodules |
| --- | --- | --- | --- |
| `Gamma` | 1 | 5 | 23 |
| `Hypergeometric` | 2–3 | 15 | 20 |
| `Confluent` | 4.1–4.4 | 13 | 17 |
| `Bessel` | 4.5–4.15 | 10 | 11 |
| `Legendre` | (Temme 8) | 14 | 5 |
| `Statistical` | (Temme 11) | 7–8 | 3 |
| `Elliptic` | (Temme 12) | 19, 20, 22 | 4 |
| `WaveEquation` | (Temme 10) | | 1 |
| `Polylog` | (Duverney 8) | 25 | 3 |
| `Constants` | (Duverney 2, 8) | 25 | 3 |
| `OrthogonalPolynomials` | 5–7 | 18 | 18 |
| `Selberg` | 8 | | 2 |
| `SphericalHarmonics` | 9 | | 2 |
| `QSeries` | 10 | | 2 |
| `Partitions` | 11 | | single file |
| `Bailey` | 12 | | single file |

`AAR.lean` imports all areas.

## Status

Many statements are admitted (`sorry`) and remain proof obligations; the proved
declarations do not depend on them. Confluent functions and orthogonal polynomials hold
most of the admissions. Not every admitted statement has been checked for correctness:
statements found to be false or weaker than intended are repaired as they are reviewed.

## Dependencies and upstream reuse

The project uses Lean `v4.35.0-rc3`, Mathlib revision
`5e0c4e5239cb0a2d86d68a884bf52cfd963fce22`, and TauCeti revision
`a780c7ad6beb23f60a17351a492d177878020ad5`, matching the companion projects.
Prefer **Mathlib, then TauCeti, then local code**, preserving theorem hypotheses and the
meaning of each special-function definition. Import the particular TauCeti module;
`import TauCeti` is not a library umbrella.

See [TauCetiReview.md](TauCetiReview.md) for checked reuse candidates and the review's limits,
and [CREDITS.md](CREDITS.md) for related-work credits. The first six adaptations are implemented, including proofs of
both Hermite Fourier eigenfunction identities and compact-support Parseval. A later
pass (2026-10-05) proved 35 further admissions in the Gamma and orthogonal-polynomial
chapters (see [TauCetiReview.md](TauCetiReview.md)). A further pass (2026-10-07)
repaired the Gamma sine integral and two finite
Kummer–Bessel statements, and proved all ten theorems in priority groups 1–4:
the two Kummer zero results, compact-support expansion and kernel orthogonality,
three Hermite integrals, and three parameter/Euler integrals. The project-wide pass
on 2026-10-08 proved the Whittaker M pole limit, the `q`-Gegenbauer classical limit,
and both Laguerre fractional integrals, and repaired a missing parameter bound in
the Whittaker W Bessel-K integral. The next priority pass proved the Jacobi fractional
integral, both Rodrigues formulas, Legendre orthogonality, the unweighted Laguerre
convolution, the regularized Kummer Laplace self-transform, and the closed Whittaker M
Laplace transform. It also established convergence of Tricomi's Laplace kernel in the
full stated region and its `b = a + 1` specialization. The continuation pass proved
the weighted Laguerre convolution, the Jacobi squared norm, and Gegenbauer
orthogonality. Supporting lemmas now give the general Kummer transform when
`‖k‖ < Re z` and Tricomi's Laplace representation for every `b = a + N + 1`,
with nonnegative integer `N`. The full half-plane Kummer transform is now proved
using a polynomial exponential growth bound and holomorphic continuation, with
all denominator parameters retained. Tricomi's full Laplace representation is now
proved by a Gauss confluence limit, holomorphic continuation in the argument,
and continuity in the second parameter, including integer parameters. The
Whittaker W Laplace representation follows by an affine substitution. These
complete the remaining integral priorities without changing their statements.
Tricomi's Mellin transform is also proved throughout its original convergence
strip, with a separate absolute-integrability theorem. A Gamma pass on 2026-10-15,
guided by Temme's *Special Functions* (Wiley, 1996), Chapter 3, proved 24 further
admissions: Binet's three formulas for `log Γ`, the remaining digamma and
Euler-constant integrals of DLMF §5.9, Prym's and the Cauchy–Saalschütz
representations, the oscillatory and Fresnel-type Gamma integrals, derivatives and
integrals of `Γ` in its argument, Stirling's series for `log Γ`, `ψ` and `ψ⁽ⁿ⁾`, the
modulus and balanced Gamma products, and four Gamma inequalities. It also corrected
the bracketing of `Gamma_incomplete_sum`. A confluent pass, following Temme's Chapter 7,
derived Tricomi's and Kummer's asymptotic expansions from Watson's lemma (proving six
admissions in `AAR.Confluent.Asymptotics`) and added admission-free modules for the
incomplete Gamma functions, the exponential, sine and cosine integrals, parabolic cylinder
functions, the Fresnel and Dawson integrals, and Coulomb wave functions. A further pass on
Temme's §§6.8–6.9 proved Laplace's integral for Legendre polynomials and added modules on
Legendre bounds, expansions and large-degree asymptotics and on Chebyshev expansions. Laplace's
integral for Gegenbauer polynomials and the exponential generating function of Legendre
polynomials are now proved. Tricomi's expansion is extended to complex sectors
`|arg z| ≤ π - ε`, which gives the asymptotics of the auxiliary Fresnel functions and of the
Coulomb functions `H^±`. The connection formula 13.2.41 and the Wronskians derived from it
(13.2.24–13.2.25, 13.2.35, 13.2.37–13.2.38) are proved. These give the irregular Coulomb
function `G_ℓ`, `H^±_ℓ = G_ℓ ± iF_ℓ`, the Coulomb Wronskian and the limits `F_ℓ ~ sin θ_ℓ`,
`G_ℓ ~ cos θ_ℓ`. Bounds for `Γ` on vertical lines and Mellin inversion give the Barnes
integrals for `₂F₁`, `𝐌`, `U`, `W` and AAR Theorem 4.2.1. The two-sided expansion 13.7.2 and the
Whittaker connection formula are proved. New results include the loop integral 15.6.2 and the
generalized hypergeometric equation. There are
now 266 remaining source admissions; see [REVIEW.md](REVIEW.md) for the current inventory and the corrected
statements.

## Supporting library `ToMathlib`

General results that the special-function library uses, following Temme's *Special
Functions* (Wiley, 1996), Chapters 1–2, and written for eventual contribution to Mathlib:

* `ToMathlib.NumberTheory.EulerPolynomials`: Euler polynomials and numbers, the difference
  equation `Eₙ(x+1) + Eₙ(x) = 2xⁿ`, the Appell property, reflection, alternating power sums,
  and the Euler-number recurrence.
* `ToMathlib.Analysis.EulerMaclaurin`: the Euler–Maclaurin formula with remainder.
* `ToMathlib.Analysis.BooleSummation`: Boole's alternating summation formula.
* `ToMathlib.Analysis.Asymptotics.AsymptoticExpansion` and `.Watson`: Poincaré asymptotic
  expansions and Watson's lemma, also with a complex exponent. In `AAR.Gamma.Asymptotics`
  they give Stirling's series for `log Γ` as an asymptotic expansion
  (`hasAsymptoticExpansion_log_Gamma`); in `AAR.Confluent` they give the expansions of
  Tricomi's and Kummer's functions and of the functions derived from them.
* `ToMathlib.Analysis.Asymptotics.WatsonSector`: Watson's lemma for complex `z → ∞` in a
  sector `δ|z| ≤ re z`, and the Gamma integral `∫₀^∞ u^{s-1} e^{-zu} du = Γ(s) z^{-s}`.
* `ToMathlib.Analysis.Complex.RotateRay`: rotation of a ray integral `∫₀^∞ f` to the ray
  `arg t = α`, from Cauchy's theorem for rectangles.
* `ToMathlib.Analysis.Integral.Laplace`: quantitative Laplace asymptotics, copied from
  `lean-codes`.

`ToMathlib` imports Mathlib only and contains no admissions.

## Building

Run `lake build` from the repository root. The existing `.lake` symlink to the
local-disk cache is intentional and must not be replaced or retargeted.

Build outputs remain in `.lake/build-AAR`, separate from companion projects.
