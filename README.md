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
| `Confluent` | 4.1–4.4 | 13 | 15 |
| `Bessel` | 4.5–4.15 | | 5 |
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
both Hermite Fourier eigenfunction identities and compact-support Parseval. There
are now 382 remaining source admissions (the earlier `REVIEW.md` inventory predates
these three completed proofs).

## Building

Run `lake build` from the repository root. The existing `.lake` symlink to the
local-disk cache is intentional and must not be replaced or retargeted.

Build outputs remain in `.lake/build-AAR`, separate from companion projects.
