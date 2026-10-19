# Project instructions — lean-AAR

Before working, read and follow [the shared Lean instructions](../lean-codes/AGENTS.common.md),
then apply the project-specific rules below. Resolve that path relative to this file.
Local rules take precedence over the shared defaults. If the shared file is unavailable,
report that fact rather than proceeding without it.

## Build settings

- Lake root: the directory containing this `AGENTS.md`.
- Build output: `.lake/build-AAR`; preserve the matching `buildDir` in `lakefile.toml`.
- Ordinary build command: `lake build > /tmp/AAR-build.log 2>&1`.

## Project

This project is to formalize the content of Special Functions by Andrews, Askey and Roy
(henceforth AAR) and related content from the NIST Digital Library of Mathematical
Functions (DLMF).
The PDF source for the entire AAR book and for separate chapters is in the References
subdirectory. The other directories contain Lean code, more or less following the
arrangement in AAR.
Our concern is with results in AAR and DLMF that are not yet in Mathlib. We do not insist
on a faithful sequential reproduction of AAR or DLMF. Instead, we use those sources to
identify gaps in the special functions coverage of Mathlib and then we attempt to fill in
those gaps.

## Dependencies and import layers

- `ToMathlib/` holds general results that are not specific to special functions
  (Euler polynomials, Euler–Maclaurin and Boole summation, asymptotic expansions,
  Watson's lemma, Laplace asymptotics), in the namespaces of the Mathlib APIs they extend.
  `ToMathlib` imports Mathlib only, never `AAR`; `AAR` modules may import `ToMathlib`.
  A `ToMathlib` file that also exists in `../lean-codes/ToMathlib` (currently
  `Analysis/Integral/Laplace.lean` and `Analysis/Complex/Carlson.lean`) must keep identical
  content and path; make changes in lean-codes and copy them here.

Mathlib and TauCeti are allowed throughout the AAR library, including when filling
existing admissions. Preserve complex branches, normalizations, exceptional parameters
and the meaning of totalized series and integrals when adopting upstream statements.

## DLMF statement acquisition

- Cover definitions and mathematical theorems in the selected DLMF scope, including
  results stated in prose. Exclude graphical results and application notes.
- When a result is already in Mathlib, record a comment and a precise pointer to
  the upstream declaration instead of reproving it locally. Preserve any domain
  or branch differences when distinguishing upstream coverage from missing results.
