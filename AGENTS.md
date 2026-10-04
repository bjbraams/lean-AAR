# Project instructions

## Build topology (do not change)

- Lake root is the directory of this file; this directory is on NFS.
- .lake is a symlink to /export/scratch1/braams/lean-codes-lake on local disk.
- Never replace, delete, or retarget that symlink.
- Never run lake build from a subdirectory as if it were the package root.
- Never copy Mathlib or .lake onto NFS ($HOME).
- Do not “fix” the link because it points outside the repo. That is intentional.
- That lake directory is shared with the companion projects (lean-SCV, lean-CA, lean-codes, lean-LCS).
  They share `.lake/packages` (all pin the same Mathlib), but this project writes its own
  build outputs to `.lake/build-AAR` (`buildDir` in `lakefile.toml`), because Lake's build
  traces include the package name and modules with equal names in different projects would
  otherwise overwrite each other. Keep that `buildDir` setting; never write to or delete
  another project's build directory.
- Do not set `LEAN_PATH`, `LAKE_HOME`, or a custom cache dir unless asked.
- If `.lake` is missing or is no longer a symlink to the path above, stop and ask. Do not
  repair it.
- After every Lean edit: `lake build` from the Lake root.
- For ordinary builds, use lake build > /tmp/AAR-build.log 2>&1; reuse this filename to
  preserve the existing command approval.
- Without LSP/MCP: treat `lake build` output as the only proof-state.
- Do not bump lean-toolchain or Mathlib unless asked.
- Active work: (To be described)

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

## Proof requirements

- Do not introduce axioms.
- Do not replace `sorry` with `by exact Classical.choice ...` or other
  logically equivalent escape mechanisms.
- Search Mathlib first, then the pinned TauCeti modules, before developing substantial
  local theory. Follow the upstream reuse policy below.
- Additional lemmas are welcome when they clarify the mathematical structure.
- Preserve theorem statements unless they are false or require missing
  assumptions.
- If a statement appears false then mark the issue clearly before changing it.
- Pay particular attention to empty, singleton, and nontrivial index types.

## Upstream reuse policy

The order of preference is **Mathlib, then the pinned TauCeti, then local project code**.
Apply this policy throughout the AAR library, including when filling existing admissions.

- Use a suitable Mathlib result before a TauCeti or local version.
- Import the specific TauCeti module providing a suitable result before developing a local
  proof. Prefer imports to copied proofs; `import TauCeti` is not a library umbrella.
- Compare definitions, hypotheses and conclusions before substituting an upstream result.
  Preserve generality, complex branches, convergence regions and normalization conventions.
  Check exceptional parameters, empty and singleton index types, and totalized series/integrals.
- Check for namespace conflicts. Remove redundant local proofs when adopting upstream results;
  small adapters may preserve useful local interfaces without duplicating the mathematics.
- Credit imported results in module headers and at their point of use, with adoption recorded
  in `CREDITS.md`. Resolve TauCeti prerequisites when preparing a Mathlib contribution.
- Validate each proposed use with Lean. An admitted statement or a roadmap entry is not a
  proved upstream result. Check axiom dependencies before declaring an admission resolved.
- Keep TauCeti pinned to the compatible revision in `lakefile.toml`; preserve the common
  Mathlib pin, toolchain and separate build directory unless an update is requested.

Mathlib and TauCeti are allowed external dependencies throughout the project. The shared
`.lake/packages` checkout does not itself register either as a dependency of another project.
Review notes and other new project-wide documentation belong at the repository root.

## Editing

- Keep changes narrowly related to the requested theorem or proof cluster.
- Preserve unrelated user changes.
- Temporary experiments may go in `Scratch.lean`, but remove that file before
  finishing unless asked to retain it.
- Do not commit changes unless explicitly requested.

## Validation

For any lean file `f.lean` that has been changed, run:

    lake env lean f.lean

Also run:

    git diff --check
    rg -n '\bsorry\b' ...

## Completion report

Report:

- which theorems were proved;
- which `sorry`s remain;
- validation commands and their results;
- any changed assumptions;
- any theorem found or suspected to be false.
