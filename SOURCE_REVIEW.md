# Comparison of the five counterexamples with AAR

This follow-up checks the five examples from the initial review against the supplied scans.
OCR was used to locate passages; the defining formulas and relevant hypotheses were then
checked visually. Page numbers below are the printed book pages. The corresponding chapter-PDF
page numbers are included to make the passages easy to find.

The four still-false declarations have been replaced in place. `qGamma_one` had already been
corrected in the initial pass. The obsolete `AAR/Review/Counterexamples.lean` module has been
removed. The other formulation findings were outside this five-case check; their subsequent
source review and corrections are recorded in `FORMULATION_REVIEW.md`.

| Case | AAR source | Assessment | Current Lean formulation |
| --- | --- | --- | --- |
| `qGamma_one` | §10.3, (10.3.3), pp. 493–494; Chapter 10 PDF pp. 13–14 | The old `q ≠ 1` hypothesis lost AAR's explicit `|q| < 1` restriction. | Retained the proved statement with `‖q‖ < 1`; added the precise source reference. |
| `qGamma_add_one` | Definition and pole discussion on p. 493; functional equation on p. 494 | The original Lean statement treated a meromorphic identity as an equality of totalized values at poles. It also admitted `q = 0`. | Added `q ≠ 0` and `∀ n : ℕ, q^(x+n) ≠ 1`, and proved the recurrence. |
| `confluentM_kummer_transform` | (4.1.11), p. 191, Chapter 4 PDF p. 5; standing parameter restriction on p. 62, Chapter 2 PDF p. 2 | Lean omitted the standing restriction on the denominator parameter. The supplied AAR printing also has a denominator typo in (4.1.11). | Added `∀ k : ℕ, c ≠ -k`; retained the intended denominator `c` on both sides. Proof remains open. |
| `spherical_addition` | (9.4.4), p. 452, and Theorem 9.6.3 / (9.6.6), p. 456; Chapter 9 PDF pp. 8 and 12 | The zero summands and absent harmonic-family hypotheses were transcription errors. AAR's theorem uses genuine surface measure. | Supplies `2k+1` real homogeneous harmonic polynomials, orthonormal for surface measure, and sums their evaluation products. Proof remains open. |
| `siegel_inequality` | Theorem 8.6.2 and (8.6.2)–(8.6.4), p. 420; Chapter 8 PDF p. 20; proof pp. 421–422 | The interval-spacing inequality was not AAR's theorem. It was an unrelated false placeholder. | Replaced it with Siegel's refinement of the arithmetic–geometric mean inequality, including `P_n`, `Q_n`, `Δ`, and the positive root parameter. General proof remains open; the two-variable equality is proved. |

## q-gamma: domains and meromorphic values

[AAR Chapter 10](References/AAR1999Chapter10.pdf), p. 493, first introduces the factorial
interpolation with `0 < q < 1`, then gives the complex-power definition (10.3.3) under the
printed condition `|q| < 1`. It specifies principal powers and explicitly discusses poles.
The normalization and recurrence appear in the Bohr–Mollerup discussion on p. 494.

The normalization `Γ_q(1) = 1` is correctly represented by the existing theorem with
`‖q‖ < 1`. Its Lean definition also evaluates to 1 at `q = 0`; no exclusion is needed for
this particular statement.

For the recurrence, the corrected pointwise domain is

- `‖q‖ < 1`;
- `q ≠ 0`;
- `q^(x+n) ≠ 1` for every natural `n`.

The last condition excludes the vanishing factors of `(q^x;q)_∞`. It is the direct
product-form description of the poles discussed by AAR. For nonzero `q`,
`q^(x+n) = q^x q^n`. These conditions also keep `x+1` away from the poles.

A qualification in the source deserves an explicit note: the display `|q| < 1` in (10.3.3)
literally includes zero, whereas the subsequent meromorphic discussion and pole formula
involving `log q` require nonzero `q`. Also, the functional equation does not repeat the
regular-point domain. These are implicit domain conventions in the surrounding discussion,
not evidence that AAR claims an equality of finite complex values at poles. Lean needs
those conditions explicitly because division by zero and powers of zero are totalized.

`qPochhammerInf_shift` now proves the first-factor identity using Mathlib's
`tprod_eq_zero_mul'`. Together with nonvanishing of the product and the complex-power
addition rule, it gives a complete proof of `qGamma_add_one`.

## Kummer: a missing Lean restriction and a printed AAR typo

[AAR Chapter 2](References/AAR1999Chapter02.pdf), p. 62, excludes zero and negative integers
from denominator parameters in the definition of generalized hypergeometric series. This
standing restriction applies to the denominator `c` of the confluent series as well.
The former unrestricted Lean declaration did not encode it.

In the supplied [Chapter 4 scan](References/AAR1999Chapter04.pdf), p. 191, equation (4.1.11)
prints the right-hand confluent function with upper parameter `c-a` and lower parameter `a`.
The intended lower parameter is **`c`**:

\[
M(a,c,z)=e^z M(c-a,c,-z),\qquad c\notin\{0,-1,-2,\ldots\}.
\]

This correction follows from the Pfaff transformation printed immediately above it: taking
the confluent limit does not change the denominator parameter. It can also be checked from
the coefficient of `z`. The original Lean formula already used `c`, so its repair is the
explicit parameter hypothesis; the book's separate typographical error is now recorded in
the theorem's docstring. No restriction on `z` is needed for these entire confluent series.

## Spherical addition: restore the actual harmonic family

[AAR Chapter 9](References/AAR1999Chapter09.pdf), p. 452, defines the real inner product by
integration against surface measure. Theorem 9.6.3 on p. 456 uses an orthonormal set with the
full dimension of the degree-`k` harmonic space. For three variables this is `2k+1`, and the
unit sphere has area `4π`. The specialization is

\[
\frac{2k+1}{4\pi}P_k(x\cdot y)
  =\sum_{m=1}^{2k+1}S_m(x)S_m(y).
\]

The corrected declaration takes real polynomials `S_m`, their harmonicity and homogeneity
hypotheses, and orthonormality for the new `sphericalHarmonicInner`. This definition uses
Mathlib's `Measure.toSphere` applied to canonical Euclidean volume. It does not restrict
ambient volume to a null sphere. The real formulation needs no complex conjugation;
evaluations are cast into `ℂ` only to match this project's `legendreP` codomain.

`sphericalHarmonicInner_one_three` proves that the inner product of the constant polynomial
1 with itself is `4π`. This confirms the normalization in the corrected addition statement.
There is no defect in the AAR theorem in this case. Other pre-existing sphere-integral
declarations have not been silently changed as part of this correction.

## Siegel: restore the theorem from §8.6

[AAR Chapter 8](References/AAR1999Chapter08.pdf), p. 420, defines

\[
P_n(t)=\frac1{n!}\prod_{k=0}^{n-2}
       \left(\frac{t+k}{n-k}\right)^{n-k-1},\qquad
Q_n(t)=\prod_{k=1}^{n-1}\left(1+\frac{n-k}{t+k-1}\right),
\]

and `Δ = ∏_{i<j}(x_i-x_j)^2`. For `n ≥ 2`, positive `x_i`, and `Δ ≠ 0`, the parameter
`μ > 0` is determined by

\[
P_n(\mu)=\frac{(\prod_i x_i)^{n-1}}{\Delta}.
\]

The theorem is

\[
\left(\frac{\sum_i x_i}{n}\right)^n
\geq \left(\prod_i x_i\right)Q_n(\mu).
\]

The definitions `siegelP`, `siegelQ`, and `siegelDiscriminant`, and the replacement theorem
now match these formulas. The positive root is supplied as a parameter with its defining
equation, rather than chosen by a nonconstructive definition. Existence and uniqueness of
that root, and the general inequality proof, remain future work. No defect in the statement
of AAR Theorem 8.6.2 was found.

`siegel_inequality_two` proves the exact two-variable equality from the defining equation
and nonzero denominators, without using the unfinished general theorem. Thus the first
nontrivial index size has also been verified algebraically.

## Validation

- `lake build` from the Lake root: passed (3675 jobs).
- `lake env lean AAR/QSeries/Pochhammer.lean`: passed.
- `lake env lean AAR/Confluent/Basic.lean`: passed.
- `lake env lean AAR/SphericalHarmonics/Basic.lean`: passed.
- `lake env lean AAR/SphericalHarmonics/Theorems.lean`: passed.
- `lake env lean AAR/Selberg/Applications.lean`: passed.
- `git diff --check`: passed. Since the sources were already untracked, a separate direct
  whitespace check also covered every modified/new file and passed.
- At the end of this source-check pass, `rg -n '\bsorry\b' AAR` found 91 occurrences,
  down from 92. Subsequent proof progress and the current inventory are in `REVIEW.md`.
- `#print axioms` for `qPochhammerInf_shift`, `qGamma_one`, `qGamma_add_one`,
  `sphericalHarmonicInner_one_three`, and `siegel_inequality_two`: only `propext`,
  `Classical.choice`, and `Quot.sound`; none depends on `sorryAx`.
- The replaced declarations' types were checked after building. The corrected Kummer,
  spherical-addition, and general Siegel proofs remain `sorry`; they are corrected targets,
  not claimed completed formalizations.
- The obsolete counterexample declarations are absent. No `Scratch.lean` remains, the
  intentional `.lake` symlink is unchanged, and no commits were made.
