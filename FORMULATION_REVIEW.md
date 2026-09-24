# Source-level formulation review

This pass addresses every row of the “Further formulation findings” table in `REVIEW.md`.
The supplied chapter scans in `References/` were rendered and OCR-indexed; formulas with
ambiguous OCR, including the connection coefficients and finite-field evaluation, were
checked visually. Page numbers below are printed book pages.

Corrections to Lean transcriptions are recorded here rather than in historical notes beside
the Lean declarations. The Lean text retains notes about deficiencies in AAR itself.
A corrected statement with `sorry` is a proof target, not a completed formalization.

## Corrections corresponding to the review table

| Finding | Source and correction |
| --- | --- |
| Gauss asymptotic at one | Theorem 2.1.3, p. 63, and the standing denominator convention on p. 62. Replaced `Γ(c-a)Γ(c-b)` by `Γ(a)Γ(b)` and excluded nonpositive integer `c`. |
| Euler/Pfaff transformations | Theorem 2.2.5, pp. 68–69. Exchanged the incorrect names. The fractional-linear formulas are now `pfaff_transformation` and `pfaff_transformation_symm`; each requires `‖z/(z-1)‖ < 1` as well as `‖z‖ < 1`. The same-argument formula is `euler_transformation`. AAR explicitly discusses continuation beyond the disk; the Lean function is still a series sum. |
| Dixon's sum and nearby identities | Theorem 3.4.1, p. 143. Removed the spurious `(1+a/2)_n` denominator and supplied regular-parameter hypotheses. The malformed nearby Whipple and Dougall identities were also replaced; see below. |
| Barnes integral for `M` | Theorem 4.2.1, p. 193. Added the missing factor `1/Γ(a)`, a vertical line `s=σ+it` with `-Re a < σ < 0`, its differential `i dt`, the sector `|arg(-z)| < π/2`, `z ≠ 0`, and regular denominator parameter `c`. This represents the straight-contour case of AAR's more general separating contour. |
| Confluent zero-free region | Corollary 4.16.4, p. 234. Replaced the false half-plane claim by `confluentM_ne_zero_of_mem_parabolicRegion`, with real parameters and all three source cases for the parabola parameter. Its region is `-α < Re z` and `(Im z)² < 4α(Re z+α)`. |
| Bessel/Whittaker branch domains | §§4.3, 4.5–4.6, 4.12. Derivative and differential-equation assertions involving nonintegral powers now use `Complex.slitPlane`. The half-order square-root evaluations use that domain too. Whittaker's equations exclude singular confluent parameters; the `W` combination requires `2μ ∉ ℤ`. The `J`–`M` identity also excludes nonpositive integer `2ν+1`. The rotation identity uses `z ≠ 0` and `arg z ≤ π/2`, as in (4.12.2), p. 222, and is now proved. |
| First positive Bessel zero | Restricted the assertion to `StrictMonoOn … (Set.Ici 0)`. The old §4.15 citation was inaccurate: pp. 229–231 concern spacings of successive zeros, rather than monotonicity in the order. No defect in those source results is asserted. The corrected order-monotonicity target remains unproved. |
| General orthogonal-polynomial definition | Definition 5.2.1 and surrounding hypotheses, pp. 244–245. Added integrability and strict positivity of every squared norm. These exclude zero measures, zero constant polynomials, and default-zero nonintegrable integrals. Favard now includes the initial recurrence and `p 0 ≠ 0`, and has a genuine open proof obligation. |
| Christoffel–Darboux normalization | Theorem 5.2.4, p. 246. Restored the squared norm of `p_(n-1)` in the denominator. |
| Parseval assumptions | Theorem 5.7.4, p. 264. Added `MemLp f 2 μ` and bounded interval support for `μ`, matching AAR's finite-interval setting. |
| Laguerre generating function | (6.2.4), p. 283. Replaced `t ≠ 1` by `‖t‖ < 1` and restricted the denominator parameter to the domain of the existing hypergeometric realization. |
| Jacobi completeness | §§5.7 and 6.5. Replaced the zero-norm implication by the actual completeness assertion: an `L²` function whose integrals against every Jacobi polynomial vanish is zero almost everywhere on `(-1,1)`. Added the weighted measure `jacobiMeasure`. |
| Exceptional polynomial parameters | §§6.2–6.4. Retained the existing hypergeometric realizations and explicitly documented their regular-parameter domains. The generating-function and connection identities now have suitable restrictions. No polynomial extension at exceptional parameters is claimed: the totalized definitions outside those domains remain unsuitable as definitions of the classical polynomials. Existing zero-degree identities and the restricted Gegenbauer–Jacobi relation remain proved. |
| Jacobi connection coefficients | Lemma 7.1.1, p. 357. Restored the terminating `₃F₂` factor and prefactor, with real parameters greater than `-1`. The Gamma ratio in the prefactor is expressed as a Pochhammer reciprocal, so the removable exceptional case `k=0`, `α+β=-1` is included. |
| Ultraspherical partial-sum positivity | Corollary 7.6.4, p. 389. The source result uses Cesàro weights `(2λ)_(n-k)/(n-k)!`. Restored these and renamed the target `gegenbauer_cesaro_nonneg`; the former `askey_gasper` name and unweighted sum did not express this result. |
| Sphere integrals | (9.4.4), p. 452, Theorem 9.7.1, pp. 458–459, and §9.9, p. 463. Orthogonality now uses `sphericalHarmonicInner`. Funk–Hecke includes a degree-`k` spherical harmonic, its evaluation at `x`, continuous `f`, and genuine surface measure. Poisson reproduction requires harmonicity in the ball, continuity on its closure, dimension at least two, surface measure, and the sphere-area factor. |
| Selberg convergence | Theorem 8.1.1, p. 402. Require positive `n`, positive real parts of `a,b`, and `1+n Re c > 0`, `Re a+(n-1)Re c > 0`, `Re b+(n-1)Re c > 0`. This multiplication form avoids division by zero at `n=1`. The separate proved beta-integral case remains unrestricted in `c`. |
| Aomoto prefactor | Theorem 8.1.2, p. 402. The zero-based factor is now `(a+(n-1-j)c)/(a+b+(2n-2-j)c)`. Retained the existing sufficient assumption `Re c > 0` and `m ≤ n`, including the empty inserted product. |
| Finite-field Selberg | (8.11.7) and Theorem 8.11.2, pp. 435–438. Replaced the false nonvanishing assertion in the field by the actual complex character-sum evaluation over all monic polynomials of degree `n`. Added an odd field cardinality, character hypotheses, positive integer parameters, and the source's divisibility exclusions. Uses Mathlib's polynomial discriminant and Gauss sums. |
| Bilateral q-Pochhammer | (10.5.2)–(10.5.3), p. 502. Added `qPochhammerInt`, with `(a;q)_(-m)=1/(aq^(-m);q)_m`, and used it in `ramanujan_1psi1`. Added nonzero `q,a` and regularity conditions on shifted factors, as well as the original convergence annulus. This version asserts an identity away from the parameter poles. |
| q-ultraspherical powers | (10.11.1), p. 527. The exponent is now `(n : ℤ)-2k`, preserving negative powers. The docstring identifies the Laurent variable `x=e^(iθ)`, corresponding to the polynomial argument `cos θ`. |

## Related corrections found while checking these clusters

- Kummer's boundary evaluation (Corollary 3.1.2, p. 126) now requires `Re b < 1/2`
  and excludes numerator Gamma poles. The stronger absolute-convergence condition is
  intentional: Lean's unordered `tsum` does not represent a conditionally convergent
  alternating series.
- Restored Gauss's quadratic transformation (3.1.3), p. 125, including the convergence
  component containing zero (`Re z < 1/2` and both series arguments in the disk).
  Both quadratic targets now exclude singular denominator parameters.
- `whipple_7F6` replaces the spurious `whipple_4F3` formula with the terminating
  `₇F₆` to balanced `₄F₃` transformation of Theorem 3.4.4, p. 145. Its denominator
  parameters are explicitly regular.
- `dougall_bilateral` now states the Gamma-form bilateral `₂H₂` evaluation of
  Theorem 2.8.2, p. 110, with its convergence condition and noninteger numerator
  parameters. The former `₅H₅` label and formula were incorrect.
- Gauss quadrature now asserts the existence of positive weights, rather than accepting
  arbitrary weights (Theorem 5.3.2, p. 250).
- The ultraspherical Turán target is now normalized at one; the former unnormalized
  inequality fails already at `λ=1/4`, degree one, `x=1`. Corrected the references
  to Exercises 6.22 and 6.23(b), pp. 342–343.
- Bessel `Y` and `K` now use limits in the order parameter at integer orders, as in
  §§4.6 and 4.12. In particular, `K 0` is no longer defined by division of zero by
  zero. The existence of these limits is not yet a separate proved lemma.
- Nicholson's integral uses `K₀(2x sinh t)`, as in §4.13, p. 224, rather than `cosh t`.
  The integer-order definition is essential here.
- Restored the Gegenbauer polynomial and Gamma factor in Bessel's addition formula
  (4.10.5), p. 215; use positive radii, nonzero distance, and `Re ν > 0`.
  The Bessel generating function excludes `t=0`; Sonine's integral assumes `a>0`.
- Restored the coefficient, shifted degrees/parameters, sine powers, and third angular
  factor in the spherical Gegenbauer addition theorem (9.8.5'), p. 462. The present
  statement uses real `λ>1/2`, avoiding the limiting lower-dimensional cases.
- Corrected the Jacobi theta product's third factor to equal its second factor.
  Heine's transformation now requires convergence of both series and regular
  denominators; the q-beta integral uses real `0<q<1`.

## Deficiencies in the supplied AAR printing

Two further issues warranted notes in Lean:

1. In (9.9.2) and Theorem 9.9.1, p. 463, the printed Poisson denominator contains
   `cos(α·η)`. The dot already denotes the Euclidean inner product (as defined in
   §9.7); the intended denominator is `1-2r(α·η)+r²`. The norm-based Lean kernel
   expresses that intended denominator.
2. Section 8.10, p. 431, specifies only a nontrivial multiplicative character `χ`.
   Section 8.11 identifies `χ^((q-1)/2)` with the quadratic character and uses
   divisibility by `q-1` to test character powers. A character of order `q-1`
   supplies the missing sufficient hypothesis. It is imposed in `selberg_finite_field`.

The previously recorded denominator typo in Kummer's transformation (4.1.11),
p. 191, remains noted in `AAR/Confluent/Basic.lean`. Ordinary transcription-history
notes were removed from the q-gamma, Siegel, and spherical-addition declarations.

## Proof progress and validation

Completed two formerly unfinished results:

- `besselI_eq_besselJ`, on the corrected sector, using Mathlib's complex logarithm
  product formula and exponential identities.
- `errorFn_eq_integral`, for every real endpoint, including negative endpoints.
  The new lemmas `confluentHGCoeff_half`, `confluentM_half_add_two_mul_deriv`, and
  `hasDerivAt_gaussianPrimitive` connect the confluent series to the exponential
  series and then apply Mathlib's fundamental theorem of calculus.

The corrected Favard statement reopens one proof obligation: the previous proof
used the zero measure and proved only the deficient formulation. Thus the explicit
`sorry` count changes from **88 to 87**, not to 86. All other corrected targets
remain open. The current declaration-by-declaration inventory is in `REVIEW.md`.

Validation:

- `lake build` from the Lake root passed (3678 jobs).
- `lake env lean` passed for all 17 edited Lean files.
- Axiom audits of both completed theorems, all three Gaussian helper lemmas, the two
  integer q-Pochhammer evaluation lemmas, and the affected existing completed results
  returned only `propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx`.
- `git diff --check` and a direct whitespace check passed. The source files are
  untracked, so the direct check and comparison against the pre-pass snapshot are
  needed in addition to the git command.
- `rg -n '\bsorry\b' AAR` finds 87 occurrences.
- The `.lake` symlink, toolchain, and dependency versions are unchanged. No
  `Scratch.lean` remains and no commits were made.

This is a formulation review and a proof batch, not a certification of every remaining
unfinished statement in the project.
