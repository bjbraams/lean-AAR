# DLMF Chapters 11, 12 and 14: acquisition and first proofs

Acquired on 2026-10-19 from NIST DLMF version 1.2.8 (2026-09-15):
[Chapter 11, Struve and Related Functions](https://dlmf.nist.gov/11), by R. B. Paris;
[Chapter 12, Parabolic Cylinder Functions](https://dlmf.nist.gov/12), by N. M. Temme;
and [Chapter 14, Legendre and Related Functions](https://dlmf.nist.gov/14), by T. M. Dunster.
The entry modules are [Struve](AAR/Struve.lean),
[ParabolicCylinder](AAR/ParabolicCylinder.lean) and [Legendre](AAR/Legendre.lean).

This is a statement acquisition and first proof pass. A numbered equation being
indexed below means that its mathematical content has a Lean location, with the
qualifications below; it does not certify a proof or full source generality.
The new modules add 198 definitions and abbreviations and 626 initially admitted
theorem statements. Twenty-five statements now have complete proofs, and 601
remain admitted. Definitions contain no `sorry`; definitions made using choice
or removable limits have separate, generally admitted specification theorems.
Their existence and classical interpretation are not established by the definition alone.

The selected scope contains 601 numbered equations: 149 in Chapter 11, 172 in
Chapter 12 and 280 in Chapter 14. Of these, 599 have indexed local declarations,
one has an upstream-only pointer, and one is refuted. This is a count of source
slots, distinct from the theorem count. Bundled identities, prose theorems and
supporting statements account for the difference.

## Scope and exclusions

The acquisition targets definitions and mathematical assertions, including unnumbered
formulas and prose; the remaining domain gaps are itemized below.
Bibliographies, software lists and computational suggestions are
not turned into mathematical theorems merely because they occur in these chapters.
Mathematical error estimates and approximation assertions in computational sections
are included. Graphs and application notes are excluded:

- §§11.3 and 11.12, and the graphics in §11.10(iv).
- §§12.3, 12.16 and 12.17, and the graphics in §12.14(iii).
- §§14.4, 14.22 and 14.31, and the graphics in §14.20(ii).
- §14.30(iv), including application equations 14.30.10–14.30.13.
  The mathematical spherical-harmonic definitions and results of §14.30(i)–(iii) remain included.

## Upstream coverage

Existing Mathlib results receive comments and precise pointers rather than duplicate
local proofs. In particular:

- DLMF 14.7.13: Mathlib's
  [`Polynomial.factorial_mul_shiftedLegendre_eq`](.lake/packages/mathlib/Mathlib/RingTheory/Polynomial/ShiftedLegendre.lean),
  together with the existing normalization bridge
  `AAR.OrthogonalPolynomials.aeval_shiftedLegendre_eq_legendrePolyP`.
  See [IntegerTheory.lean](AAR/Legendre/IntegerTheory.lean).
- The Gamma/Pochhammer coefficient identity in DLMF 12.14.22 is Mathlib's
  `Complex.Gamma_add_nat_div_Gamma_eq`, specialized at `z = 1/2 + i*a` and `n = 2*r`.
  See the comment beside `pcfWCoeff` in [Weber.lean](AAR/ParabolicCylinder/Weber.lean).
  Its local duplicate theorem was removed during the upstream review.
- Mathlib supplies `Complex.besselJ`, `Complex.digamma`, Gamma, Chebyshev and
  probabilists' Hermite polynomials, and inverse hyperbolic functions.
  Existing proved project normalization bridges distinguish those APIs from
  differently normalized or continued functions.

The new proofs extend the pre-existing proved parabolic-cylinder, hypergeometric
continuation and polynomial theory. The existing cylinder core's TauCeti Hermite
derivative dependency is retained; no TauCeti proof source was copied in this pass.

## Formally verified source discrepancies

[DLMF 12.13.6](https://dlmf.nist.gov/12.13.E6) fails at `n = 0`, `z = 0`:
its right side is one, whereas `U(1/2,0) = sqrt(pi/2)` is not one.
[SourceChecks.lean](AAR/ParabolicCylinder/SourceChecks.lean) proves
`pcfU_half_zero_ne_one` and `dlmf_12_13_6_counterexample` using the existing
proved cylinder and error-function theory. The false equation is not admitted.

The left-cut zero rule in [DLMF §14.27](https://dlmf.nist.gov/14.27) predicts
one zero for degree `1`, order `-1/2`. The terminating hypergeometric expression
has its sole algebraic zero at `-1/2`, and neither boundary on `x < -1` can tend
to zero. [SourceChecks.lean](AAR/Legendre/SourceChecks.lean) proves both the exact
formula (`associatedP_one_neg_half`) and the absence of a zero on either boundary
(`dlmf_14_27_no_boundary_zero`). No unqualified version of the printed rule is admitted.
Both counterexamples are independent of the new admissions.

## Mathematical conventions and statement corrections

- Struve entire cores use reciprocal Gamma coefficients. Principal and logarithmic-plane
  variants retain their distinct branches. Small and capital Lommel functions remain distinct.
- Associated Legendre `P`, classical `Q`, regularized Olver `Q`, and Ferrers functions
  remain separate. The inherited power uses separate logarithms of `z-1` and `z+1`;
  replacing them by a principal power of `z*z-1` changes left-half-plane values.
- Continued classical Gauss expressions use the regularized continuation multiplied
  by Gamma, not a totalized power series outside its disk. Exceptional parameter
  identities use limits of whole expressions where Gamma cancellations require them.
- The Fourier series in §14.13 and Dougall's series 14.18.9 use limits of ordered
  finite partial sums. They are not stated as unordered `HasSum` assertions.
  Absolute and conditional convergence assertions are separate.
- The 12.13.5 rotation-addition statement has the endpoint hypothesis
  `t = pi/4 → abs(y.im) ≤ x.re`. The unrestricted complex endpoint convergence
  is still to be assessed; no counterexample to 12.13.5 is claimed here.
- The 14.12.4 cosh integral includes `Re(mu+nu) > -1` to ensure convergence;
  extending by degree symmetry requires a separate statement. The singular
  `theta = pi` endpoint is excluded in 14.20.10.
- Mellin–Barnes cylinder formulas include explicit finite residues when a chosen
  vertical contour crosses poles. Their acquired versions cover arbitrary regular
  parameters, not just the initial separating strip. Hankel rays have the lower-ray,
  counterclockwise-circle and returning upper-ray orientations.
- Anger scaled coefficients use removable limits at `lambda = 1`; literal division
  by `1-lambda^2` would give the wrong totalized value. The initial formulas include
  this removable point. Struve scaled coefficients are polynomial expressions valid
  also at nonzero complex arguments needed in the modified-function expansions.
- Turning-point coordinate values are supplied at endpoints by their removable limits.
  Polynomial coefficient systems and implicit coordinates are defined independently
  of the asymptotic conclusions and have separate existence/uniqueness specifications.
- Bessel envelopes follow DLMF 2.8.32–2.8.34, with their switching points explicitly
  specified. Auxiliary asymptotic normalizers that DLMF characterizes through expansions
  occur as existential witnesses, not as an invented exact normalization.
- The exterior Legendre generating square root is normalized at infinity. Product
  integrals retain parameter limits at negative integral degrees and avoid an
  unnecessary order bound in 14.17.16. Primitive formulas impose `Q` regularity
  only when the selected solution actually contains `Q`.
- Elliptic and one-point continuation is represented by ODE transport along paths,
  not defined to equal the desired connection formula. Gamma phases in Weber theory
  use a continuous lift where required.

## Remaining acquisition gaps and proof priorities

The following domain extensions remain; the equation ledger must be read with them:

- The 11.11 turning-point expansions currently use principal sectors and positive real
  order with bounded complex transition parameter. Additional logarithmic-plane sectors remain.
- The 11.9.7–11.9.8 Bessel series require regular `mu` for their literal Gamma terms;
  negative integral `mu` needs whole-series limits.
- The inverse turning-point expansion 12.10.41 is acquired through its fifth-order
  Taylor polynomial and `O(zeta^6)`. Its full convergence-radius assertion is not yet acquired.
  Exact coefficient degrees and the complete double-asymptotic theory in §12.10
  also need further statements beyond the acquired degree bounds and uniform expansions.
- The 14.3.17 square-hypergeometric identity is acquired for real `x > 1`;
  14.3.18 and the Whipple formulas use right-half-plane domains. Their full inherited
  complex branches and boundary transformations need a continuation API.
- The 14.7.22 `Q` generating identity uses real arguments. The complex extension
  remains. The §14.8 singularity limits currently cover real approaches, with
  the complex extensions mentioned in §14.21 still to acquire.
- The §14.11 degree-derivative series is acquired for `norm(1-z) < 2`;
  continuation of its auxiliary function remains. The §14.28 addition formulas
  impose a principal-domain condition on the composite argument; boundary versions remain.
- The generalized Mehler–Fock transform and inverse are concrete integral definitions,
  with the displayed special identities acquired. A general inversion theorem needs
  an explicit convergence and spectral domain before acquisition.

Recommended next work, in dependency order:

1. Bridge the Struve series to Mathlib's regularized hypergeometric API, then prove
   convergence, calculus, initial values and inhomogeneous ODEs.
2. Prove Weber `W` calculus, initial values and Wronskians; finish the elementary
   cylinder derivatives, recurrences and special-function relations.
3. Prove associated Legendre and Olver `Q` ODE/calculus and the Ferrers connection formulas.
4. Complete the domain extensions above before attempting the long sectorial estimates.
5. Establish coefficient-system existence and uniqueness, turning-point removable
   limits and Sturm zero results, then prove the uniform asymptotic expansions.

## Completed proofs

- [`AAR.Legendre.olverQ_normalization`](AAR/Legendre/Associated.lean#L84)
- [`AAR.Legendre.associatedP_zero_order`](AAR/Legendre/Associated.lean#L91)
- [`AAR.Legendre.associatedQ_zero_order`](AAR/Legendre/Associated.lean#L102)
- [`AAR.Legendre.generalizedLegendre_equal_orders`](AAR/Legendre/Associated.lean#L256)
- [`AAR.Legendre.legendreGaussF_normalization`](AAR/Legendre/Hypergeometric.lean#L34)
- [`AAR.Legendre.ferrersP_nat_polynomial`](AAR/Legendre/IntegerTheory.lean#L33)
- [`AAR.Legendre.legendre_infinite_singular_exponents`](AAR/Legendre/LocalTheory.lean#L44)
- [`AAR.Legendre.legendreQPoly_initial`](AAR/Legendre/Series.lean#L73)
- [`AAR.Legendre.olverQ_nat_normalization`](AAR/Legendre/Series.lean#L94)
- [`AAR.Legendre.associatedP_one_neg_half`](AAR/Legendre/SourceChecks.lean#L25)
- [`AAR.Legendre.dlmf_14_27_no_boundary_zero`](AAR/Legendre/SourceChecks.lean#L56)
- [`AAR.Confluent.pcfD_ode`](AAR/ParabolicCylinder/Basic.lean#L44)
- [`AAR.Confluent.pcfU_entire`](AAR/ParabolicCylinder/Basic.lean#L52)
- [`AAR.Confluent.pcfV_entire`](AAR/ParabolicCylinder/Basic.lean#L68)
- [`AAR.Confluent.pcfV_nat_add_half`](AAR/ParabolicCylinder/Relations.lean#L30)
- [`AAR.Confluent.pcfU_half_zero_ne_one`](AAR/ParabolicCylinder/SourceChecks.lean#L25)
- [`AAR.Confluent.dlmf_12_13_6_counterexample`](AAR/ParabolicCylinder/SourceChecks.lean#L44)
- [`AAR.Confluent.pcfWK_inv`](AAR/ParabolicCylinder/Weber.lean#L81)
- [`AAR.Struve.angerJ_neg`](AAR/Struve/AngerWeber.lean#L143)
- [`AAR.Struve.weberE_neg`](AAR/Struve/AngerWeber.lean#L154)
- [`AAR.Struve.angerJ_zero`](AAR/Struve/AngerWeber.lean#L252)
- [`AAR.Struve.weberE_zero`](AAR/Struve/AngerWeber.lean#L267)
- [`AAR.Struve.angerFG_poch`](AAR/Struve/Asymptotics.lean#L115)
- [`AAR.Struve.lommelA_poch`](AAR/Struve/Lommel.lean#L68)
- [`AAR.Struve.lommelS_neg_order`](AAR/Struve/Lommel.lean#L87)

These include the full Hermite specialization `pcfV_nat_add_half`, the `D` ODE,
entireness of `U` and `V`, and Anger/Weber symmetries, as well as normalization
bridges and the two source checks. All 25 passed the final axiom audit without `sorryAx`.

## Module inventory and unnumbered assertions

Each entry gives definitions/abbreviations, theorem statements, proved statements
and remaining admissions. The additional names list theorem statements without a
numbered-equation index; these include prose assertions, auxiliary specifications
and source checks. They are acquired statements unless listed as proved above.

- [AAR/Legendre/Associated.lean](AAR/Legendre/Associated.lean): 11 definitions, 31 statements, 4 proved, 27 admitted.
  Additional assertions: [`AAR.Legendre.associatedP_zero_order`](AAR/Legendre/Associated.lean#L91), [`AAR.Legendre.associatedQ_zero_order`](AAR/Legendre/Associated.lean#L102), [`AAR.Legendre.associatedP_analytic`](AAR/Legendre/Associated.lean#L109), [`AAR.Legendre.associatedP_entire_degree`](AAR/Legendre/Associated.lean#L114), [`AAR.Legendre.associatedP_entire_order`](AAR/Legendre/Associated.lean#L119), [`AAR.Legendre.associatedP_real`](AAR/Legendre/Associated.lean#L130), [`AAR.Legendre.olverQ_analytic`](AAR/Legendre/Associated.lean#L135), [`AAR.Legendre.olverQ_entire_degree`](AAR/Legendre/Associated.lean#L140), [`AAR.Legendre.olverQ_entire_order`](AAR/Legendre/Associated.lean#L145), [`AAR.Legendre.olverQ_real`](AAR/Legendre/Associated.lean#L156), [`AAR.Legendre.ferrersP_real`](AAR/Legendre/Associated.lean#L167), [`AAR.Legendre.ferrersQ_real`](AAR/Legendre/Associated.lean#L172), [`AAR.Legendre.ferrersP_conical_real`](AAR/Legendre/Associated.lean#L177).

- [AAR/Legendre/AssociatedRecurrences.lean](AAR/Legendre/AssociatedRecurrences.lean): 0 definitions, 24 statements, 0 proved, 24 admitted.

- [AAR/Legendre/Conical.lean](AAR/Legendre/Conical.lean): 4 definitions, 12 statements, 0 proved, 12 admitted.
  Additional assertions: [`AAR.Legendre.conical_positive`](AAR/Legendre/Conical.lean#L89).

- [AAR/Legendre/ConicalAsymptotics.lean](AAR/Legendre/ConicalAsymptotics.lean): 6 definitions, 8 statements, 0 proved, 8 admitted.
  Additional assertions: [`AAR.Legendre.conicalEta_mapping`](AAR/Legendre/ConicalAsymptotics.lean#L65), [`AAR.Legendre.conicalRho_mapping`](AAR/Legendre/ConicalAsymptotics.lean#L92).

- [AAR/Legendre/Connections.lean](AAR/Legendre/Connections.lean): 0 definitions, 17 statements, 0 proved, 17 admitted.

- [AAR/Legendre/Continuation.lean](AAR/Legendre/Continuation.lean): 8 definitions, 18 statements, 0 proved, 18 admitted.
  Additional assertions: [`AAR.Legendre.legendreTransport_exists`](AAR/Legendre/Continuation.lean#L110), [`AAR.Legendre.legendreTransport_unique`](AAR/Legendre/Continuation.lean#L115).

- [AAR/Legendre/Harmonics.lean](AAR/Legendre/Harmonics.lean): 7 definitions, 11 statements, 0 proved, 11 admitted.
  Additional assertions: [`AAR.Legendre.herglotz_generating`](AAR/Legendre/Harmonics.lean#L105), [`AAR.Legendre.scaledOblate_real`](AAR/Legendre/Harmonics.lean#L118).

- [AAR/Legendre/Hypergeometric.lean](AAR/Legendre/Hypergeometric.lean): 2 definitions, 17 statements, 1 proved, 16 admitted.

- [AAR/Legendre/IntegerTheory.lean](AAR/Legendre/IntegerTheory.lean): 0 definitions, 9 statements, 1 proved, 8 admitted.

- [AAR/Legendre/IntegralRepresentations.lean](AAR/Legendre/IntegralRepresentations.lean): 1 definitions, 20 statements, 0 proved, 20 admitted.

- [AAR/Legendre/Integrals.lean](AAR/Legendre/Integrals.lean): 0 definitions, 16 statements, 0 proved, 16 admitted.

- [AAR/Legendre/LocalTheory.lean](AAR/Legendre/LocalTheory.lean): 2 definitions, 6 statements, 1 proved, 5 admitted.
  Additional assertions: [`AAR.Legendre.legendre_finite_singular_exponents_1`](AAR/Legendre/LocalTheory.lean#L34), [`AAR.Legendre.legendre_finite_singular_exponents_2`](AAR/Legendre/LocalTheory.lean#L39), [`AAR.Legendre.legendre_infinite_singular_exponents`](AAR/Legendre/LocalTheory.lean#L44), [`AAR.Legendre.ferrersP_reflected_dependence`](AAR/Legendre/LocalTheory.lean#L59), [`AAR.Legendre.associatedPQ_independent`](AAR/Legendre/LocalTheory.lean#L64), [`AAR.Legendre.ferrersP_positive_integer_order_zero_count`](AAR/Legendre/LocalTheory.lean#L69).

- [AAR/Legendre/ParameterLimits.lean](AAR/Legendre/ParameterLimits.lean): 2 definitions, 6 statements, 0 proved, 6 admitted.
  Additional assertions: [`AAR.Legendre.legendreSinDigamma_limit`](AAR/Legendre/ParameterLimits.lean#L34), [`AAR.Legendre.legendreSinSqTrigamma_limit`](AAR/Legendre/ParameterLimits.lean#L39).

- [AAR/Legendre/Primitives.lean](AAR/Legendre/Primitives.lean): 2 definitions, 4 statements, 0 proved, 4 admitted.

- [AAR/Legendre/RelatedFunctions.lean](AAR/Legendre/RelatedFunctions.lean): 3 definitions, 4 statements, 0 proved, 4 admitted.

- [AAR/Legendre/Series.lean](AAR/Legendre/Series.lean): 4 definitions, 22 statements, 2 proved, 20 admitted.
  Additional assertions: [`AAR.Legendre.ferrersP_fourier_absolute`](AAR/Legendre/Series.lean#L32), [`AAR.Legendre.ferrersQ_fourier_absolute`](AAR/Legendre/Series.lean#L49), [`AAR.Legendre.ferrersP_fourier_not_absolute`](AAR/Legendre/Series.lean#L167), [`AAR.Legendre.ferrersQ_fourier_not_absolute`](AAR/Legendre/Series.lean#L175), [`AAR.Legendre.ferrersPQ_fourier_hypergeometric`](AAR/Legendre/Series.lean#L183).

- [AAR/Legendre/Singularities.lean](AAR/Legendre/Singularities.lean): 0 definitions, 16 statements, 0 proved, 16 admitted.

- [AAR/Legendre/SourceChecks.lean](AAR/Legendre/SourceChecks.lean): 0 definitions, 2 statements, 2 proved, 0 admitted.
  Additional assertions: [`AAR.Legendre.associatedP_one_neg_half`](AAR/Legendre/SourceChecks.lean#L25), [`AAR.Legendre.dlmf_14_27_no_boundary_zero`](AAR/Legendre/SourceChecks.lean#L56).

- [AAR/Legendre/SpecialValues.lean](AAR/Legendre/SpecialValues.lean): 0 definitions, 34 statements, 0 proved, 34 admitted.

- [AAR/Legendre/Sums.lean](AAR/Legendre/Sums.lean): 1 definitions, 12 statements, 0 proved, 12 admitted.

- [AAR/Legendre/Toroidal.lean](AAR/Legendre/Toroidal.lean): 3 definitions, 7 statements, 0 proved, 7 admitted.

- [AAR/Legendre/Uniform.lean](AAR/Legendre/Uniform.lean): 1 definitions, 17 statements, 0 proved, 17 admitted.

- [AAR/Legendre/UniformCoordinates.lean](AAR/Legendre/UniformCoordinates.lean): 20 definitions, 7 statements, 0 proved, 7 admitted.
  Additional assertions: [`AAR.Legendre.legendreOrderEta_bijective`](AAR/Legendre/UniformCoordinates.lean#L62), [`AAR.Legendre.legendreDegreeY_monotone`](AAR/Legendre/UniformCoordinates.lean#L92), [`AAR.Legendre.besselEnvelopeCross_spec`](AAR/Legendre/UniformCoordinates.lean#L152).

- [AAR/Legendre/Zeros.lean](AAR/Legendre/Zeros.lean): 6 definitions, 9 statements, 0 proved, 9 admitted.
  Additional assertions: [`AAR.Legendre.ferrersP_zero_count`](AAR/Legendre/Zeros.lean#L46), [`AAR.Legendre.ferrersP_nonpositive_order_zero_count`](AAR/Legendre/Zeros.lean#L51), [`AAR.Legendre.ferrersP_nat_degree_zero_count`](AAR/Legendre/Zeros.lean#L56), [`AAR.Legendre.ferrersQ_nat_zero_count`](AAR/Legendre/Zeros.lean#L61), [`AAR.Legendre.ferrersPQ_interlace`](AAR/Legendre/Zeros.lean#L70), [`AAR.Legendre.ferrersQ_zero_count_range`](AAR/Legendre/Zeros.lean#L75), [`AAR.Legendre.associatedP_zero_count`](AAR/Legendre/Zeros.lean#L84), [`AAR.Legendre.olverQ_no_exterior_zero`](AAR/Legendre/Zeros.lean#L89), [`AAR.Legendre.olverQ_at_most_one_exterior_zero`](AAR/Legendre/Zeros.lean#L94).

- [AAR/ParabolicCylinder/AsymptoticsZeros.lean](AAR/ParabolicCylinder/AsymptoticsZeros.lean): 5 definitions, 13 statements, 0 proved, 13 admitted.
  Additional assertions: [`AAR.Confluent.pcfU_no_real_zero`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L73), [`AAR.Confluent.pcfU_no_positive_zero`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L78), [`AAR.Confluent.pcfU_positive_zero_count`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L83), [`AAR.Confluent.pcfU_hermite_zero_count`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L88), [`AAR.Confluent.pcfV_no_positive_zero`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L93), [`AAR.Confluent.pcfV_integer_zero`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L98).

- [AAR/ParabolicCylinder/BarnesContinuation.lean](AAR/ParabolicCylinder/BarnesContinuation.lean): 2 definitions, 2 statements, 0 proved, 2 admitted.

- [AAR/ParabolicCylinder/Basic.lean](AAR/ParabolicCylinder/Basic.lean): 9 definitions, 25 statements, 3 proved, 22 admitted.
  Additional assertions: [`AAR.Confluent.pcfU_entire`](AAR/ParabolicCylinder/Basic.lean#L52), [`AAR.Confluent.pcfU_entire_order`](AAR/ParabolicCylinder/Basic.lean#L58), [`AAR.Confluent.pcfU_real`](AAR/ParabolicCylinder/Basic.lean#L63), [`AAR.Confluent.pcfV_entire`](AAR/ParabolicCylinder/Basic.lean#L68), [`AAR.Confluent.pcfV_entire_order`](AAR/ParabolicCylinder/Basic.lean#L74), [`AAR.Confluent.pcfV_real`](AAR/ParabolicCylinder/Basic.lean#L79), [`AAR.Confluent.pcfUBar_recurrences`](AAR/ParabolicCylinder/Basic.lean#L209).

- [AAR/ParabolicCylinder/Computation.lean](AAR/ParabolicCylinder/Computation.lean): 0 definitions, 3 statements, 0 proved, 3 admitted.
  Additional assertions: [`AAR.Confluent.pcfU_chebyshev_compact`](AAR/ParabolicCylinder/Computation.lean#L25), [`AAR.Confluent.pcfV_chebyshev_compact`](AAR/ParabolicCylinder/Computation.lean#L30), [`AAR.Confluent.pcfU_chebyshev_infinite`](AAR/ParabolicCylinder/Computation.lean#L35).

- [AAR/ParabolicCylinder/Hermite.lean](AAR/ParabolicCylinder/Hermite.lean): 0 definitions, 2 statements, 0 proved, 2 admitted.

- [AAR/ParabolicCylinder/Integrals.lean](AAR/ParabolicCylinder/Integrals.lean): 1 definitions, 12 statements, 0 proved, 12 admitted.

- [AAR/ParabolicCylinder/Relations.lean](AAR/ParabolicCylinder/Relations.lean): 1 definitions, 16 statements, 1 proved, 15 admitted.

- [AAR/ParabolicCylinder/SourceChecks.lean](AAR/ParabolicCylinder/SourceChecks.lean): 0 definitions, 2 statements, 2 proved, 0 admitted.
  Additional assertions: [`AAR.Confluent.pcfU_half_zero_ne_one`](AAR/ParabolicCylinder/SourceChecks.lean#L25), [`AAR.Confluent.dlmf_12_13_6_counterexample`](AAR/ParabolicCylinder/SourceChecks.lean#L44).

- [AAR/ParabolicCylinder/TurningPoint.lean](AAR/ParabolicCylinder/TurningPoint.lean): 5 definitions, 8 statements, 0 proved, 8 admitted.
  Additional assertions: [`AAR.Confluent.pcfDescendingZero_eventually`](AAR/ParabolicCylinder/TurningPoint.lean#L52).

- [AAR/ParabolicCylinder/Uniform.lean](AAR/ParabolicCylinder/Uniform.lean): 34 definitions, 19 statements, 0 proved, 19 admitted.
  Additional assertions: [`AAR.Confluent.pcfZeta_analytic_at_one`](AAR/ParabolicCylinder/Uniform.lean#L231).

- [AAR/ParabolicCylinder/Weber.lean](AAR/ParabolicCylinder/Weber.lean): 17 definitions, 20 statements, 1 proved, 19 admitted.
  Additional assertions: [`AAR.Confluent.pcfW_real`](AAR/ParabolicCylinder/Weber.lean#L64), [`AAR.Confluent.pcfW_connection_neg`](AAR/ParabolicCylinder/Weber.lean#L116).

- [AAR/ParabolicCylinder/WeberUniform.lean](AAR/ParabolicCylinder/WeberUniform.lean): 4 definitions, 3 statements, 0 proved, 3 admitted.

- [AAR/Struve/AngerWeber.lean](AAR/Struve/AngerWeber.lean): 10 definitions, 45 statements, 4 proved, 41 admitted.
  Additional assertions: [`AAR.Struve.angerJ_entire`](AAR/Struve/AngerWeber.lean#L35), [`AAR.Struve.angerJ_entire_order`](AAR/Struve/AngerWeber.lean#L40), [`AAR.Struve.weberE_entire`](AAR/Struve/AngerWeber.lean#L50), [`AAR.Struve.weberE_entire_order`](AAR/Struve/AngerWeber.lean#L55), [`AAR.Struve.angerA_regular`](AAR/Struve/AngerWeber.lean#L69), [`AAR.Struve.angerA_order_limit`](AAR/Struve/AngerWeber.lean#L74), [`AAR.Struve.angerA_boundary_integral`](AAR/Struve/AngerWeber.lean#L85).

- [AAR/Struve/Asymptotics.lean](AAR/Struve/Asymptotics.lean): 8 definitions, 33 statements, 1 proved, 32 admitted.
  Additional assertions: [`AAR.Struve.struveK_remainder_sign`](AAR/Struve/Asymptotics.lean#L99), [`AAR.Struve.angerScaledA_removable`](AAR/Struve/Asymptotics.lean#L256), [`AAR.Struve.struveH_large_order_expansion`](AAR/Struve/Asymptotics.lean#L262), [`AAR.Struve.struveL_large_order_expansion`](AAR/Struve/Asymptotics.lean#L270).

- [AAR/Struve/Basic.lean](AAR/Struve/Basic.lean): 11 definitions, 21 statements, 0 proved, 21 admitted.
  Additional assertions: [`AAR.Struve.entire_struveHCore`](AAR/Struve/Basic.lean#L51), [`AAR.Struve.entire_order_struveHCore`](AAR/Struve/Basic.lean#L56), [`AAR.Struve.entire_struveLCore`](AAR/Struve/Basic.lean#L86), [`AAR.Struve.entire_order_struveLCore`](AAR/Struve/Basic.lean#L91).

- [AAR/Struve/Coefficients.lean](AAR/Struve/Coefficients.lean): 1 definitions, 1 statements, 0 proved, 1 admitted.
  Additional assertions: [`AAR.Struve.angerScaledB_debye`](AAR/Struve/Coefficients.lean#L33).

- [AAR/Struve/Computation.lean](AAR/Struve/Computation.lean): 0 definitions, 2 statements, 0 proved, 2 admitted.
  Additional assertions: [`AAR.Struve.struveH_polynomial_approximation`](AAR/Struve/Computation.lean#L25), [`AAR.Struve.struveK_rational_approximation`](AAR/Struve/Computation.lean#L30).

- [AAR/Struve/Lommel.lean](AAR/Struve/Lommel.lean): 5 definitions, 13 statements, 2 proved, 11 admitted.
  Additional assertions: [`AAR.Struve.lommelCapital_parameter_limit`](AAR/Struve/Lommel.lean#L56).

- [AAR/Struve/Properties.lean](AAR/Struve/Properties.lean): 0 definitions, 35 statements, 0 proved, 35 admitted.

- [AAR/Struve/Representations.lean](AAR/Struve/Representations.lean): 2 definitions, 22 statements, 0 proved, 22 admitted.

## Section and equation ledger

Each link points to an acquired definition or statement. “Admitted” means its proof
is still `sorry`; “defined” does not prove the associated analytic specifications.
“Proved” refers only to the linked theorem. Section summaries and the unnumbered
assertions above complement the numbered inventory. Sections devoted to notation,
references, tables or software may have no numbered equation or theorem to acquire.
The deliberately excluded graphical/application sections are omitted below.

### [§11.1 Special Notation](https://dlmf.nist.gov/11.1)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§11.2 Definitions](https://dlmf.nist.gov/11.2)

- [11.2.E1](https://dlmf.nist.gov/11.2.E1): [`AAR.Struve.struveH`](AAR/Struve/Basic.lean#L37) (defined); [`AAR.Struve.hasSum_struveHCore`](AAR/Struve/Basic.lean#L46) (admitted).
- [11.2.E2](https://dlmf.nist.gov/11.2.E2): [`AAR.Struve.struveL`](AAR/Struve/Basic.lean#L72) (defined); [`AAR.Struve.hasSum_struveLCore`](AAR/Struve/Basic.lean#L81) (admitted).
- [11.2.E3](https://dlmf.nist.gov/11.2.E3): [`AAR.Struve.struveH_zero_order_series`](AAR/Struve/Basic.lean#L188) (admitted).
- [11.2.E4](https://dlmf.nist.gov/11.2.E4): [`AAR.Struve.struveL_zero_order_series`](AAR/Struve/Basic.lean#L194) (admitted).
- [11.2.E5](https://dlmf.nist.gov/11.2.E5): [`AAR.Struve.struveK`](AAR/Struve/Basic.lean#L103) (defined).
- [11.2.E6](https://dlmf.nist.gov/11.2.E6): [`AAR.Struve.struveM`](AAR/Struve/Basic.lean#L108) (defined).
- [11.2.E7](https://dlmf.nist.gov/11.2.E7): [`AAR.Struve.struveEquation`](AAR/Struve/Basic.lean#L113) (defined).
- [11.2.E8](https://dlmf.nist.gov/11.2.E8): [`AAR.Struve.struveH_ode`](AAR/Struve/Basic.lean#L118) (admitted); [`AAR.Struve.struveK_ode`](AAR/Struve/Basic.lean#L124) (admitted).
- [11.2.E9](https://dlmf.nist.gov/11.2.E9): [`AAR.Struve.struveEquation`](AAR/Struve/Basic.lean#L113) (defined).
- [11.2.E10](https://dlmf.nist.gov/11.2.E10): [`AAR.Struve.struveL_ode`](AAR/Struve/Basic.lean#L130) (admitted); [`AAR.Struve.struveM_ode`](AAR/Struve/Basic.lean#L136) (admitted).
- [11.2.E11](https://dlmf.nist.gov/11.2.E11): [`AAR.Struve.struve_general_solution_11`](AAR/Struve/Basic.lean#L146) (admitted).
- [11.2.E12](https://dlmf.nist.gov/11.2.E12): [`AAR.Struve.struve_general_solution_12`](AAR/Struve/Basic.lean#L152) (admitted).
- [11.2.E13](https://dlmf.nist.gov/11.2.E13): [`AAR.Struve.struve_general_solution_13`](AAR/Struve/Basic.lean#L158) (admitted).
- [11.2.E14](https://dlmf.nist.gov/11.2.E14): [`AAR.Struve.struve_general_solution_14`](AAR/Struve/Basic.lean#L164) (admitted).
- [11.2.E15](https://dlmf.nist.gov/11.2.E15): [`AAR.Struve.struve_general_solution_15`](AAR/Struve/Basic.lean#L170) (admitted).
- [11.2.E16](https://dlmf.nist.gov/11.2.E16): [`AAR.Struve.struve_general_solution_16`](AAR/Struve/Basic.lean#L176) (admitted).
- [11.2.E17](https://dlmf.nist.gov/11.2.E17): [`AAR.Struve.struve_general_solution_17`](AAR/Struve/Basic.lean#L182) (admitted).

### [§11.4 Basic Properties](https://dlmf.nist.gov/11.4)

- [11.4.E1](https://dlmf.nist.gov/11.4.E1): [`AAR.Struve.struveK_nat_add_half`](AAR/Struve/Properties.lean#L28) (admitted).
- [11.4.E2](https://dlmf.nist.gov/11.4.E2): [`AAR.Struve.struveL_nat_add_half`](AAR/Struve/Properties.lean#L34) (admitted).
- [11.4.E3](https://dlmf.nist.gov/11.4.E3): [`AAR.Struve.struveH_neg_nat_sub_half`](AAR/Struve/Properties.lean#L40) (admitted).
- [11.4.E4](https://dlmf.nist.gov/11.4.E4): [`AAR.Struve.struveL_neg_nat_sub_half`](AAR/Struve/Properties.lean#L46) (admitted).
- [11.4.E5](https://dlmf.nist.gov/11.4.E5): [`AAR.Struve.struve_special_5`](AAR/Struve/Properties.lean#L52) (admitted).
- [11.4.E6](https://dlmf.nist.gov/11.4.E6): [`AAR.Struve.struve_special_6`](AAR/Struve/Properties.lean#L58) (admitted).
- [11.4.E7](https://dlmf.nist.gov/11.4.E7): [`AAR.Struve.struve_special_7`](AAR/Struve/Properties.lean#L64) (admitted).
- [11.4.E8](https://dlmf.nist.gov/11.4.E8): [`AAR.Struve.struve_special_8`](AAR/Struve/Properties.lean#L70) (admitted).
- [11.4.E9](https://dlmf.nist.gov/11.4.E9): [`AAR.Struve.struve_special_9`](AAR/Struve/Properties.lean#L76) (admitted).
- [11.4.E10](https://dlmf.nist.gov/11.4.E10): [`AAR.Struve.struve_special_10`](AAR/Struve/Properties.lean#L82) (admitted).
- [11.4.E11](https://dlmf.nist.gov/11.4.E11): [`AAR.Struve.struve_special_11`](AAR/Struve/Properties.lean#L88) (admitted).
- [11.4.E12](https://dlmf.nist.gov/11.4.E12): [`AAR.Struve.struve_special_12`](AAR/Struve/Properties.lean#L94) (admitted).
- [11.4.E13](https://dlmf.nist.gov/11.4.E13): [`AAR.Struve.struveH_nonneg`](AAR/Struve/Properties.lean#L100) (admitted).
- [11.4.E14](https://dlmf.nist.gov/11.4.E14): [`AAR.Struve.struveH_relative_bound`](AAR/Struve/Properties.lean#L106) (admitted).
- [11.4.E15](https://dlmf.nist.gov/11.4.E15): [`AAR.Struve.struveH_relative_bound`](AAR/Struve/Properties.lean#L106) (admitted).
- [11.4.E16](https://dlmf.nist.gov/11.4.E16): [`AAR.Struve.struveHOnLog_shift`](AAR/Struve/Basic.lean#L62) (admitted).
- [11.4.E17](https://dlmf.nist.gov/11.4.E17): [`AAR.Struve.struveLOnLog_shift`](AAR/Struve/Basic.lean#L97) (admitted).
- [11.4.E18](https://dlmf.nist.gov/11.4.E18): [`AAR.Struve.struveH_bessel_series_18`](AAR/Struve/Properties.lean#L112) (admitted).
- [11.4.E19](https://dlmf.nist.gov/11.4.E19): [`AAR.Struve.struveH_bessel_series_19`](AAR/Struve/Properties.lean#L118) (admitted).
- [11.4.E20](https://dlmf.nist.gov/11.4.E20): [`AAR.Struve.struveH_bessel_series_20`](AAR/Struve/Properties.lean#L124) (admitted).
- [11.4.E21](https://dlmf.nist.gov/11.4.E21): [`AAR.Struve.struveH_zero_odd`](AAR/Struve/Properties.lean#L130) (admitted); [`AAR.Struve.struveH_zero_products`](AAR/Struve/Properties.lean#L136) (admitted).
- [11.4.E22](https://dlmf.nist.gov/11.4.E22): [`AAR.Struve.struveH_one_even`](AAR/Struve/Properties.lean#L142) (admitted); [`AAR.Struve.struveH_one_products`](AAR/Struve/Properties.lean#L148) (admitted).
- [11.4.E23](https://dlmf.nist.gov/11.4.E23): [`AAR.Struve.struveH_recurrence`](AAR/Struve/Properties.lean#L154) (admitted).
- [11.4.E24](https://dlmf.nist.gov/11.4.E24): [`AAR.Struve.struveH_derivative`](AAR/Struve/Properties.lean#L160) (admitted).
- [11.4.E25](https://dlmf.nist.gov/11.4.E25): [`AAR.Struve.struveL_recurrence`](AAR/Struve/Properties.lean#L196) (admitted).
- [11.4.E26](https://dlmf.nist.gov/11.4.E26): [`AAR.Struve.struveL_derivative`](AAR/Struve/Properties.lean#L202) (admitted).
- [11.4.E27](https://dlmf.nist.gov/11.4.E27): [`AAR.Struve.struveH_weighted_deriv_27`](AAR/Struve/Properties.lean#L166) (admitted).
- [11.4.E28](https://dlmf.nist.gov/11.4.E28): [`AAR.Struve.struveH_weighted_deriv_28`](AAR/Struve/Properties.lean#L172) (admitted).
- [11.4.E29](https://dlmf.nist.gov/11.4.E29): [`AAR.Struve.struveL_weighted_deriv_29`](AAR/Struve/Properties.lean#L208) (admitted).
- [11.4.E30](https://dlmf.nist.gov/11.4.E30): [`AAR.Struve.struveL_weighted_deriv_30`](AAR/Struve/Properties.lean#L214) (admitted).
- [11.4.E31](https://dlmf.nist.gov/11.4.E31): [`AAR.Struve.struveH_iterated_weighted_deriv`](AAR/Struve/Properties.lean#L178) (admitted); [`AAR.Struve.struveL_iterated_weighted_deriv`](AAR/Struve/Properties.lean#L220) (admitted).
- [11.4.E32](https://dlmf.nist.gov/11.4.E32): [`AAR.Struve.struveH_zero_deriv`](AAR/Struve/Properties.lean#L184) (admitted); [`AAR.Struve.struveH_one_weighted_deriv`](AAR/Struve/Properties.lean#L190) (admitted).
- [11.4.E33](https://dlmf.nist.gov/11.4.E33): [`AAR.Struve.struveL_zero_deriv`](AAR/Struve/Properties.lean#L226) (admitted); [`AAR.Struve.struveL_one_weighted_deriv`](AAR/Struve/Properties.lean#L232) (admitted).

### [§11.5 Integral Representations](https://dlmf.nist.gov/11.5)

- [11.5.E1](https://dlmf.nist.gov/11.5.E1): [`AAR.Struve.struveH_trig_integral`](AAR/Struve/Representations.lean#L29) (admitted); [`AAR.Struve.struveH_integral`](AAR/Struve/Representations.lean#L41) (admitted).
- [11.5.E2](https://dlmf.nist.gov/11.5.E2): [`AAR.Struve.struveK_laplace`](AAR/Struve/Representations.lean#L47) (admitted).
- [11.5.E3](https://dlmf.nist.gov/11.5.E3): [`AAR.Struve.struveK_zero_laplace`](AAR/Struve/Representations.lean#L53) (admitted).
- [11.5.E4](https://dlmf.nist.gov/11.5.E4): [`AAR.Struve.struveM_integral`](AAR/Struve/Representations.lean#L59) (admitted).
- [11.5.E5](https://dlmf.nist.gov/11.5.E5): [`AAR.Struve.struveM_zero_integral`](AAR/Struve/Representations.lean#L65) (admitted).
- [11.5.E6](https://dlmf.nist.gov/11.5.E6): [`AAR.Struve.struveL_trig_integral`](AAR/Struve/Representations.lean#L35) (admitted).
- [11.5.E7](https://dlmf.nist.gov/11.5.E7): [`AAR.Struve.struveL_fourier`](AAR/Struve/Representations.lean#L71) (admitted).
- [11.5.E8](https://dlmf.nist.gov/11.5.E8): [`AAR.Struve.struveH_barnes`](AAR/Struve/Representations.lean#L77) (admitted).
- [11.5.E9](https://dlmf.nist.gov/11.5.E9): [`AAR.Struve.struveL_barnes_loop`](AAR/Struve/Representations.lean#L87) (admitted).

### [§11.6 Asymptotic Expansions](https://dlmf.nist.gov/11.6)

- [11.6.E1](https://dlmf.nist.gov/11.6.E1): [`AAR.Struve.struveK_asymptotic`](AAR/Struve/Asymptotics.lean#L33) (admitted).
- [11.6.E2](https://dlmf.nist.gov/11.6.E2): [`AAR.Struve.struveM_asymptotic`](AAR/Struve/Asymptotics.lean#L39) (admitted).
- [11.6.E3](https://dlmf.nist.gov/11.6.E3): [`AAR.Struve.struveK_primitive_asymptotic`](AAR/Struve/Asymptotics.lean#L45) (admitted).
- [11.6.E4](https://dlmf.nist.gov/11.6.E4): [`AAR.Struve.struveM_primitive_asymptotic`](AAR/Struve/Asymptotics.lean#L51) (admitted).
- [11.6.E5](https://dlmf.nist.gov/11.6.E5): [`AAR.Struve.struveH_large_order`](AAR/Struve/Asymptotics.lean#L57) (admitted); [`AAR.Struve.struveL_large_order`](AAR/Struve/Asymptotics.lean#L63) (admitted).
- [11.6.E6](https://dlmf.nist.gov/11.6.E6): [`AAR.Struve.struveK_scaled_asymptotic`](AAR/Struve/Asymptotics.lean#L76) (admitted).
- [11.6.E7](https://dlmf.nist.gov/11.6.E7): [`AAR.Struve.struveM_scaled_asymptotic`](AAR/Struve/Asymptotics.lean#L82) (admitted).
- [11.6.E8](https://dlmf.nist.gov/11.6.E8): [`AAR.Struve.struveScaledCoeff_initial`](AAR/Struve/Asymptotics.lean#L88) (admitted).
- [11.6.E9](https://dlmf.nist.gov/11.6.E9): [`AAR.Struve.struveL_scaled_equiv`](AAR/Struve/Asymptotics.lean#L94) (admitted).

### [§11.7 Integrals and Sums](https://dlmf.nist.gov/11.7)

- [11.7.E1](https://dlmf.nist.gov/11.7.E1): [`AAR.Struve.struveH_weighted_deriv_27`](AAR/Struve/Properties.lean#L166) (admitted).
- [11.7.E2](https://dlmf.nist.gov/11.7.E2): [`AAR.Struve.struveH_weighted_deriv_28`](AAR/Struve/Properties.lean#L172) (admitted).
- [11.7.E3](https://dlmf.nist.gov/11.7.E3): [`AAR.Struve.struveL_weighted_deriv_29`](AAR/Struve/Properties.lean#L208) (admitted).
- [11.7.E4](https://dlmf.nist.gov/11.7.E4): [`AAR.Struve.struveL_weighted_deriv_30`](AAR/Struve/Properties.lean#L214) (admitted).
- [11.7.E5](https://dlmf.nist.gov/11.7.E5): [`AAR.Struve.struveHPrimitive`](AAR/Struve/Representations.lean#L93) (defined).
- [11.7.E6](https://dlmf.nist.gov/11.7.E6): [`AAR.Struve.struveHPrimitive_recurrence`](AAR/Struve/Representations.lean#L98) (admitted).
- [11.7.E7](https://dlmf.nist.gov/11.7.E7): [`AAR.Struve.struveH_sonine`](AAR/Struve/Representations.lean#L104) (admitted).
- [11.7.E8](https://dlmf.nist.gov/11.7.E8): [`AAR.Struve.struveH_integral_zero_div`](AAR/Struve/Representations.lean#L110) (admitted); [`AAR.Struve.struveH_integral_one_div_sq`](AAR/Struve/Representations.lean#L116) (admitted).
- [11.7.E9](https://dlmf.nist.gov/11.7.E9): [`AAR.Struve.struveH_integral_plain`](AAR/Struve/Representations.lean#L122) (admitted).
- [11.7.E10](https://dlmf.nist.gov/11.7.E10): [`AAR.Struve.struveH_integral_mellin_zero`](AAR/Struve/Representations.lean#L128) (admitted).
- [11.7.E11](https://dlmf.nist.gov/11.7.E11): [`AAR.Struve.struveH_integral_mellin`](AAR/Struve/Representations.lean#L134) (admitted).
- [11.7.E12](https://dlmf.nist.gov/11.7.E12): [`AAR.Struve.struveH_integral_product`](AAR/Struve/Representations.lean#L140) (admitted).
- [11.7.E13](https://dlmf.nist.gov/11.7.E13): [`AAR.Struve.struve_laplace_13`](AAR/Struve/Representations.lean#L146) (admitted).
- [11.7.E14](https://dlmf.nist.gov/11.7.E14): [`AAR.Struve.struve_laplace_14`](AAR/Struve/Representations.lean#L152) (admitted).
- [11.7.E15](https://dlmf.nist.gov/11.7.E15): [`AAR.Struve.struve_laplace_15`](AAR/Struve/Representations.lean#L158) (admitted).
- [11.7.E16](https://dlmf.nist.gov/11.7.E16): [`AAR.Struve.struve_laplace_16`](AAR/Struve/Representations.lean#L164) (admitted).

### [§11.8 Analogs to Kelvin Functions](https://dlmf.nist.gov/11.8)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§11.9 Lommel Functions](https://dlmf.nist.gov/11.9)

- [11.9.E1](https://dlmf.nist.gov/11.9.E1): [`AAR.Struve.lommelS_ode`](AAR/Struve/Lommel.lean#L81) (admitted); [`AAR.Struve.lommelCapital_ode`](AAR/Struve/Lommel.lean#L94) (admitted).
- [11.9.E2](https://dlmf.nist.gov/11.9.E2): [`AAR.Struve.lommel_general_solution`](AAR/Struve/Lommel.lean#L106) (admitted).
- [11.9.E3](https://dlmf.nist.gov/11.9.E3): [`AAR.Struve.lommelS`](AAR/Struve/Lommel.lean#L37) (defined); [`AAR.Struve.hasSum_lommelS`](AAR/Struve/Lommel.lean#L62) (admitted).
- [11.9.E4](https://dlmf.nist.gov/11.9.E4): [`AAR.Struve.lommelA`](AAR/Struve/Lommel.lean#L28) (defined); [`AAR.Struve.lommelA_poch`](AAR/Struve/Lommel.lean#L68) (proved).
- [11.9.E5](https://dlmf.nist.gov/11.9.E5): [`AAR.Struve.lommelCapitalRegular`](AAR/Struve/Lommel.lean#L42) (defined); [`AAR.Struve.lommelCapital_regular`](AAR/Struve/Lommel.lean#L51) (admitted).
- [11.9.E6](https://dlmf.nist.gov/11.9.E6): [`AAR.Struve.lommelS_neg_order`](AAR/Struve/Lommel.lean#L87) (proved); [`AAR.Struve.lommelCapital_neg_order`](AAR/Struve/Lommel.lean#L100) (admitted).
- [11.9.E7](https://dlmf.nist.gov/11.9.E7): [`AAR.Struve.lommelS_bessel_series_7`](AAR/Struve/Lommel.lean#L112) (admitted).
- [11.9.E8](https://dlmf.nist.gov/11.9.E8): [`AAR.Struve.lommelS_bessel_series_8`](AAR/Struve/Lommel.lean#L118) (admitted).
- [11.9.E9](https://dlmf.nist.gov/11.9.E9): [`AAR.Struve.lommelCapital_asymptotic`](AAR/Struve/Lommel.lean#L124) (admitted); [`AAR.Struve.lommelCapital_terminates`](AAR/Struve/Lommel.lean#L130) (admitted).

### [§11.10 Anger–Weber Functions](https://dlmf.nist.gov/11.10)

- [11.10.E1](https://dlmf.nist.gov/11.10.E1): [`AAR.Struve.angerJ`](AAR/Struve/AngerWeber.lean#L31) (defined).
- [11.10.E2](https://dlmf.nist.gov/11.10.E2): [`AAR.Struve.weberE`](AAR/Struve/AngerWeber.lean#L46) (defined).
- [11.10.E3](https://dlmf.nist.gov/11.10.E3): [`AAR.Struve.angerJ_double_integral`](AAR/Struve/AngerWeber.lean#L91) (admitted).
- [11.10.E4](https://dlmf.nist.gov/11.10.E4): [`AAR.Struve.angerA`](AAR/Struve/AngerWeber.lean#L65) (defined); [`AAR.Struve.angerA_integral`](AAR/Struve/AngerWeber.lean#L80) (admitted).
- [11.10.E5](https://dlmf.nist.gov/11.10.E5): [`AAR.Struve.angerJ_ode`](AAR/Struve/AngerWeber.lean#L97) (admitted); [`AAR.Struve.weberE_ode`](AAR/Struve/AngerWeber.lean#L103) (admitted).
- [11.10.E6](https://dlmf.nist.gov/11.10.E6): [`AAR.Struve.angerJ_ode`](AAR/Struve/AngerWeber.lean#L97) (admitted).
- [11.10.E7](https://dlmf.nist.gov/11.10.E7): [`AAR.Struve.weberE_ode`](AAR/Struve/AngerWeber.lean#L103) (admitted).
- [11.10.E8](https://dlmf.nist.gov/11.10.E8): [`AAR.Struve.angerJ_series`](AAR/Struve/AngerWeber.lean#L131) (admitted).
- [11.10.E9](https://dlmf.nist.gov/11.10.E9): [`AAR.Struve.weberE_series`](AAR/Struve/AngerWeber.lean#L137) (admitted).
- [11.10.E10](https://dlmf.nist.gov/11.10.E10): [`AAR.Struve.angerS1`](AAR/Struve/AngerWeber.lean#L109) (defined); [`AAR.Struve.hasSum_angerS1`](AAR/Struve/AngerWeber.lean#L114) (admitted).
- [11.10.E11](https://dlmf.nist.gov/11.10.E11): [`AAR.Struve.angerS2`](AAR/Struve/AngerWeber.lean#L120) (defined); [`AAR.Struve.hasSum_angerS2`](AAR/Struve/AngerWeber.lean#L125) (admitted).
- [11.10.E12](https://dlmf.nist.gov/11.10.E12): [`AAR.Struve.angerJ_neg`](AAR/Struve/AngerWeber.lean#L143) (proved); [`AAR.Struve.weberE_neg`](AAR/Struve/AngerWeber.lean#L154) (proved).
- [11.10.E13](https://dlmf.nist.gov/11.10.E13): [`AAR.Struve.anger_weber`](AAR/Struve/AngerWeber.lean#L166) (admitted).
- [11.10.E14](https://dlmf.nist.gov/11.10.E14): [`AAR.Struve.weber_anger`](AAR/Struve/AngerWeber.lean#L172) (admitted).
- [11.10.E15](https://dlmf.nist.gov/11.10.E15): [`AAR.Struve.anger_bessel`](AAR/Struve/AngerWeber.lean#L178) (admitted).
- [11.10.E16](https://dlmf.nist.gov/11.10.E16): [`AAR.Struve.weber_bessel`](AAR/Struve/AngerWeber.lean#L184) (admitted).
- [11.10.E17](https://dlmf.nist.gov/11.10.E17): [`AAR.Struve.angerJ_lommel`](AAR/Struve/AngerWeber.lean#L190) (admitted).
- [11.10.E18](https://dlmf.nist.gov/11.10.E18): [`AAR.Struve.weberE_lommel`](AAR/Struve/AngerWeber.lean#L196) (admitted).
- [11.10.E19](https://dlmf.nist.gov/11.10.E19): [`AAR.Struve.angerJ_half_19`](AAR/Struve/AngerWeber.lean#L212) (admitted); [`AAR.Struve.anger_weber_half`](AAR/Struve/AngerWeber.lean#L224) (admitted).
- [11.10.E20](https://dlmf.nist.gov/11.10.E20): [`AAR.Struve.angerJ_half_20`](AAR/Struve/AngerWeber.lean#L218) (admitted); [`AAR.Struve.anger_weber_half`](AAR/Struve/AngerWeber.lean#L224) (admitted).
- [11.10.E21](https://dlmf.nist.gov/11.10.E21): [`AAR.Struve.angerFresnelPlus`](AAR/Struve/AngerWeber.lean#L202) (defined); [`AAR.Struve.angerFresnelMinus`](AAR/Struve/AngerWeber.lean#L207) (defined).
- [11.10.E22](https://dlmf.nist.gov/11.10.E22): [`AAR.Struve.weberE_nat`](AAR/Struve/AngerWeber.lean#L240) (admitted).
- [11.10.E23](https://dlmf.nist.gov/11.10.E23): [`AAR.Struve.weberE_neg_nat`](AAR/Struve/AngerWeber.lean#L246) (admitted).
- [11.10.E24](https://dlmf.nist.gov/11.10.E24): [`AAR.Struve.weberM1`](AAR/Struve/AngerWeber.lean#L230) (defined); [`AAR.Struve.weberM2`](AAR/Struve/AngerWeber.lean#L235) (defined).
- [11.10.E25](https://dlmf.nist.gov/11.10.E25): [`AAR.Struve.angerJ_zero`](AAR/Struve/AngerWeber.lean#L252) (proved); [`AAR.Struve.weberE_zero`](AAR/Struve/AngerWeber.lean#L267) (proved).
- [11.10.E26](https://dlmf.nist.gov/11.10.E26): [`AAR.Struve.weberE_zero_order`](AAR/Struve/AngerWeber.lean#L290) (admitted); [`AAR.Struve.weberE_one_order`](AAR/Struve/AngerWeber.lean#L296) (admitted).
- [11.10.E27](https://dlmf.nist.gov/11.10.E27): [`AAR.Struve.angerJ_order_deriv_zero`](AAR/Struve/AngerWeber.lean#L302) (admitted).
- [11.10.E28](https://dlmf.nist.gov/11.10.E28): [`AAR.Struve.weberE_order_deriv_zero`](AAR/Struve/AngerWeber.lean#L308) (admitted).
- [11.10.E29](https://dlmf.nist.gov/11.10.E29): [`AAR.Struve.angerJ_int`](AAR/Struve/AngerWeber.lean#L314) (admitted).
- [11.10.E30](https://dlmf.nist.gov/11.10.E30): [`AAR.Struve.angerJ_bessel_products`](AAR/Struve/AngerWeber.lean#L320) (admitted).
- [11.10.E31](https://dlmf.nist.gov/11.10.E31): [`AAR.Struve.weberE_bessel_products`](AAR/Struve/AngerWeber.lean#L326) (admitted).
- [11.10.E32](https://dlmf.nist.gov/11.10.E32): [`AAR.Struve.angerJ_recurrence`](AAR/Struve/AngerWeber.lean#L332) (admitted).
- [11.10.E33](https://dlmf.nist.gov/11.10.E33): [`AAR.Struve.weberE_recurrence`](AAR/Struve/AngerWeber.lean#L356) (admitted).
- [11.10.E34](https://dlmf.nist.gov/11.10.E34): [`AAR.Struve.angerJ_deriv`](AAR/Struve/AngerWeber.lean#L338) (admitted).
- [11.10.E35](https://dlmf.nist.gov/11.10.E35): [`AAR.Struve.weberE_deriv`](AAR/Struve/AngerWeber.lean#L362) (admitted).
- [11.10.E36](https://dlmf.nist.gov/11.10.E36): [`AAR.Struve.angerJ_weighted_deriv_add`](AAR/Struve/AngerWeber.lean#L344) (admitted); [`AAR.Struve.angerJ_weighted_deriv_sub`](AAR/Struve/AngerWeber.lean#L350) (admitted).
- [11.10.E37](https://dlmf.nist.gov/11.10.E37): [`AAR.Struve.weberE_weighted_deriv_add`](AAR/Struve/AngerWeber.lean#L368) (admitted); [`AAR.Struve.weberE_weighted_deriv_sub`](AAR/Struve/AngerWeber.lean#L374) (admitted).

### [§11.11 Asymptotic Expansions of Anger–Weber Functions](https://dlmf.nist.gov/11.11)

- [11.11.E1](https://dlmf.nist.gov/11.11.E1): [`AAR.Struve.angerF`](AAR/Struve/Asymptotics.lean#L105) (defined); [`AAR.Struve.angerG`](AAR/Struve/Asymptotics.lean#L110) (defined); [`AAR.Struve.angerFG_poch`](AAR/Struve/Asymptotics.lean#L115) (proved).
- [11.11.E2](https://dlmf.nist.gov/11.11.E2): [`AAR.Struve.angerJ_large_argument`](AAR/Struve/Asymptotics.lean#L131) (admitted).
- [11.11.E3](https://dlmf.nist.gov/11.11.E3): [`AAR.Struve.weberE_large_argument`](AAR/Struve/Asymptotics.lean#L137) (admitted).
- [11.11.E4](https://dlmf.nist.gov/11.11.E4): [`AAR.Struve.angerA_large_argument`](AAR/Struve/Asymptotics.lean#L143) (admitted).
- [11.11.E5](https://dlmf.nist.gov/11.11.E5): [`AAR.Struve.angerJ_large_order`](AAR/Struve/Asymptotics.lean#L153) (admitted).
- [11.11.E6](https://dlmf.nist.gov/11.11.E6): [`AAR.Struve.weberE_large_order`](AAR/Struve/Asymptotics.lean#L159) (admitted).
- [11.11.E7](https://dlmf.nist.gov/11.11.E7): [`AAR.Struve.weberE_large_integer_0`](AAR/Struve/Asymptotics.lean#L165) (admitted); [`AAR.Struve.weberE_large_integer_1`](AAR/Struve/Asymptotics.lean#L171) (admitted).
- [11.11.E8](https://dlmf.nist.gov/11.11.E8): [`AAR.Struve.angerA_scaled_8`](AAR/Struve/Asymptotics.lean#L188) (admitted).
- [11.11.E9](https://dlmf.nist.gov/11.11.E9): [`AAR.Struve.angerScaledA_initial`](AAR/Struve/Asymptotics.lean#L182) (admitted).
- [11.11.E10](https://dlmf.nist.gov/11.11.E10): [`AAR.Struve.angerA_scaled_10`](AAR/Struve/Asymptotics.lean#L194) (admitted).
- [11.11.E11](https://dlmf.nist.gov/11.11.E11): [`AAR.Struve.angerA_scaled_saddle`](AAR/Struve/Asymptotics.lean#L209) (admitted).
- [11.11.E12](https://dlmf.nist.gov/11.11.E12): [`AAR.Struve.angerMu`](AAR/Struve/Asymptotics.lean#L200) (defined).
- [11.11.E13](https://dlmf.nist.gov/11.11.E13): [`AAR.Struve.angerScaledB_initial`](AAR/Struve/Asymptotics.lean#L215) (admitted).
- [11.11.E14](https://dlmf.nist.gov/11.11.E14): [`AAR.Struve.angerA_scaled_outer_equiv`](AAR/Struve/Asymptotics.lean#L221) (admitted).
- [11.11.E15](https://dlmf.nist.gov/11.11.E15): [`AAR.Struve.angerA_scaled_inner_equiv`](AAR/Struve/Asymptotics.lean#L227) (admitted).
- [11.11.E16](https://dlmf.nist.gov/11.11.E16): [`AAR.Struve.angerA_turning_equiv`](AAR/Struve/Asymptotics.lean#L233) (admitted).
- [11.11.E17](https://dlmf.nist.gov/11.11.E17): [`AAR.Struve.angerA_turning_uniform`](AAR/Struve/Asymptotics.lean#L251) (admitted).
- [11.11.E18](https://dlmf.nist.gov/11.11.E18): [`AAR.Struve.angerJ_turning_equiv`](AAR/Struve/Asymptotics.lean#L239) (admitted).
- [11.11.E19](https://dlmf.nist.gov/11.11.E19): [`AAR.Struve.weberE_turning_equiv`](AAR/Struve/Asymptotics.lean#L245) (admitted).

### [§11.13 Methods of Computation](https://dlmf.nist.gov/11.13)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§11.14 Tables](https://dlmf.nist.gov/11.14)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§11.15 Approximations](https://dlmf.nist.gov/11.15)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§11.16 Software](https://dlmf.nist.gov/11.16)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.1 Special Notation](https://dlmf.nist.gov/12.1)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.2 Differential Equations](https://dlmf.nist.gov/12.2)

- [12.2.E1](https://dlmf.nist.gov/12.2.E1): [`AAR.Confluent.IsQuadraticCylinderSolution`](AAR/ParabolicCylinder/Basic.lean#L28) (defined); [`AAR.Confluent.quadraticCylinder_transform`](AAR/ParabolicCylinder/Basic.lean#L38) (admitted).
- [12.2.E2](https://dlmf.nist.gov/12.2.E2): [`AAR.Confluent.hasDerivAt_pcfUDeriv`](AAR/Confluent/ParabolicCylinder.lean#L161) (proved); [`AAR.Confluent.hasDerivAt_pcfVDeriv`](AAR/Confluent/ParabolicCylinder.lean#L1072) (proved).
- [12.2.E3](https://dlmf.nist.gov/12.2.E3): [`AAR.Confluent.IsOscillatoryCylinderSolution`](AAR/ParabolicCylinder/Basic.lean#L33) (defined); [`AAR.Confluent.pcfW_ode`](AAR/ParabolicCylinder/Weber.lean#L59) (admitted).
- [12.2.E4](https://dlmf.nist.gov/12.2.E4): [`AAR.Confluent.pcfD_ode`](AAR/ParabolicCylinder/Basic.lean#L44) (proved).
- [12.2.E5](https://dlmf.nist.gov/12.2.E5): [`AAR.Confluent.pcfD`](AAR/Confluent/ParabolicCylinder.lean#L154) (defined).
- [12.2.E6](https://dlmf.nist.gov/12.2.E6): [`AAR.Confluent.pcfU_zero`](AAR/Confluent/ParabolicCylinder.lean#L176) (proved).
- [12.2.E7](https://dlmf.nist.gov/12.2.E7): [`AAR.Confluent.pcfUDeriv_zero`](AAR/Confluent/ParabolicCylinder.lean#L184) (proved).
- [12.2.E8](https://dlmf.nist.gov/12.2.E8): [`AAR.Confluent.pcfV_zero`](AAR/Confluent/ParabolicCylinder.lean#L1093) (proved).
- [12.2.E9](https://dlmf.nist.gov/12.2.E9): [`AAR.Confluent.pcfVDeriv_zero`](AAR/Confluent/ParabolicCylinder.lean#L1102) (proved).
- [12.2.E10](https://dlmf.nist.gov/12.2.E10): [`AAR.Confluent.pcfV_wronskian`](AAR/Confluent/ParabolicCylinder.lean#L1154) (proved).
- [12.2.E11](https://dlmf.nist.gov/12.2.E11): [`AAR.Confluent.pcfU_wronskian_neg`](AAR/Confluent/ParabolicCylinder.lean#L813) (proved).
- [12.2.E12](https://dlmf.nist.gov/12.2.E12): [`AAR.Confluent.pcfU_wronskian_mul_I`](AAR/Confluent/ParabolicCylinder.lean#L869) (proved); [`AAR.Confluent.pcfU_wronskian_mul_neg_I`](AAR/Confluent/ParabolicCylinder.lean#L907) (proved).
- [12.2.E13](https://dlmf.nist.gov/12.2.E13): [`AAR.Confluent.pcfU_neg_nat_sub_half_neg`](AAR/Confluent/ParabolicCylinder.lean#L1310) (proved).
- [12.2.E14](https://dlmf.nist.gov/12.2.E14): [`AAR.Confluent.pcfV_nat_add_half_neg`](AAR/Confluent/ParabolicCylinder.lean#L1321) (proved).
- [12.2.E15](https://dlmf.nist.gov/12.2.E15): [`AAR.Confluent.pcfU_neg_eq`](AAR/Confluent/ParabolicCylinder.lean#L1203) (proved).
- [12.2.E16](https://dlmf.nist.gov/12.2.E16): [`AAR.Confluent.pcfV_neg_eq`](AAR/Confluent/ParabolicCylinder.lean#L1252) (proved).
- [12.2.E17](https://dlmf.nist.gov/12.2.E17): [`AAR.Confluent.pcfU_connection_mul_I`](AAR/Confluent/ParabolicCylinder.lean#L957) (proved); [`AAR.Confluent.pcfU_connection_mul_neg_I`](AAR/Confluent/ParabolicCylinder.lean#L1042) (proved).
- [12.2.E18](https://dlmf.nist.gov/12.2.E18): [`AAR.Confluent.pcfU_rotated_connection_pos`](AAR/ParabolicCylinder/Basic.lean#L126) (admitted); [`AAR.Confluent.pcfU_rotated_connection_neg`](AAR/ParabolicCylinder/Basic.lean#L138) (admitted).
- [12.2.E19](https://dlmf.nist.gov/12.2.E19): [`AAR.Confluent.pcfU_rotated_connection_entire_pos`](AAR/ParabolicCylinder/Basic.lean#L132) (admitted); [`AAR.Confluent.pcfU_rotated_connection_entire_neg`](AAR/ParabolicCylinder/Basic.lean#L144) (admitted).
- [12.2.E20](https://dlmf.nist.gov/12.2.E20): [`AAR.Confluent.pcfV_eq_mul_I`](AAR/Confluent/ParabolicCylinder.lean#L1357) (proved); [`AAR.Confluent.pcfV_eq_mul_neg_I`](AAR/Confluent/ParabolicCylinder.lean#L1419) (proved).
- [12.2.E21](https://dlmf.nist.gov/12.2.E21): [`AAR.Confluent.pcfUBar`](AAR/ParabolicCylinder/Basic.lean#L85) (defined).
- [12.2.E22](https://dlmf.nist.gov/12.2.E22): [`AAR.Confluent.pcfF`](AAR/ParabolicCylinder/Basic.lean#L94) (defined); [`AAR.Confluent.pcfTheta`](AAR/ParabolicCylinder/Basic.lean#L99) (defined); [`AAR.Confluent.pcfF_phase`](AAR/ParabolicCylinder/Basic.lean#L104) (admitted).
- [12.2.E23](https://dlmf.nist.gov/12.2.E23): [`AAR.Confluent.pcfG`](AAR/ParabolicCylinder/Basic.lean#L110) (defined); [`AAR.Confluent.pcfPsi`](AAR/ParabolicCylinder/Basic.lean#L115) (defined); [`AAR.Confluent.pcfG_phase`](AAR/ParabolicCylinder/Basic.lean#L120) (admitted).

### [§12.4 Power-Series Expansions](https://dlmf.nist.gov/12.4)

- [12.4.E1](https://dlmf.nist.gov/12.4.E1): [`AAR.Confluent.pcfU`](AAR/Confluent/ParabolicCylinder.lean#L142) (defined).
- [12.4.E2](https://dlmf.nist.gov/12.4.E2): [`AAR.Confluent.pcfV`](AAR/Confluent/ParabolicCylinder.lean#L1062) (defined).
- [12.4.E3](https://dlmf.nist.gov/12.4.E3): [`AAR.Confluent.pcfEven_series_3`](AAR/ParabolicCylinder/Basic.lean#L150) (admitted).
- [12.4.E4](https://dlmf.nist.gov/12.4.E4): [`AAR.Confluent.pcfOdd_series_4`](AAR/ParabolicCylinder/Basic.lean#L162) (admitted).
- [12.4.E5](https://dlmf.nist.gov/12.4.E5): [`AAR.Confluent.pcfEven_series_5`](AAR/ParabolicCylinder/Basic.lean#L156) (admitted).
- [12.4.E6](https://dlmf.nist.gov/12.4.E6): [`AAR.Confluent.pcfOdd_series_6`](AAR/ParabolicCylinder/Basic.lean#L168) (admitted).

### [§12.5 Integral Representations](https://dlmf.nist.gov/12.5)

- [12.5.E1](https://dlmf.nist.gov/12.5.E1): [`AAR.Confluent.pcfU_eq_integral`](AAR/Confluent/ParabolicCylinder.lean#L694) (proved).
- [12.5.E2](https://dlmf.nist.gov/12.5.E2): [`AAR.Confluent.pcfU_integral_2`](AAR/ParabolicCylinder/Integrals.lean#L26) (admitted).
- [12.5.E3](https://dlmf.nist.gov/12.5.E3): [`AAR.Confluent.pcfU_integral_3`](AAR/ParabolicCylinder/Integrals.lean#L32) (admitted).
- [12.5.E4](https://dlmf.nist.gov/12.5.E4): [`AAR.Confluent.pcfU_integral_4`](AAR/ParabolicCylinder/Integrals.lean#L38) (admitted).
- [12.5.E5](https://dlmf.nist.gov/12.5.E5): [`AAR.Confluent.pcfU_hankel_integral`](AAR/ParabolicCylinder/Integrals.lean#L60) (admitted).
- [12.5.E6](https://dlmf.nist.gov/12.5.E6): [`AAR.Confluent.pcfU_vertical_integral`](AAR/ParabolicCylinder/Integrals.lean#L44) (admitted).
- [12.5.E7](https://dlmf.nist.gov/12.5.E7): [`AAR.Confluent.pcfV_horizontal_integral`](AAR/ParabolicCylinder/Integrals.lean#L50) (admitted).
- [12.5.E8](https://dlmf.nist.gov/12.5.E8): [`AAR.Confluent.pcfU_barnes_integral`](AAR/ParabolicCylinder/Integrals.lean#L66) (admitted); [`AAR.Confluent.pcfU_barnes_continued`](AAR/ParabolicCylinder/BarnesContinuation.lean#L33) (admitted).
- [12.5.E9](https://dlmf.nist.gov/12.5.E9): [`AAR.Confluent.pcfV_barnes_integral`](AAR/ParabolicCylinder/Integrals.lean#L72) (admitted); [`AAR.Confluent.pcfV_barnes_continued`](AAR/ParabolicCylinder/BarnesContinuation.lean#L39) (admitted).

### [§12.6 Continued Fraction](https://dlmf.nist.gov/12.6)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.7 Relations to Other Functions](https://dlmf.nist.gov/12.7)

- [12.7.E1](https://dlmf.nist.gov/12.7.E1): [`AAR.Confluent.pcfU_neg_half`](AAR/Confluent/ParabolicCylinder.lean#L193) (proved).
- [12.7.E2](https://dlmf.nist.gov/12.7.E2): [`AAR.Confluent.pcfU_physicists_hermite`](AAR/ParabolicCylinder/Hermite.lean#L26) (admitted); [`AAR.Confluent.pcfD_nat`](AAR/Confluent/ParabolicCylinder.lean#L494) (proved).
- [12.7.E3](https://dlmf.nist.gov/12.7.E3): [`AAR.Confluent.pcfV_nat_add_half`](AAR/ParabolicCylinder/Relations.lean#L30) (proved); [`AAR.Confluent.pcfV_physicists_hermite`](AAR/ParabolicCylinder/Hermite.lean#L32) (admitted).
- [12.7.E4](https://dlmf.nist.gov/12.7.E4): [`AAR.Confluent.pcfV_neg_half`](AAR/ParabolicCylinder/Relations.lean#L48) (admitted).
- [12.7.E5](https://dlmf.nist.gov/12.7.E5): [`AAR.Confluent.pcfU_half`](AAR/ParabolicCylinder/Relations.lean#L54) (admitted).
- [12.7.E6](https://dlmf.nist.gov/12.7.E6): [`AAR.Confluent.pcfU_nat_add_half_deriv`](AAR/ParabolicCylinder/Relations.lean#L60) (admitted).
- [12.7.E7](https://dlmf.nist.gov/12.7.E7): [`AAR.Confluent.hhFunction`](AAR/ParabolicCylinder/Relations.lean#L66) (defined); [`AAR.Confluent.pcfU_hh`](AAR/ParabolicCylinder/Relations.lean#L71) (admitted).
- [12.7.E8](https://dlmf.nist.gov/12.7.E8): [`AAR.Confluent.pcfU_bessel_8`](AAR/ParabolicCylinder/Relations.lean#L77) (admitted).
- [12.7.E9](https://dlmf.nist.gov/12.7.E9): [`AAR.Confluent.pcfU_bessel_9`](AAR/ParabolicCylinder/Relations.lean#L83) (admitted).
- [12.7.E10](https://dlmf.nist.gov/12.7.E10): [`AAR.Confluent.pcfU_bessel_10`](AAR/ParabolicCylinder/Relations.lean#L89) (admitted).
- [12.7.E11](https://dlmf.nist.gov/12.7.E11): [`AAR.Confluent.pcfU_bessel_11`](AAR/ParabolicCylinder/Relations.lean#L95) (admitted).
- [12.7.E12](https://dlmf.nist.gov/12.7.E12): [`AAR.Confluent.pcfEven_kummer_alternative`](AAR/ParabolicCylinder/Basic.lean#L174) (admitted); [`AAR.Confluent.pcfEven`](AAR/Confluent/ParabolicCylinder.lean#L60) (defined).
- [12.7.E13](https://dlmf.nist.gov/12.7.E13): [`AAR.Confluent.pcfOdd_kummer_alternative`](AAR/ParabolicCylinder/Basic.lean#L180) (admitted); [`AAR.Confluent.pcfOdd`](AAR/Confluent/ParabolicCylinder.lean#L65) (defined).
- [12.7.E14](https://dlmf.nist.gov/12.7.E14): [`AAR.Confluent.pcfU_kummerU_odd`](AAR/ParabolicCylinder/Relations.lean#L101) (admitted); [`AAR.Confluent.pcfU_whittaker`](AAR/ParabolicCylinder/Relations.lean#L107) (admitted); [`AAR.Confluent.pcfU_eq_kummerU`](AAR/Confluent/ParabolicCylinder.lean#L211) (proved).

### [§12.8 Recurrence Relations and Derivatives](https://dlmf.nist.gov/12.8)

- [12.8.E1](https://dlmf.nist.gov/12.8.E1): [`AAR.Confluent.pcfU_three_term`](AAR/Confluent/ParabolicCylinder.lean#L460) (proved).
- [12.8.E2](https://dlmf.nist.gov/12.8.E2): [`AAR.Confluent.pcfU_recurrence_add`](AAR/Confluent/ParabolicCylinder.lean#L425) (proved).
- [12.8.E3](https://dlmf.nist.gov/12.8.E3): [`AAR.Confluent.pcfU_recurrence_sub`](AAR/Confluent/ParabolicCylinder.lean#L391) (proved).
- [12.8.E4](https://dlmf.nist.gov/12.8.E4): [`AAR.Confluent.pcfU_deriv_recurrence`](AAR/Confluent/ParabolicCylinder.lean#L466) (proved).
- [12.8.E5](https://dlmf.nist.gov/12.8.E5): [`AAR.Confluent.pcfV_three_term`](AAR/Confluent/ParabolicCylinder.lean#L1562) (proved).
- [12.8.E6](https://dlmf.nist.gov/12.8.E6): [`AAR.Confluent.pcfV_recurrence_sub`](AAR/Confluent/ParabolicCylinder.lean#L1520) (proved).
- [12.8.E7](https://dlmf.nist.gov/12.8.E7): [`AAR.Confluent.pcfV_recurrence_add`](AAR/Confluent/ParabolicCylinder.lean#L1480) (proved).
- [12.8.E8](https://dlmf.nist.gov/12.8.E8): [`AAR.Confluent.pcfV_deriv_recurrence`](AAR/Confluent/ParabolicCylinder.lean#L1568) (proved).
- [12.8.E9](https://dlmf.nist.gov/12.8.E9): [`AAR.Confluent.pcfU_iterated_deriv_9`](AAR/ParabolicCylinder/Basic.lean#L186) (admitted).
- [12.8.E10](https://dlmf.nist.gov/12.8.E10): [`AAR.Confluent.pcfU_iterated_deriv_10`](AAR/ParabolicCylinder/Basic.lean#L192) (admitted).
- [12.8.E11](https://dlmf.nist.gov/12.8.E11): [`AAR.Confluent.pcfV_iterated_deriv_11`](AAR/ParabolicCylinder/Basic.lean#L198) (admitted).
- [12.8.E12](https://dlmf.nist.gov/12.8.E12): [`AAR.Confluent.pcfV_iterated_deriv_12`](AAR/ParabolicCylinder/Basic.lean#L204) (admitted).

### [§12.9 Asymptotic Expansions for Large Variable](https://dlmf.nist.gov/12.9)

- [12.9.E1](https://dlmf.nist.gov/12.9.E1): [`AAR.Confluent.pcfU_sector_asymptotic`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L34) (admitted); [`AAR.Confluent.hasAsymptoticExpansion_pcfU`](AAR/Confluent/ParabolicCylinder.lean#L266) (proved).
- [12.9.E2](https://dlmf.nist.gov/12.9.E2): [`AAR.Confluent.pcfV_sector_asymptotic`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L40) (admitted).
- [12.9.E3](https://dlmf.nist.gov/12.9.E3): [`AAR.Confluent.pcfU_adjacent_asymptotic_pos`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L50) (admitted); [`AAR.Confluent.pcfU_adjacent_asymptotic_neg`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L56) (admitted).
- [12.9.E4](https://dlmf.nist.gov/12.9.E4): [`AAR.Confluent.pcfV_adjacent_asymptotic_pos`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L62) (admitted); [`AAR.Confluent.pcfV_adjacent_asymptotic_neg`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L68) (admitted).

### [§12.10 Uniform Asymptotic Expansions for Large Parameter](https://dlmf.nist.gov/12.10)

- [12.10.E1](https://dlmf.nist.gov/12.10.E1): [`AAR.Confluent.pcf_parameter_scaling`](AAR/ParabolicCylinder/TurningPoint.lean#L29) (admitted).
- [12.10.E2](https://dlmf.nist.gov/12.10.E2): [`AAR.Confluent.pcf_parameter_scaling`](AAR/ParabolicCylinder/TurningPoint.lean#L29) (admitted).
- [12.10.E3](https://dlmf.nist.gov/12.10.E3): [`AAR.Confluent.pcf_negative_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L147) (admitted).
- [12.10.E4](https://dlmf.nist.gov/12.10.E4): [`AAR.Confluent.pcf_negative_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L147) (admitted).
- [12.10.E5](https://dlmf.nist.gov/12.10.E5): [`AAR.Confluent.pcf_negative_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L147) (admitted).
- [12.10.E6](https://dlmf.nist.gov/12.10.E6): [`AAR.Confluent.pcf_negative_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L147) (admitted).
- [12.10.E7](https://dlmf.nist.gov/12.10.E7): [`AAR.Confluent.pcfXi`](AAR/ParabolicCylinder/Uniform.lean#L29) (defined).
- [12.10.E8](https://dlmf.nist.gov/12.10.E8): [`AAR.Confluent.pcfOlverA`](AAR/ParabolicCylinder/Uniform.lean#L104) (defined); [`AAR.Confluent.pcfOlverB`](AAR/ParabolicCylinder/Uniform.lean#L119) (defined).
- [12.10.E9](https://dlmf.nist.gov/12.10.E9): [`AAR.Confluent.pcfOlverUV_initial`](AAR/ParabolicCylinder/Uniform.lean#L98) (admitted).
- [12.10.E10](https://dlmf.nist.gov/12.10.E10): [`AAR.Confluent.pcfOlverUV_initial`](AAR/ParabolicCylinder/Uniform.lean#L98) (admitted).
- [12.10.E11](https://dlmf.nist.gov/12.10.E11): [`AAR.Confluent.pcfOlverU`](AAR/ParabolicCylinder/Uniform.lean#L77) (defined); [`AAR.Confluent.pcfOlverU_spec`](AAR/ParabolicCylinder/Uniform.lean#L92) (admitted).
- [12.10.E12](https://dlmf.nist.gov/12.10.E12): [`AAR.Confluent.pcfOlverR`](AAR/ParabolicCylinder/Uniform.lean#L82) (defined).
- [12.10.E13](https://dlmf.nist.gov/12.10.E13): [`AAR.Confluent.pcfOlverV`](AAR/ParabolicCylinder/Uniform.lean#L87) (defined).
- [12.10.E14](https://dlmf.nist.gov/12.10.E14): [`AAR.Confluent.IsCylinderGNormalizer`](AAR/ParabolicCylinder/Uniform.lean#L142) (defined); [`AAR.Confluent.pcf_negative_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L147) (admitted).
- [12.10.E15](https://dlmf.nist.gov/12.10.E15): [`AAR.Confluent.pcfH`](AAR/ParabolicCylinder/Uniform.lean#L44) (defined).
- [12.10.E16](https://dlmf.nist.gov/12.10.E16): [`AAR.Confluent.pcfGammaCoeff`](AAR/ParabolicCylinder/Uniform.lean#L49) (defined); [`AAR.Confluent.pcfGammaCoeff_expansion`](AAR/ParabolicCylinder/Uniform.lean#L54) (admitted).
- [12.10.E17](https://dlmf.nist.gov/12.10.E17): [`AAR.Confluent.pcfGammaCoeff_initial`](AAR/ParabolicCylinder/Uniform.lean#L60) (admitted).
- [12.10.E18](https://dlmf.nist.gov/12.10.E18): [`AAR.Confluent.pcf_oscillatory_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L163) (admitted).
- [12.10.E19](https://dlmf.nist.gov/12.10.E19): [`AAR.Confluent.pcf_oscillatory_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L163) (admitted).
- [12.10.E20](https://dlmf.nist.gov/12.10.E20): [`AAR.Confluent.pcf_oscillatory_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L163) (admitted).
- [12.10.E21](https://dlmf.nist.gov/12.10.E21): [`AAR.Confluent.pcf_oscillatory_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L163) (admitted).
- [12.10.E22](https://dlmf.nist.gov/12.10.E22): [`AAR.Confluent.pcfKappa`](AAR/ParabolicCylinder/Uniform.lean#L153) (defined); [`AAR.Confluent.pcfChi`](AAR/ParabolicCylinder/Uniform.lean#L158) (defined).
- [12.10.E23](https://dlmf.nist.gov/12.10.E23): [`AAR.Confluent.pcfEta`](AAR/ParabolicCylinder/Uniform.lean#L34) (defined).
- [12.10.E24](https://dlmf.nist.gov/12.10.E24): [`AAR.Confluent.pcfOlverATilde`](AAR/ParabolicCylinder/Uniform.lean#L109) (defined); [`AAR.Confluent.pcfOlverBTilde`](AAR/ParabolicCylinder/Uniform.lean#L124) (defined).
- [12.10.E25](https://dlmf.nist.gov/12.10.E25): [`AAR.Confluent.pcf_positive_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L174) (admitted).
- [12.10.E26](https://dlmf.nist.gov/12.10.E26): [`AAR.Confluent.pcfXiBar`](AAR/ParabolicCylinder/Uniform.lean#L39) (defined).
- [12.10.E27](https://dlmf.nist.gov/12.10.E27): [`AAR.Confluent.pcfOlverUBar`](AAR/ParabolicCylinder/Uniform.lean#L114) (defined).
- [12.10.E28](https://dlmf.nist.gov/12.10.E28): [`AAR.Confluent.IsCylinderGBarNormalizer`](AAR/ParabolicCylinder/Uniform.lean#L169) (defined).
- [12.10.E29](https://dlmf.nist.gov/12.10.E29): [`AAR.Confluent.pcf_positive_parameter_uniform`](AAR/ParabolicCylinder/Uniform.lean#L174) (admitted).
- [12.10.E30](https://dlmf.nist.gov/12.10.E30): [`AAR.Confluent.pcfOlverVBar`](AAR/ParabolicCylinder/Uniform.lean#L129) (defined).
- [12.10.E31](https://dlmf.nist.gov/12.10.E31): [`AAR.Confluent.pcfU_temme_uniform`](AAR/ParabolicCylinder/Uniform.lean#L206) (admitted).
- [12.10.E32](https://dlmf.nist.gov/12.10.E32): [`AAR.Confluent.pcfTau`](AAR/ParabolicCylinder/Uniform.lean#L180) (defined).
- [12.10.E33](https://dlmf.nist.gov/12.10.E33): [`AAR.Confluent.pcfTemmePoly_recurrence`](AAR/ParabolicCylinder/Uniform.lean#L200) (admitted).
- [12.10.E34](https://dlmf.nist.gov/12.10.E34): [`AAR.Confluent.pcfTemmePoly_initial`](AAR/ParabolicCylinder/Uniform.lean#L194) (admitted).
- [12.10.E35](https://dlmf.nist.gov/12.10.E35): [`AAR.Confluent.pcf_airy_uniform`](AAR/ParabolicCylinder/TurningPoint.lean#L43) (admitted).
- [12.10.E36](https://dlmf.nist.gov/12.10.E36): [`AAR.Confluent.pcf_airy_uniform`](AAR/ParabolicCylinder/TurningPoint.lean#L43) (admitted).
- [12.10.E37](https://dlmf.nist.gov/12.10.E37): [`AAR.Confluent.pcf_airy_uniform`](AAR/ParabolicCylinder/TurningPoint.lean#L43) (admitted).
- [12.10.E38](https://dlmf.nist.gov/12.10.E38): [`AAR.Confluent.pcf_airy_uniform`](AAR/ParabolicCylinder/TurningPoint.lean#L43) (admitted).
- [12.10.E39](https://dlmf.nist.gov/12.10.E39): [`AAR.Confluent.pcfZeta`](AAR/ParabolicCylinder/Uniform.lean#L212) (defined); [`AAR.Confluent.pcfInverseZeta_spec`](AAR/ParabolicCylinder/Uniform.lean#L221) (admitted).
- [12.10.E40](https://dlmf.nist.gov/12.10.E40): [`AAR.Confluent.pcfPhi`](AAR/ParabolicCylinder/Uniform.lean#L227) (defined).
- [12.10.E41](https://dlmf.nist.gov/12.10.E41): [`AAR.Confluent.pcfInverseZeta_taylor`](AAR/ParabolicCylinder/Uniform.lean#L237) (admitted).
- [12.10.E42](https://dlmf.nist.gov/12.10.E42): [`AAR.Confluent.pcfAiryA`](AAR/ParabolicCylinder/Uniform.lean#L253) (defined); [`AAR.Confluent.pcfAiryA_limit`](AAR/ParabolicCylinder/Uniform.lean#L258) (admitted); [`AAR.Confluent.pcfAiryB`](AAR/ParabolicCylinder/Uniform.lean#L264) (defined); [`AAR.Confluent.pcfAiryB_limit`](AAR/ParabolicCylinder/Uniform.lean#L269) (admitted).
- [12.10.E43](https://dlmf.nist.gov/12.10.E43): [`AAR.Confluent.pcfAiryAlpha`](AAR/ParabolicCylinder/Uniform.lean#L243) (defined); [`AAR.Confluent.pcfAiryBeta`](AAR/ParabolicCylinder/Uniform.lean#L248) (defined).
- [12.10.E44](https://dlmf.nist.gov/12.10.E44): [`AAR.Confluent.pcfAiryCD_derivative`](AAR/ParabolicCylinder/Uniform.lean#L308) (admitted).
- [12.10.E45](https://dlmf.nist.gov/12.10.E45): [`AAR.Confluent.pcfAiryChi`](AAR/ParabolicCylinder/Uniform.lean#L297) (defined); [`AAR.Confluent.pcfAiryChi_formula`](AAR/ParabolicCylinder/Uniform.lean#L302) (admitted).
- [12.10.E46](https://dlmf.nist.gov/12.10.E46): [`AAR.Confluent.pcfAiryC`](AAR/ParabolicCylinder/Uniform.lean#L275) (defined); [`AAR.Confluent.pcfAiryC_limit`](AAR/ParabolicCylinder/Uniform.lean#L280) (admitted); [`AAR.Confluent.pcfAiryD`](AAR/ParabolicCylinder/Uniform.lean#L286) (defined); [`AAR.Confluent.pcfAiryD_limit`](AAR/ParabolicCylinder/Uniform.lean#L291) (admitted).

### [§12.11 Zeros](https://dlmf.nist.gov/12.11)

- [12.11.E1](https://dlmf.nist.gov/12.11.E1): [`AAR.Confluent.pcfU_complex_zero_strings`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L114) (admitted).
- [12.11.E2](https://dlmf.nist.gov/12.11.E2): [`AAR.Confluent.pcfZeroTau`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L104) (defined).
- [12.11.E3](https://dlmf.nist.gov/12.11.E3): [`AAR.Confluent.pcfZeroLambda`](AAR/ParabolicCylinder/AsymptoticsZeros.lean#L109) (defined).
- [12.11.E4](https://dlmf.nist.gov/12.11.E4): [`AAR.Confluent.pcf_real_zero_expansion_4`](AAR/ParabolicCylinder/TurningPoint.lean#L69) (admitted).
- [12.11.E5](https://dlmf.nist.gov/12.11.E5): [`AAR.Confluent.pcf_real_zero_expansion_4`](AAR/ParabolicCylinder/TurningPoint.lean#L69) (admitted).
- [12.11.E6](https://dlmf.nist.gov/12.11.E6): [`AAR.Confluent.pcfZeroP1`](AAR/ParabolicCylinder/TurningPoint.lean#L58) (defined); [`AAR.Confluent.pcfZeroP1_limit`](AAR/ParabolicCylinder/TurningPoint.lean#L63) (admitted).
- [12.11.E7](https://dlmf.nist.gov/12.11.E7): [`AAR.Confluent.pcf_real_zero_expansion_7`](AAR/ParabolicCylinder/TurningPoint.lean#L75) (admitted).
- [12.11.E8](https://dlmf.nist.gov/12.11.E8): [`AAR.Confluent.pcf_real_zero_expansion_7`](AAR/ParabolicCylinder/TurningPoint.lean#L75) (admitted).
- [12.11.E9](https://dlmf.nist.gov/12.11.E9): [`AAR.Confluent.pcfFirstZeroCoeff`](AAR/ParabolicCylinder/TurningPoint.lean#L81) (defined); [`AAR.Confluent.pcfFirstZero_expansion`](AAR/ParabolicCylinder/TurningPoint.lean#L86) (admitted); [`AAR.Confluent.pcfFirstZero_coefficients`](AAR/ParabolicCylinder/TurningPoint.lean#L92) (admitted).

### [§12.12 Integrals](https://dlmf.nist.gov/12.12)

- [12.12.E1](https://dlmf.nist.gov/12.12.E1): [`AAR.Confluent.pcf_integral_1`](AAR/ParabolicCylinder/Integrals.lean#L78) (admitted).
- [12.12.E2](https://dlmf.nist.gov/12.12.E2): [`AAR.Confluent.pcf_integral_2`](AAR/ParabolicCylinder/Integrals.lean#L84) (admitted).
- [12.12.E3](https://dlmf.nist.gov/12.12.E3): [`AAR.Confluent.pcf_integral_3`](AAR/ParabolicCylinder/Integrals.lean#L90) (admitted).
- [12.12.E4](https://dlmf.nist.gov/12.12.E4): [`AAR.Confluent.pcf_integral_4`](AAR/ParabolicCylinder/Integrals.lean#L96) (admitted).

### [§12.13 Sums](https://dlmf.nist.gov/12.13)

- [12.13.E1](https://dlmf.nist.gov/12.13.E1): [`AAR.Confluent.pcfU_addition_1`](AAR/ParabolicCylinder/Relations.lean#L113) (admitted).
- [12.13.E2](https://dlmf.nist.gov/12.13.E2): [`AAR.Confluent.pcfU_addition_2`](AAR/ParabolicCylinder/Relations.lean#L119) (admitted).
- [12.13.E3](https://dlmf.nist.gov/12.13.E3): [`AAR.Confluent.pcfV_addition_3`](AAR/ParabolicCylinder/Relations.lean#L125) (admitted).
- [12.13.E4](https://dlmf.nist.gov/12.13.E4): [`AAR.Confluent.pcfV_addition_4`](AAR/ParabolicCylinder/Relations.lean#L131) (admitted).
- [12.13.E5](https://dlmf.nist.gov/12.13.E5): [`AAR.Confluent.pcfU_rotational_addition`](AAR/ParabolicCylinder/Relations.lean#L137) (admitted).
- [12.13.E6](https://dlmf.nist.gov/12.13.E6): refuted; see the proved [counterexample](AAR/ParabolicCylinder/SourceChecks.lean).

### [§12.14 The Function 𝑊(𝑎,𝑥)](https://dlmf.nist.gov/12.14)

- [12.14.E1](https://dlmf.nist.gov/12.14.E1): [`AAR.Confluent.pcfWZero`](AAR/ParabolicCylinder/Weber.lean#L28) (defined); [`AAR.Confluent.pcfW_initial`](AAR/ParabolicCylinder/Weber.lean#L53) (admitted).
- [12.14.E2](https://dlmf.nist.gov/12.14.E2): [`AAR.Confluent.pcfWDerivZero`](AAR/ParabolicCylinder/Weber.lean#L33) (defined); [`AAR.Confluent.pcfW_initial`](AAR/ParabolicCylinder/Weber.lean#L53) (admitted).
- [12.14.E3](https://dlmf.nist.gov/12.14.E3): [`AAR.Confluent.pcfW_wronskian`](AAR/ParabolicCylinder/Weber.lean#L70) (admitted).
- [12.14.E4](https://dlmf.nist.gov/12.14.E4): [`AAR.Confluent.pcfW_connection`](AAR/ParabolicCylinder/Weber.lean#L111) (admitted).
- [12.14.E5](https://dlmf.nist.gov/12.14.E5): [`AAR.Confluent.pcfWK`](AAR/ParabolicCylinder/Weber.lean#L76) (defined); [`AAR.Confluent.pcfWK_inv`](AAR/ParabolicCylinder/Weber.lean#L81) (proved).
- [12.14.E6](https://dlmf.nist.gov/12.14.E6): [`AAR.Confluent.pcfWRho`](AAR/ParabolicCylinder/Weber.lean#L106) (defined).
- [12.14.E7](https://dlmf.nist.gov/12.14.E7): [`AAR.Confluent.pcfGammaPhase`](AAR/ParabolicCylinder/Weber.lean#L95) (defined); [`AAR.Confluent.pcfGammaPhase_spec`](AAR/ParabolicCylinder/Weber.lean#L100) (admitted).
- [12.14.E8](https://dlmf.nist.gov/12.14.E8): [`AAR.Confluent.pcfW`](AAR/ParabolicCylinder/Weber.lean#L48) (defined).
- [12.14.E9](https://dlmf.nist.gov/12.14.E9): [`AAR.Confluent.pcfWEven_series`](AAR/ParabolicCylinder/Weber.lean#L134) (admitted).
- [12.14.E10](https://dlmf.nist.gov/12.14.E10): [`AAR.Confluent.pcfWOdd_series`](AAR/ParabolicCylinder/Weber.lean#L140) (admitted).
- [12.14.E11](https://dlmf.nist.gov/12.14.E11): [`AAR.Confluent.pcfWEven_series`](AAR/ParabolicCylinder/Weber.lean#L134) (admitted); [`AAR.Confluent.pcfWOdd_series`](AAR/ParabolicCylinder/Weber.lean#L140) (admitted).
- [12.14.E12](https://dlmf.nist.gov/12.14.E12): [`AAR.Confluent.pcfWEven_series`](AAR/ParabolicCylinder/Weber.lean#L134) (admitted); [`AAR.Confluent.pcfWOdd_series`](AAR/ParabolicCylinder/Weber.lean#L140) (admitted).
- [12.14.E13](https://dlmf.nist.gov/12.14.E13): [`AAR.Confluent.pcfW_zero_bessel_1`](AAR/ParabolicCylinder/Weber.lean#L158) (admitted); [`AAR.Confluent.pcfW_zero_bessel_2`](AAR/ParabolicCylinder/Weber.lean#L170) (admitted).
- [12.14.E14](https://dlmf.nist.gov/12.14.E14): [`AAR.Confluent.pcfW_zero_bessel_deriv_1`](AAR/ParabolicCylinder/Weber.lean#L164) (admitted); [`AAR.Confluent.pcfW_zero_bessel_deriv_2`](AAR/ParabolicCylinder/Weber.lean#L176) (admitted).
- [12.14.E15](https://dlmf.nist.gov/12.14.E15): [`AAR.Confluent.pcfWEven`](AAR/ParabolicCylinder/Weber.lean#L38) (defined); [`AAR.Confluent.pcfWEven_kummer`](AAR/ParabolicCylinder/Weber.lean#L146) (admitted).
- [12.14.E16](https://dlmf.nist.gov/12.14.E16): [`AAR.Confluent.pcfWOdd`](AAR/ParabolicCylinder/Weber.lean#L43) (defined); [`AAR.Confluent.pcfWOdd_kummer`](AAR/ParabolicCylinder/Weber.lean#L152) (admitted).
- [12.14.E17](https://dlmf.nist.gov/12.14.E17): [`AAR.Confluent.pcfWS`](AAR/ParabolicCylinder/Weber.lean#L187) (defined); [`AAR.Confluent.pcfW_amplitude`](AAR/ParabolicCylinder/Weber.lean#L192) (admitted).
- [12.14.E18](https://dlmf.nist.gov/12.14.E18): [`AAR.Confluent.pcfWS`](AAR/ParabolicCylinder/Weber.lean#L187) (defined); [`AAR.Confluent.pcfW_amplitude`](AAR/ParabolicCylinder/Weber.lean#L192) (admitted).
- [12.14.E19](https://dlmf.nist.gov/12.14.E19): [`AAR.Confluent.pcfWOmega`](AAR/ParabolicCylinder/Weber.lean#L182) (defined).
- [12.14.E20](https://dlmf.nist.gov/12.14.E20): [`AAR.Confluent.pcfWS_asymptotic`](AAR/ParabolicCylinder/Weber.lean#L208) (admitted).
- [12.14.E21](https://dlmf.nist.gov/12.14.E21): [`AAR.Confluent.pcfWS_asymptotic`](AAR/ParabolicCylinder/Weber.lean#L208) (admitted).
- [12.14.E22](https://dlmf.nist.gov/12.14.E22): [`AAR.Confluent.pcfWCoeff`](AAR/ParabolicCylinder/Weber.lean#L198) (defined); Gamma/Pochhammer identity: Mathlib `Complex.Gamma_add_nat_div_Gamma_eq`.
- [12.14.E23](https://dlmf.nist.gov/12.14.E23): [`AAR.Confluent.pcfWS_asymptotic`](AAR/ParabolicCylinder/Weber.lean#L208) (admitted).
- [12.14.E24](https://dlmf.nist.gov/12.14.E24): [`AAR.Confluent.pcfW_parameter_scaling`](AAR/ParabolicCylinder/WeberUniform.lean#L26) (admitted).
- [12.14.E25](https://dlmf.nist.gov/12.14.E25): [`AAR.Confluent.pcfW_elementary_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L52) (admitted).
- [12.14.E26](https://dlmf.nist.gov/12.14.E26): [`AAR.Confluent.pcfW_elementary_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L52) (admitted).
- [12.14.E27](https://dlmf.nist.gov/12.14.E27): [`AAR.Confluent.pcfWSigma`](AAR/ParabolicCylinder/WeberUniform.lean#L32) (defined).
- [12.14.E28](https://dlmf.nist.gov/12.14.E28): [`AAR.Confluent.pcfWOlverL`](AAR/ParabolicCylinder/WeberUniform.lean#L42) (defined).
- [12.14.E29](https://dlmf.nist.gov/12.14.E29): [`AAR.Confluent.IsCylinderLNormalizer`](AAR/ParabolicCylinder/WeberUniform.lean#L47) (defined).
- [12.14.E30](https://dlmf.nist.gov/12.14.E30): [`AAR.Confluent.IsCylinderLNormalizer`](AAR/ParabolicCylinder/WeberUniform.lean#L47) (defined).
- [12.14.E31](https://dlmf.nist.gov/12.14.E31): [`AAR.Confluent.pcfW_elementary_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L52) (admitted).
- [12.14.E32](https://dlmf.nist.gov/12.14.E32): [`AAR.Confluent.pcfW_airy_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L60) (admitted).
- [12.14.E33](https://dlmf.nist.gov/12.14.E33): [`AAR.Confluent.pcfW_airy_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L60) (admitted).
- [12.14.E34](https://dlmf.nist.gov/12.14.E34): [`AAR.Confluent.pcfW_elementary_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L52) (admitted).
- [12.14.E35](https://dlmf.nist.gov/12.14.E35): [`AAR.Confluent.pcfW_elementary_uniform`](AAR/ParabolicCylinder/WeberUniform.lean#L52) (admitted).
- [12.14.E36](https://dlmf.nist.gov/12.14.E36): [`AAR.Confluent.pcfWSigmaBar`](AAR/ParabolicCylinder/WeberUniform.lean#L37) (defined).
- [12.14.E37](https://dlmf.nist.gov/12.14.E37): [`AAR.Confluent.pcfWF`](AAR/ParabolicCylinder/Weber.lean#L214) (defined); [`AAR.Confluent.pcfWTheta`](AAR/ParabolicCylinder/Weber.lean#L219) (defined); [`AAR.Confluent.pcfWF_phase`](AAR/ParabolicCylinder/Weber.lean#L224) (admitted).
- [12.14.E38](https://dlmf.nist.gov/12.14.E38): [`AAR.Confluent.pcfWG`](AAR/ParabolicCylinder/Weber.lean#L230) (defined); [`AAR.Confluent.pcfWPsi`](AAR/ParabolicCylinder/Weber.lean#L235) (defined); [`AAR.Confluent.pcfWG_phase`](AAR/ParabolicCylinder/Weber.lean#L240) (admitted).

### [§12.15 Generalized Parabolic Cylinder Functions](https://dlmf.nist.gov/12.15)

- [12.15.E1](https://dlmf.nist.gov/12.15.E1): [`AAR.Confluent.IsGeneralizedCylinderSolution`](AAR/ParabolicCylinder/Basic.lean#L215) (defined).

### [§12.18 Methods of Computation](https://dlmf.nist.gov/12.18)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.19 Tables](https://dlmf.nist.gov/12.19)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.20 Approximations](https://dlmf.nist.gov/12.20)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§12.21 Software](https://dlmf.nist.gov/12.21)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.1 Special Notation](https://dlmf.nist.gov/14.1)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.2 Differential Equations](https://dlmf.nist.gov/14.2)

- [14.2.E1](https://dlmf.nist.gov/14.2.E1): [`ferrersP_ode`](AAR/Legendre/Ferrers.lean#L142) (proved).
- [14.2.E2](https://dlmf.nist.gov/14.2.E2): [`legendreP_ode`](AAR/Legendre/Basic.lean#L118) (proved); [`AAR.Legendre.legendreQ_ode`](AAR/Legendre/SecondKind.lean#L115) (proved); [`AAR.Legendre.associatedP_ode`](AAR/Legendre/Associated.lean#L125) (admitted); [`AAR.Legendre.olverQ_ode`](AAR/Legendre/Associated.lean#L151) (admitted); [`AAR.Legendre.ferrersQ_ode`](AAR/Legendre/Associated.lean#L162) (admitted).
- [14.2.E3](https://dlmf.nist.gov/14.2.E3): [`AAR.Legendre.ferrers_wronskian_3`](AAR/Legendre/Associated.lean#L191) (admitted).
- [14.2.E4](https://dlmf.nist.gov/14.2.E4): [`AAR.Legendre.ferrers_wronskian_4`](AAR/Legendre/Associated.lean#L197) (admitted).
- [14.2.E5](https://dlmf.nist.gov/14.2.E5): [`AAR.Legendre.ferrers_wronskian_5`](AAR/Legendre/Associated.lean#L203) (admitted).
- [14.2.E6](https://dlmf.nist.gov/14.2.E6): [`AAR.Legendre.ferrers_wronskian_6`](AAR/Legendre/Associated.lean#L209) (admitted).
- [14.2.E7](https://dlmf.nist.gov/14.2.E7): [`AAR.Legendre.ferrers_wronskian_7`](AAR/Legendre/Associated.lean#L215) (admitted); [`AAR.Legendre.associated_wronskian_7`](AAR/Legendre/Associated.lean#L221) (admitted).
- [14.2.E8](https://dlmf.nist.gov/14.2.E8): [`AAR.Legendre.associated_wronskian_8`](AAR/Legendre/Associated.lean#L227) (admitted).
- [14.2.E9](https://dlmf.nist.gov/14.2.E9): [`AAR.Legendre.associated_wronskian_9`](AAR/Legendre/Associated.lean#L233) (admitted).
- [14.2.E10](https://dlmf.nist.gov/14.2.E10): [`AAR.Legendre.associated_wronskian_10`](AAR/Legendre/Associated.lean#L239) (admitted).
- [14.2.E11](https://dlmf.nist.gov/14.2.E11): [`AAR.Legendre.associated_wronskian_11`](AAR/Legendre/Associated.lean#L245) (admitted).

### [§14.3 Definitions and Hypergeometric Representations](https://dlmf.nist.gov/14.3)

- [14.3.E1](https://dlmf.nist.gov/14.3.E1): [`ferrersP`](AAR/Legendre/Ferrers.lean#L55) (defined).
- [14.3.E2](https://dlmf.nist.gov/14.3.E2): [`AAR.Legendre.ferrersQ_hypergeometric`](AAR/Legendre/Associated.lean#L66) (admitted); [`AAR.Legendre.ferrersQ_order_limit`](AAR/Legendre/Associated.lean#L72) (admitted).
- [14.3.E3](https://dlmf.nist.gov/14.3.E3): [`AAR.Legendre.legendreGaussF`](AAR/Legendre/Hypergeometric.lean#L28) (defined); [`AAR.Legendre.legendreGaussF_normalization`](AAR/Legendre/Hypergeometric.lean#L34) (proved).
- [14.3.E4](https://dlmf.nist.gov/14.3.E4): [`AAR.Legendre.ferrersP_integer_hypergeometric_4`](AAR/Legendre/Hypergeometric.lean#L41) (admitted).
- [14.3.E5](https://dlmf.nist.gov/14.3.E5): [`AAR.Legendre.ferrersP_integer_hypergeometric_5`](AAR/Legendre/Hypergeometric.lean#L47) (admitted).
- [14.3.E6](https://dlmf.nist.gov/14.3.E6): [`legendreP`](AAR/Legendre/Basic.lean#L51) (defined); [`AAR.Legendre.associatedP`](AAR/Legendre/Associated.lean#L32) (defined).
- [14.3.E7](https://dlmf.nist.gov/14.3.E7): [`AAR.Legendre.legendreQ`](AAR/Legendre/SecondKind.lean#L109) (defined); [`AAR.Legendre.associatedQ`](AAR/Legendre/Associated.lean#L42) (defined).
- [14.3.E8](https://dlmf.nist.gov/14.3.E8): [`AAR.Legendre.associatedP_integer_hypergeometric_8`](AAR/Legendre/Hypergeometric.lean#L53) (admitted).
- [14.3.E9](https://dlmf.nist.gov/14.3.E9): [`AAR.Legendre.associated_hypergeometric_9`](AAR/Legendre/Hypergeometric.lean#L59) (admitted).
- [14.3.E10](https://dlmf.nist.gov/14.3.E10): [`AAR.Legendre.olverQ`](AAR/Legendre/Associated.lean#L37) (defined); [`AAR.Legendre.olverQ_normalization`](AAR/Legendre/Associated.lean#L84) (proved).
- [14.3.E11](https://dlmf.nist.gov/14.3.E11): [`AAR.Legendre.ferrersP_w1_w2`](AAR/Legendre/Associated.lean#L78) (admitted).
- [14.3.E12](https://dlmf.nist.gov/14.3.E12): [`AAR.Legendre.ferrersQ`](AAR/Legendre/Associated.lean#L61) (defined).
- [14.3.E13](https://dlmf.nist.gov/14.3.E13): [`AAR.Legendre.ferrersW1`](AAR/Legendre/Associated.lean#L51) (defined).
- [14.3.E14](https://dlmf.nist.gov/14.3.E14): [`AAR.Legendre.ferrersW2`](AAR/Legendre/Associated.lean#L56) (defined).
- [14.3.E15](https://dlmf.nist.gov/14.3.E15): [`AAR.Legendre.associated_hypergeometric_15`](AAR/Legendre/Hypergeometric.lean#L65) (admitted).
- [14.3.E16](https://dlmf.nist.gov/14.3.E16): [`AAR.Legendre.associated_hypergeometric_16`](AAR/Legendre/Hypergeometric.lean#L71) (admitted).
- [14.3.E17](https://dlmf.nist.gov/14.3.E17): [`AAR.Legendre.associatedP_square_hypergeometric`](AAR/Legendre/Hypergeometric.lean#L89) (admitted).
- [14.3.E18](https://dlmf.nist.gov/14.3.E18): [`AAR.Legendre.associated_hypergeometric_18`](AAR/Legendre/Hypergeometric.lean#L77) (admitted).
- [14.3.E19](https://dlmf.nist.gov/14.3.E19): [`AAR.Legendre.olverQ_linear_hypergeometric`](AAR/Legendre/Hypergeometric.lean#L95) (admitted).
- [14.3.E20](https://dlmf.nist.gov/14.3.E20): [`AAR.Legendre.associated_hypergeometric_20`](AAR/Legendre/Hypergeometric.lean#L83) (admitted).
- [14.3.E21](https://dlmf.nist.gov/14.3.E21): [`AAR.Legendre.ferrersP_gegenbauer`](AAR/Legendre/RelatedFunctions.lean#L35) (admitted).
- [14.3.E22](https://dlmf.nist.gov/14.3.E22): [`AAR.Legendre.associatedP_gegenbauer`](AAR/Legendre/RelatedFunctions.lean#L41) (admitted).
- [14.3.E23](https://dlmf.nist.gov/14.3.E23): [`AAR.Legendre.associatedP_jacobi`](AAR/Legendre/RelatedFunctions.lean#L47) (admitted).

### [§14.5 Special Values](https://dlmf.nist.gov/14.5)

- [14.5.E1](https://dlmf.nist.gov/14.5.E1): [`AAR.Legendre.legendreP_zero_arg`](AAR/Legendre/Recurrences.lean#L89) (proved); [`AAR.Legendre.ferrersP_zero_1`](AAR/Legendre/SpecialValues.lean#L27) (admitted).
- [14.5.E2](https://dlmf.nist.gov/14.5.E2): [`AAR.Legendre.ferrersP_zero_2`](AAR/Legendre/SpecialValues.lean#L33) (admitted).
- [14.5.E3](https://dlmf.nist.gov/14.5.E3): [`AAR.Legendre.ferrersQ_zero_3`](AAR/Legendre/SpecialValues.lean#L39) (admitted).
- [14.5.E4](https://dlmf.nist.gov/14.5.E4): [`AAR.Legendre.ferrersQ_zero_4`](AAR/Legendre/SpecialValues.lean#L45) (admitted).
- [14.5.E5](https://dlmf.nist.gov/14.5.E5): [`AAR.Legendre.ferrersP_degree_0`](AAR/Legendre/SpecialValues.lean#L51) (admitted); [`AAR.Legendre.associatedP_degree_0`](AAR/Legendre/SpecialValues.lean#L69) (admitted).
- [14.5.E6](https://dlmf.nist.gov/14.5.E6): [`AAR.Legendre.ferrersP_degree_1`](AAR/Legendre/SpecialValues.lean#L57) (admitted); [`AAR.Legendre.associatedP_degree_1`](AAR/Legendre/SpecialValues.lean#L75) (admitted).
- [14.5.E7](https://dlmf.nist.gov/14.5.E7): [`AAR.Legendre.ferrersQ_degree_0`](AAR/Legendre/SpecialValues.lean#L87) (admitted).
- [14.5.E8](https://dlmf.nist.gov/14.5.E8): [`AAR.Legendre.ferrersQ_degree_1`](AAR/Legendre/SpecialValues.lean#L93) (admitted).
- [14.5.E9](https://dlmf.nist.gov/14.5.E9): [`AAR.Legendre.olverQ_degree_0`](AAR/Legendre/SpecialValues.lean#L105) (admitted).
- [14.5.E10](https://dlmf.nist.gov/14.5.E10): [`AAR.Legendre.olverQ_degree_1`](AAR/Legendre/SpecialValues.lean#L111) (admitted).
- [14.5.E11](https://dlmf.nist.gov/14.5.E11): [`AAR.Legendre.ferrersP_half_order_11`](AAR/Legendre/SpecialValues.lean#L123) (admitted).
- [14.5.E12](https://dlmf.nist.gov/14.5.E12): [`AAR.Legendre.ferrersP_half_order_12`](AAR/Legendre/SpecialValues.lean#L129) (admitted).
- [14.5.E13](https://dlmf.nist.gov/14.5.E13): [`AAR.Legendre.ferrersQ_half_order_13`](AAR/Legendre/SpecialValues.lean#L135) (admitted).
- [14.5.E14](https://dlmf.nist.gov/14.5.E14): [`AAR.Legendre.ferrersQ_half_order_14`](AAR/Legendre/SpecialValues.lean#L141) (admitted).
- [14.5.E15](https://dlmf.nist.gov/14.5.E15): [`AAR.Legendre.associatedP_half_order_15`](AAR/Legendre/SpecialValues.lean#L147) (admitted).
- [14.5.E16](https://dlmf.nist.gov/14.5.E16): [`AAR.Legendre.associatedP_half_order_16`](AAR/Legendre/SpecialValues.lean#L153) (admitted).
- [14.5.E17](https://dlmf.nist.gov/14.5.E17): [`AAR.Legendre.olverQ_half_order_1`](AAR/Legendre/SpecialValues.lean#L159) (admitted); [`AAR.Legendre.olverQ_half_order_2`](AAR/Legendre/SpecialValues.lean#L165) (admitted).
- [14.5.E18](https://dlmf.nist.gov/14.5.E18): [`AAR.Legendre.ferrersP_negative_degree_order`](AAR/Legendre/SpecialValues.lean#L171) (admitted).
- [14.5.E19](https://dlmf.nist.gov/14.5.E19): [`AAR.Legendre.associatedP_negative_degree_order`](AAR/Legendre/SpecialValues.lean#L177) (admitted).
- [14.5.E20](https://dlmf.nist.gov/14.5.E20): [`AAR.Legendre.legendre_elliptic_20`](AAR/Legendre/SpecialValues.lean#L183) (admitted).
- [14.5.E21](https://dlmf.nist.gov/14.5.E21): [`AAR.Legendre.legendre_elliptic_21`](AAR/Legendre/SpecialValues.lean#L189) (admitted).
- [14.5.E22](https://dlmf.nist.gov/14.5.E22): [`AAR.Legendre.legendre_elliptic_22`](AAR/Legendre/SpecialValues.lean#L195) (admitted).
- [14.5.E23](https://dlmf.nist.gov/14.5.E23): [`AAR.Legendre.legendre_elliptic_23`](AAR/Legendre/SpecialValues.lean#L201) (admitted).
- [14.5.E24](https://dlmf.nist.gov/14.5.E24): [`AAR.Legendre.legendre_elliptic_24`](AAR/Legendre/SpecialValues.lean#L207) (admitted).
- [14.5.E25](https://dlmf.nist.gov/14.5.E25): [`AAR.Legendre.legendre_elliptic_25`](AAR/Legendre/SpecialValues.lean#L213) (admitted).
- [14.5.E26](https://dlmf.nist.gov/14.5.E26): [`AAR.Legendre.legendre_elliptic_26`](AAR/Legendre/SpecialValues.lean#L219) (admitted).
- [14.5.E27](https://dlmf.nist.gov/14.5.E27): [`AAR.Legendre.legendre_elliptic_27`](AAR/Legendre/SpecialValues.lean#L225) (admitted).
- [14.5.E28](https://dlmf.nist.gov/14.5.E28): [`AAR.Legendre.ferrersP_degree_2`](AAR/Legendre/SpecialValues.lean#L63) (admitted); [`AAR.Legendre.associatedP_degree_2`](AAR/Legendre/SpecialValues.lean#L81) (admitted).
- [14.5.E29](https://dlmf.nist.gov/14.5.E29): [`AAR.Legendre.ferrersQ_degree_2`](AAR/Legendre/SpecialValues.lean#L99) (admitted).
- [14.5.E30](https://dlmf.nist.gov/14.5.E30): [`AAR.Legendre.olverQ_degree_2`](AAR/Legendre/SpecialValues.lean#L117) (admitted).

### [§14.6 Integer Order](https://dlmf.nist.gov/14.6)

- [14.6.E1](https://dlmf.nist.gov/14.6.E1): [`ferrersP_nat`](AAR/Legendre/Ferrers.lean#L66) (proved).
- [14.6.E2](https://dlmf.nist.gov/14.6.E2): [`AAR.Legendre.ferrersQ_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L146) (admitted).
- [14.6.E3](https://dlmf.nist.gov/14.6.E3): [`AAR.Legendre.associatedP_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L152) (admitted).
- [14.6.E4](https://dlmf.nist.gov/14.6.E4): [`AAR.Legendre.associatedQ_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L158) (admitted).
- [14.6.E5](https://dlmf.nist.gov/14.6.E5): [`AAR.Legendre.olverQ_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L164) (admitted).
- [14.6.E6](https://dlmf.nist.gov/14.6.E6): [`AAR.Legendre.ferrersP_negative_order_integral`](AAR/Legendre/IntegralRepresentations.lean#L122) (admitted).
- [14.6.E7](https://dlmf.nist.gov/14.6.E7): [`AAR.Legendre.associatedP_negative_order_integral`](AAR/Legendre/IntegralRepresentations.lean#L128) (admitted); [`AAR.Legendre.associatedP_negative_order_integral_complex`](AAR/Legendre/IntegralRepresentations.lean#L140) (admitted).
- [14.6.E8](https://dlmf.nist.gov/14.6.E8): [`AAR.Legendre.associatedQ_negative_order_integral`](AAR/Legendre/IntegralRepresentations.lean#L134) (admitted); [`AAR.Legendre.associatedQ_negative_order_integral_complex`](AAR/Legendre/IntegralRepresentations.lean#L148) (admitted).

### [§14.7 Integer Degree and Order](https://dlmf.nist.gov/14.7)

- [14.7.E1](https://dlmf.nist.gov/14.7.E1): [`AAR.Legendre.ferrersP_nat_polynomial`](AAR/Legendre/IntegerTheory.lean#L33) (proved).
- [14.7.E2](https://dlmf.nist.gov/14.7.E2): [`AAR.Legendre.ferrersQ_nat_logarithm`](AAR/Legendre/Series.lean#L88) (admitted).
- [14.7.E3](https://dlmf.nist.gov/14.7.E3): [`AAR.Legendre.legendreQPoly_explicit`](AAR/Legendre/Series.lean#L67) (admitted).
- [14.7.E4](https://dlmf.nist.gov/14.7.E4): [`AAR.Legendre.legendreQPoly_convolution`](AAR/Legendre/Series.lean#L61) (admitted).
- [14.7.E5](https://dlmf.nist.gov/14.7.E5): [`AAR.Legendre.legendreQPoly_initial`](AAR/Legendre/Series.lean#L73) (proved).
- [14.7.E6](https://dlmf.nist.gov/14.7.E6): [`AAR.Legendre.olverQ_nat_normalization`](AAR/Legendre/Series.lean#L94) (proved).
- [14.7.E7](https://dlmf.nist.gov/14.7.E7): [`AAR.Legendre.associatedQ_nat_logarithm`](AAR/Legendre/Series.lean#L100) (admitted).
- [14.7.E8](https://dlmf.nist.gov/14.7.E8): [`AAR.Legendre.ferrersP_nat_order_rodrigues`](AAR/Legendre/IntegerTheory.lean#L42) (admitted); [`AAR.Legendre.ferrersPNat_eq`](AAR/Legendre/Harmonics.lean#L33) (admitted).
- [14.7.E9](https://dlmf.nist.gov/14.7.E9): [`AAR.Legendre.ferrersQ_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L146) (admitted).
- [14.7.E10](https://dlmf.nist.gov/14.7.E10): [`AAR.Legendre.ferrersP_nat_order_rodrigues`](AAR/Legendre/IntegerTheory.lean#L42) (admitted).
- [14.7.E11](https://dlmf.nist.gov/14.7.E11): [`AAR.Legendre.associatedP_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L152) (admitted).
- [14.7.E12](https://dlmf.nist.gov/14.7.E12): [`AAR.Legendre.associatedQ_nat_order_derivative`](AAR/Legendre/AssociatedRecurrences.lean#L158) (admitted).
- [14.7.E13](https://dlmf.nist.gov/14.7.E13): Mathlib `Polynomial.factorial_mul_shiftedLegendre_eq`; see the [upstream pointer](AAR/Legendre/IntegerTheory.lean).
- [14.7.E14](https://dlmf.nist.gov/14.7.E14): [`AAR.Legendre.associatedP_nat_order_rodrigues`](AAR/Legendre/IntegerTheory.lean#L48) (admitted).
- [14.7.E15](https://dlmf.nist.gov/14.7.E15): [`AAR.Legendre.associatedP_equal_nat_order`](AAR/Legendre/IntegerTheory.lean#L54) (admitted).
- [14.7.E16](https://dlmf.nist.gov/14.7.E16): [`AAR.Legendre.ferrersP_order_gt_degree`](AAR/Legendre/IntegerTheory.lean#L60) (admitted); [`AAR.Legendre.associatedP_order_gt_degree`](AAR/Legendre/IntegerTheory.lean#L66) (admitted).
- [14.7.E17](https://dlmf.nist.gov/14.7.E17): [`AAR.Legendre.ferrersP_nat_reflection`](AAR/Legendre/IntegerTheory.lean#L72) (admitted).
- [14.7.E18](https://dlmf.nist.gov/14.7.E18): [`AAR.Legendre.ferrersQ_nat_reflection_1`](AAR/Legendre/IntegerTheory.lean#L78) (admitted); [`AAR.Legendre.ferrersQ_nat_reflection_2`](AAR/Legendre/IntegerTheory.lean#L84) (admitted).
- [14.7.E19](https://dlmf.nist.gov/14.7.E19): [`AAR.Legendre.ferrersP_generating`](AAR/Legendre/Series.lean#L106) (admitted); [`AAR.Legendre.associatedP_generating_complex`](AAR/Legendre/Series.lean#L124) (admitted).
- [14.7.E20](https://dlmf.nist.gov/14.7.E20): [`AAR.Legendre.ferrersQ_generating`](AAR/Legendre/Series.lean#L112) (admitted).
- [14.7.E21](https://dlmf.nist.gov/14.7.E21): [`AAR.Legendre.associatedP_exterior_generating`](AAR/Legendre/Series.lean#L130) (admitted).
- [14.7.E22](https://dlmf.nist.gov/14.7.E22): [`AAR.Legendre.associatedQ_generating`](AAR/Legendre/Series.lean#L118) (admitted).

### [§14.8 Behavior at Singularities](https://dlmf.nist.gov/14.8)

- [14.8.E1](https://dlmf.nist.gov/14.8.E1): [`AAR.Legendre.legendre_singular_1`](AAR/Legendre/Singularities.lean#L26) (admitted).
- [14.8.E2](https://dlmf.nist.gov/14.8.E2): [`AAR.Legendre.legendre_singular_2`](AAR/Legendre/Singularities.lean#L32) (admitted).
- [14.8.E3](https://dlmf.nist.gov/14.8.E3): [`AAR.Legendre.ferrersQ_log_singular`](AAR/Legendre/Singularities.lean#L104) (admitted).
- [14.8.E4](https://dlmf.nist.gov/14.8.E4): [`AAR.Legendre.legendre_singular_4`](AAR/Legendre/Singularities.lean#L38) (admitted).
- [14.8.E5](https://dlmf.nist.gov/14.8.E5): [`AAR.Legendre.legendre_singular_5`](AAR/Legendre/Singularities.lean#L44) (admitted).
- [14.8.E6](https://dlmf.nist.gov/14.8.E6): [`AAR.Legendre.legendre_singular_6`](AAR/Legendre/Singularities.lean#L50) (admitted).
- [14.8.E7](https://dlmf.nist.gov/14.8.E7): [`AAR.Legendre.legendre_singular_7`](AAR/Legendre/Singularities.lean#L56) (admitted).
- [14.8.E8](https://dlmf.nist.gov/14.8.E8): [`AAR.Legendre.legendre_singular_8`](AAR/Legendre/Singularities.lean#L62) (admitted).
- [14.8.E9](https://dlmf.nist.gov/14.8.E9): [`AAR.Legendre.olverQ_log_singular`](AAR/Legendre/Singularities.lean#L110) (admitted).
- [14.8.E10](https://dlmf.nist.gov/14.8.E10): [`AAR.Legendre.olverQ_negative_degree_singular`](AAR/Legendre/Singularities.lean#L116) (admitted).
- [14.8.E11](https://dlmf.nist.gov/14.8.E11): [`AAR.Legendre.legendre_singular_11`](AAR/Legendre/Singularities.lean#L68) (admitted).
- [14.8.E12](https://dlmf.nist.gov/14.8.E12): [`AAR.Legendre.legendre_singular_12`](AAR/Legendre/Singularities.lean#L74) (admitted).
- [14.8.E13](https://dlmf.nist.gov/14.8.E13): [`AAR.Legendre.legendre_singular_13`](AAR/Legendre/Singularities.lean#L80) (admitted).
- [14.8.E14](https://dlmf.nist.gov/14.8.E14): [`AAR.Legendre.legendre_singular_14`](AAR/Legendre/Singularities.lean#L86) (admitted).
- [14.8.E15](https://dlmf.nist.gov/14.8.E15): [`AAR.Legendre.legendre_singular_15`](AAR/Legendre/Singularities.lean#L92) (admitted).
- [14.8.E16](https://dlmf.nist.gov/14.8.E16): [`AAR.Legendre.legendre_singular_16`](AAR/Legendre/Singularities.lean#L98) (admitted).

### [§14.9 Connection Formulas](https://dlmf.nist.gov/14.9)

- [14.9.E1](https://dlmf.nist.gov/14.9.E1): [`AAR.Legendre.ferrers_connection_1`](AAR/Legendre/Connections.lean#L26) (admitted).
- [14.9.E2](https://dlmf.nist.gov/14.9.E2): [`AAR.Legendre.ferrers_connection_2`](AAR/Legendre/Connections.lean#L32) (admitted).
- [14.9.E3](https://dlmf.nist.gov/14.9.E3): [`AAR.Legendre.ferrersP_negative_order_parameter_limit`](AAR/Legendre/ParameterLimits.lean#L57) (admitted); [`AAR.Legendre.ferrersP_negative_integer_order`](AAR/Legendre/Connections.lean#L74) (admitted).
- [14.9.E4](https://dlmf.nist.gov/14.9.E4): [`AAR.Legendre.ferrersQ_negative_integer_order`](AAR/Legendre/Connections.lean#L80) (admitted).
- [14.9.E5](https://dlmf.nist.gov/14.9.E5): [`legendreP_neg_sub_one`](AAR/Legendre/Basic.lean#L70) (proved); [`AAR.Legendre.ferrers_connection_5`](AAR/Legendre/Connections.lean#L38) (admitted).
- [14.9.E6](https://dlmf.nist.gov/14.9.E6): [`AAR.Legendre.ferrers_connection_6`](AAR/Legendre/Connections.lean#L44) (admitted).
- [14.9.E7](https://dlmf.nist.gov/14.9.E7): [`AAR.Legendre.ferrers_connection_7`](AAR/Legendre/Connections.lean#L50) (admitted).
- [14.9.E8](https://dlmf.nist.gov/14.9.E8): [`AAR.Legendre.ferrers_connection_8`](AAR/Legendre/Connections.lean#L56) (admitted).
- [14.9.E9](https://dlmf.nist.gov/14.9.E9): [`AAR.Legendre.ferrers_connection_9`](AAR/Legendre/Connections.lean#L62) (admitted).
- [14.9.E10](https://dlmf.nist.gov/14.9.E10): [`AAR.Legendre.ferrers_connection_10`](AAR/Legendre/Connections.lean#L68) (admitted).
- [14.9.E11](https://dlmf.nist.gov/14.9.E11): [`AAR.Legendre.associated_connection_11`](AAR/Legendre/Connections.lean#L86) (admitted).
- [14.9.E12](https://dlmf.nist.gov/14.9.E12): [`AAR.Legendre.associated_connection_12`](AAR/Legendre/Connections.lean#L92) (admitted).
- [14.9.E13](https://dlmf.nist.gov/14.9.E13): [`AAR.Legendre.associatedP_negative_order_parameter_limit`](AAR/Legendre/ParameterLimits.lean#L63) (admitted); [`AAR.Legendre.associatedP_negative_integer_order`](AAR/Legendre/Connections.lean#L122) (admitted).
- [14.9.E14](https://dlmf.nist.gov/14.9.E14): [`AAR.Legendre.associated_connection_14`](AAR/Legendre/Connections.lean#L98) (admitted).
- [14.9.E15](https://dlmf.nist.gov/14.9.E15): [`AAR.Legendre.associated_connection_15`](AAR/Legendre/Connections.lean#L104) (admitted).
- [14.9.E16](https://dlmf.nist.gov/14.9.E16): [`AAR.Legendre.associated_connection_16`](AAR/Legendre/Connections.lean#L110) (admitted).
- [14.9.E17](https://dlmf.nist.gov/14.9.E17): [`AAR.Legendre.associated_connection_17`](AAR/Legendre/Connections.lean#L116) (admitted).

### [§14.10 Recurrence Relations and Derivatives](https://dlmf.nist.gov/14.10)

- [14.10.E1](https://dlmf.nist.gov/14.10.E1): [`AAR.Legendre.ferrersP_recurrence_1`](AAR/Legendre/AssociatedRecurrences.lean#L26) (admitted); [`AAR.Legendre.ferrersQ_recurrence_1`](AAR/Legendre/AssociatedRecurrences.lean#L56) (admitted).
- [14.10.E2](https://dlmf.nist.gov/14.10.E2): [`AAR.Legendre.ferrersP_recurrence_2`](AAR/Legendre/AssociatedRecurrences.lean#L32) (admitted); [`AAR.Legendre.ferrersQ_recurrence_2`](AAR/Legendre/AssociatedRecurrences.lean#L62) (admitted).
- [14.10.E3](https://dlmf.nist.gov/14.10.E3): [`AAR.Legendre.legendreP_recurrence`](AAR/Legendre/Recurrences.lean#L31) (proved); [`AAR.Legendre.ferrersP_recurrence_3`](AAR/Legendre/AssociatedRecurrences.lean#L38) (admitted); [`AAR.Legendre.ferrersQ_recurrence_3`](AAR/Legendre/AssociatedRecurrences.lean#L68) (admitted); [`AAR.Legendre.associatedP_recurrence_3`](AAR/Legendre/AssociatedRecurrences.lean#L98) (admitted); [`AAR.Legendre.associatedQ_recurrence_3`](AAR/Legendre/AssociatedRecurrences.lean#L128) (admitted).
- [14.10.E4](https://dlmf.nist.gov/14.10.E4): [`AAR.Legendre.ferrersP_recurrence_4`](AAR/Legendre/AssociatedRecurrences.lean#L44) (admitted); [`AAR.Legendre.ferrersQ_recurrence_4`](AAR/Legendre/AssociatedRecurrences.lean#L74) (admitted); [`AAR.Legendre.associatedP_recurrence_4`](AAR/Legendre/AssociatedRecurrences.lean#L104) (admitted); [`AAR.Legendre.associatedQ_recurrence_4`](AAR/Legendre/AssociatedRecurrences.lean#L134) (admitted).
- [14.10.E5](https://dlmf.nist.gov/14.10.E5): [`AAR.Legendre.ferrersP_recurrence_5`](AAR/Legendre/AssociatedRecurrences.lean#L50) (admitted); [`AAR.Legendre.ferrersQ_recurrence_5`](AAR/Legendre/AssociatedRecurrences.lean#L80) (admitted); [`AAR.Legendre.associatedP_recurrence_5`](AAR/Legendre/AssociatedRecurrences.lean#L110) (admitted); [`AAR.Legendre.associatedQ_recurrence_5`](AAR/Legendre/AssociatedRecurrences.lean#L140) (admitted).
- [14.10.E6](https://dlmf.nist.gov/14.10.E6): [`AAR.Legendre.associatedP_recurrence_6`](AAR/Legendre/AssociatedRecurrences.lean#L86) (admitted); [`AAR.Legendre.associatedQ_recurrence_6`](AAR/Legendre/AssociatedRecurrences.lean#L116) (admitted).
- [14.10.E7](https://dlmf.nist.gov/14.10.E7): [`AAR.Legendre.associatedP_recurrence_7`](AAR/Legendre/AssociatedRecurrences.lean#L92) (admitted); [`AAR.Legendre.associatedQ_recurrence_7`](AAR/Legendre/AssociatedRecurrences.lean#L122) (admitted).

### [§14.11 Derivatives with Respect to Degree or Order](https://dlmf.nist.gov/14.11)

- [14.11.E1](https://dlmf.nist.gov/14.11.E1): [`AAR.Legendre.ferrersP_degree_deriv`](AAR/Legendre/Hypergeometric.lean#L112) (admitted); [`AAR.Legendre.associatedP_degree_deriv`](AAR/Legendre/RelatedFunctions.lean#L57) (admitted).
- [14.11.E2](https://dlmf.nist.gov/14.11.E2): [`AAR.Legendre.ferrersQ_degree_deriv`](AAR/Legendre/Hypergeometric.lean#L118) (admitted).
- [14.11.E3](https://dlmf.nist.gov/14.11.E3): [`AAR.Legendre.legendreDegreeA`](AAR/Legendre/Hypergeometric.lean#L101) (defined); [`AAR.Legendre.legendreDegreeA_hasSum`](AAR/Legendre/Hypergeometric.lean#L106) (admitted).
- [14.11.E4](https://dlmf.nist.gov/14.11.E4): [`AAR.Legendre.ferrersP_order_deriv_zero`](AAR/Legendre/Hypergeometric.lean#L124) (admitted); [`AAR.Legendre.associatedP_order_deriv_zero`](AAR/Legendre/Hypergeometric.lean#L136) (admitted).
- [14.11.E5](https://dlmf.nist.gov/14.11.E5): [`AAR.Legendre.ferrersQ_order_deriv_zero`](AAR/Legendre/Hypergeometric.lean#L130) (admitted).

### [§14.12 Integral Representations](https://dlmf.nist.gov/14.12)

- [14.12.E1](https://dlmf.nist.gov/14.12.E1): [`AAR.Legendre.ferrersP_mehler_dirichlet`](AAR/Legendre/IntegralRepresentations.lean#L27) (admitted).
- [14.12.E2](https://dlmf.nist.gov/14.12.E2): [`AAR.Legendre.ferrersP_fractional_integral`](AAR/Legendre/IntegralRepresentations.lean#L33) (admitted).
- [14.12.E3](https://dlmf.nist.gov/14.12.E3): [`AAR.Legendre.ferrersQ_complex_integral`](AAR/Legendre/IntegralRepresentations.lean#L45) (admitted).
- [14.12.E4](https://dlmf.nist.gov/14.12.E4): [`AAR.Legendre.associatedP_cosh_integral`](AAR/Legendre/IntegralRepresentations.lean#L51) (admitted).
- [14.12.E5](https://dlmf.nist.gov/14.12.E5): [`AAR.Legendre.associatedP_fractional_integral`](AAR/Legendre/IntegralRepresentations.lean#L39) (admitted).
- [14.12.E6](https://dlmf.nist.gov/14.12.E6): [`AAR.Legendre.olverQ_real_integral`](AAR/Legendre/IntegralRepresentations.lean#L57) (admitted).
- [14.12.E7](https://dlmf.nist.gov/14.12.E7): [`AAR.Legendre.associatedP_fourier_integral`](AAR/Legendre/IntegralRepresentations.lean#L63) (admitted).
- [14.12.E8](https://dlmf.nist.gov/14.12.E8): [`AAR.Legendre.associatedP_nat_integral`](AAR/Legendre/IntegralRepresentations.lean#L69) (admitted).
- [14.12.E9](https://dlmf.nist.gov/14.12.E9): [`AAR.Legendre.olverQ_nat_finite_integral`](AAR/Legendre/IntegralRepresentations.lean#L80) (admitted).
- [14.12.E10](https://dlmf.nist.gov/14.12.E10): [`AAR.Legendre.legendreUCoordinate`](AAR/Legendre/IntegralRepresentations.lean#L75) (defined).
- [14.12.E11](https://dlmf.nist.gov/14.12.E11): [`AAR.Legendre.olverQ_nat_interval_integral`](AAR/Legendre/IntegralRepresentations.lean#L86) (admitted).
- [14.12.E12](https://dlmf.nist.gov/14.12.E12): [`AAR.Legendre.olverQ_nat_reduction_integral`](AAR/Legendre/IntegralRepresentations.lean#L92) (admitted).
- [14.12.E13](https://dlmf.nist.gov/14.12.E13): [`AAR.Legendre.olverQ_nat_neumann`](AAR/Legendre/IntegralRepresentations.lean#L98) (admitted).
- [14.12.E14](https://dlmf.nist.gov/14.12.E14): [`AAR.Legendre.olverQ_nat_heine`](AAR/Legendre/IntegralRepresentations.lean#L104) (admitted).

### [§14.13 Trigonometric Expansions](https://dlmf.nist.gov/14.13)

- [14.13.E1](https://dlmf.nist.gov/14.13.E1): [`AAR.Legendre.ferrersP_fourier_series`](AAR/Legendre/Series.lean#L27) (admitted).
- [14.13.E2](https://dlmf.nist.gov/14.13.E2): [`AAR.Legendre.ferrersQ_fourier_series`](AAR/Legendre/Series.lean#L44) (admitted).
- [14.13.E3](https://dlmf.nist.gov/14.13.E3): [`AAR.Legendre.ferrersP_nat_fourier`](AAR/Legendre/Series.lean#L38) (admitted).
- [14.13.E4](https://dlmf.nist.gov/14.13.E4): [`AAR.Legendre.ferrersQ_nat_fourier`](AAR/Legendre/Series.lean#L55) (admitted).

### [§14.14 Continued Fractions](https://dlmf.nist.gov/14.14)

- [14.14.E1](https://dlmf.nist.gov/14.14.E1): [`AAR.Legendre.associatedP_continued_fraction`](AAR/Legendre/Series.lean#L156) (admitted).
- [14.14.E2](https://dlmf.nist.gov/14.14.E2): [`AAR.Legendre.legendrePCFNum`](AAR/Legendre/Series.lean#L136) (defined); [`AAR.Legendre.legendrePCFDen`](AAR/Legendre/Series.lean#L141) (defined).
- [14.14.E3](https://dlmf.nist.gov/14.14.E3): [`AAR.Legendre.associatedQ_continued_fraction`](AAR/Legendre/Series.lean#L162) (admitted).
- [14.14.E4](https://dlmf.nist.gov/14.14.E4): [`AAR.Legendre.legendreQCFNum`](AAR/Legendre/Series.lean#L146) (defined); [`AAR.Legendre.legendreQCFDen`](AAR/Legendre/Series.lean#L151) (defined).

### [§14.15 Uniform Asymptotic Approximations](https://dlmf.nist.gov/14.15)

- [14.15.E1](https://dlmf.nist.gov/14.15.E1): [`AAR.Legendre.ferrersP_large_order_uniform`](AAR/Legendre/Uniform.lean#L28) (admitted).
- [14.15.E2](https://dlmf.nist.gov/14.15.E2): [`AAR.Legendre.associatedP_large_order_uniform`](AAR/Legendre/Uniform.lean#L34) (admitted).
- [14.15.E3](https://dlmf.nist.gov/14.15.E3): [`AAR.Legendre.olverQ_large_order_uniform`](AAR/Legendre/Uniform.lean#L40) (admitted).
- [14.15.E4](https://dlmf.nist.gov/14.15.E4): [`AAR.Legendre.ferrersP_two_large_parameters`](AAR/Legendre/Uniform.lean#L50) (admitted).
- [14.15.E5](https://dlmf.nist.gov/14.15.E5): [`AAR.Legendre.legendreOrderAlpha`](AAR/Legendre/UniformCoordinates.lean#L32) (defined).
- [14.15.E6](https://dlmf.nist.gov/14.15.E6): [`AAR.Legendre.legendreOrderP`](AAR/Legendre/UniformCoordinates.lean#L37) (defined).
- [14.15.E7](https://dlmf.nist.gov/14.15.E7): [`AAR.Legendre.legendreOrderRho`](AAR/Legendre/UniformCoordinates.lean#L42) (defined).
- [14.15.E8](https://dlmf.nist.gov/14.15.E8): [`AAR.Legendre.associatedP_two_large_order_uniform`](AAR/Legendre/Uniform.lean#L56) (admitted).
- [14.15.E9](https://dlmf.nist.gov/14.15.E9): [`AAR.Legendre.olverQ_two_large_order_uniform`](AAR/Legendre/Uniform.lean#L62) (admitted).
- [14.15.E10](https://dlmf.nist.gov/14.15.E10): [`AAR.Legendre.LegendreEtaRelation`](AAR/Legendre/UniformCoordinates.lean#L47) (defined); [`AAR.Legendre.legendreOrderEta`](AAR/Legendre/UniformCoordinates.lean#L52) (defined); [`AAR.Legendre.legendreOrderEta_spec`](AAR/Legendre/UniformCoordinates.lean#L57) (admitted).
- [14.15.E11](https://dlmf.nist.gov/14.15.E11): [`AAR.Legendre.ferrersP_large_degree_uniform`](AAR/Legendre/Uniform.lean#L68) (admitted).
- [14.15.E12](https://dlmf.nist.gov/14.15.E12): [`AAR.Legendre.ferrersQ_large_degree_uniform`](AAR/Legendre/Uniform.lean#L74) (admitted).
- [14.15.E13](https://dlmf.nist.gov/14.15.E13): [`AAR.Legendre.associatedP_large_degree_uniform`](AAR/Legendre/Uniform.lean#L80) (admitted).
- [14.15.E14](https://dlmf.nist.gov/14.15.E14): [`AAR.Legendre.olverQ_large_degree_uniform`](AAR/Legendre/Uniform.lean#L86) (admitted).
- [14.15.E15](https://dlmf.nist.gov/14.15.E15): [`AAR.Legendre.ferrersP_two_large_degree_uniform`](AAR/Legendre/Uniform.lean#L92) (admitted).
- [14.15.E16](https://dlmf.nist.gov/14.15.E16): [`AAR.Legendre.ferrersQ_two_large_degree_uniform`](AAR/Legendre/Uniform.lean#L98) (admitted).
- [14.15.E17](https://dlmf.nist.gov/14.15.E17): [`AAR.Legendre.associatedP_two_large_degree_modified`](AAR/Legendre/Uniform.lean#L104) (admitted).
- [14.15.E18](https://dlmf.nist.gov/14.15.E18): [`AAR.Legendre.olverQ_two_large_degree_modified`](AAR/Legendre/Uniform.lean#L110) (admitted).
- [14.15.E19](https://dlmf.nist.gov/14.15.E19): [`AAR.Legendre.legendreDegreeAlpha`](AAR/Legendre/UniformCoordinates.lean#L68) (defined).
- [14.15.E20](https://dlmf.nist.gov/14.15.E20): [`AAR.Legendre.legendreDegreeBeta`](AAR/Legendre/UniformCoordinates.lean#L73) (defined).
- [14.15.E21](https://dlmf.nist.gov/14.15.E21): [`AAR.Legendre.LegendreYRelation`](AAR/Legendre/UniformCoordinates.lean#L78) (defined); [`AAR.Legendre.legendreDegreeY_spec`](AAR/Legendre/UniformCoordinates.lean#L87) (admitted).
- [14.15.E22](https://dlmf.nist.gov/14.15.E22): [`AAR.Legendre.LegendreYRelation`](AAR/Legendre/UniformCoordinates.lean#L78) (defined); [`AAR.Legendre.legendreDegreeY_spec`](AAR/Legendre/UniformCoordinates.lean#L87) (admitted).
- [14.15.E23](https://dlmf.nist.gov/14.15.E23): [`AAR.Legendre.cylinderEnvelopeCross`](AAR/Legendre/UniformCoordinates.lean#L110) (defined); [`AAR.Legendre.legendreCylinderEnvelope`](AAR/Legendre/UniformCoordinates.lean#L115) (defined); [`AAR.Legendre.cylinderEnvelopeCross_spec`](AAR/Legendre/UniformCoordinates.lean#L160) (admitted).
- [14.15.E24](https://dlmf.nist.gov/14.15.E24): [`AAR.Legendre.ferrersP_cylinder_uniform`](AAR/Legendre/Uniform.lean#L116) (admitted).
- [14.15.E25](https://dlmf.nist.gov/14.15.E25): [`AAR.Legendre.ferrersQ_cylinder_uniform`](AAR/Legendre/Uniform.lean#L122) (admitted).
- [14.15.E26](https://dlmf.nist.gov/14.15.E26): [`AAR.Legendre.legendreCylinderA`](AAR/Legendre/UniformCoordinates.lean#L120) (defined); [`AAR.Legendre.legendreCylinderAlpha`](AAR/Legendre/UniformCoordinates.lean#L125) (defined).
- [14.15.E27](https://dlmf.nist.gov/14.15.E27): [`AAR.Legendre.LegendreCylinderRelation`](AAR/Legendre/UniformCoordinates.lean#L130) (defined); [`AAR.Legendre.legendreCylinderZeta_spec`](AAR/Legendre/UniformCoordinates.lean#L139) (admitted).
- [14.15.E28](https://dlmf.nist.gov/14.15.E28): [`AAR.Legendre.LegendreCylinderRelation`](AAR/Legendre/UniformCoordinates.lean#L130) (defined); [`AAR.Legendre.legendreCylinderZeta_spec`](AAR/Legendre/UniformCoordinates.lean#L139) (admitted).
- [14.15.E29](https://dlmf.nist.gov/14.15.E29): [`AAR.Legendre.LegendreCylinderRelation`](AAR/Legendre/UniformCoordinates.lean#L130) (defined); [`AAR.Legendre.legendreCylinderZeta_spec`](AAR/Legendre/UniformCoordinates.lean#L139) (admitted).
- [14.15.E30](https://dlmf.nist.gov/14.15.E30): [`AAR.Legendre.ferrersP_cylinder_exponential_uniform`](AAR/Legendre/Uniform.lean#L128) (admitted).
- [14.15.E31](https://dlmf.nist.gov/14.15.E31): [`AAR.Legendre.LegendreCylinderRelation`](AAR/Legendre/UniformCoordinates.lean#L130) (defined); [`AAR.Legendre.legendreCylinderZeta_spec`](AAR/Legendre/UniformCoordinates.lean#L139) (admitted).

### [§14.16 Zeros](https://dlmf.nist.gov/14.16)

- [14.16.E1](https://dlmf.nist.gov/14.16.E1): [`AAR.Legendre.legendreIntegerPart`](AAR/Legendre/Zeros.lean#L29) (defined); [`AAR.Legendre.legendreFractionalPart`](AAR/Legendre/Zeros.lean#L34) (defined).

### [§14.17 Integrals](https://dlmf.nist.gov/14.17)

- [14.17.E1](https://dlmf.nist.gov/14.17.E1): [`AAR.Legendre.ferrers_primitive_1`](AAR/Legendre/Primitives.lean#L30) (admitted).
- [14.17.E2](https://dlmf.nist.gov/14.17.E2): [`AAR.Legendre.ferrers_primitive_2`](AAR/Legendre/Primitives.lean#L36) (admitted).
- [14.17.E3](https://dlmf.nist.gov/14.17.E3): [`AAR.Legendre.ferrersProductPrimitive`](AAR/Legendre/Primitives.lean#L42) (defined); [`AAR.Legendre.ferrers_product_primitive_3`](AAR/Legendre/Primitives.lean#L47) (admitted).
- [14.17.E4](https://dlmf.nist.gov/14.17.E4): [`AAR.Legendre.ferrersProductPrimitive`](AAR/Legendre/Primitives.lean#L42) (defined); [`AAR.Legendre.ferrers_product_primitive_4`](AAR/Legendre/Primitives.lean#L53) (admitted).
- [14.17.E5](https://dlmf.nist.gov/14.17.E5): [`AAR.Legendre.ferrers_barnes_integral`](AAR/Legendre/Integrals.lean#L26) (admitted).
- [14.17.E6](https://dlmf.nist.gov/14.17.E6): [`AAR.Legendre.ferrers_orthogonality_6`](AAR/Legendre/Integrals.lean#L32) (admitted).
- [14.17.E7](https://dlmf.nist.gov/14.17.E7): [`AAR.Legendre.ferrers_orthogonality_7`](AAR/Legendre/Integrals.lean#L38) (admitted).
- [14.17.E8](https://dlmf.nist.gov/14.17.E8): [`AAR.Legendre.ferrers_orthogonality_8`](AAR/Legendre/Integrals.lean#L44) (admitted).
- [14.17.E9](https://dlmf.nist.gov/14.17.E9): [`AAR.Legendre.ferrers_orthogonality_9`](AAR/Legendre/Integrals.lean#L50) (admitted).
- [14.17.E10](https://dlmf.nist.gov/14.17.E10): [`AAR.Legendre.ferrers_product_integral_10`](AAR/Legendre/Integrals.lean#L56) (admitted); [`AAR.Legendre.ferrersPP_integral_all_degrees`](AAR/Legendre/ParameterLimits.lean#L45) (admitted).
- [14.17.E11](https://dlmf.nist.gov/14.17.E11): [`AAR.Legendre.ferrers_product_integral_11`](AAR/Legendre/Integrals.lean#L62) (admitted); [`AAR.Legendre.ferrersP_sq_integral_all_degrees`](AAR/Legendre/ParameterLimits.lean#L51) (admitted).
- [14.17.E12](https://dlmf.nist.gov/14.17.E12): [`AAR.Legendre.ferrers_product_integral_12`](AAR/Legendre/Integrals.lean#L68) (admitted).
- [14.17.E13](https://dlmf.nist.gov/14.17.E13): [`AAR.Legendre.ferrers_product_integral_13`](AAR/Legendre/Integrals.lean#L74) (admitted).
- [14.17.E14](https://dlmf.nist.gov/14.17.E14): [`AAR.Legendre.ferrers_product_integral_14`](AAR/Legendre/Integrals.lean#L80) (admitted).
- [14.17.E15](https://dlmf.nist.gov/14.17.E15): [`AAR.Legendre.ferrers_product_integral_15`](AAR/Legendre/Integrals.lean#L86) (admitted).
- [14.17.E16](https://dlmf.nist.gov/14.17.E16): [`AAR.Legendre.ferrersPQ_nat_integral`](AAR/Legendre/Integrals.lean#L92) (admitted).
- [14.17.E17](https://dlmf.nist.gov/14.17.E17): [`AAR.Legendre.ferrers_triple_integral`](AAR/Legendre/Integrals.lean#L98) (admitted).
- [14.17.E18](https://dlmf.nist.gov/14.17.E18): [`AAR.Legendre.legendre_product_integral_18`](AAR/Legendre/Integrals.lean#L104) (admitted).
- [14.17.E19](https://dlmf.nist.gov/14.17.E19): [`AAR.Legendre.legendre_product_integral_19`](AAR/Legendre/Integrals.lean#L110) (admitted).
- [14.17.E20](https://dlmf.nist.gov/14.17.E20): [`AAR.Legendre.legendre_product_integral_20`](AAR/Legendre/Integrals.lean#L116) (admitted).

### [§14.18 Sums](https://dlmf.nist.gov/14.18)

- [14.18.E1](https://dlmf.nist.gov/14.18.E1): [`AAR.Legendre.ferrersP_addition`](AAR/Legendre/Sums.lean#L28) (admitted).
- [14.18.E2](https://dlmf.nist.gov/14.18.E2): [`AAR.Legendre.ferrersP_nat_addition`](AAR/Legendre/Sums.lean#L40) (admitted).
- [14.18.E3](https://dlmf.nist.gov/14.18.E3): [`AAR.Legendre.ferrersQ_addition`](AAR/Legendre/Sums.lean#L34) (admitted).
- [14.18.E4](https://dlmf.nist.gov/14.18.E4): [`AAR.Legendre.associatedP_addition`](AAR/Legendre/Sums.lean#L46) (admitted).
- [14.18.E5](https://dlmf.nist.gov/14.18.E5): [`AAR.Legendre.associatedQ_addition`](AAR/Legendre/Sums.lean#L52) (admitted).
- [14.18.E6](https://dlmf.nist.gov/14.18.E6): [`AAR.Legendre.legendre_christoffel_6`](AAR/Legendre/Sums.lean#L58) (admitted).
- [14.18.E7](https://dlmf.nist.gov/14.18.E7): [`AAR.Legendre.legendre_christoffel_7`](AAR/Legendre/Sums.lean#L64) (admitted).
- [14.18.E8](https://dlmf.nist.gov/14.18.E8): [`AAR.Legendre.ferrersP_zonal_series`](AAR/Legendre/Sums.lean#L70) (admitted).
- [14.18.E9](https://dlmf.nist.gov/14.18.E9): [`AAR.Legendre.ferrersP_dougall_series`](AAR/Legendre/Sums.lean#L76) (admitted).

### [§14.19 Toroidal (or Ring) Functions](https://dlmf.nist.gov/14.19)

- [14.19.E1](https://dlmf.nist.gov/14.19.E1): [`AAR.Legendre.toroidalCoordinates`](AAR/Legendre/Toroidal.lean#L27) (defined).
- [14.19.E2](https://dlmf.nist.gov/14.19.E2): [`AAR.Legendre.toroidalP_hypergeometric`](AAR/Legendre/Toroidal.lean#L40) (admitted).
- [14.19.E3](https://dlmf.nist.gov/14.19.E3): [`AAR.Legendre.toroidalQ_hypergeometric`](AAR/Legendre/Toroidal.lean#L46) (admitted).
- [14.19.E4](https://dlmf.nist.gov/14.19.E4): [`AAR.Legendre.toroidalP_integral`](AAR/Legendre/Toroidal.lean#L52) (admitted).
- [14.19.E5](https://dlmf.nist.gov/14.19.E5): [`AAR.Legendre.toroidalQ_integral`](AAR/Legendre/Toroidal.lean#L58) (admitted).
- [14.19.E6](https://dlmf.nist.gov/14.19.E6): [`AAR.Legendre.toroidalQ_fourier`](AAR/Legendre/Toroidal.lean#L64) (admitted).
- [14.19.E7](https://dlmf.nist.gov/14.19.E7): [`AAR.Legendre.toroidal_whipple_P`](AAR/Legendre/Toroidal.lean#L70) (admitted).
- [14.19.E8](https://dlmf.nist.gov/14.19.E8): [`AAR.Legendre.toroidal_whipple_Q`](AAR/Legendre/Toroidal.lean#L76) (admitted).

### [§14.20 Conical (or Mehler) Functions](https://dlmf.nist.gov/14.20)

- [14.20.E1](https://dlmf.nist.gov/14.20.E1): [`AAR.Legendre.conical_ode`](AAR/Legendre/Conical.lean#L36) (admitted).
- [14.20.E2](https://dlmf.nist.gov/14.20.E2): [`AAR.Legendre.conicalQHat`](AAR/Legendre/Conical.lean#L31) (defined).
- [14.20.E3](https://dlmf.nist.gov/14.20.E3): [`AAR.Legendre.conicalQHat_connection`](AAR/Legendre/Conical.lean#L42) (admitted).
- [14.20.E4](https://dlmf.nist.gov/14.20.E4): [`AAR.Legendre.conical_wronskian`](AAR/Legendre/Conical.lean#L48) (admitted).
- [14.20.E5](https://dlmf.nist.gov/14.20.E5): [`AAR.Legendre.conicalQHat_wronskian`](AAR/Legendre/Conical.lean#L54) (admitted).
- [14.20.E6](https://dlmf.nist.gov/14.20.E6): [`AAR.Legendre.conical_associated_connection`](AAR/Legendre/Conical.lean#L60) (admitted).
- [14.20.E7](https://dlmf.nist.gov/14.20.E7): [`AAR.Legendre.conical_singular_7`](AAR/Legendre/Conical.lean#L66) (admitted).
- [14.20.E8](https://dlmf.nist.gov/14.20.E8): [`AAR.Legendre.conical_singular_8`](AAR/Legendre/Conical.lean#L72) (admitted).
- [14.20.E9](https://dlmf.nist.gov/14.20.E9): [`AAR.Legendre.conical_mehler_integral`](AAR/Legendre/Conical.lean#L78) (admitted).
- [14.20.E10](https://dlmf.nist.gov/14.20.E10): [`AAR.Legendre.conical_power_series`](AAR/Legendre/Conical.lean#L84) (admitted).
- [14.20.E11](https://dlmf.nist.gov/14.20.E11): [`AAR.Legendre.mehlerFockTransform`](AAR/Legendre/Conical.lean#L95) (defined).
- [14.20.E12](https://dlmf.nist.gov/14.20.E12): [`AAR.Legendre.mehlerFockInverse`](AAR/Legendre/Conical.lean#L100) (defined).
- [14.20.E13](https://dlmf.nist.gov/14.20.E13): [`AAR.Legendre.conical_stieltjes_integral`](AAR/Legendre/Conical.lean#L105) (admitted).
- [14.20.E14](https://dlmf.nist.gov/14.20.E14): [`AAR.Legendre.conical_product_transform`](AAR/Legendre/Conical.lean#L111) (admitted).
- [14.20.E15](https://dlmf.nist.gov/14.20.E15): [`AAR.Legendre.conicalP_large_tau_uniform`](AAR/Legendre/ConicalAsymptotics.lean#L28) (admitted).
- [14.20.E16](https://dlmf.nist.gov/14.20.E16): [`AAR.Legendre.conicalQHat_large_tau_uniform`](AAR/Legendre/ConicalAsymptotics.lean#L34) (admitted).
- [14.20.E17](https://dlmf.nist.gov/14.20.E17): [`AAR.Legendre.conicalP_two_large_tau_uniform`](AAR/Legendre/ConicalAsymptotics.lean#L71) (admitted).
- [14.20.E18](https://dlmf.nist.gov/14.20.E18): [`AAR.Legendre.conicalQHat_two_large_tau_uniform`](AAR/Legendre/ConicalAsymptotics.lean#L77) (admitted).
- [14.20.E19](https://dlmf.nist.gov/14.20.E19): [`AAR.Legendre.conicalAlpha`](AAR/Legendre/ConicalAsymptotics.lean#L40) (defined).
- [14.20.E20](https://dlmf.nist.gov/14.20.E20): [`AAR.Legendre.conicalSigma`](AAR/Legendre/ConicalAsymptotics.lean#L45) (defined).
- [14.20.E21](https://dlmf.nist.gov/14.20.E21): [`AAR.Legendre.ConicalEtaRelation`](AAR/Legendre/ConicalAsymptotics.lean#L50) (defined); [`AAR.Legendre.conicalEta`](AAR/Legendre/ConicalAsymptotics.lean#L55) (defined); [`AAR.Legendre.conicalEta_spec`](AAR/Legendre/ConicalAsymptotics.lean#L60) (admitted).
- [14.20.E22](https://dlmf.nist.gov/14.20.E22): [`AAR.Legendre.conicalP_two_large_mu_uniform`](AAR/Legendre/ConicalAsymptotics.lean#L98) (admitted).
- [14.20.E23](https://dlmf.nist.gov/14.20.E23): [`AAR.Legendre.conicalBeta`](AAR/Legendre/ConicalAsymptotics.lean#L83) (defined).
- [14.20.E24](https://dlmf.nist.gov/14.20.E24): [`AAR.Legendre.conicalRho`](AAR/Legendre/ConicalAsymptotics.lean#L88) (defined).

### [§14.21 Definitions and Basic Properties](https://dlmf.nist.gov/14.21)

- [14.21.E1](https://dlmf.nist.gov/14.21.E1): [`AAR.Legendre.associatedP_ode`](AAR/Legendre/Associated.lean#L125) (admitted); [`AAR.Legendre.olverQ_ode`](AAR/Legendre/Associated.lean#L151) (admitted).

### [§14.23 Values on the Cut](https://dlmf.nist.gov/14.23)

- [14.23.E1](https://dlmf.nist.gov/14.23.E1): [`AAR.Legendre.associatedP_boundary_upper`](AAR/Legendre/Continuation.lean#L31) (admitted); [`AAR.Legendre.associatedP_boundary_lower`](AAR/Legendre/Continuation.lean#L61) (admitted).
- [14.23.E2](https://dlmf.nist.gov/14.23.E2): [`AAR.Legendre.olverQ_boundary_upper`](AAR/Legendre/Continuation.lean#L37) (admitted); [`AAR.Legendre.olverQ_boundary_lower`](AAR/Legendre/Continuation.lean#L67) (admitted).
- [14.23.E3](https://dlmf.nist.gov/14.23.E3): [`AAR.Legendre.olverQ_boundary_hypergeometric_upper`](AAR/Legendre/Continuation.lean#L55) (admitted); [`AAR.Legendre.olverQ_boundary_hypergeometric_lower`](AAR/Legendre/Continuation.lean#L85) (admitted).
- [14.23.E4](https://dlmf.nist.gov/14.23.E4): [`AAR.Legendre.ferrersP_boundary_inverse_upper`](AAR/Legendre/Continuation.lean#L43) (admitted); [`AAR.Legendre.ferrersP_boundary_inverse_lower`](AAR/Legendre/Continuation.lean#L73) (admitted).
- [14.23.E5](https://dlmf.nist.gov/14.23.E5): [`AAR.Legendre.ferrersQ_boundary_average`](AAR/Legendre/Continuation.lean#L91) (admitted).
- [14.23.E6](https://dlmf.nist.gov/14.23.E6): [`AAR.Legendre.ferrersQ_boundary_inverse_upper`](AAR/Legendre/Continuation.lean#L49) (admitted); [`AAR.Legendre.ferrersQ_boundary_inverse_lower`](AAR/Legendre/Continuation.lean#L79) (admitted).
- [14.23.E7](https://dlmf.nist.gov/14.23.E7): [`AAR.Legendre.conicalQHat_boundary`](AAR/Legendre/Continuation.lean) (proved; corrected, DLMF prints e^{-3μπi/2} where e^{μπi/2} is required).

### [§14.24 Analytic Continuation](https://dlmf.nist.gov/14.24)

- [14.24.E1](https://dlmf.nist.gov/14.24.E1): [`AAR.Legendre.associatedP_ellipse_continuation`](AAR/Legendre/Continuation.lean#L129) (admitted).
- [14.24.E2](https://dlmf.nist.gov/14.24.E2): [`AAR.Legendre.olverQ_ellipse_continuation`](AAR/Legendre/Continuation.lean#L135) (admitted).
- [14.24.E3](https://dlmf.nist.gov/14.24.E3): [`AAR.Legendre.associatedP_one_continuation`](AAR/Legendre/Continuation.lean#L153) (admitted).
- [14.24.E4](https://dlmf.nist.gov/14.24.E4): [`AAR.Legendre.olverQ_one_continuation`](AAR/Legendre/Continuation.lean#L159) (admitted).

### [§14.25 Integral Representations](https://dlmf.nist.gov/14.25)

- [14.25.E1](https://dlmf.nist.gov/14.25.E1): [`AAR.Legendre.associatedP_complex_integral`](AAR/Legendre/IntegralRepresentations.lean#L110) (admitted).
- [14.25.E2](https://dlmf.nist.gov/14.25.E2): [`AAR.Legendre.olverQ_complex_integral`](AAR/Legendre/IntegralRepresentations.lean#L116) (admitted).

### [§14.26 Uniform Asymptotic Expansions](https://dlmf.nist.gov/14.26)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.27 Zeros](https://dlmf.nist.gov/14.27)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.28 Sums](https://dlmf.nist.gov/14.28)

- [14.28.E1](https://dlmf.nist.gov/14.28.E1): [`AAR.Legendre.associatedP_complex_addition`](AAR/Legendre/Sums.lean#L98) (admitted).
- [14.28.E2](https://dlmf.nist.gov/14.28.E2): [`AAR.Legendre.legendre_heine_series`](AAR/Legendre/Sums.lean#L86) (admitted); [`AAR.Legendre.legendre_heine_uniform`](AAR/Legendre/Sums.lean#L92) (admitted).

### [§14.29 Generalizations](https://dlmf.nist.gov/14.29)

- [14.29.E1](https://dlmf.nist.gov/14.29.E1): [`AAR.Legendre.IsGeneralizedLegendreSolution`](AAR/Legendre/Associated.lean#L251) (defined); [`AAR.Legendre.generalizedLegendre_equal_orders`](AAR/Legendre/Associated.lean#L256) (proved).

### [§14.30 Spherical and Spheroidal Harmonics](https://dlmf.nist.gov/14.30)

- [14.30.E1](https://dlmf.nist.gov/14.30.E1): [`AAR.Legendre.sphericalHarmonicNonneg`](AAR/Legendre/Harmonics.lean#L39) (defined); [`AAR.Legendre.sphericalHarmonic`](AAR/Legendre/Harmonics.lean#L44) (defined); [`AAR.Legendre.sphericalHarmonic_ferrers`](AAR/Legendre/Harmonics.lean#L49) (admitted).
- [14.30.E2](https://dlmf.nist.gov/14.30.E2): [`AAR.Legendre.surfaceHarmonic`](AAR/Legendre/Harmonics.lean#L55) (defined).
- [14.30.E3](https://dlmf.nist.gov/14.30.E3): [`AAR.Legendre.sphericalHarmonic_rodrigues`](AAR/Legendre/Harmonics.lean#L60) (admitted).
- [14.30.E4](https://dlmf.nist.gov/14.30.E4): [`AAR.Legendre.sphericalHarmonic_north`](AAR/Legendre/Harmonics.lean#L66) (admitted).
- [14.30.E5](https://dlmf.nist.gov/14.30.E5): [`AAR.Legendre.sphericalHarmonic_equator`](AAR/Legendre/Harmonics.lean#L72) (admitted).
- [14.30.E6](https://dlmf.nist.gov/14.30.E6): [`AAR.Legendre.sphericalHarmonic_negative_order`](AAR/Legendre/Harmonics.lean#L78) (admitted).
- [14.30.E7](https://dlmf.nist.gov/14.30.E7): [`AAR.Legendre.sphericalHarmonic_parity`](AAR/Legendre/Harmonics.lean#L84) (admitted).
- [14.30.E8](https://dlmf.nist.gov/14.30.E8): [`AAR.Legendre.sphericalHarmonic_orthonormal`](AAR/Legendre/Harmonics.lean#L90) (admitted).
- [14.30.E9](https://dlmf.nist.gov/14.30.E9): [`AAR.Legendre.sphericalHarmonic_addition`](AAR/Legendre/Harmonics.lean#L96) (admitted).

### [§14.32 Methods of Computation](https://dlmf.nist.gov/14.32)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.33 Tables](https://dlmf.nist.gov/14.33)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

### [§14.34 Software](https://dlmf.nist.gov/14.34)

No selected numbered equations. Mathematical prose is recorded in the module inventory where applicable.

## Validation and counts

The ordinary `lake build > /tmp/AAR-build.log 2>&1` passes (9,791 jobs).
Final direct `lake env lean` checks cover all 48 changed or new Lean files,
including the three subject entry points and `AAR.lean`, plus `Main.lean` (49 checks).
The source comparison verifies that all 626 initial theorem statements were retained
except the explicitly reviewed mathematical corrections described above. No old
admission was silently removed or counted as a proof. The dependency pins, toolchain,
Lake build directory and existing cache symlink are unchanged.

The final compiled audit covers 6,971 public `AAR.*` theorem declarations. Exactly
1,609 depend on `sorryAx`, matching the explicit source admissions: 601 from this
acquisition, plus the previous 1,008. There are no completed public proofs depending
on an admission and no unexpected axioms. The 25 new completed proofs and both
upstream pointers were checked separately. Only Lean's standard `propext`,
`Classical.choice` and `Quot.sound` occur in their axiom dependencies.

The source census covers 330 Lean files under `AAR/` and `ToMathlib/`, with admissions
in 118 files. The new theory occupies 44 substantive modules, two new entry modules
and the expanded existing Legendre entry point. `ToMathlib` retains no admissions.
The admission scan, direct-file checks, axiom audit and whitespace/link checks pass.
These checks validate the accepted Lean proofs and the acquisition inventory;
they do not establish the truth of admitted statements.
