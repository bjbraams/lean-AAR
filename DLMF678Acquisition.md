# DLMF Chapters 6–8 acquisition (2026-10-19)

The source is NIST DLMF version 1.2.8, downloaded and reviewed on 2026-10-19.
The acquisition covers **468 active numbered equations**: 95 in Chapter 6,
136 in Chapter 7 and 237 in Chapter 8. There are 469 numbered slots, because
8.18.13 is a retired equation that now points to 5.11.3. Of the active labels,
467 have Lean declarations and 8.17.3 is covered directly by Mathlib.

This is a statement acquisition and an initial proof batch, not a completed
proof of these chapters. The 30 new modules contain **160 concrete definitions**
and **547 initially admitted theorem statements**. **19 are now proved**;
**528 new admissions remain**. The project now has **1,008 source admissions in
76 files**, across 284 Lean files under `AAR/` and `ToMathlib/`. The previous
480 obligations, including 363 in Airy, are unchanged.

## Scope and project policy

The exported entry modules are [ExpIntegrals](AAR/ExpIntegrals.lean),
[ErrorFunctions](AAR/ErrorFunctions.lean) and
[IncompleteGamma](AAR/IncompleteGamma.lean). Existing real-variable functions
and their proofs are retained. The only change to an existing theory source
is the addition of two DLMF attributes to already proved exponential-integral
identities; their statements and proofs are unchanged.

- Excluded graphical sections: 6.3, 7.3 and 8.3, together with the graphical
  subsections inside 7.18, 7.19 and 8.19.
- Excluded application notes: 6.16–6.17, 7.20–7.21 and 8.22–8.24.
- Computational sections remain in scope when they state explicit mathematics:
  the Acton recurrences in 6.18 and the DiDonato approximation with its
  `O(x⁻⁷)` error in 8.27 are acquired.
- Explicit unnumbered results are acquired, including entire/meromorphic
  dependence, residues, monotonicity, zero classification and enumeration,
  the inverse-erf coefficient recurrence, and the extra Laplace transform
  following 7.14.4. Numerical Tables 7.13.1–4 and 8.13.1 become rational bounds.
- Special notation is recorded through definitions and a glossary: the
  alternative functions of 7.1 are defined in `ErrorFunctions.Basic`; the aliases
  of 8.1 are recorded in `DLMF.MathlibCoverage`.
- Bibliographic lists, software lists and pointers to results whose formulas
  appear only in cited papers do not acquire the contents of those papers.
  Thus 8.16 contains no additional explicit formula to formalize. Unquantified
  descriptions such as “closed form,” “rapid convergence” and numerical
  stability are retained as source guidance; they are not assigned invented
  numerical performance bounds.

Your rule is recorded in [AGENTS.md](AGENTS.md): when Mathlib already provides a
DLMF result, add a comment and precise upstream pointer rather than reprove it.

## Mathlib and existing coverage

[MathlibCoverage.lean](AAR/DLMF/MathlibCoverage.lean) records the checked pointers:

- 8.17.3: `Complex.betaIntegral_eq_Gamma_mul_div`, in
  `Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean`. No duplicate local theorem
  is introduced for the complete Beta/Gamma identity.
- 8.2.1 for a real nonnegative endpoint: `Complex.partialGamma`, in
  `Mathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`.
- 8.8.1 in the corresponding integral domain: `Complex.partialGamma_add_one`.
- The Gaussian specialization of 7.7.6: `integral_gaussian_complex_Ioi`, in
  `Mathlib/Analysis/SpecialFunctions/Gaussian/GaussianIntegral.lean`, and its
  full-line counterpart `integral_gaussian_complex`.

The new continued fractions use Mathlib's `GenContFract.nextConts` for their
continuant recurrence. The helper adds explicit termination and argument
conventions; it introduces no new continued-fraction proof theory.

Mathlib's Hurwitz zeta takes a periodic real argument, so it does not supply the
complex second argument in 8.15.2. The acquisition defines an Euler–Maclaurin
continuation and an admitted bridge on the overlap. The named real error and
inverse error functions imported by the project come from TauCeti. In
particular, `Real.erfInv` is in TauCeti's source despite its unprefixed namespace.
The new inverse definitions reuse it.

## Branches, convergence and exceptional values

- Complex `Ein`, `Si`, `Cin` and `Shi` use entire power series. `E₁`, `Ci` and
  `Chi` retain their principal logarithms. Continued versions use an explicit
  logarithmic coordinate. Boundary-value theorems specify approach from above
  and below the negative axis.
- Oscillatory integrals assert limits of finite integrals. Whole-line formulas
  assert convergence of both tails, and principal values specify the symmetric
  limit separately from the infinite tail. Finite complex integrals have
  explicit segment Jacobians. Fresnel tails approach infinity on the original
  real ray after continuation, not on a horizontally shifted ray that could
  produce exponential growth.
- Square arguments in the error/Gamma and error/U formulas retain `2 log z`.
  Principal-branch statements on the right half-plane have additional
  logarithmic-plane versions on the whole punctured plane. Modified spherical
  Bessel functions are defined with entire regularized ₀F₁ formulas, so no
  artificial square-root cut is introduced at negative arguments.
- Uniform expansions use filters with explicit parameter domains, finite
  truncations and remainders. They are not equalities to totalized divergent
  infinite sums. Logarithmic sectors can exceed a principal argument interval.
  Uniform transition coefficients are concretely defined by derivatives,
  specified normalized analytic inverses, removable limits or successive
  asymptotic coefficient limits. Their existence and asserted expansions remain
  proof obligations; a definition using `limUnder` or `Classical.epsilon` does
  not prove its specification.
- The Paris transition expansion 8.12.18 specifies uniformity for bounded χ on
  closed right-half-plane sectors. The general Beta expansion 8.18.14 keeps
  the full positive b range and a `sqrt(1+b/a)` coefficient-growth envelope
  after normalization. These explicit remainder formulations remain admitted
  and require analytic justification during proof development.
- `normIncGammaPContinued` and `normIncGammaQContinued` give the analytic
  exceptional-parameter values. They have bridge statements to the existing
  quotient functions at regular parameters. The existing quotients keep their
  totalized values at Gamma poles.
- `genExpIntEExtended` supplies the value `1/(p-1)` at zero when `Re p>1`.
  The old `genExpIntE` definition is preserved. Positive-integer series and
  monodromy formulas have explicit limiting forms.
- The upper incomplete Gamma continuation remains meaningful at integral a.
  Mellin–Barnes formulas specify separating lines, finite crossed-pole
  residues and inherited logarithms. The pole bypass in 8.6.9 is represented by
  a convergent symmetric principal value plus its signed indentation term.
- Generalized trigonometric integrals distinguish their sine and cosine
  parameter poles. Products `Γ(a)sin(πa/2)` and `Γ(a)cos(πa/2)` fill removable
  singularities by limits. Ordinary limits at infinity require `Re a<1`;
  values outside the convergence region have their parameter-continuation
  meaning rather than an unsupported improper-integral claim.
- Fresnel zero representatives lie in the first octant. Rotation and conjugation
  supply the other octants. Counting all first-quadrant zeros would create
  equal-modulus ties. The two coalescing parameter zeros in 8.13 are counted
  with multiplicity: at the threshold there is one distinct double zero.
- Normalized inverse Q uses `ENNReal` so that q=0 has x=∞ and q=1 has x=0.
  The incomplete Beta inverse includes both endpoints of [0,1].

## Source qualifications and a proved counterexample

The universal upper/lower convergent claim following DLMF 8.17.23 is false
without further qualifications. With `a=1`, `b=1/2`, `x=1/2`,

- `Iₓ(a,b)=1-sqrt(2)/2`.
- The two-level continued fraction is `sqrt(2)/5`, strictly below I.
- The three-level continued fraction is `23 sqrt(2)/112`, also strictly below I.

All four bound/value statements are proved in
[Beta.lean](AAR/IncompleteGamma/Beta.lean), using the existing proved incomplete
Beta symmetry and power specializations. Thus the counterexample covers both
common indexing conventions. The unqualified source inequality is recorded as
an error, not introduced as an admitted universal theorem. The continued-fraction
convergence identity itself remains an obligation.

Additional explicit qualifications are:

- Continued fractions use a ratio of continuants and stop at a zero partial
  numerator. Nested totalized division can give incorrect values at an internal
  zero denominator. This infrastructure definition was corrected during review.
- The Beta fraction is acquired for x<1. Its value at x=1 is a separate endpoint
  limit; multiplying each finite convergent by a zero endpoint prefactor would
  incorrectly produce zero. Some downward parameter recurrences have poles at
  a+b=1; their limiting statements are separate from their totalized formulas.
- The integral in 8.10.8 needs a>0. Its a=0 normalized boundary is an explicit
  limit. The scaled power bounds in 8.10.10 likewise use their limit at x=0.
- The “equalities only for a=1” description of 8.10.11 needs x>0: at x=0 both
  exponential bounds are zero for every a>0. The strict theorem has x>0.
- 8.19.25 needs `Re b>0` for convergence at the zero endpoint, in addition to
  the displayed conditions. For example, p>1 does not remove that endpoint
  obstruction when `Re b≤0`.
- The 8.14 transforms and 8.19.24 include removable zero-parameter limits.
  The 8.15.2 Fourier sum states a right-half-plane convergence domain and
  excludes its singular a=-1 expression. These domains are not silently
  inferred from totalized division.

## Module status

- [MathlibCoverage](AAR/DLMF/MathlibCoverage.lean): upstream pointer comments; no admissions.
- [Framework](AAR/DLMF/Framework.lean): 0 admissions.
- [Basic](AAR/ErrorFunctions/Basic.lean): 18 admissions.
- [BoundsAsymptotics](AAR/ErrorFunctions/BoundsAsymptotics.lean): 21 admissions.
- [Integrals](AAR/ErrorFunctions/Integrals.lean): 25 admissions.
- [InverseGeneralized](AAR/ErrorFunctions/InverseGeneralized.lean): 5 admissions.
- [Relations](AAR/ErrorFunctions/Relations.lean): 28 admissions.
- [Repeated](AAR/ErrorFunctions/Repeated.lean): 16 admissions.
- [Series](AAR/ErrorFunctions/Series.lean): 12 admissions.
- [Voigt](AAR/ErrorFunctions/Voigt.lean): 9 admissions.
- [Zeros](AAR/ErrorFunctions/Zeros.lean): 33 admissions.
- [Asymptotics](AAR/ExpIntegrals/Asymptotics.lean): 11 admissions.
- [Basic](AAR/ExpIntegrals/Basic.lean): 29 admissions.
- [Continuation](AAR/ExpIntegrals/Continuation.lean): 14 admissions.
- [Expansions](AAR/ExpIntegrals/Expansions.lean): 12 admissions.
- [Representations](AAR/ExpIntegrals/Representations.lean): 22 admissions.
- [ZerosIntegrals](AAR/ExpIntegrals/ZerosIntegrals.lean): 20 admissions.
- [Asymptotics](AAR/IncompleteGamma/Asymptotics.lean): 16 admissions.
- [Basic](AAR/IncompleteGamma/Basic.lean): 17 admissions.
- [Beta](AAR/IncompleteGamma/Beta.lean): 20 admissions.
- [BetaAsymptotics](AAR/IncompleteGamma/BetaAsymptotics.lean): 20 admissions.
- [BoundsFractions](AAR/IncompleteGamma/BoundsFractions.lean): 19 admissions.
- [ExpIntegralAsymptotics](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean): 5 admissions.
- [ExponentialIntegral](AAR/IncompleteGamma/ExponentialIntegral.lean): 28 admissions.
- [Representations](AAR/IncompleteGamma/Representations.lean): 13 admissions.
- [SeriesRecurrences](AAR/IncompleteGamma/SeriesRecurrences.lean): 23 admissions.
- [SineCosine](AAR/IncompleteGamma/SineCosine.lean): 31 admissions.
- [SpecialValues](AAR/IncompleteGamma/SpecialValues.lean): 19 admissions.
- [UniformAsymptotics](AAR/IncompleteGamma/UniformAsymptotics.lean): 21 admissions.
- [ZerosIntegrals](AAR/IncompleteGamma/ZerosIntegrals.lean): 21 admissions.

## Completed first proof batch

Each statement below was initially admitted. Its current proof has no transitive
`sorryAx` dependency. Existing Mathlib and TauCeti results retain their ownership.

- [AAR.Confluent.Real.invErf_spec](AAR/ErrorFunctions/InverseGeneralized.lean#L52).
- [AAR.Confluent.Real.invErfc_spec](AAR/ErrorFunctions/InverseGeneralized.lean#L58).
- [AAR.Confluent.invErfSeriesCoeff_initial](AAR/ErrorFunctions/InverseGeneralized.lean#L76).
- [AAR.Confluent.erf_negative](AAR/ErrorFunctions/Relations.lean#L25).
- [AAR.Confluent.erfc_negative](AAR/ErrorFunctions/Relations.lean#L31).
- [AAR.Confluent.faddeevaW_negative](AAR/ErrorFunctions/Relations.lean#L38).
- [AAR.Confluent.fresnel_sum_tail](AAR/ErrorFunctions/Relations.lean#L81).
- [AAR.Confluent.expIntInverseFactorialCoeff_initial](AAR/ExpIntegrals/Expansions.lean#L68).
- [AAR.Confluent.expIntE1_eq_upperIncGamma](AAR/ExpIntegrals/Expansions.lean#L110).
- [AAR.Confluent.expIntE1_eq_kummerU](AAR/ExpIntegrals/Expansions.lean#L116).
- [AAR.Confluent.incGammaLambdaPolynomial_initial](AAR/IncompleteGamma/Asymptotics.lean#L73).
- [AAR.Confluent.normIncGammaContinued_complement](AAR/IncompleteGamma/Basic.lean#L77).
- [AAR.Statistical.incBeta_cf_upper_bound_counterexample](AAR/IncompleteGamma/Beta.lean#L165).
- [AAR.Statistical.incBeta_cf_second_counterexample_value](AAR/IncompleteGamma/Beta.lean#L185).
- [AAR.Statistical.incBeta_cf_third_bound_counterexample](AAR/IncompleteGamma/Beta.lean#L209).
- [AAR.Statistical.incBeta_cf_third_counterexample_value](AAR/IncompleteGamma/Beta.lean#L229).
- [AAR.Confluent.expIntLargeOrderPolynomial_initial](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L50).
- [AAR.Confluent.upperIncGamma_zero_E1](AAR/IncompleteGamma/SpecialValues.lean#L50).
- [AAR.Confluent.upperIncGamma_kummerU_pair](AAR/IncompleteGamma/SpecialValues.lean#L122).

## Equation-by-equation inventory

A label may have a proved real specialization together with admitted complex
extensions. Each declaration's status is stated separately. A source-error note
is not counted as a proved version of the incorrect universal claim.

### Chapter 6

#### §6.2

- [6.2.E1](https://dlmf.nist.gov/6.2.E1): [expIntE1_horizontal_integral](AAR/ExpIntegrals/Basic.lean#L160) (admitted); [genExpIntE_one_eq_integral](AAR/Confluent/ExpIntegral.lean#L134) (proved).
- [6.2.E2](https://dlmf.nist.gov/6.2.E2): [expIntE1_stieltjes](AAR/ExpIntegrals/Basic.lean#L166) (admitted).
- [6.2.E3](https://dlmf.nist.gov/6.2.E3): [expIntEin](AAR/ExpIntegrals/Basic.lean#L25) (definition); [expIntEin_segment_integral](AAR/ExpIntegrals/Basic.lean#L130) (admitted); [Real.expIntEin](AAR/Confluent/ExpIntegral.lean#L146) (definition).
- [6.2.E4](https://dlmf.nist.gov/6.2.E4): [expIntE1_eq_Ein_complex](AAR/ExpIntegrals/Basic.lean#L172) (admitted); [genExpIntE_one_eq_Ein](AAR/Confluent/ExpIntegral.lean#L219) (proved).
- [6.2.E5](https://dlmf.nist.gov/6.2.E5): [Real.expIntEi](AAR/ExpIntegrals/Basic.lean#L60) (definition); [Real.expIntEi_principalValue](AAR/ExpIntegrals/Basic.lean#L178) (admitted).
- [6.2.E6](https://dlmf.nist.gov/6.2.E6): [Real.expIntEi_negative](AAR/ExpIntegrals/Basic.lean#L184) (admitted).
- [6.2.E7](https://dlmf.nist.gov/6.2.E7): [Real.expIntEi_Ein](AAR/ExpIntegrals/Basic.lean#L190) (admitted).
- [6.2.E8](https://dlmf.nist.gov/6.2.E8): [Real.logIntLi](AAR/ExpIntegrals/Basic.lean#L65) (definition); [Real.logIntLi_principalValue](AAR/ExpIntegrals/Basic.lean#L196) (admitted).
- [6.2.E9](https://dlmf.nist.gov/6.2.E9): [sinInt](AAR/ExpIntegrals/Basic.lean#L30) (definition); [sinInt_segment_integral](AAR/ExpIntegrals/Basic.lean#L136) (admitted); [Real.sinInt](AAR/Confluent/ExpIntegral.lean#L350) (definition).
- [6.2.E10](https://dlmf.nist.gov/6.2.E10): [sinIntTail](AAR/ExpIntegrals/Basic.lean#L45) (definition); [sinIntTail_horizontal_integral](AAR/ExpIntegrals/Basic.lean#L202) (admitted).
- [6.2.E11](https://dlmf.nist.gov/6.2.E11): [cosInt_horizontal_integral](AAR/ExpIntegrals/Basic.lean#L208) (admitted).
- [6.2.E12](https://dlmf.nist.gov/6.2.E12): [cosIntCin](AAR/ExpIntegrals/Basic.lean#L35) (definition); [cosIntCin_segment_integral](AAR/ExpIntegrals/Basic.lean#L142) (admitted); [Real.cosIntCin](AAR/Confluent/ExpIntegral.lean#L397) (definition).
- [6.2.E13](https://dlmf.nist.gov/6.2.E13): [cosInt](AAR/ExpIntegrals/Basic.lean#L40) (definition); [Real.cosInt](AAR/Confluent/ExpIntegral.lean#L402) (definition).
- [6.2.E14](https://dlmf.nist.gov/6.2.E14): [cosInt_tendsto_atTop](AAR/ExpIntegrals/Basic.lean#L214) (admitted); [Real.tendsto_sinInt_atTop](AAR/Confluent/ExpIntegral.lean#L365) (proved).
- [6.2.E15](https://dlmf.nist.gov/6.2.E15): [sinhInt](AAR/ExpIntegrals/Basic.lean#L50) (definition); [sinhInt_segment_integral](AAR/ExpIntegrals/Basic.lean#L148) (admitted).
- [6.2.E16](https://dlmf.nist.gov/6.2.E16): [coshInt](AAR/ExpIntegrals/Basic.lean#L55) (definition); [coshInt_segment_integral](AAR/ExpIntegrals/Basic.lean#L154) (admitted).
- [6.2.E17](https://dlmf.nist.gov/6.2.E17): [expIntAuxF](AAR/ExpIntegrals/Basic.lean#L70) (definition).
- [6.2.E18](https://dlmf.nist.gov/6.2.E18): [expIntAuxG](AAR/ExpIntegrals/Basic.lean#L75) (definition).
- [6.2.E19](https://dlmf.nist.gov/6.2.E19): [sinInt_eq_aux](AAR/ExpIntegrals/Basic.lean#L220) (admitted).
- [6.2.E20](https://dlmf.nist.gov/6.2.E20): [cosInt_eq_aux](AAR/ExpIntegrals/Basic.lean#L226) (admitted).
- [6.2.E21](https://dlmf.nist.gov/6.2.E21): [hasDerivAt_expIntAuxF](AAR/ExpIntegrals/Basic.lean#L232) (admitted); [hasDerivAt_expIntAuxG](AAR/ExpIntegrals/Basic.lean#L238) (admitted).

#### §6.4

- [6.4.E1](https://dlmf.nist.gov/6.4.E1): [expIntE1OnLog](AAR/ExpIntegrals/Continuation.lean#L25) (definition); [expIntE1OnLog_principal](AAR/ExpIntegrals/Continuation.lean#L46) (admitted).
- [6.4.E2](https://dlmf.nist.gov/6.4.E2): [expIntE1OnLog_monodromy](AAR/ExpIntegrals/Continuation.lean#L52) (admitted).
- [6.4.E3](https://dlmf.nist.gov/6.4.E3): [expIntE1OnLog_halfTurn](AAR/ExpIntegrals/Continuation.lean#L58) (admitted).
- [6.4.E4](https://dlmf.nist.gov/6.4.E4): [cosIntOnLog_halfTurn](AAR/ExpIntegrals/Continuation.lean#L64) (admitted).
- [6.4.E5](https://dlmf.nist.gov/6.4.E5): [coshIntOnLog_halfTurn](AAR/ExpIntegrals/Continuation.lean#L70) (admitted).
- [6.4.E6](https://dlmf.nist.gov/6.4.E6): [expIntAuxFOnLog_halfTurn](AAR/ExpIntegrals/Continuation.lean#L76) (admitted).
- [6.4.E7](https://dlmf.nist.gov/6.4.E7): [expIntAuxGOnLog_halfTurn](AAR/ExpIntegrals/Continuation.lean#L82) (admitted).

#### §6.5

- [6.5.E1](https://dlmf.nist.gov/6.5.E1): [expIntE1_negative_boundary](AAR/ExpIntegrals/Continuation.lean#L88) (admitted).
- [6.5.E2](https://dlmf.nist.gov/6.5.E2): [expIntEi_boundary_average](AAR/ExpIntegrals/Continuation.lean#L94) (admitted).
- [6.5.E3](https://dlmf.nist.gov/6.5.E3): [sinhInt_eq_Ei](AAR/ExpIntegrals/Continuation.lean#L100) (admitted).
- [6.5.E4](https://dlmf.nist.gov/6.5.E4): [coshInt_eq_Ei](AAR/ExpIntegrals/Continuation.lean#L106) (admitted).
- [6.5.E5](https://dlmf.nist.gov/6.5.E5): [sinInt_eq_E1](AAR/ExpIntegrals/Continuation.lean#L112) (admitted).
- [6.5.E6](https://dlmf.nist.gov/6.5.E6): [cosInt_eq_E1](AAR/ExpIntegrals/Continuation.lean#L118) (admitted).
- [6.5.E7](https://dlmf.nist.gov/6.5.E7): [expIntAux_eq_E1](AAR/ExpIntegrals/Continuation.lean#L124) (admitted).

#### §6.6

- [6.6.E1](https://dlmf.nist.gov/6.6.E1): [Real.hasSum_expIntEi](AAR/ExpIntegrals/Expansions.lean#L25) (admitted).
- [6.6.E2](https://dlmf.nist.gov/6.6.E2): [expIntE1_hasSum](AAR/ExpIntegrals/Expansions.lean#L31) (admitted); [genExpIntE_one_eq_tsum](AAR/Confluent/ExpIntegral.lean#L339) (proved).
- [6.6.E3](https://dlmf.nist.gov/6.6.E3): [expIntE1_digamma_series](AAR/ExpIntegrals/Expansions.lean#L37) (admitted).
- [6.6.E4](https://dlmf.nist.gov/6.6.E4): [hasSum_Ein_complex](AAR/ExpIntegrals/Expansions.lean#L43) (admitted); [Real.hasSum_expIntEin](AAR/Confluent/ExpIntegral.lean#L320) (proved).
- [6.6.E5](https://dlmf.nist.gov/6.6.E5): [hasSum_Si_complex](AAR/ExpIntegrals/Expansions.lean#L49) (admitted); [Real.hasSum_sinInt](AAR/Confluent/ExpIntegral.lean#L371) (proved).
- [6.6.E6](https://dlmf.nist.gov/6.6.E6): [hasSum_Ci_complex](AAR/ExpIntegrals/Expansions.lean#L55) (admitted); [Real.cosInt_eq_tsum](AAR/Confluent/ExpIntegral.lean#L442) (proved).

#### §6.7

- [6.7.E1](https://dlmf.nist.gov/6.7.E1): [expIntE1_scaled_integrals](AAR/ExpIntegrals/Representations.lean#L25) (admitted).
- [6.7.E2](https://dlmf.nist.gov/6.7.E2): [expIntEi_finite_integral](AAR/ExpIntegrals/Representations.lean#L31) (admitted).
- [6.7.E3](https://dlmf.nist.gov/6.7.E3): [expIntE1_rational_fourier_0](AAR/ExpIntegrals/Representations.lean#L37) (admitted).
- [6.7.E4](https://dlmf.nist.gov/6.7.E4): [expIntE1_rational_fourier_1](AAR/ExpIntegrals/Representations.lean#L49) (admitted).
- [6.7.E5](https://dlmf.nist.gov/6.7.E5): [expIntE1_rational_laplace_0](AAR/ExpIntegrals/Representations.lean#L43) (admitted).
- [6.7.E6](https://dlmf.nist.gov/6.7.E6): [expIntE1_rational_laplace_1](AAR/ExpIntegrals/Representations.lean#L55) (admitted).
- [6.7.E7](https://dlmf.nist.gov/6.7.E7): [expIntEin_real_integral_7](AAR/ExpIntegrals/Representations.lean#L61) (admitted).
- [6.7.E8](https://dlmf.nist.gov/6.7.E8): [expIntEin_real_integral_8](AAR/ExpIntegrals/Representations.lean#L67) (admitted).
- [6.7.E9](https://dlmf.nist.gov/6.7.E9): [sinIntTail_angular_integral](AAR/ExpIntegrals/Representations.lean#L79) (admitted).
- [6.7.E10](https://dlmf.nist.gov/6.7.E10): [Ein_sub_Cin_angular_integral](AAR/ExpIntegrals/Representations.lean#L85) (admitted).
- [6.7.E11](https://dlmf.nist.gov/6.7.E11): [expIntEin_real_integral_11](AAR/ExpIntegrals/Representations.lean#L73) (admitted).
- [6.7.E12](https://dlmf.nist.gov/6.7.E12): [expIntAux_horizontal_integral](AAR/ExpIntegrals/Representations.lean#L91) (admitted).
- [6.7.E13](https://dlmf.nist.gov/6.7.E13): [expIntAuxF_oscillatory_integral](AAR/ExpIntegrals/Representations.lean#L97) (admitted); [expIntAuxF_laplace_integral](AAR/ExpIntegrals/Representations.lean#L103) (admitted).
- [6.7.E14](https://dlmf.nist.gov/6.7.E14): [expIntAuxG_oscillatory_integral](AAR/ExpIntegrals/Representations.lean#L115) (admitted); [expIntAuxG_laplace_integral](AAR/ExpIntegrals/Representations.lean#L121) (admitted).
- [6.7.E15](https://dlmf.nist.gov/6.7.E15): [expIntAuxF_besselK_integral](AAR/ExpIntegrals/Representations.lean#L109) (admitted).
- [6.7.E16](https://dlmf.nist.gov/6.7.E16): [expIntAuxG_besselK_integral](AAR/ExpIntegrals/Representations.lean#L127) (admitted).

#### §6.8

- [6.8.E1](https://dlmf.nist.gov/6.8.E1): [expIntE1_inequality_1](AAR/ExpIntegrals/Representations.lean#L133) (admitted).
- [6.8.E2](https://dlmf.nist.gov/6.8.E2): [expIntE1_inequality_2](AAR/ExpIntegrals/Representations.lean#L139) (admitted).
- [6.8.E3](https://dlmf.nist.gov/6.8.E3): [expIntE1_inequality_3](AAR/ExpIntegrals/Representations.lean#L145) (admitted).

#### §6.9

- [6.9.E1](https://dlmf.nist.gov/6.9.E1): [expIntE1_continuedFraction](AAR/ExpIntegrals/Representations.lean#L151) (admitted).

#### §6.10

- [6.10.E1](https://dlmf.nist.gov/6.10.E1): [expIntE1_inverse_factorial_series](AAR/ExpIntegrals/Expansions.lean#L75) (admitted).
- [6.10.E2](https://dlmf.nist.gov/6.10.E2): [expIntInverseFactorialCoeff_initial](AAR/ExpIntegrals/Expansions.lean#L68) (proved).
- [6.10.E3](https://dlmf.nist.gov/6.10.E3): [expIntInverseFactorialCoeff](AAR/ExpIntegrals/Expansions.lean#L61) (definition).
- [6.10.E4](https://dlmf.nist.gov/6.10.E4): [sinInt_spherical_series](AAR/ExpIntegrals/Expansions.lean#L86) (admitted).
- [6.10.E5](https://dlmf.nist.gov/6.10.E5): [cosIntCin_spherical_series](AAR/ExpIntegrals/Expansions.lean#L92) (admitted).
- [6.10.E6](https://dlmf.nist.gov/6.10.E6): [expIntEi_spherical_series](AAR/ExpIntegrals/Expansions.lean#L98) (admitted).
- [6.10.E7](https://dlmf.nist.gov/6.10.E7): [expIntSphericalCoeff](AAR/ExpIntegrals/Expansions.lean#L81) (definition).
- [6.10.E8](https://dlmf.nist.gov/6.10.E8): [Ein_spherical_series](AAR/ExpIntegrals/Expansions.lean#L104) (admitted).

#### §6.11

- [6.11.E1](https://dlmf.nist.gov/6.11.E1): [expIntE1_eq_upperIncGamma](AAR/ExpIntegrals/Expansions.lean#L110) (proved).
- [6.11.E2](https://dlmf.nist.gov/6.11.E2): [expIntE1_eq_kummerU](AAR/ExpIntegrals/Expansions.lean#L116) (proved).
- [6.11.E3](https://dlmf.nist.gov/6.11.E3): [expIntAux_eq_kummerU](AAR/ExpIntegrals/Expansions.lean#L122) (admitted).

#### §6.12

- [6.12.E1](https://dlmf.nist.gov/6.12.E1): [expIntE1_logSector_asymptotic](AAR/ExpIntegrals/Asymptotics.lean#L34) (admitted).
- [6.12.E2](https://dlmf.nist.gov/6.12.E2): [expIntEi_asymptotic](AAR/ExpIntegrals/Asymptotics.lean#L40) (admitted).
- [6.12.E3](https://dlmf.nist.gov/6.12.E3): [expIntAuxF_sector_asymptotic](AAR/ExpIntegrals/Asymptotics.lean#L46) (admitted).
- [6.12.E4](https://dlmf.nist.gov/6.12.E4): [expIntAuxG_sector_asymptotic](AAR/ExpIntegrals/Asymptotics.lean#L58) (admitted).
- [6.12.E5](https://dlmf.nist.gov/6.12.E5): [expIntAsymptoticRemainder](AAR/ExpIntegrals/Asymptotics.lean#L29) (definition).
- [6.12.E6](https://dlmf.nist.gov/6.12.E6): [expIntAsymptoticRemainder](AAR/ExpIntegrals/Asymptotics.lean#L29) (definition).
- [6.12.E7](https://dlmf.nist.gov/6.12.E7): [expIntAuxF_remainder_integral](AAR/ExpIntegrals/Asymptotics.lean#L52) (admitted).
- [6.12.E8](https://dlmf.nist.gov/6.12.E8): [expIntAuxG_remainder_integral](AAR/ExpIntegrals/Asymptotics.lean#L64) (admitted).

#### §6.13

- [6.13.E1](https://dlmf.nist.gov/6.13.E1): [Real.expIntEiZero](AAR/ExpIntegrals/ZerosIntegrals.lean#L25) (definition); [Real.expIntEiZero_decimal](AAR/ExpIntegrals/ZerosIntegrals.lean#L43) (admitted).
- [6.13.E2](https://dlmf.nist.gov/6.13.E2): [Real.trigonometric_integral_zero_asymptotics](AAR/ExpIntegrals/ZerosIntegrals.lean#L69) (admitted).

#### §6.14

- [6.14.E1](https://dlmf.nist.gov/6.14.E1): [expIntE1_laplace](AAR/ExpIntegrals/ZerosIntegrals.lean#L75) (admitted).
- [6.14.E2](https://dlmf.nist.gov/6.14.E2): [cosInt_laplace](AAR/ExpIntegrals/ZerosIntegrals.lean#L81) (admitted).
- [6.14.E3](https://dlmf.nist.gov/6.14.E3): [sinIntTail_laplace](AAR/ExpIntegrals/ZerosIntegrals.lean#L87) (admitted).
- [6.14.E4](https://dlmf.nist.gov/6.14.E4): [expIntE1_squared_integral](AAR/ExpIntegrals/ZerosIntegrals.lean#L93) (admitted).
- [6.14.E5](https://dlmf.nist.gov/6.14.E5): [cosInt_fourier_integral](AAR/ExpIntegrals/ZerosIntegrals.lean#L99) (admitted).
- [6.14.E6](https://dlmf.nist.gov/6.14.E6): [trigIntegral_squared_integrals](AAR/ExpIntegrals/ZerosIntegrals.lean#L105) (admitted).
- [6.14.E7](https://dlmf.nist.gov/6.14.E7): [trigIntegral_product_integral](AAR/ExpIntegrals/ZerosIntegrals.lean#L111) (admitted).

#### §6.15

- [6.15.E1](https://dlmf.nist.gov/6.15.E1): [trigIntegral_hasSum_1](AAR/ExpIntegrals/ZerosIntegrals.lean#L117) (admitted).
- [6.15.E2](https://dlmf.nist.gov/6.15.E2): [trigIntegral_hasSum_2](AAR/ExpIntegrals/ZerosIntegrals.lean#L123) (admitted).
- [6.15.E3](https://dlmf.nist.gov/6.15.E3): [trigIntegral_hasSum_3](AAR/ExpIntegrals/ZerosIntegrals.lean#L129) (admitted).
- [6.15.E4](https://dlmf.nist.gov/6.15.E4): [trigIntegral_hasSum_4](AAR/ExpIntegrals/ZerosIntegrals.lean#L135) (admitted).

#### §6.18

- [6.18.E1](https://dlmf.nist.gov/6.18.E1): [expIntActonA](AAR/ExpIntegrals/ZerosIntegrals.lean#L141) (definition); [expIntActonB](AAR/ExpIntegrals/ZerosIntegrals.lean#L146) (definition); [expIntActonC](AAR/ExpIntegrals/ZerosIntegrals.lean#L151) (definition).
- [6.18.E2](https://dlmf.nist.gov/6.18.E2): [expIntActon_recurrence](AAR/ExpIntegrals/ZerosIntegrals.lean#L161) (admitted).

### Chapter 7

#### §7.2

- [7.2.E1](https://dlmf.nist.gov/7.2.E1): [erf_complex_segment_integral](AAR/ErrorFunctions/Basic.lean#L125) (admitted); [erf_eq_integral](AAR/Confluent/Basic.lean#L629) (proved).
- [7.2.E2](https://dlmf.nist.gov/7.2.E2): [erfc_horizontal_integral](AAR/ErrorFunctions/Basic.lean#L131) (admitted).
- [7.2.E3](https://dlmf.nist.gov/7.2.E3): [faddeevaW](AAR/ErrorFunctions/Basic.lean#L25) (definition); [faddeevaW_integral](AAR/ErrorFunctions/Basic.lean#L137) (admitted).
- [7.2.E4](https://dlmf.nist.gov/7.2.E4): [erf_sector_limit](AAR/ErrorFunctions/Basic.lean#L143) (admitted).
- [7.2.E5](https://dlmf.nist.gov/7.2.E5): [dawsonF](AAR/ErrorFunctions/Basic.lean#L30) (definition); [Real.dawsonF](AAR/Confluent/ErrorFunctions.lean#L156) (definition).
- [7.2.E6](https://dlmf.nist.gov/7.2.E6): [fresnelTail](AAR/ErrorFunctions/Basic.lean#L45) (definition); [fresnelTail_horizontal_integral](AAR/ErrorFunctions/Basic.lean#L149) (admitted).
- [7.2.E7](https://dlmf.nist.gov/7.2.E7): [fresnelCosInt](AAR/ErrorFunctions/Basic.lean#L35) (definition); [Real.fresnelCosInt](AAR/Confluent/ErrorFunctions.lean#L44) (definition).
- [7.2.E8](https://dlmf.nist.gov/7.2.E8): [fresnelSinInt](AAR/ErrorFunctions/Basic.lean#L40) (definition); [Real.fresnelSinInt](AAR/Confluent/ErrorFunctions.lean#L48) (definition).
- [7.2.E9](https://dlmf.nist.gov/7.2.E9): [Real.tendsto_fresnelCosInt_atTop](AAR/Confluent/ErrorFunctions.lean#L120) (proved); [Real.tendsto_fresnelSinInt_atTop](AAR/Confluent/ErrorFunctions.lean#L138) (proved).
- [7.2.E10](https://dlmf.nist.gov/7.2.E10): [fresnelAuxFComplex](AAR/ErrorFunctions/Basic.lean#L50) (definition); [fresnelAuxF](AAR/Confluent/FresnelAsymptotics.lean#L41) (definition).
- [7.2.E11](https://dlmf.nist.gov/7.2.E11): [fresnelAuxGComplex](AAR/ErrorFunctions/Basic.lean#L55) (definition); [fresnelAuxG](AAR/Confluent/FresnelAsymptotics.lean#L48) (definition).
- [7.2.E12](https://dlmf.nist.gov/7.2.E12): [goodwinStatonG](AAR/ErrorFunctions/Basic.lean#L60) (definition); [goodwinStatonG_integrable](AAR/ErrorFunctions/Basic.lean#L155) (admitted).

#### §7.4

- [7.4.E1](https://dlmf.nist.gov/7.4.E1): [erf_negative](AAR/ErrorFunctions/Relations.lean#L25) (proved).
- [7.4.E2](https://dlmf.nist.gov/7.4.E2): [erfc_negative](AAR/ErrorFunctions/Relations.lean#L31) (proved).
- [7.4.E3](https://dlmf.nist.gov/7.4.E3): [faddeevaW_negative](AAR/ErrorFunctions/Relations.lean#L38) (proved).
- [7.4.E4](https://dlmf.nist.gov/7.4.E4): [dawsonF_negative](AAR/ErrorFunctions/Relations.lean#L45) (admitted).
- [7.4.E5](https://dlmf.nist.gov/7.4.E5): [fresnel_negative](AAR/ErrorFunctions/Relations.lean#L51) (admitted).
- [7.4.E6](https://dlmf.nist.gov/7.4.E6): [fresnel_mul_I](AAR/ErrorFunctions/Relations.lean#L57) (admitted).
- [7.4.E7](https://dlmf.nist.gov/7.4.E7): [fresnelAux_mul_I](AAR/ErrorFunctions/Relations.lean#L63) (admitted).
- [7.4.E8](https://dlmf.nist.gov/7.4.E8): [fresnelAux_negative](AAR/ErrorFunctions/Relations.lean#L69) (admitted).

#### §7.5

- [7.5.E1](https://dlmf.nist.gov/7.5.E1): [dawsonF_faddeeva](AAR/ErrorFunctions/Relations.lean#L75) (admitted).
- [7.5.E2](https://dlmf.nist.gov/7.5.E2): [fresnel_sum_tail](AAR/ErrorFunctions/Relations.lean#L81) (proved).
- [7.5.E3](https://dlmf.nist.gov/7.5.E3): [fresnelCosInt_aux](AAR/ErrorFunctions/Relations.lean#L88) (admitted).
- [7.5.E4](https://dlmf.nist.gov/7.5.E4): [fresnelSinInt_aux](AAR/ErrorFunctions/Relations.lean#L94) (admitted).
- [7.5.E5](https://dlmf.nist.gov/7.5.E5): [fresnelTail_aux](AAR/ErrorFunctions/Relations.lean#L100) (admitted).
- [7.5.E6](https://dlmf.nist.gov/7.5.E6): [fresnel_signed_tail](AAR/ErrorFunctions/Relations.lean#L106) (admitted).
- [7.5.E7](https://dlmf.nist.gov/7.5.E7): [fresnelZetaComplex](AAR/ErrorFunctions/Relations.lean#L112) (definition).
- [7.5.E8](https://dlmf.nist.gov/7.5.E8): [fresnel_signed_erf](AAR/ErrorFunctions/Relations.lean#L117) (admitted); [Real.fresnelCosInt_add_I_mul_fresnelSinInt](AAR/Confluent/ErrorFunctions.lean#L67) (proved).
- [7.5.E9](https://dlmf.nist.gov/7.5.E9): [fresnel_signed_faddeeva](AAR/ErrorFunctions/Relations.lean#L123) (admitted).
- [7.5.E10](https://dlmf.nist.gov/7.5.E10): [fresnelAux_signed_erfc](AAR/ErrorFunctions/Relations.lean#L129) (admitted); [fresnelAuxG_add_I_mul_fresnelAuxF](AAR/Confluent/FresnelAsymptotics.lean#L66) (proved).
- [7.5.E11](https://dlmf.nist.gov/7.5.E11): [fresnelTail_norm_sq_nonneg](AAR/ErrorFunctions/Relations.lean#L135) (admitted).
- [7.5.E12](https://dlmf.nist.gov/7.5.E12): [fresnelTail_norm_sq_nonpos](AAR/ErrorFunctions/Relations.lean#L141) (admitted).
- [7.5.E13](https://dlmf.nist.gov/7.5.E13): [goodwinStatonG_dawson](AAR/ErrorFunctions/Relations.lean#L147) (admitted).

#### §7.6

- [7.6.E1](https://dlmf.nist.gov/7.6.E1): [hasSum_erf_complex](AAR/ErrorFunctions/Series.lean#L25) (admitted).
- [7.6.E2](https://dlmf.nist.gov/7.6.E2): [hasSum_erf_scaled](AAR/ErrorFunctions/Series.lean#L31) (admitted).
- [7.6.E3](https://dlmf.nist.gov/7.6.E3): [hasSum_faddeevaW](AAR/ErrorFunctions/Series.lean#L37) (admitted).
- [7.6.E4](https://dlmf.nist.gov/7.6.E4): [fresnelCosInt_hasSum](AAR/ErrorFunctions/Series.lean#L43) (admitted).
- [7.6.E5](https://dlmf.nist.gov/7.6.E5): [fresnelCosInt_alternate_series](AAR/ErrorFunctions/Series.lean#L64) (admitted).
- [7.6.E6](https://dlmf.nist.gov/7.6.E6): [fresnelSinInt_hasSum](AAR/ErrorFunctions/Series.lean#L49) (admitted).
- [7.6.E7](https://dlmf.nist.gov/7.6.E7): [fresnelSinInt_alternate_series](AAR/ErrorFunctions/Series.lean#L70) (admitted).
- [7.6.E8](https://dlmf.nist.gov/7.6.E8): [erf_spherical_series](AAR/ErrorFunctions/Series.lean#L76) (admitted).
- [7.6.E9](https://dlmf.nist.gov/7.6.E9): [erf_chebyshev_spherical_series](AAR/ErrorFunctions/Series.lean#L82) (admitted).
- [7.6.E10](https://dlmf.nist.gov/7.6.E10): [fresnelCosInt_spherical_series](AAR/ErrorFunctions/Series.lean#L88) (admitted).
- [7.6.E11](https://dlmf.nist.gov/7.6.E11): [fresnelSinInt_spherical_series](AAR/ErrorFunctions/Series.lean#L94) (admitted).

#### §7.7

- [7.7.E1](https://dlmf.nist.gov/7.7.E1): [erfc_rational_gaussian_integral](AAR/ErrorFunctions/Integrals.lean#L25) (admitted).
- [7.7.E2](https://dlmf.nist.gov/7.7.E2): [faddeevaW_cauchy_integral](AAR/ErrorFunctions/Integrals.lean#L31) (admitted).
- [7.7.E3](https://dlmf.nist.gov/7.7.E3): [gaussian_fourier_halfLine](AAR/ErrorFunctions/Integrals.lean#L37) (admitted).
- [7.7.E4](https://dlmf.nist.gov/7.7.E4): [gaussian_sqrt_laplace](AAR/ErrorFunctions/Integrals.lean#L43) (admitted).
- [7.7.E5](https://dlmf.nist.gov/7.7.E5): [erf_squared_integral](AAR/ErrorFunctions/Integrals.lean#L49) (admitted).
- [7.7.E6](https://dlmf.nist.gov/7.7.E6): [gaussian_quadratic_tail](AAR/ErrorFunctions/Integrals.lean#L55) (admitted).
- [7.7.E7](https://dlmf.nist.gov/7.7.E7): [gaussian_reciprocal_tail](AAR/ErrorFunctions/Integrals.lean#L61) (admitted).
- [7.7.E8](https://dlmf.nist.gov/7.7.E8): [gaussian_reciprocal_integral](AAR/ErrorFunctions/Integrals.lean#L67) (admitted).
- [7.7.E9](https://dlmf.nist.gov/7.7.E9): [erf_primitive](AAR/ErrorFunctions/Integrals.lean#L73) (admitted).
- [7.7.E10](https://dlmf.nist.gov/7.7.E10): [fresnelAuxFComplex_laplace_integral](AAR/ErrorFunctions/Integrals.lean#L79) (admitted).
- [7.7.E11](https://dlmf.nist.gov/7.7.E11): [fresnelAuxGComplex_laplace_integral](AAR/ErrorFunctions/Integrals.lean#L85) (admitted).
- [7.7.E12](https://dlmf.nist.gov/7.7.E12): [fresnelAux_contour_tail](AAR/ErrorFunctions/Integrals.lean#L91) (admitted).
- [7.7.E13](https://dlmf.nist.gov/7.7.E13): [fresnelAuxFComplex_mellinBarnes](AAR/ErrorFunctions/Integrals.lean#L97) (admitted).
- [7.7.E14](https://dlmf.nist.gov/7.7.E14): [fresnelAuxGComplex_mellinBarnes](AAR/ErrorFunctions/Integrals.lean#L103) (admitted).
- [7.7.E15](https://dlmf.nist.gov/7.7.E15): [fresnelAuxFComplex_laplace_square](AAR/ErrorFunctions/Integrals.lean#L109) (admitted).
- [7.7.E16](https://dlmf.nist.gov/7.7.E16): [fresnelAuxGComplex_laplace_square](AAR/ErrorFunctions/Integrals.lean#L115) (admitted).

#### §7.8

- [7.8.E1](https://dlmf.nist.gov/7.8.E1): [Real.millsRatio](AAR/ErrorFunctions/BoundsAsymptotics.lean#L25) (definition); [Real.millsRatio_integral](AAR/ErrorFunctions/BoundsAsymptotics.lean#L30) (admitted).
- [7.8.E2](https://dlmf.nist.gov/7.8.E2): [Real.millsRatio_bound_2](AAR/ErrorFunctions/BoundsAsymptotics.lean#L36) (admitted).
- [7.8.E3](https://dlmf.nist.gov/7.8.E3): [Real.millsRatio_bound_3](AAR/ErrorFunctions/BoundsAsymptotics.lean#L42) (admitted).
- [7.8.E4](https://dlmf.nist.gov/7.8.E4): [Real.millsRatio_bound_four](AAR/ErrorFunctions/BoundsAsymptotics.lean#L48) (admitted).
- [7.8.E5](https://dlmf.nist.gov/7.8.E5): [Real.millsRatio_rational_bounds](AAR/ErrorFunctions/BoundsAsymptotics.lean#L54) (admitted).
- [7.8.E6](https://dlmf.nist.gov/7.8.E6): [Real.exp_sq_integral_bound](AAR/ErrorFunctions/BoundsAsymptotics.lean#L60) (admitted).
- [7.8.E7](https://dlmf.nist.gov/7.8.E7): [Real.dawsonF_integral_bounds](AAR/ErrorFunctions/BoundsAsymptotics.lean#L66) (admitted).
- [7.8.E8](https://dlmf.nist.gov/7.8.E8): [Real.erf_exponential_bound](AAR/ErrorFunctions/BoundsAsymptotics.lean#L72) (admitted).

#### §7.9

- [7.9.E1](https://dlmf.nist.gov/7.9.E1): [erfc_continuedFraction_one](AAR/ErrorFunctions/BoundsAsymptotics.lean#L83) (admitted).
- [7.9.E2](https://dlmf.nist.gov/7.9.E2): [erfc_continuedFraction_two](AAR/ErrorFunctions/BoundsAsymptotics.lean#L89) (admitted).
- [7.9.E3](https://dlmf.nist.gov/7.9.E3): [faddeevaW_continuedFraction](AAR/ErrorFunctions/BoundsAsymptotics.lean#L95) (admitted).

#### §7.10

- [7.10.E1](https://dlmf.nist.gov/7.10.E1): [iteratedDeriv_erf_hermite](AAR/ErrorFunctions/Relations.lean#L153) (admitted).
- [7.10.E2](https://dlmf.nist.gov/7.10.E2): [hasDerivAt_faddeevaW](AAR/ErrorFunctions/Relations.lean#L159) (admitted).
- [7.10.E3](https://dlmf.nist.gov/7.10.E3): [iteratedDeriv_faddeevaW_recurrence](AAR/ErrorFunctions/Relations.lean#L165) (admitted).
- [7.10.E4](https://dlmf.nist.gov/7.10.E4): [hasDerivAt_fresnelAux](AAR/ErrorFunctions/Relations.lean#L171) (admitted).

#### §7.11

- [7.11.E1](https://dlmf.nist.gov/7.11.E1): [erf_lowerIncGamma](AAR/ErrorFunctions/Relations.lean#L177) (admitted); [erf_lowerIncGammaOnLog_square](AAR/IncompleteGamma/SpecialValues.lean#L142) (admitted).
- [7.11.E2](https://dlmf.nist.gov/7.11.E2): [erfc_upperIncGamma](AAR/ErrorFunctions/Relations.lean#L183) (admitted); [erfc_upperIncGammaOnLog_square](AAR/IncompleteGamma/SpecialValues.lean#L148) (admitted).
- [7.11.E3](https://dlmf.nist.gov/7.11.E3): [erfc_genExpIntE](AAR/ErrorFunctions/Relations.lean#L189) (admitted); [erfc_genExpIntEOnLog_square](AAR/IncompleteGamma/ExponentialIntegral.lean#L200) (admitted).
- [7.11.E4](https://dlmf.nist.gov/7.11.E4): [erf_kummerM_pair](AAR/ErrorFunctions/Relations.lean#L195) (admitted).
- [7.11.E5](https://dlmf.nist.gov/7.11.E5): [erfc_kummerU_pair](AAR/ErrorFunctions/Relations.lean#L201) (admitted); [erfc_kummerUOnLog_square](AAR/IncompleteGamma/SpecialValues.lean#L154) (admitted).
- [7.11.E6](https://dlmf.nist.gov/7.11.E6): [fresnel_kummerM_pair](AAR/ErrorFunctions/Relations.lean#L207) (admitted).
- [7.11.E7](https://dlmf.nist.gov/7.11.E7): [fresnelCosInt_hypergeometric](AAR/ErrorFunctions/Relations.lean#L213) (admitted).
- [7.11.E8](https://dlmf.nist.gov/7.11.E8): [fresnelSinInt_hypergeometric](AAR/ErrorFunctions/Relations.lean#L219) (admitted).

#### §7.12

- [7.12.E1](https://dlmf.nist.gov/7.12.E1): [erfc_sector_asymptotic](AAR/ErrorFunctions/BoundsAsymptotics.lean#L101) (admitted); [hasAsymptoticExpansion_erfc](AAR/Confluent/IncompleteGamma.lean#L238) (proved).
- [7.12.E2](https://dlmf.nist.gov/7.12.E2): [fresnelAuxFComplex_sector_asymptotic](AAR/ErrorFunctions/BoundsAsymptotics.lean#L130) (admitted); [hasAsymptoticExpansion_fresnelAuxG_add_I_mul_fresnelAuxF](AAR/Confluent/FresnelAsymptotics.lean#L117) (proved).
- [7.12.E3](https://dlmf.nist.gov/7.12.E3): [fresnelAuxGComplex_sector_asymptotic](AAR/ErrorFunctions/BoundsAsymptotics.lean#L142) (admitted).
- [7.12.E4](https://dlmf.nist.gov/7.12.E4): [fresnelAsymptoticRemainder](AAR/ErrorFunctions/BoundsAsymptotics.lean#L125) (definition).
- [7.12.E5](https://dlmf.nist.gov/7.12.E5): [fresnelAsymptoticRemainder](AAR/ErrorFunctions/BoundsAsymptotics.lean#L125) (definition).
- [7.12.E6](https://dlmf.nist.gov/7.12.E6): [fresnelAuxFComplex_remainder_integral](AAR/ErrorFunctions/BoundsAsymptotics.lean#L136) (admitted).
- [7.12.E7](https://dlmf.nist.gov/7.12.E7): [fresnelAuxGComplex_remainder_integral](AAR/ErrorFunctions/BoundsAsymptotics.lean#L148) (admitted).

#### §7.13

- [7.13.E1](https://dlmf.nist.gov/7.13.E1): [errorFunctionZero_asymptotic](AAR/ErrorFunctions/Zeros.lean#L98) (admitted).
- [7.13.E2](https://dlmf.nist.gov/7.13.E2): [errorZeroLambda](AAR/ErrorFunctions/Zeros.lean#L88) (definition); [errorZeroMu](AAR/ErrorFunctions/Zeros.lean#L93) (definition).
- [7.13.E3](https://dlmf.nist.gov/7.13.E3): [errorFunctionZero_asymptotic](AAR/ErrorFunctions/Zeros.lean#L98) (admitted).
- [7.13.E4](https://dlmf.nist.gov/7.13.E4): [errorZeroLambda](AAR/ErrorFunctions/Zeros.lean#L88) (definition); [errorZeroMu](AAR/ErrorFunctions/Zeros.lean#L93) (definition).
- [7.13.E5](https://dlmf.nist.gov/7.13.E5): [fresnelFunctionZero_asymptotic](AAR/ErrorFunctions/Zeros.lean#L114) (admitted).
- [7.13.E6](https://dlmf.nist.gov/7.13.E6): [fresnelZeroLambda](AAR/ErrorFunctions/Zeros.lean#L104) (definition); [fresnelZeroAlpha](AAR/ErrorFunctions/Zeros.lean#L109) (definition).
- [7.13.E7](https://dlmf.nist.gov/7.13.E7): [fresnelZeroLambda](AAR/ErrorFunctions/Zeros.lean#L104) (definition); [fresnelZeroAlpha](AAR/ErrorFunctions/Zeros.lean#L109) (definition).

#### §7.14

- [7.14.E1](https://dlmf.nist.gov/7.14.E1): [erfc_fourier_halfLine](AAR/ErrorFunctions/Integrals.lean#L121) (admitted).
- [7.14.E2](https://dlmf.nist.gov/7.14.E2): [erf_laplace](AAR/ErrorFunctions/Integrals.lean#L127) (admitted).
- [7.14.E3](https://dlmf.nist.gov/7.14.E3): [erf_sqrt_laplace](AAR/ErrorFunctions/Integrals.lean#L133) (admitted).
- [7.14.E4](https://dlmf.nist.gov/7.14.E4): [erfc_sqrt_reciprocal_laplace](AAR/ErrorFunctions/Integrals.lean#L139) (admitted).
- [7.14.E5](https://dlmf.nist.gov/7.14.E5): [fresnelCosInt_laplace](AAR/ErrorFunctions/Integrals.lean#L150) (admitted).
- [7.14.E6](https://dlmf.nist.gov/7.14.E6): [fresnelSinInt_laplace](AAR/ErrorFunctions/Integrals.lean#L162) (admitted).
- [7.14.E7](https://dlmf.nist.gov/7.14.E7): [fresnelCosInt_sqrt_laplace](AAR/ErrorFunctions/Integrals.lean#L156) (admitted).
- [7.14.E8](https://dlmf.nist.gov/7.14.E8): [fresnelSinInt_sqrt_laplace](AAR/ErrorFunctions/Integrals.lean#L168) (admitted).

#### §7.17

- [7.17.E1](https://dlmf.nist.gov/7.17.E1): [Real.invErf](AAR/ErrorFunctions/InverseGeneralized.lean#L43) (definition); [Real.invErfc](AAR/ErrorFunctions/InverseGeneralized.lean#L48) (definition).
- [7.17.E2](https://dlmf.nist.gov/7.17.E2): [invErfSeriesCoeff_initial](AAR/ErrorFunctions/InverseGeneralized.lean#L76) (proved); [hasSum_invErf](AAR/ErrorFunctions/InverseGeneralized.lean#L83) (admitted).
- [7.17.E3](https://dlmf.nist.gov/7.17.E3): [invErfc_asymptotic](AAR/ErrorFunctions/InverseGeneralized.lean#L104) (admitted).
- [7.17.E4](https://dlmf.nist.gov/7.17.E4): [invErfc_asymptotic](AAR/ErrorFunctions/InverseGeneralized.lean#L104) (admitted).
- [7.17.E5](https://dlmf.nist.gov/7.17.E5): [invErfcAsymptoticU](AAR/ErrorFunctions/InverseGeneralized.lean#L94) (definition).
- [7.17.E6](https://dlmf.nist.gov/7.17.E6): [invErfcAsymptoticV](AAR/ErrorFunctions/InverseGeneralized.lean#L99) (definition).

#### §7.18

- [7.18.E1](https://dlmf.nist.gov/7.18.E1): [iteratedErfc](AAR/ErrorFunctions/Repeated.lean#L26) (definition); [iteratedErfc_initial](AAR/ErrorFunctions/Repeated.lean#L31) (admitted).
- [7.18.E2](https://dlmf.nist.gov/7.18.E2): [iteratedErfc](AAR/ErrorFunctions/Repeated.lean#L26) (definition); [iteratedErfc_tail](AAR/ErrorFunctions/Repeated.lean#L37) (admitted).
- [7.18.E3](https://dlmf.nist.gov/7.18.E3): [hasDerivAt_iteratedErfc](AAR/ErrorFunctions/Repeated.lean#L43) (admitted).
- [7.18.E4](https://dlmf.nist.gov/7.18.E4): [iteratedDeriv_scaled_erfc](AAR/ErrorFunctions/Repeated.lean#L49) (admitted).
- [7.18.E5](https://dlmf.nist.gov/7.18.E5): [iteratedErfc_ode](AAR/ErrorFunctions/Repeated.lean#L55) (admitted); [iteratedErfc_general_solution](AAR/ErrorFunctions/Repeated.lean#L61) (admitted).
- [7.18.E6](https://dlmf.nist.gov/7.18.E6): [iteratedErfc_hasSum](AAR/ErrorFunctions/Repeated.lean#L67) (admitted).
- [7.18.E7](https://dlmf.nist.gov/7.18.E7): [iteratedErfc_recurrence](AAR/ErrorFunctions/Repeated.lean#L73) (admitted).
- [7.18.E8](https://dlmf.nist.gov/7.18.E8): [iteratedErfc_hermite](AAR/ErrorFunctions/Repeated.lean#L79) (admitted).
- [7.18.E9](https://dlmf.nist.gov/7.18.E9): [iteratedErfc_kummerM](AAR/ErrorFunctions/Repeated.lean#L85) (admitted).
- [7.18.E10](https://dlmf.nist.gov/7.18.E10): [iteratedErfc_kummerU](AAR/ErrorFunctions/Repeated.lean#L91) (admitted); [iteratedErfc_kummerUOnLog](AAR/ErrorFunctions/Repeated.lean#L97) (admitted).
- [7.18.E11](https://dlmf.nist.gov/7.18.E11): [iteratedErfc_pcfU](AAR/ErrorFunctions/Repeated.lean#L103) (admitted).
- [7.18.E12](https://dlmf.nist.gov/7.18.E12): [iteratedErfc_probability](AAR/ErrorFunctions/Repeated.lean#L113) (admitted).
- [7.18.E13](https://dlmf.nist.gov/7.18.E13): [iteratedErfc_continuedFraction](AAR/ErrorFunctions/Repeated.lean#L119) (admitted).
- [7.18.E14](https://dlmf.nist.gov/7.18.E14): [iteratedErfc_asymptotic](AAR/ErrorFunctions/Repeated.lean#L125) (admitted).

#### §7.19

- [7.19.E1](https://dlmf.nist.gov/7.19.E1): [Real.voigtU](AAR/ErrorFunctions/Voigt.lean#L25) (definition).
- [7.19.E2](https://dlmf.nist.gov/7.19.E2): [Real.voigtV](AAR/ErrorFunctions/Voigt.lean#L30) (definition).
- [7.19.E3](https://dlmf.nist.gov/7.19.E3): [voigt_erfc](AAR/ErrorFunctions/Voigt.lean#L40) (admitted).
- [7.19.E4](https://dlmf.nist.gov/7.19.E4): [Real.voigtH](AAR/ErrorFunctions/Voigt.lean#L35) (definition); [Real.voigtH_eq_voigtU](AAR/ErrorFunctions/Voigt.lean#L46) (admitted).
- [7.19.E5](https://dlmf.nist.gov/7.19.E5): [Real.voigt_limits](AAR/ErrorFunctions/Voigt.lean#L52) (admitted).
- [7.19.E6](https://dlmf.nist.gov/7.19.E6): [Real.voigt_symmetry](AAR/ErrorFunctions/Voigt.lean#L58) (admitted).
- [7.19.E7](https://dlmf.nist.gov/7.19.E7): [Real.voigt_bounds](AAR/ErrorFunctions/Voigt.lean#L64) (admitted).
- [7.19.E8](https://dlmf.nist.gov/7.19.E8): [Real.voigtV_derivative_relation](AAR/ErrorFunctions/Voigt.lean#L70) (admitted).
- [7.19.E9](https://dlmf.nist.gov/7.19.E9): [Real.voigtU_derivative_relation](AAR/ErrorFunctions/Voigt.lean#L76) (admitted).
- [7.19.E10](https://dlmf.nist.gov/7.19.E10): [Real.voigtU_fourier_laplace](AAR/ErrorFunctions/Voigt.lean#L82) (admitted).
- [7.19.E11](https://dlmf.nist.gov/7.19.E11): [Real.voigtV_fourier_laplace](AAR/ErrorFunctions/Voigt.lean#L88) (admitted).

### Chapter 8

#### §8.2

- [8.2.E1](https://dlmf.nist.gov/8.2.E1): [lowerIncGamma_eq_integral](AAR/Confluent/IncompleteGamma.lean#L168) (proved); [lowerIncGamma_segment_integral](AAR/IncompleteGamma/Basic.lean#L65) (admitted).
- [8.2.E2](https://dlmf.nist.gov/8.2.E2): [upperIncGamma_eq_integral](AAR/Confluent/IncompleteGamma.lean#L95) (proved); [upperIncGamma_horizontal_integral](AAR/IncompleteGamma/Basic.lean#L71) (admitted).
- [8.2.E3](https://dlmf.nist.gov/8.2.E3): [lowerIncGamma_add_upperIncGamma](AAR/Confluent/IncompleteGamma.lean#L146) (proved).
- [8.2.E4](https://dlmf.nist.gov/8.2.E4): [normIncGammaP](AAR/Statistical/IncompleteGamma.lean#L44) (definition); [normIncGammaQ](AAR/Statistical/IncompleteGamma.lean#L48) (definition); [normIncGammaPContinued](AAR/IncompleteGamma/Basic.lean#L35) (definition); [normIncGammaQContinued](AAR/IncompleteGamma/Basic.lean#L40) (definition); [normIncGammaPContinued_eq](AAR/IncompleteGamma/Basic.lean#L53) (admitted); [normIncGammaQContinued_eq](AAR/IncompleteGamma/Basic.lean#L59) (admitted).
- [8.2.E5](https://dlmf.nist.gov/8.2.E5): [normIncGammaP_add_normIncGammaQ](AAR/Statistical/IncompleteGamma.lean#L52) (proved); [normIncGammaContinued_complement](AAR/IncompleteGamma/Basic.lean#L77) (proved).
- [8.2.E6](https://dlmf.nist.gov/8.2.E6): [scIncGamma_eq](AAR/Statistical/IncompleteGamma.lean#L193) (proved).
- [8.2.E7](https://dlmf.nist.gov/8.2.E7): [scIncGamma_eq_normIncGammaP](AAR/Statistical/IncompleteGamma.lean#L213) (proved); [scIncGamma_integral](AAR/IncompleteGamma/Basic.lean#L83) (admitted).
- [8.2.E8](https://dlmf.nist.gov/8.2.E8): [lowerIncGammaOnLog_monodromy](AAR/IncompleteGamma/Basic.lean#L109) (admitted).
- [8.2.E9](https://dlmf.nist.gov/8.2.E9): [upperIncGammaOnLog_monodromy](AAR/IncompleteGamma/Basic.lean#L115) (admitted); [upperIncGammaOnLog_monodromy_limit](AAR/IncompleteGamma/Basic.lean#L121) (admitted).
- [8.2.E10](https://dlmf.nist.gov/8.2.E10): [upperIncGammaOnLog_jump](AAR/IncompleteGamma/Basic.lean#L127) (admitted).
- [8.2.E11](https://dlmf.nist.gov/8.2.E11): [upperIncGammaOnLog_halfTurn](AAR/IncompleteGamma/Basic.lean#L133) (admitted).
- [8.2.E12](https://dlmf.nist.gov/8.2.E12): [lower_upperIncGamma_ode](AAR/IncompleteGamma/Basic.lean#L139) (admitted).
- [8.2.E13](https://dlmf.nist.gov/8.2.E13): [upperIncGamma_scaled_ode](AAR/IncompleteGamma/Basic.lean#L145) (admitted).
- [8.2.E14](https://dlmf.nist.gov/8.2.E14): [scIncGamma_ode](AAR/IncompleteGamma/Basic.lean#L151) (admitted).

#### §8.4

- [8.4.E1](https://dlmf.nist.gov/8.4.E1): [lowerIncGamma_half_square](AAR/IncompleteGamma/SpecialValues.lean#L32) (admitted); [erf_lowerIncGammaOnLog_square](AAR/IncompleteGamma/SpecialValues.lean#L142) (admitted).
- [8.4.E2](https://dlmf.nist.gov/8.4.E2): [scIncGamma_zero](AAR/IncompleteGamma/SpecialValues.lean#L38) (admitted).
- [8.4.E3](https://dlmf.nist.gov/8.4.E3): [scIncGamma_half_negative_square](AAR/IncompleteGamma/SpecialValues.lean#L44) (admitted).
- [8.4.E4](https://dlmf.nist.gov/8.4.E4): [upperIncGamma_zero_E1](AAR/IncompleteGamma/SpecialValues.lean#L50) (proved).
- [8.4.E5](https://dlmf.nist.gov/8.4.E5): [upperIncGamma_one](AAR/Confluent/IncompleteGamma.lean#L206) (proved).
- [8.4.E6](https://dlmf.nist.gov/8.4.E6): [upperIncGamma_one_half_sq](AAR/Confluent/IncompleteGamma.lean#L211) (proved); [upperIncGamma_half_square](AAR/IncompleteGamma/SpecialValues.lean#L56) (admitted); [erfc_upperIncGammaOnLog_square](AAR/IncompleteGamma/SpecialValues.lean#L148) (admitted).
- [8.4.E7](https://dlmf.nist.gov/8.4.E7): [lowerIncGamma_nat_succ_expPartialSum](AAR/IncompleteGamma/SpecialValues.lean#L62) (admitted).
- [8.4.E8](https://dlmf.nist.gov/8.4.E8): [upperIncGamma_nat_succ_expPartialSum](AAR/IncompleteGamma/SpecialValues.lean#L68) (admitted).
- [8.4.E9](https://dlmf.nist.gov/8.4.E9): [normIncGammaPContinued_nat_succ_expPartialSum](AAR/IncompleteGamma/SpecialValues.lean#L74) (admitted).
- [8.4.E10](https://dlmf.nist.gov/8.4.E10): [normIncGammaQ_nat_succ](AAR/Statistical/IncompleteGamma.lean#L95) (proved); [normIncGammaQContinued_nat_succ_expPartialSum](AAR/IncompleteGamma/SpecialValues.lean#L80) (admitted).
- [8.4.E11](https://dlmf.nist.gov/8.4.E11): [normIncGammaP_nat_succ](AAR/Statistical/IncompleteGamma.lean#L108) (proved); [expPartialSum](AAR/IncompleteGamma/SpecialValues.lean#L27) (definition).
- [8.4.E12](https://dlmf.nist.gov/8.4.E12): [scIncGamma_neg_nat](AAR/Statistical/IncompleteGamma.lean#L219) (proved).
- [8.4.E13](https://dlmf.nist.gov/8.4.E13): [upperIncGamma_one_minus_nat](AAR/IncompleteGamma/SpecialValues.lean#L86) (admitted).
- [8.4.E14](https://dlmf.nist.gov/8.4.E14): [normIncGammaQ_half_nat](AAR/IncompleteGamma/SpecialValues.lean#L92) (admitted).
- [8.4.E15](https://dlmf.nist.gov/8.4.E15): [upperIncGamma_neg_nat_finite](AAR/IncompleteGamma/SpecialValues.lean#L98) (admitted); [upperIncGamma_neg_nat_hasSum](AAR/IncompleteGamma/SpecialValues.lean#L104) (admitted).

#### §8.5

- [8.5.E1](https://dlmf.nist.gov/8.5.E1): [lowerIncGamma_eq_regularized](AAR/Confluent/IncompleteGamma.lean#L115) (proved); [lowerIncGamma_kummerM_pair](AAR/IncompleteGamma/SpecialValues.lean#L110) (admitted).
- [8.5.E2](https://dlmf.nist.gov/8.5.E2): [scIncGamma_regularized_pair](AAR/IncompleteGamma/SpecialValues.lean#L116) (admitted).
- [8.5.E3](https://dlmf.nist.gov/8.5.E3): [upperIncGamma_kummerU_pair](AAR/IncompleteGamma/SpecialValues.lean#L122) (proved).
- [8.5.E4](https://dlmf.nist.gov/8.5.E4): [lowerIncGamma_whittakerM](AAR/IncompleteGamma/SpecialValues.lean#L130) (admitted).
- [8.5.E5](https://dlmf.nist.gov/8.5.E5): [upperIncGamma_whittakerW](AAR/IncompleteGamma/SpecialValues.lean#L136) (admitted).

#### §8.6

- [8.6.E1](https://dlmf.nist.gov/8.6.E1): [lowerIncGamma_trigonometric_integral](AAR/IncompleteGamma/Representations.lean#L27) (admitted).
- [8.6.E2](https://dlmf.nist.gov/8.6.E2): [lowerIncGamma_besselJ_integral](AAR/IncompleteGamma/Representations.lean#L33) (admitted).
- [8.6.E3](https://dlmf.nist.gov/8.6.E3): [lowerIncGamma_logarithmic_integral](AAR/IncompleteGamma/Representations.lean#L39) (admitted).
- [8.6.E4](https://dlmf.nist.gov/8.6.E4): [upperIncGamma_stieltjes_integral](AAR/IncompleteGamma/Representations.lean#L45) (admitted).
- [8.6.E5](https://dlmf.nist.gov/8.6.E5): [upperIncGamma_laplace_integral_complex](AAR/IncompleteGamma/Representations.lean#L51) (admitted).
- [8.6.E6](https://dlmf.nist.gov/8.6.E6): [upperIncGamma_besselK_integral](AAR/IncompleteGamma/Representations.lean#L57) (admitted).
- [8.6.E7](https://dlmf.nist.gov/8.6.E7): [upperIncGamma_logarithmic_integral](AAR/IncompleteGamma/Representations.lean#L63) (admitted).
- [8.6.E8](https://dlmf.nist.gov/8.6.E8): [lowerIncGamma_circle_integral](AAR/IncompleteGamma/Representations.lean#L69) (admitted).
- [8.6.E9](https://dlmf.nist.gov/8.6.E9): [upperGammaIndentPV_converges](AAR/IncompleteGamma/Representations.lean#L79) (admitted); [upperIncGamma_indented_integral](AAR/IncompleteGamma/Representations.lean#L85) (admitted).
- [8.6.E10](https://dlmf.nist.gov/8.6.E10): [lowerIncGamma_mellinBarnes](AAR/IncompleteGamma/Representations.lean#L91) (admitted).
- [8.6.E11](https://dlmf.nist.gov/8.6.E11): [upperIncGamma_mellinBarnes](AAR/IncompleteGamma/Representations.lean#L97) (admitted).
- [8.6.E12](https://dlmf.nist.gov/8.6.E12): [upperIncGamma_mellinBarnes_continued](AAR/IncompleteGamma/Representations.lean#L107) (admitted).

#### §8.7

- [8.7.E1](https://dlmf.nist.gov/8.7.E1): [lowerIncGamma_eq_tsum](AAR/Statistical/IncompleteGamma.lean#L117) (proved); [scIncGamma_eq_tsum](AAR/Statistical/IncompleteGamma.lean#L178) (proved); [scIncGamma_hasSum_exponential](AAR/IncompleteGamma/SeriesRecurrences.lean#L27) (admitted); [scIncGamma_hasSum_alternating](AAR/IncompleteGamma/SeriesRecurrences.lean#L33) (admitted).
- [8.7.E2](https://dlmf.nist.gov/8.7.E2): [incompleteGamma_increment_series](AAR/IncompleteGamma/SeriesRecurrences.lean#L39) (admitted).
- [8.7.E3](https://dlmf.nist.gov/8.7.E3): [upperIncGamma_hasSum_alternating](AAR/IncompleteGamma/SeriesRecurrences.lean#L45) (admitted); [upperIncGamma_hasSum_exponential](AAR/IncompleteGamma/SeriesRecurrences.lean#L51) (admitted).
- [8.7.E4](https://dlmf.nist.gov/8.7.E4): [lowerIncGamma_besselI_series](AAR/IncompleteGamma/SeriesRecurrences.lean#L57) (admitted).
- [8.7.E5](https://dlmf.nist.gov/8.7.E5): [scIncGamma_sphericalI_series](AAR/IncompleteGamma/SeriesRecurrences.lean#L63) (admitted).
- [8.7.E6](https://dlmf.nist.gov/8.7.E6): [upperIncGamma_laguerre_series](AAR/IncompleteGamma/SeriesRecurrences.lean#L69) (admitted).

#### §8.8

- [8.8.E1](https://dlmf.nist.gov/8.8.E1): [lowerIncGamma_add_one](AAR/Statistical/IncompleteGamma.lean#L62) (proved).
- [8.8.E2](https://dlmf.nist.gov/8.8.E2): [upperIncGamma_add_one](AAR/Confluent/IncompleteGamma.lean#L196) (proved).
- [8.8.E3](https://dlmf.nist.gov/8.8.E3): [incompleteGamma_threeTerm](AAR/IncompleteGamma/SeriesRecurrences.lean#L75) (admitted).
- [8.8.E4](https://dlmf.nist.gov/8.8.E4): [scIncGamma_recurrence](AAR/IncompleteGamma/SeriesRecurrences.lean#L81) (admitted).
- [8.8.E5](https://dlmf.nist.gov/8.8.E5): [normIncGammaP_add_one](AAR/Statistical/IncompleteGamma.lean#L81) (proved).
- [8.8.E6](https://dlmf.nist.gov/8.8.E6): [normIncGammaQ_add_one](AAR/Statistical/IncompleteGamma.lean#L72) (proved).
- [8.8.E7](https://dlmf.nist.gov/8.8.E7): [lowerIncGamma_shift_up](AAR/IncompleteGamma/SeriesRecurrences.lean#L87) (admitted).
- [8.8.E8](https://dlmf.nist.gov/8.8.E8): [lowerIncGamma_shift_down](AAR/IncompleteGamma/SeriesRecurrences.lean#L93) (admitted).
- [8.8.E9](https://dlmf.nist.gov/8.8.E9): [upperIncGamma_shift_up](AAR/IncompleteGamma/SeriesRecurrences.lean#L99) (admitted).
- [8.8.E10](https://dlmf.nist.gov/8.8.E10): [upperIncGamma_shift_down](AAR/IncompleteGamma/SeriesRecurrences.lean#L105) (admitted).
- [8.8.E11](https://dlmf.nist.gov/8.8.E11): [normIncGammaPContinued_shift_up](AAR/IncompleteGamma/SeriesRecurrences.lean#L111) (admitted).
- [8.8.E12](https://dlmf.nist.gov/8.8.E12): [normIncGammaQContinued_shift_up](AAR/IncompleteGamma/SeriesRecurrences.lean#L117) (admitted).
- [8.8.E13](https://dlmf.nist.gov/8.8.E13): [hasDerivAt_lowerIncGamma_ofReal](AAR/Statistical/IncompleteGamma.lean#L151) (proved); [hasDerivAt_incompleteGamma](AAR/IncompleteGamma/SeriesRecurrences.lean#L123) (admitted).
- [8.8.E14](https://dlmf.nist.gov/8.8.E14): [scIncGamma_deriv_parameter_zero](AAR/IncompleteGamma/SeriesRecurrences.lean#L129) (admitted).
- [8.8.E15](https://dlmf.nist.gov/8.8.E15): [lowerIncGamma_iteratedDeriv_scaled_power](AAR/IncompleteGamma/SeriesRecurrences.lean#L135) (admitted).
- [8.8.E16](https://dlmf.nist.gov/8.8.E16): [upperIncGamma_iteratedDeriv_scaled_power](AAR/IncompleteGamma/SeriesRecurrences.lean#L141) (admitted).
- [8.8.E17](https://dlmf.nist.gov/8.8.E17): [lowerIncGamma_iteratedDeriv_scaled_exp](AAR/IncompleteGamma/SeriesRecurrences.lean#L147) (admitted).
- [8.8.E18](https://dlmf.nist.gov/8.8.E18): [scIncGamma_iteratedDeriv_scaled](AAR/IncompleteGamma/SeriesRecurrences.lean#L159) (admitted).
- [8.8.E19](https://dlmf.nist.gov/8.8.E19): [upperIncGamma_iteratedDeriv_scaled_exp](AAR/IncompleteGamma/SeriesRecurrences.lean#L153) (admitted).

#### §8.9

- [8.9.E1](https://dlmf.nist.gov/8.9.E1): [scIncGamma_continuedFraction](AAR/IncompleteGamma/BoundsFractions.lean#L27) (admitted).
- [8.9.E2](https://dlmf.nist.gov/8.9.E2): [tendsto_gammaIncContFract](AAR/Statistical/ContinuedFraction.lean#L666) (proved); [upperIncGamma_continuedFraction_complex](AAR/IncompleteGamma/BoundsFractions.lean#L33) (admitted).

#### §8.10

- [8.10.E1](https://dlmf.nist.gov/8.10.E1): [upperIncGamma_bound_le_one](AAR/IncompleteGamma/BoundsFractions.lean#L39) (admitted); [upperIncGamma_bound_ge_one](AAR/IncompleteGamma/BoundsFractions.lean#L51) (admitted).
- [8.10.E2](https://dlmf.nist.gov/8.10.E2): [lowerIncGamma_bound_ge](AAR/IncompleteGamma/BoundsFractions.lean#L45) (admitted); [lowerIncGamma_bound_le](AAR/IncompleteGamma/BoundsFractions.lean#L57) (admitted).
- [8.10.E3](https://dlmf.nist.gov/8.10.E3): [Real.upperGammaTheta](AAR/IncompleteGamma/BoundsFractions.lean#L63) (definition); [Real.upperGammaTheta_identity](AAR/IncompleteGamma/BoundsFractions.lean#L68) (admitted).
- [8.10.E4](https://dlmf.nist.gov/8.10.E4): [Real.upperGammaTheta_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L79) (admitted).
- [8.10.E5](https://dlmf.nist.gov/8.10.E5): [Real.upperGammaPade_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L89) (admitted).
- [8.10.E6](https://dlmf.nist.gov/8.10.E6): [Real.upperGammaPade_first](AAR/IncompleteGamma/BoundsFractions.lean#L95) (admitted).
- [8.10.E7](https://dlmf.nist.gov/8.10.E7): [incompleteGamma_positive_exponential_integral](AAR/IncompleteGamma/BoundsFractions.lean#L101) (admitted).
- [8.10.E8](https://dlmf.nist.gov/8.10.E8): [incompleteGamma_positive_exponential_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L107) (admitted); [incompleteGamma_positive_exponential_limit](AAR/IncompleteGamma/BoundsFractions.lean#L113) (admitted).
- [8.10.E9](https://dlmf.nist.gov/8.10.E9): [Real.upperGammaCa](AAR/IncompleteGamma/BoundsFractions.lean#L119) (definition); [Real.upperGammaDa](AAR/IncompleteGamma/BoundsFractions.lean#L124) (definition).
- [8.10.E10](https://dlmf.nist.gov/8.10.E10): [upperIncGamma_power_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L129) (admitted); [upperIncGamma_power_bounds_zero_limit](AAR/IncompleteGamma/BoundsFractions.lean#L135) (admitted).
- [8.10.E11](https://dlmf.nist.gov/8.10.E11): [normIncGammaP_exponential_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L151) (admitted); [normIncGammaP_exponential_bounds_strict](AAR/IncompleteGamma/BoundsFractions.lean#L157) (admitted).
- [8.10.E12](https://dlmf.nist.gov/8.10.E12): [Real.gammaPAlpha](AAR/IncompleteGamma/BoundsFractions.lean#L141) (definition); [Real.gammaPBeta](AAR/IncompleteGamma/BoundsFractions.lean#L146) (definition).
- [8.10.E13](https://dlmf.nist.gov/8.10.E13): [normIncGammaQ_diagonal_bounds](AAR/IncompleteGamma/BoundsFractions.lean#L163) (admitted).

#### §8.11

- [8.11.E1](https://dlmf.nist.gov/8.11.E1): [incGammaAsymptoticCoeff](AAR/IncompleteGamma/Asymptotics.lean#L27) (definition).
- [8.11.E2](https://dlmf.nist.gov/8.11.E2): [hasAsymptoticExpansion_upperIncGamma](AAR/Confluent/IncompleteGamma.lean#L221) (proved); [incGammaAsymptoticRemainder](AAR/IncompleteGamma/Asymptotics.lean#L32) (definition).
- [8.11.E3](https://dlmf.nist.gov/8.11.E3): [upperIncGamma_log_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L37) (admitted).
- [8.11.E4](https://dlmf.nist.gov/8.11.E4): [lowerIncGamma_large_parameter_hasSum](AAR/IncompleteGamma/Asymptotics.lean#L48) (admitted); [lowerIncGamma_large_parameter_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L54) (admitted).
- [8.11.E5](https://dlmf.nist.gov/8.11.E5): [normIncGammaP_large_parameter_equivalent](AAR/IncompleteGamma/Asymptotics.lean#L60) (admitted).
- [8.11.E6](https://dlmf.nist.gov/8.11.E6): [lowerIncGamma_fixed_ratio_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L80) (admitted).
- [8.11.E7](https://dlmf.nist.gov/8.11.E7): [upperIncGamma_fixed_ratio_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L86) (admitted); [upperIncGamma_negative_parameter_ratio_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L92) (admitted).
- [8.11.E8](https://dlmf.nist.gov/8.11.E8): [incGammaLambdaPolynomial_initial](AAR/IncompleteGamma/Asymptotics.lean#L73) (proved).
- [8.11.E9](https://dlmf.nist.gov/8.11.E9): [incGammaLambdaPolynomial](AAR/IncompleteGamma/Asymptotics.lean#L66) (definition).
- [8.11.E10](https://dlmf.nist.gov/8.11.E10): [normIncGammaP_central_expansion](AAR/IncompleteGamma/Asymptotics.lean#L102) (admitted).
- [8.11.E11](https://dlmf.nist.gov/8.11.E11): [scIncGamma_central_expansion](AAR/IncompleteGamma/Asymptotics.lean#L108) (admitted).
- [8.11.E12](https://dlmf.nist.gov/8.11.E12): [upperIncGamma_diagonal_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L114) (admitted).
- [8.11.E13](https://dlmf.nist.gov/8.11.E13): [expPartialSum_poisson_limit](AAR/IncompleteGamma/Asymptotics.lean#L120) (admitted).
- [8.11.E14](https://dlmf.nist.gov/8.11.E14): [expPartialSumRemainderS_identity](AAR/IncompleteGamma/Asymptotics.lean#L131) (admitted).
- [8.11.E15](https://dlmf.nist.gov/8.11.E15): [expPartialSumRemainderS](AAR/IncompleteGamma/Asymptotics.lean#L126) (definition).
- [8.11.E16](https://dlmf.nist.gov/8.11.E16): [expPartialSumRemainderS_one_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L137) (admitted).
- [8.11.E17](https://dlmf.nist.gov/8.11.E17): [expPartialSumRemainderS_neg_one_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L143) (admitted).
- [8.11.E18](https://dlmf.nist.gov/8.11.E18): [expPartialSumRemainderS_uniform_asymptotic](AAR/IncompleteGamma/Asymptotics.lean#L154) (admitted).
- [8.11.E19](https://dlmf.nist.gov/8.11.E19): [expPartialSumRemainderCoeff](AAR/IncompleteGamma/Asymptotics.lean#L149) (definition).

#### §8.12

- [8.12.E1](https://dlmf.nist.gov/8.12.E1): [gammaUniformEtaOnLog](AAR/IncompleteGamma/UniformAsymptotics.lean#L40) (definition); [gammaUniformEta_normalization](AAR/IncompleteGamma/UniformAsymptotics.lean#L57) (admitted).
- [8.12.E2](https://dlmf.nist.gov/8.12.E2): [gammaUniformEta_equation](AAR/IncompleteGamma/UniformAsymptotics.lean#L45) (admitted); [gammaUniformEta_derivative](AAR/IncompleteGamma/UniformAsymptotics.lean#L51) (admitted).
- [8.12.E3](https://dlmf.nist.gov/8.12.E3): [gammaUniformP_identity](AAR/IncompleteGamma/UniformAsymptotics.lean#L72) (admitted).
- [8.12.E4](https://dlmf.nist.gov/8.12.E4): [gammaUniformS](AAR/IncompleteGamma/UniformAsymptotics.lean#L63) (definition).
- [8.12.E5](https://dlmf.nist.gov/8.12.E5): [gammaUniformQ_negative_identity](AAR/IncompleteGamma/UniformAsymptotics.lean#L78) (admitted).
- [8.12.E6](https://dlmf.nist.gov/8.12.E6): [gammaUniform_scIncGamma_identity](AAR/IncompleteGamma/UniformAsymptotics.lean#L84) (admitted).
- [8.12.E7](https://dlmf.nist.gov/8.12.E7): [gammaUniformS_uniform_expansion](AAR/IncompleteGamma/UniformAsymptotics.lean#L108) (admitted).
- [8.12.E8](https://dlmf.nist.gov/8.12.E8): [gammaUniformT_uniform_expansion](AAR/IncompleteGamma/UniformAsymptotics.lean#L114) (admitted).
- [8.12.E9](https://dlmf.nist.gov/8.12.E9): [gammaUniformC](AAR/IncompleteGamma/UniformAsymptotics.lean#L90) (definition); [gammaUniformC_first](AAR/IncompleteGamma/UniformAsymptotics.lean#L98) (admitted).
- [8.12.E10](https://dlmf.nist.gov/8.12.E10): [gammaUniformC](AAR/IncompleteGamma/UniformAsymptotics.lean#L90) (definition).
- [8.12.E11](https://dlmf.nist.gov/8.12.E11): [gammaUniformC_maclaurin](AAR/IncompleteGamma/UniformAsymptotics.lean#L138) (admitted).
- [8.12.E12](https://dlmf.nist.gov/8.12.E12): [gammaUniformD_recurrence](AAR/IncompleteGamma/UniformAsymptotics.lean#L144) (admitted).
- [8.12.E13](https://dlmf.nist.gov/8.12.E13): [gammaUniformInverseLog_spec](AAR/IncompleteGamma/UniformAsymptotics.lean#L132) (admitted); [gammaUniformAlpha_hasSum](AAR/IncompleteGamma/UniformAsymptotics.lean#L150) (admitted).
- [8.12.E14](https://dlmf.nist.gov/8.12.E14): [gammaUniformAlpha_printed](AAR/IncompleteGamma/UniformAsymptotics.lean#L156) (admitted).
- [8.12.E15](https://dlmf.nist.gov/8.12.E15): [normIncGammaQ_diagonal_uniform_asymptotic](AAR/IncompleteGamma/UniformAsymptotics.lean#L168) (admitted).
- [8.12.E16](https://dlmf.nist.gov/8.12.E16): [normIncGammaQ_negative_diagonal_asymptotic](AAR/IncompleteGamma/UniformAsymptotics.lean#L174) (admitted).
- [8.12.E17](https://dlmf.nist.gov/8.12.E17): [gammaUniformC_at_zero_printed](AAR/IncompleteGamma/UniformAsymptotics.lean#L162) (admitted).
- [8.12.E18](https://dlmf.nist.gov/8.12.E18): [gammaParis_uniform_expansion](AAR/IncompleteGamma/UniformAsymptotics.lean#L203) (admitted).
- [8.12.E19](https://dlmf.nist.gov/8.12.E19): [gammaParisD](AAR/IncompleteGamma/UniformAsymptotics.lean#L180) (definition).
- [8.12.E20](https://dlmf.nist.gov/8.12.E20): [gammaParis_printed](AAR/IncompleteGamma/UniformAsymptotics.lean#L197) (admitted).
- [8.12.E21](https://dlmf.nist.gov/8.12.E21): [gammaQInverse](AAR/IncompleteGamma/UniformAsymptotics.lean#L209) (definition); [gammaQInverse_spec](AAR/IncompleteGamma/UniformAsymptotics.lean#L214) (admitted).
- [8.12.E22](https://dlmf.nist.gov/8.12.E22): [gammaQInverse_median_asymptotic](AAR/IncompleteGamma/UniformAsymptotics.lean#L220) (admitted).

#### §8.13

- [8.13.E1](https://dlmf.nist.gov/8.13.E1): [Real.scIncGammaNegativeZero_bounds](AAR/IncompleteGamma/ZerosIntegrals.lean#L57) (admitted).

#### §8.14

- [8.14.E1](https://dlmf.nist.gov/8.14.E1): [normIncGammaP_laplace](AAR/IncompleteGamma/ZerosIntegrals.lean#L92) (admitted).
- [8.14.E2](https://dlmf.nist.gov/8.14.E2): [upperIncGamma_laplace](AAR/IncompleteGamma/ZerosIntegrals.lean#L98) (admitted).
- [8.14.E3](https://dlmf.nist.gov/8.14.E3): [lowerIncGamma_mellin](AAR/IncompleteGamma/ZerosIntegrals.lean#L104) (admitted).
- [8.14.E4](https://dlmf.nist.gov/8.14.E4): [upperIncGamma_mellin](AAR/IncompleteGamma/ZerosIntegrals.lean#L110) (admitted).
- [8.14.E5](https://dlmf.nist.gov/8.14.E5): [lowerIncGamma_mellin_laplace](AAR/IncompleteGamma/ZerosIntegrals.lean#L116) (admitted).
- [8.14.E6](https://dlmf.nist.gov/8.14.E6): [upperIncGamma_mellin_laplace](AAR/IncompleteGamma/ZerosIntegrals.lean#L122) (admitted).

#### §8.15

- [8.15.E1](https://dlmf.nist.gov/8.15.E1): [lowerIncGamma_multiplication_hasSum](AAR/IncompleteGamma/ZerosIntegrals.lean#L128) (admitted).
- [8.15.E2](https://dlmf.nist.gov/8.15.E2): [incompleteGamma_hurwitz_fourier_sum](AAR/IncompleteGamma/ZerosIntegrals.lean#L143) (admitted).

#### §8.17

- [8.17.E1](https://dlmf.nist.gov/8.17.E1): [Real.incBeta](AAR/Statistical/IncompleteBeta.lean#L54) (definition); [incBeta_ofReal](AAR/IncompleteGamma/Beta.lean#L33) (admitted).
- [8.17.E2](https://dlmf.nist.gov/8.17.E2): [Real.normIncBetaI](AAR/Statistical/IncompleteBeta.lean#L59) (definition); [normIncBetaI_ofReal](AAR/IncompleteGamma/Beta.lean#L39) (admitted).
- [8.17.E3](https://dlmf.nist.gov/8.17.E3): Mathlib: [`Complex.betaIntegral_eq_Gamma_mul_div`](.lake/packages/mathlib/Mathlib/Analysis/SpecialFunctions/Gamma/Beta.lean#L537); see [the pointer comments](AAR/DLMF/MathlibCoverage.lean).
- [8.17.E4](https://dlmf.nist.gov/8.17.E4): [Real.normIncBetaI_symm](AAR/Statistical/IncompleteBeta.lean#L109) (proved).
- [8.17.E5](https://dlmf.nist.gov/8.17.E5): [Real.normIncBetaI_nat](AAR/Statistical/IncompleteBeta.lean#L279) (proved).
- [8.17.E6](https://dlmf.nist.gov/8.17.E6): [normIncBetaI_quadratic](AAR/IncompleteGamma/Beta.lean#L45) (admitted).
- [8.17.E7](https://dlmf.nist.gov/8.17.E7): [Real.incBeta_eq_ordinaryHypergeometric](AAR/Statistical/IncompleteBeta.lean#L297) (proved).
- [8.17.E8](https://dlmf.nist.gov/8.17.E8): [incBeta_hypergeometric_euler](AAR/IncompleteGamma/Beta.lean#L51) (admitted).
- [8.17.E9](https://dlmf.nist.gov/8.17.E9): [incBeta_hypergeometric_pfaff](AAR/IncompleteGamma/Beta.lean#L57) (admitted).
- [8.17.E10](https://dlmf.nist.gov/8.17.E10): [normIncBetaI_mellinBarnes](AAR/IncompleteGamma/Beta.lean#L63) (admitted).
- [8.17.E11](https://dlmf.nist.gov/8.17.E11): [incBetaComplement](AAR/IncompleteGamma/Beta.lean#L69) (definition); [incBetaContiguousParameter](AAR/IncompleteGamma/Beta.lean#L74) (definition).
- [8.17.E12](https://dlmf.nist.gov/8.17.E12): [normIncBetaI_contiguous_12](AAR/IncompleteGamma/Beta.lean#L79) (admitted); [normIncBetaI_contiguous_limit_12](AAR/IncompleteGamma/Beta.lean#L127) (admitted).
- [8.17.E13](https://dlmf.nist.gov/8.17.E13): [normIncBetaI_contiguous_13](AAR/IncompleteGamma/Beta.lean#L85) (admitted).
- [8.17.E14](https://dlmf.nist.gov/8.17.E14): [normIncBetaI_contiguous_14](AAR/IncompleteGamma/Beta.lean#L91) (admitted).
- [8.17.E15](https://dlmf.nist.gov/8.17.E15): [normIncBetaI_contiguous_15](AAR/IncompleteGamma/Beta.lean#L97) (admitted).
- [8.17.E16](https://dlmf.nist.gov/8.17.E16): [normIncBetaI_contiguous_16](AAR/IncompleteGamma/Beta.lean#L103) (admitted); [normIncBetaI_contiguous_limit_16](AAR/IncompleteGamma/Beta.lean#L133) (admitted).
- [8.17.E17](https://dlmf.nist.gov/8.17.E17): [normIncBetaI_contiguous_17](AAR/IncompleteGamma/Beta.lean#L109) (admitted); [normIncBetaI_contiguous_limit_17](AAR/IncompleteGamma/Beta.lean#L139) (admitted).
- [8.17.E18](https://dlmf.nist.gov/8.17.E18): [normIncBetaI_contiguous_18](AAR/IncompleteGamma/Beta.lean#L115) (admitted).
- [8.17.E19](https://dlmf.nist.gov/8.17.E19): [normIncBetaI_contiguous_19](AAR/IncompleteGamma/Beta.lean#L121) (admitted).
- [8.17.E20](https://dlmf.nist.gov/8.17.E20): [Real.normIncBetaI_add_one_left](AAR/Statistical/IncompleteBeta.lean#L203) (proved).
- [8.17.E21](https://dlmf.nist.gov/8.17.E21): [Real.normIncBetaI_add_one_right](AAR/Statistical/IncompleteBeta.lean#L228) (proved).
- [8.17.E22](https://dlmf.nist.gov/8.17.E22): [incBeta_continuedFraction](AAR/IncompleteGamma/Beta.lean#L154) (admitted); [incBeta_continuedFraction_endpoint_limit](AAR/IncompleteGamma/Beta.lean#L160) (admitted).
- [8.17.E23](https://dlmf.nist.gov/8.17.E23): [incBetaFractionD](AAR/IncompleteGamma/Beta.lean#L145) (definition).
- [8.17.E24](https://dlmf.nist.gov/8.17.E24): [normIncBetaI_negative_binomial_sum](AAR/IncompleteGamma/Beta.lean#L204) (admitted).

#### §8.18

- [8.18.E1](https://dlmf.nist.gov/8.18.E1): [incBeta_large_a_fixed_x](AAR/IncompleteGamma/BetaAsymptotics.lean#L28) (admitted); [incBeta_large_a_integer_b_exact](AAR/IncompleteGamma/BetaAsymptotics.lean#L34) (admitted).
- [8.18.E2](https://dlmf.nist.gov/8.18.E2): [Real.betaXi](AAR/IncompleteGamma/BetaAsymptotics.lean#L40) (definition).
- [8.18.E3](https://dlmf.nist.gov/8.18.E3): [incBeta_large_a_uniform](AAR/IncompleteGamma/BetaAsymptotics.lean#L88) (admitted).
- [8.18.E4](https://dlmf.nist.gov/8.18.E4): [betaAuxF_recurrence](AAR/IncompleteGamma/BetaAsymptotics.lean#L58) (admitted).
- [8.18.E5](https://dlmf.nist.gov/8.18.E5): [betaAuxF_initial](AAR/IncompleteGamma/BetaAsymptotics.lean#L64) (admitted).
- [8.18.E6](https://dlmf.nist.gov/8.18.E6): [Real.betaGeneratingCoeff](AAR/IncompleteGamma/BetaAsymptotics.lean#L49) (definition); [Real.betaGenerating_hasSum](AAR/IncompleteGamma/BetaAsymptotics.lean#L70) (admitted).
- [8.18.E7](https://dlmf.nist.gov/8.18.E7): [Real.betaGeneratingCoeff_first](AAR/IncompleteGamma/BetaAsymptotics.lean#L76) (admitted); [Real.betaGeneratingCoeff_at_endpoint](AAR/IncompleteGamma/BetaAsymptotics.lean#L82) (admitted).
- [8.18.E8](https://dlmf.nist.gov/8.18.E8): [Real.betaCenter](AAR/IncompleteGamma/BetaAsymptotics.lean#L94) (definition).
- [8.18.E9](https://dlmf.nist.gov/8.18.E9): [incBeta_symmetric_uniform_expansion](AAR/IncompleteGamma/BetaAsymptotics.lean#L141) (admitted).
- [8.18.E10](https://dlmf.nist.gov/8.18.E10): [Real.betaEta](AAR/IncompleteGamma/BetaAsymptotics.lean#L99) (definition); [Real.betaEta_equation](AAR/IncompleteGamma/BetaAsymptotics.lean#L108) (admitted); [Real.betaEtaInverse_spec](AAR/IncompleteGamma/BetaAsymptotics.lean#L114) (admitted).
- [8.18.E11](https://dlmf.nist.gov/8.18.E11): [betaSymmetricC_first](AAR/IncompleteGamma/BetaAsymptotics.lean#L124) (admitted).
- [8.18.E12](https://dlmf.nist.gov/8.18.E12): [betaSymmetricC_at_zero](AAR/IncompleteGamma/BetaAsymptotics.lean#L130) (admitted).
- [8.18.E13](https://dlmf.nist.gov/8.18.E13): retired slot; see [5.11.3](https://dlmf.nist.gov/5.11.E3) and `gammaScaled`.
- [8.18.E14](https://dlmf.nist.gov/8.18.E14): [incBeta_general_uniform_expansion](AAR/IncompleteGamma/BetaAsymptotics.lean#L183) (admitted).
- [8.18.E15](https://dlmf.nist.gov/8.18.E15): [Real.betaZeta](AAR/IncompleteGamma/BetaAsymptotics.lean#L147) (definition); [Real.betaZeta_spec](AAR/IncompleteGamma/BetaAsymptotics.lean#L156) (admitted).
- [8.18.E16](https://dlmf.nist.gov/8.18.E16): [betaGeneralH_first](AAR/IncompleteGamma/BetaAsymptotics.lean#L166) (admitted).
- [8.18.E17](https://dlmf.nist.gov/8.18.E17): [betaGeneralH_at_transition](AAR/IncompleteGamma/BetaAsymptotics.lean#L172) (admitted).
- [8.18.E18](https://dlmf.nist.gov/8.18.E18): [Real.incBetaInverse](AAR/IncompleteGamma/BetaAsymptotics.lean#L189) (definition); [Real.incBetaInverse_spec](AAR/IncompleteGamma/BetaAsymptotics.lean#L194) (admitted).

#### §8.19

- [8.19.E1](https://dlmf.nist.gov/8.19.E1): [genExpIntE](AAR/Confluent/ExpIntegral.lean#L49) (definition).
- [8.19.E2](https://dlmf.nist.gov/8.19.E2): [genExpIntE_horizontal_integral](AAR/IncompleteGamma/ExponentialIntegral.lean#L35) (admitted).
- [8.19.E3](https://dlmf.nist.gov/8.19.E3): [genExpIntE_eq_integral](AAR/Confluent/ExpIntegral.lean#L69) (proved); [genExpIntE_laplace_complex](AAR/IncompleteGamma/ExponentialIntegral.lean#L41) (admitted).
- [8.19.E4](https://dlmf.nist.gov/8.19.E4): [genExpIntE_stieltjes](AAR/IncompleteGamma/ExponentialIntegral.lean#L47) (admitted).
- [8.19.E5](https://dlmf.nist.gov/8.19.E5): [genExpIntE_zero](AAR/Confluent/ExpIntegral.lean#L78) (proved).
- [8.19.E6](https://dlmf.nist.gov/8.19.E6): [genExpIntEExtended_zero](AAR/IncompleteGamma/ExponentialIntegral.lean#L53) (admitted).
- [8.19.E7](https://dlmf.nist.gov/8.19.E7): [genExpIntE_nat_finite](AAR/IncompleteGamma/ExponentialIntegral.lean#L59) (admitted).
- [8.19.E8](https://dlmf.nist.gov/8.19.E8): [genExpIntE_nat_hasSum](AAR/IncompleteGamma/ExponentialIntegral.lean#L65) (admitted).
- [8.19.E9](https://dlmf.nist.gov/8.19.E9): [genExpIntE_nat_digamma_series](AAR/IncompleteGamma/ExponentialIntegral.lean#L71) (admitted).
- [8.19.E10](https://dlmf.nist.gov/8.19.E10): [genExpIntE_hasSum_noninteger](AAR/IncompleteGamma/ExponentialIntegral.lean#L77) (admitted); [genExpIntE_series_integer_limits](AAR/IncompleteGamma/ExponentialIntegral.lean#L89) (admitted).
- [8.19.E11](https://dlmf.nist.gov/8.19.E11): [genExpIntE_hasSum_exponential](AAR/IncompleteGamma/ExponentialIntegral.lean#L83) (admitted); [genExpIntE_series_integer_limits](AAR/IncompleteGamma/ExponentialIntegral.lean#L89) (admitted).
- [8.19.E12](https://dlmf.nist.gov/8.19.E12): [genExpIntE_add_one](AAR/Confluent/ExpIntegral.lean#L84) (proved).
- [8.19.E13](https://dlmf.nist.gov/8.19.E13): [hasDerivAt_genExpIntE](AAR/Confluent/ExpIntegral.lean#L98) (proved).
- [8.19.E14](https://dlmf.nist.gov/8.19.E14): [genExpIntE_scaled_derivative](AAR/IncompleteGamma/ExponentialIntegral.lean#L95) (admitted).
- [8.19.E15](https://dlmf.nist.gov/8.19.E15): [genExpIntE_parameter_derivatives](AAR/IncompleteGamma/ExponentialIntegral.lean#L101) (admitted).
- [8.19.E16](https://dlmf.nist.gov/8.19.E16): [genExpIntE_eq_cpow_mul_kummerU](AAR/Confluent/ExpIntegral.lean#L54) (proved).
- [8.19.E17](https://dlmf.nist.gov/8.19.E17): [genExpIntE_continuedFraction](AAR/IncompleteGamma/ExponentialIntegral.lean#L107) (admitted).
- [8.19.E18](https://dlmf.nist.gov/8.19.E18): [genExpIntEOnLog_monodromy](AAR/IncompleteGamma/ExponentialIntegral.lean#L113) (admitted); [genExpIntEOnLog_nat_monodromy](AAR/IncompleteGamma/ExponentialIntegral.lean#L119) (admitted); [genExpIntEOnLog_nonpos_nat_monodromy](AAR/IncompleteGamma/ExponentialIntegral.lean#L125) (admitted).
- [8.19.E19](https://dlmf.nist.gov/8.19.E19): [genExpIntE_nat_order_bounds](AAR/IncompleteGamma/ExponentialIntegral.lean#L141) (admitted).
- [8.19.E20](https://dlmf.nist.gov/8.19.E20): [genExpIntE_nat_logconvex](AAR/IncompleteGamma/ExponentialIntegral.lean#L147) (admitted).
- [8.19.E21](https://dlmf.nist.gov/8.19.E21): [genExpIntE_nat_rational_bounds](AAR/IncompleteGamma/ExponentialIntegral.lean#L153) (admitted).
- [8.19.E22](https://dlmf.nist.gov/8.19.E22): [genExpIntE_nat_ratio_derivative](AAR/IncompleteGamma/ExponentialIntegral.lean#L159) (admitted).
- [8.19.E23](https://dlmf.nist.gov/8.19.E23): [genExpIntE_tail_integral](AAR/IncompleteGamma/ExponentialIntegral.lean#L165) (admitted).
- [8.19.E24](https://dlmf.nist.gov/8.19.E24): [genExpIntE_nat_laplace](AAR/IncompleteGamma/ExponentialIntegral.lean#L171) (admitted).
- [8.19.E25](https://dlmf.nist.gov/8.19.E25): [genExpIntE_mellin_laplace](AAR/IncompleteGamma/ExponentialIntegral.lean#L177) (admitted).
- [8.19.E26](https://dlmf.nist.gov/8.19.E26): [genExpIntE_product_integral](AAR/IncompleteGamma/ExponentialIntegral.lean#L194) (admitted).
- [8.19.E27](https://dlmf.nist.gov/8.19.E27): [genExpIntL](AAR/IncompleteGamma/ExponentialIntegral.lean#L183) (definition); [genExpIntL_hypergeometric](AAR/IncompleteGamma/ExponentialIntegral.lean#L188) (admitted).

#### §8.20

- [8.20.E1](https://dlmf.nist.gov/8.20.E1): [genExpIntE_exact_remainder](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L25) (admitted).
- [8.20.E2](https://dlmf.nist.gov/8.20.E2): [hasAsymptoticExpansion_genExpIntE](AAR/Confluent/ExpIntegral.lean#L115) (proved); [genExpIntE_log_sector_asymptotic](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L31) (admitted).
- [8.20.E3](https://dlmf.nist.gov/8.20.E3): [genExpIntE_extended_sector_asymptotic](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L37) (admitted).
- [8.20.E4](https://dlmf.nist.gov/8.20.E4): [expIntLargeOrderPolynomial](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L43) (definition).
- [8.20.E5](https://dlmf.nist.gov/8.20.E5): [expIntLargeOrderPolynomial_initial](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L50) (proved).
- [8.20.E6](https://dlmf.nist.gov/8.20.E6): [genExpIntE_large_order_uniform](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L62) (admitted).

#### §8.21

- [8.21.E1](https://dlmf.nist.gov/8.21.E1): [genUpperTrig_gamma](AAR/IncompleteGamma/SineCosine.lean#L57) (admitted).
- [8.21.E2](https://dlmf.nist.gov/8.21.E2): [genLowerTrig_gamma](AAR/IncompleteGamma/SineCosine.lean#L63) (admitted).
- [8.21.E3](https://dlmf.nist.gov/8.21.E3): [gamma_rotated_oscillatory_integral](AAR/IncompleteGamma/SineCosine.lean#L99) (admitted).
- [8.21.E4](https://dlmf.nist.gov/8.21.E4): [genSinIntTail_horizontal_integral](AAR/IncompleteGamma/SineCosine.lean#L105) (admitted).
- [8.21.E5](https://dlmf.nist.gov/8.21.E5): [genCosIntTail_horizontal_integral](AAR/IncompleteGamma/SineCosine.lean#L111) (admitted).
- [8.21.E6](https://dlmf.nist.gov/8.21.E6): [genSinInt_segment_integral](AAR/IncompleteGamma/SineCosine.lean#L117) (admitted).
- [8.21.E7](https://dlmf.nist.gov/8.21.E7): [genCosInt_segment_integral](AAR/IncompleteGamma/SineCosine.lean#L123) (admitted).
- [8.21.E8](https://dlmf.nist.gov/8.21.E8): [genSinInt_complement](AAR/IncompleteGamma/SineCosine.lean#L137) (admitted).
- [8.21.E9](https://dlmf.nist.gov/8.21.E9): [genCosInt_complement](AAR/IncompleteGamma/SineCosine.lean#L143) (admitted).
- [8.21.E10](https://dlmf.nist.gov/8.21.E10): [genTrig_order_zero](AAR/IncompleteGamma/SineCosine.lean#L149) (admitted).
- [8.21.E11](https://dlmf.nist.gov/8.21.E11): [genSinInt_order_zero](AAR/IncompleteGamma/SineCosine.lean#L155) (admitted).
- [8.21.E12](https://dlmf.nist.gov/8.21.E12): [genSinInt_value_at_infinity](AAR/IncompleteGamma/SineCosine.lean#L161) (admitted).
- [8.21.E13](https://dlmf.nist.gov/8.21.E13): [genCosInt_value_at_infinity](AAR/IncompleteGamma/SineCosine.lean#L167) (admitted).
- [8.21.E14](https://dlmf.nist.gov/8.21.E14): [genSinInt_hasSum](AAR/IncompleteGamma/SineCosine.lean#L173) (admitted).
- [8.21.E15](https://dlmf.nist.gov/8.21.E15): [genCosInt_hasSum](AAR/IncompleteGamma/SineCosine.lean#L179) (admitted).
- [8.21.E16](https://dlmf.nist.gov/8.21.E16): [genSinInt_spherical_series](AAR/IncompleteGamma/SineCosine.lean#L185) (admitted).
- [8.21.E17](https://dlmf.nist.gov/8.21.E17): [genCosInt_spherical_series](AAR/IncompleteGamma/SineCosine.lean#L191) (admitted).
- [8.21.E18](https://dlmf.nist.gov/8.21.E18): [genTrigAuxF](AAR/IncompleteGamma/SineCosine.lean#L197) (definition).
- [8.21.E19](https://dlmf.nist.gov/8.21.E19): [genTrigAuxG](AAR/IncompleteGamma/SineCosine.lean#L202) (definition).
- [8.21.E20](https://dlmf.nist.gov/8.21.E20): [genSinIntTail_aux](AAR/IncompleteGamma/SineCosine.lean#L207) (admitted).
- [8.21.E21](https://dlmf.nist.gov/8.21.E21): [genCosIntTail_aux](AAR/IncompleteGamma/SineCosine.lean#L213) (admitted).
- [8.21.E22](https://dlmf.nist.gov/8.21.E22): [genTrigAuxF_oscillatory_integral](AAR/IncompleteGamma/SineCosine.lean#L219) (admitted).
- [8.21.E23](https://dlmf.nist.gov/8.21.E23): [genTrigAuxG_oscillatory_integral](AAR/IncompleteGamma/SineCosine.lean#L225) (admitted).
- [8.21.E24](https://dlmf.nist.gov/8.21.E24): [genTrigAuxF_laplace_integral](AAR/IncompleteGamma/SineCosine.lean#L231) (admitted).
- [8.21.E25](https://dlmf.nist.gov/8.21.E25): [genTrigAuxG_laplace_integral](AAR/IncompleteGamma/SineCosine.lean#L237) (admitted).
- [8.21.E26](https://dlmf.nist.gov/8.21.E26): [genTrigAuxF_sector_asymptotic](AAR/IncompleteGamma/SineCosine.lean#L243) (admitted).
- [8.21.E27](https://dlmf.nist.gov/8.21.E27): [genTrigAuxG_sector_asymptotic](AAR/IncompleteGamma/SineCosine.lean#L249) (admitted).

## Additional unnumbered statements and definitions

This list records declarations without a numbered-equation tag; it includes
convergence statements, mathematical prose and support definitions. Pure source
pointers and bibliographic comments are recorded above.

- [AAR.DLMF.HasIntegralAtTop](AAR/DLMF/Framework.lean#L32) (definition).
- [AAR.DLMF.HasIntegralAtBot](AAR/DLMF/Framework.lean#L35) (definition).
- [AAR.DLMF.HasIntegralWholeLine](AAR/DLMF/Framework.lean#L38) (definition).
- [AAR.DLMF.improperAtTop](AAR/DLMF/Framework.lean#L41) (definition).
- [AAR.DLMF.HasPrincipalValueIoi](AAR/DLMF/Framework.lean#L44) (definition).
- [AAR.DLMF.segmentIntegral](AAR/DLMF/Framework.lean#L50) (definition).
- [AAR.DLMF.primitive](AAR/DLMF/Framework.lean#L53) (definition).
- [AAR.DLMF.sector](AAR/DLMF/Framework.lean#L55) (definition).
- [AAR.DLMF.logSector](AAR/DLMF/Framework.lean#L58) (definition).
- [AAR.DLMF.cfContinuants](AAR/DLMF/Framework.lean#L64) (definition).
- [AAR.DLMF.cfTail](AAR/DLMF/Framework.lean#L76) (definition).
- [AAR.DLMF.HasContinuedFraction](AAR/DLMF/Framework.lean#L80) (definition).
- [AAR.DLMF.oddProduct](AAR/DLMF/Framework.lean#L83) (definition).
- [AAR.DLMF.sphericalJ](AAR/DLMF/Framework.lean#L85) (definition).
- [AAR.DLMF.sphericalI](AAR/DLMF/Framework.lean#L89) (definition).
- [AAR.DLMF.orderedZero](AAR/DLMF/Framework.lean#L93) (definition).
- [AAR.DLMF.asymptoticCoeff](AAR/DLMF/Framework.lean#L99) (definition).
- [AAR.Confluent.faddeevaW_entire](AAR/ErrorFunctions/Basic.lean#L64) (admitted).
- [AAR.Confluent.dawsonF_entire](AAR/ErrorFunctions/Basic.lean#L69) (admitted).
- [AAR.Confluent.fresnelCosInt_entire](AAR/ErrorFunctions/Basic.lean#L74) (admitted).
- [AAR.Confluent.fresnelSinInt_entire](AAR/ErrorFunctions/Basic.lean#L79) (admitted).
- [AAR.Confluent.fresnelTail_entire](AAR/ErrorFunctions/Basic.lean#L84) (admitted).
- [AAR.Confluent.fresnelAuxFComplex_entire](AAR/ErrorFunctions/Basic.lean#L89) (admitted).
- [AAR.Confluent.fresnelAuxGComplex_entire](AAR/ErrorFunctions/Basic.lean#L94) (admitted).
- [AAR.Confluent.dawsonF_ofReal](AAR/ErrorFunctions/Basic.lean#L99) (admitted).
- [AAR.Confluent.fresnelCosInt_ofReal](AAR/ErrorFunctions/Basic.lean#L104) (admitted).
- [AAR.Confluent.fresnelSinInt_ofReal](AAR/ErrorFunctions/Basic.lean#L109) (admitted).
- [AAR.Confluent.fresnelAuxFComplex_ofReal](AAR/ErrorFunctions/Basic.lean#L114) (admitted).
- [AAR.Confluent.fresnelAuxGComplex_ofReal](AAR/ErrorFunctions/Basic.lean#L119) (admitted).
- [AAR.Confluent.gaussianTail](AAR/ErrorFunctions/Basic.lean#L160) (definition).
- [AAR.Confluent.gaussianCdf](AAR/ErrorFunctions/Basic.lean#L164) (definition).
- [AAR.Confluent.scaledErf](AAR/ErrorFunctions/Basic.lean#L168) (definition).
- [AAR.Confluent.dawsonPrimitive](AAR/ErrorFunctions/Basic.lean#L172) (definition).
- [AAR.Confluent.fresnelC1](AAR/ErrorFunctions/Basic.lean#L176) (definition).
- [AAR.Confluent.fresnelS1](AAR/ErrorFunctions/Basic.lean#L180) (definition).
- [AAR.Confluent.fresnelC2](AAR/ErrorFunctions/Basic.lean#L184) (definition).
- [AAR.Confluent.fresnelS2](AAR/ErrorFunctions/Basic.lean#L188) (definition).
- [AAR.Confluent.Real.dawsonF_normalized_strictAnti](AAR/ErrorFunctions/BoundsAsymptotics.lean#L77) (admitted).
- [AAR.Confluent.erfcAsymptoticRemainder](AAR/ErrorFunctions/BoundsAsymptotics.lean#L106) (definition).
- [AAR.Confluent.erfc_remainder_bound](AAR/ErrorFunctions/BoundsAsymptotics.lean#L110) (admitted).
- [AAR.Confluent.erfc_remainder_sign](AAR/ErrorFunctions/BoundsAsymptotics.lean#L115) (admitted).
- [AAR.Confluent.fresnelAsymptoticTerm](AAR/ErrorFunctions/BoundsAsymptotics.lean#L120) (definition).
- [AAR.Confluent.fresnelAux_remainder_bound](AAR/ErrorFunctions/BoundsAsymptotics.lean#L153) (admitted).
- [AAR.Confluent.fresnelAux_remainder_sign](AAR/ErrorFunctions/BoundsAsymptotics.lean#L158) (admitted).
- [AAR.Confluent.erfc_sqrt_reciprocal_laplace_negative](AAR/ErrorFunctions/Integrals.lean#L144) (admitted).
- [AAR.Confluent.Real.generalizedErrorIntegral](AAR/ErrorFunctions/InverseGeneralized.lean#L24) (definition).
- [AAR.Confluent.Real.generalizedDawsonIntegral](AAR/ErrorFunctions/InverseGeneralized.lean#L28) (definition).
- [AAR.Confluent.Real.generalizedErrorIntegral_gamma](AAR/ErrorFunctions/InverseGeneralized.lean#L32) (admitted).
- [AAR.Confluent.Real.generalizedDawsonIntegral_gamma](AAR/ErrorFunctions/InverseGeneralized.lean#L37) (admitted).
- [AAR.Confluent.Real.invErf_spec](AAR/ErrorFunctions/InverseGeneralized.lean#L52) (proved).
- [AAR.Confluent.Real.invErfc_spec](AAR/ErrorFunctions/InverseGeneralized.lean#L58) (proved).
- [AAR.Confluent.invErfSeriesCoeff](AAR/ErrorFunctions/InverseGeneralized.lean#L68) (definition).
- [AAR.Confluent.invErfSeriesCoeff_recurrence](AAR/ErrorFunctions/InverseGeneralized.lean#L88) (admitted).
- [AAR.Confluent.gaussianProbabilityHh](AAR/ErrorFunctions/Repeated.lean#L108) (definition).
- [AAR.Confluent.fresnelAlternateSeries](AAR/ErrorFunctions/Series.lean#L54) (definition).
- [AAR.Confluent.fresnelAlternateSeries_summable](AAR/ErrorFunctions/Series.lean#L58) (admitted).
- [AAR.Confluent.errorFunctionZero](AAR/ErrorFunctions/Zeros.lean#L24) (definition).
- [AAR.Confluent.fresnelFunctionZero](AAR/ErrorFunctions/Zeros.lean#L28) (definition).
- [AAR.Confluent.erf_zero_simple](AAR/ErrorFunctions/Zeros.lean#L32) (admitted).
- [AAR.Confluent.fresnel_zero_orders](AAR/ErrorFunctions/Zeros.lean#L37) (admitted).
- [AAR.Confluent.errorFunctionZero_spec](AAR/ErrorFunctions/Zeros.lean#L42) (admitted).
- [AAR.Confluent.errorFunctionZero_ordered](AAR/ErrorFunctions/Zeros.lean#L47) (admitted).
- [AAR.Confluent.erf_zero_classification](AAR/ErrorFunctions/Zeros.lean#L52) (admitted).
- [AAR.Confluent.erfc_zero_classification](AAR/ErrorFunctions/Zeros.lean#L57) (admitted).
- [AAR.Confluent.faddeevaW_zero_classification](AAR/ErrorFunctions/Zeros.lean#L62) (admitted).
- [AAR.Confluent.fresnelFunctionZero_spec](AAR/ErrorFunctions/Zeros.lean#L67) (admitted).
- [AAR.Confluent.fresnelFunctionZero_ordered](AAR/ErrorFunctions/Zeros.lean#L72) (admitted).
- [AAR.Confluent.fresnel_zero_classification](AAR/ErrorFunctions/Zeros.lean#L77) (admitted).
- [AAR.Confluent.fresnelTail_zero_classification](AAR/ErrorFunctions/Zeros.lean#L82) (admitted).
- [AAR.Confluent.zero_table_1_1](AAR/ErrorFunctions/Zeros.lean#L119) (admitted).
- [AAR.Confluent.zero_table_1_2](AAR/ErrorFunctions/Zeros.lean#L124) (admitted).
- [AAR.Confluent.zero_table_1_3](AAR/ErrorFunctions/Zeros.lean#L129) (admitted).
- [AAR.Confluent.zero_table_1_4](AAR/ErrorFunctions/Zeros.lean#L134) (admitted).
- [AAR.Confluent.zero_table_1_5](AAR/ErrorFunctions/Zeros.lean#L139) (admitted).
- [AAR.Confluent.zero_table_2_1](AAR/ErrorFunctions/Zeros.lean#L144) (admitted).
- [AAR.Confluent.zero_table_2_2](AAR/ErrorFunctions/Zeros.lean#L149) (admitted).
- [AAR.Confluent.zero_table_2_3](AAR/ErrorFunctions/Zeros.lean#L154) (admitted).
- [AAR.Confluent.zero_table_2_4](AAR/ErrorFunctions/Zeros.lean#L159) (admitted).
- [AAR.Confluent.zero_table_2_5](AAR/ErrorFunctions/Zeros.lean#L164) (admitted).
- [AAR.Confluent.zero_table_3_1](AAR/ErrorFunctions/Zeros.lean#L169) (admitted).
- [AAR.Confluent.zero_table_3_2](AAR/ErrorFunctions/Zeros.lean#L174) (admitted).
- [AAR.Confluent.zero_table_3_3](AAR/ErrorFunctions/Zeros.lean#L179) (admitted).
- [AAR.Confluent.zero_table_3_4](AAR/ErrorFunctions/Zeros.lean#L184) (admitted).
- [AAR.Confluent.zero_table_3_5](AAR/ErrorFunctions/Zeros.lean#L189) (admitted).
- [AAR.Confluent.zero_table_4_1](AAR/ErrorFunctions/Zeros.lean#L194) (admitted).
- [AAR.Confluent.zero_table_4_2](AAR/ErrorFunctions/Zeros.lean#L199) (admitted).
- [AAR.Confluent.zero_table_4_3](AAR/ErrorFunctions/Zeros.lean#L204) (admitted).
- [AAR.Confluent.zero_table_4_4](AAR/ErrorFunctions/Zeros.lean#L209) (admitted).
- [AAR.Confluent.zero_table_4_5](AAR/ErrorFunctions/Zeros.lean#L214) (admitted).
- [AAR.Confluent.expIntAsymptoticTerm](AAR/ExpIntegrals/Asymptotics.lean#L24) (definition).
- [AAR.Confluent.expIntE1_remainder_bound](AAR/ExpIntegrals/Asymptotics.lean#L69) (admitted).
- [AAR.Confluent.expIntE1_remainder_sign](AAR/ExpIntegrals/Asymptotics.lean#L74) (admitted).
- [AAR.Confluent.expIntEi_remainder_bound](AAR/ExpIntegrals/Asymptotics.lean#L79) (admitted).
- [AAR.Confluent.expIntAux_remainder_bound](AAR/ExpIntegrals/Asymptotics.lean#L84) (admitted).
- [AAR.Confluent.expIntAux_remainder_sign](AAR/ExpIntegrals/Asymptotics.lean#L89) (admitted).
- [AAR.Confluent.expIntEin_entire](AAR/ExpIntegrals/Basic.lean#L79) (admitted).
- [AAR.Confluent.sinInt_entire](AAR/ExpIntegrals/Basic.lean#L84) (admitted).
- [AAR.Confluent.cosIntCin_entire](AAR/ExpIntegrals/Basic.lean#L89) (admitted).
- [AAR.Confluent.sinhInt_entire](AAR/ExpIntegrals/Basic.lean#L94) (admitted).
- [AAR.Confluent.expIntEin_ofReal](AAR/ExpIntegrals/Basic.lean#L99) (admitted).
- [AAR.Confluent.sinInt_ofReal](AAR/ExpIntegrals/Basic.lean#L104) (admitted).
- [AAR.Confluent.cosIntCin_ofReal](AAR/ExpIntegrals/Basic.lean#L109) (admitted).
- [AAR.Confluent.cosInt_ofReal](AAR/ExpIntegrals/Basic.lean#L114) (admitted).
- [AAR.Confluent.sinInt_odd](AAR/ExpIntegrals/Basic.lean#L119) (admitted).
- [AAR.Confluent.cosIntCin_even](AAR/ExpIntegrals/Basic.lean#L124) (admitted).
- [AAR.Confluent.cosIntOnLog](AAR/ExpIntegrals/Continuation.lean#L29) (definition).
- [AAR.Confluent.coshIntOnLog](AAR/ExpIntegrals/Continuation.lean#L33) (definition).
- [AAR.Confluent.expIntAuxFOnLog](AAR/ExpIntegrals/Continuation.lean#L37) (definition).
- [AAR.Confluent.expIntAuxGOnLog](AAR/ExpIntegrals/Continuation.lean#L41) (definition).
- [AAR.Confluent.Real.cosIntZero](AAR/ExpIntegrals/ZerosIntegrals.lean#L29) (definition).
- [AAR.Confluent.Real.sinIntTailZero](AAR/ExpIntegrals/ZerosIntegrals.lean#L33) (definition).
- [AAR.Confluent.Real.expIntEi_unique_zero](AAR/ExpIntegrals/ZerosIntegrals.lean#L37) (admitted).
- [AAR.Confluent.Real.cosIntZero_spec](AAR/ExpIntegrals/ZerosIntegrals.lean#L48) (admitted).
- [AAR.Confluent.Real.cosIntZero_enumeration](AAR/ExpIntegrals/ZerosIntegrals.lean#L53) (admitted).
- [AAR.Confluent.Real.sinIntTailZero_spec](AAR/ExpIntegrals/ZerosIntegrals.lean#L58) (admitted).
- [AAR.Confluent.Real.sinIntTailZero_enumeration](AAR/ExpIntegrals/ZerosIntegrals.lean#L63) (admitted).
- [AAR.Confluent.expIntActon_initial](AAR/ExpIntegrals/ZerosIntegrals.lean#L155) (admitted).
- [AAR.Confluent.incGammaAsymptoticRemainder_real_bound](AAR/IncompleteGamma/Asymptotics.lean#L42) (admitted).
- [AAR.Confluent.gammaCentralFilter](AAR/IncompleteGamma/Asymptotics.lean#L97) (definition).
- [AAR.Confluent.upperIncGammaOnLog](AAR/IncompleteGamma/Basic.lean#L26) (definition).
- [AAR.Confluent.lowerIncGammaOnLog](AAR/IncompleteGamma/Basic.lean#L30) (definition).
- [AAR.Confluent.normIncGammaPOnLog](AAR/IncompleteGamma/Basic.lean#L44) (definition).
- [AAR.Confluent.normIncGammaQOnLog](AAR/IncompleteGamma/Basic.lean#L48) (definition).
- [AAR.Confluent.scIncGamma_joint_entire](AAR/IncompleteGamma/Basic.lean#L88) (admitted).
- [AAR.Confluent.upperIncGamma_parameter_entire](AAR/IncompleteGamma/Basic.lean#L93) (admitted).
- [AAR.Confluent.lowerIncGamma_parameter_analytic](AAR/IncompleteGamma/Basic.lean#L98) (admitted).
- [AAR.Confluent.lowerIncGamma_parameter_residue](AAR/IncompleteGamma/Basic.lean#L103) (admitted).
- [AAR.Statistical.incBeta](AAR/IncompleteGamma/Beta.lean#L24) (definition).
- [AAR.Statistical.normIncBetaI](AAR/IncompleteGamma/Beta.lean#L28) (definition).
- [AAR.Statistical.incBetaFractionConvergent](AAR/IncompleteGamma/Beta.lean#L149) (definition).
- [AAR.Statistical.incBeta_cf_upper_bound_counterexample](AAR/IncompleteGamma/Beta.lean#L165) (proved).
- [AAR.Statistical.incBeta_cf_second_counterexample_value](AAR/IncompleteGamma/Beta.lean#L185) (proved).
- [AAR.Statistical.incBeta_cf_third_bound_counterexample](AAR/IncompleteGamma/Beta.lean#L209) (proved).
- [AAR.Statistical.incBeta_cf_third_counterexample_value](AAR/IncompleteGamma/Beta.lean#L229) (proved).
- [AAR.Statistical.Real.betaGeneratingKernel](AAR/IncompleteGamma/BetaAsymptotics.lean#L44) (definition).
- [AAR.Statistical.betaAuxF](AAR/IncompleteGamma/BetaAsymptotics.lean#L53) (definition).
- [AAR.Statistical.Real.betaEtaInverse](AAR/IncompleteGamma/BetaAsymptotics.lean#L103) (definition).
- [AAR.Statistical.betaSymmetricC](AAR/IncompleteGamma/BetaAsymptotics.lean#L119) (definition).
- [AAR.Statistical.betaSymmetricC_analytic](AAR/IncompleteGamma/BetaAsymptotics.lean#L135) (admitted).
- [AAR.Statistical.Real.betaGeneralX](AAR/IncompleteGamma/BetaAsymptotics.lean#L151) (definition).
- [AAR.Statistical.betaGeneralH](AAR/IncompleteGamma/BetaAsymptotics.lean#L161) (definition).
- [AAR.Statistical.betaGeneralH_analytic](AAR/IncompleteGamma/BetaAsymptotics.lean#L177) (admitted).
- [AAR.Confluent.Real.upperGammaTheta_limit](AAR/IncompleteGamma/BoundsFractions.lean#L73) (admitted).
- [AAR.Confluent.Real.upperGammaPade](AAR/IncompleteGamma/BoundsFractions.lean#L84) (definition).
- [AAR.Confluent.expIntLargeOrderPolynomial_degree](AAR/IncompleteGamma/ExpIntegralAsymptotics.lean#L56) (admitted).
- [AAR.Confluent.genExpIntEOnLog](AAR/IncompleteGamma/ExponentialIntegral.lean#L26) (definition).
- [AAR.Confluent.genExpIntEExtended](AAR/IncompleteGamma/ExponentialIntegral.lean#L30) (definition).
- [AAR.Confluent.genExpIntEOnLog_parameter_entire](AAR/IncompleteGamma/ExponentialIntegral.lean#L130) (admitted).
- [AAR.Confluent.genExpIntEOnLog_branch_point](AAR/IncompleteGamma/ExponentialIntegral.lean#L135) (admitted).
- [AAR.Confluent.upperGammaIndentPV](AAR/IncompleteGamma/Representations.lean#L74) (definition).
- [AAR.Confluent.gammaBarnesResidueSum](AAR/IncompleteGamma/Representations.lean#L102) (definition).
- [AAR.Confluent.genSinIntOnLog](AAR/IncompleteGamma/SineCosine.lean#L24) (definition).
- [AAR.Confluent.genCosIntOnLog](AAR/IncompleteGamma/SineCosine.lean#L28) (definition).
- [AAR.Confluent.genSinIntTailOnLog](AAR/IncompleteGamma/SineCosine.lean#L32) (definition).
- [AAR.Confluent.genCosIntTailOnLog](AAR/IncompleteGamma/SineCosine.lean#L36) (definition).
- [AAR.Confluent.genSinInt](AAR/IncompleteGamma/SineCosine.lean#L40) (definition).
- [AAR.Confluent.genCosInt](AAR/IncompleteGamma/SineCosine.lean#L44) (definition).
- [AAR.Confluent.genSinIntTail](AAR/IncompleteGamma/SineCosine.lean#L48) (definition).
- [AAR.Confluent.genCosIntTail](AAR/IncompleteGamma/SineCosine.lean#L52) (definition).
- [AAR.Confluent.genSinIntTail_parameter_entire](AAR/IncompleteGamma/SineCosine.lean#L68) (admitted).
- [AAR.Confluent.genCosIntTail_parameter_entire](AAR/IncompleteGamma/SineCosine.lean#L73) (admitted).
- [AAR.Confluent.genSinInt_parameter_analytic](AAR/IncompleteGamma/SineCosine.lean#L78) (admitted).
- [AAR.Confluent.genCosInt_parameter_analytic](AAR/IncompleteGamma/SineCosine.lean#L83) (admitted).
- [AAR.Confluent.genSinInt_parameter_residue](AAR/IncompleteGamma/SineCosine.lean#L88) (admitted).
- [AAR.Confluent.genCosInt_parameter_residue](AAR/IncompleteGamma/SineCosine.lean#L93) (admitted).
- [AAR.Confluent.gammaSinHalfPiContinued](AAR/IncompleteGamma/SineCosine.lean#L128) (definition).
- [AAR.Confluent.gammaCosHalfPiContinued](AAR/IncompleteGamma/SineCosine.lean#L132) (definition).
- [AAR.Confluent.gammaScaled](AAR/IncompleteGamma/UniformAsymptotics.lean#L27) (definition).
- [AAR.Confluent.gammaStirlingCoeff](AAR/IncompleteGamma/UniformAsymptotics.lean#L31) (definition).
- [AAR.Confluent.gammaEtaFactor](AAR/IncompleteGamma/UniformAsymptotics.lean#L35) (definition).
- [AAR.Confluent.gammaUniformT](AAR/IncompleteGamma/UniformAsymptotics.lean#L67) (definition).
- [AAR.Confluent.gammaUniformFilter](AAR/IncompleteGamma/UniformAsymptotics.lean#L103) (definition).
- [AAR.Confluent.gammaUniformInverseLog](AAR/IncompleteGamma/UniformAsymptotics.lean#L119) (definition).
- [AAR.Confluent.gammaUniformAlpha](AAR/IncompleteGamma/UniformAsymptotics.lean#L123) (definition).
- [AAR.Confluent.gammaUniformD](AAR/IncompleteGamma/UniformAsymptotics.lean#L127) (definition).
- [AAR.Confluent.gammaParisRawCoeff](AAR/IncompleteGamma/UniformAsymptotics.lean#L184) (definition).
- [AAR.Confluent.gammaParisA](AAR/IncompleteGamma/UniformAsymptotics.lean#L188) (definition).
- [AAR.Confluent.gammaParisB](AAR/IncompleteGamma/UniformAsymptotics.lean#L192) (definition).
- [AAR.Confluent.Real.scIncGammaNegativeZero](AAR/IncompleteGamma/ZerosIntegrals.lean#L28) (definition).
- [AAR.Confluent.Real.scIncGammaPositiveZero](AAR/IncompleteGamma/ZerosIntegrals.lean#L32) (definition).
- [AAR.Confluent.scIncGamma_nonnegative_parameter_no_real_zeros](AAR/IncompleteGamma/ZerosIntegrals.lean#L36) (admitted).
- [AAR.Confluent.scIncGamma_one_negative_zero](AAR/IncompleteGamma/ZerosIntegrals.lean#L41) (admitted).
- [AAR.Confluent.scIncGamma_two_real_zeros](AAR/IncompleteGamma/ZerosIntegrals.lean#L46) (admitted).
- [AAR.Confluent.Real.scIncGammaNegativeZero_strictAnti](AAR/IncompleteGamma/ZerosIntegrals.lean#L51) (admitted).
- [AAR.Confluent.scIncGammaDoubleZero](AAR/IncompleteGamma/ZerosIntegrals.lean#L62) (definition).
- [AAR.Confluent.scIncGamma_two_parameter_zeros_negative_x](AAR/IncompleteGamma/ZerosIntegrals.lean#L66) (admitted).
- [AAR.Confluent.scIncGamma_two_parameter_zeros_positive_x](AAR/IncompleteGamma/ZerosIntegrals.lean#L71) (admitted).
- [AAR.Confluent.scIncGamma_double_parameter_zero](AAR/IncompleteGamma/ZerosIntegrals.lean#L76) (admitted).
- [AAR.Confluent.scIncGamma_parameter_zeros_at_x_zero](AAR/IncompleteGamma/ZerosIntegrals.lean#L81) (admitted).
- [AAR.Confluent.scIncGamma_conjugate_zero_trajectories](AAR/IncompleteGamma/ZerosIntegrals.lean#L86) (admitted).
- [AAR.Confluent.hurwitzZetaComplex](AAR/IncompleteGamma/ZerosIntegrals.lean#L133) (definition).
- [AAR.Confluent.hurwitzZetaComplex_mathlib](AAR/IncompleteGamma/ZerosIntegrals.lean#L137) (admitted).
- [AAR.Confluent.Real.gammaDiDonatoF](AAR/IncompleteGamma/ZerosIntegrals.lean#L148) (definition).
- [AAR.Confluent.Real.gammaDiDonatoH](AAR/IncompleteGamma/ZerosIntegrals.lean#L152) (definition).
- [AAR.Confluent.Real.gammaDiDonato_gamma](AAR/IncompleteGamma/ZerosIntegrals.lean#L156) (admitted).
- [AAR.Confluent.Real.gammaDiDonato_approximation](AAR/IncompleteGamma/ZerosIntegrals.lean#L161) (admitted).

## Next proof priorities

1. Prove the complex-to-real bridges and entire power-series convergence. They
   allow the existing real theory, TauCeti inverse APIs and Mathlib Gamma/Beta
   results to discharge many initial-value, derivative and symmetry statements.
2. Prove the new Gamma/P/Q continuation bridges and integer/zero limiting
   formulas. Then derive the recurrence, hypergeometric and Whittaker identities
   from existing proved Kummer/Tricomi theory.
3. Prove the real integral representations and convergence predicates before
   their contour and transform extensions. Reuse the existing general Tricomi
   Laplace/Mellin machinery, Gaussian integral and continued-fraction theory.
4. Establish the sectorial expansions from the existing Watson and Tricomi
   expansions. Develop the normalized transition maps and coefficient
   analyticity before attempting uniform large-parameter expansions and inverse
   asymptotics.
5. Leave complete complex zero distributions and certified numerical tables
   until their analytic foundations are established. The false universal Beta
   convergent ordering must not be used as a shortcut.

## Validation

The ordinary full build passed with **9,695 jobs**. Direct `lake env lean` checks
passed for all **34 changed Lean files and `Main.lean`**. The checked files
include the new modules and umbrellas and the existing source with two added
DLMF attributes. The Mathlib pointer names and their axiom dependencies were
checked separately.

The transitive audit covers **6,270 public AAR theorem declarations**. Exactly
**1,008** depend on `sorryAx`, and their names match the explicit source
admissions. All 19 completed statements are independent of admissions; no
additional completed public theorem depends on an admission, and no unexpected
axioms were found. `ToMathlib/` remains admission-free.

All 547 acquired theorem statements match their initial admitted snapshots.
No original theorem assumptions were changed. The continued-fraction helper
was corrected as described above; its theorem statements are unchanged.
The previous exponential-integral source differs only by two source attributes.
Source scans, documentation links and `git diff --check` passed. Toolchain,
dependency pins, build directory and shared `.lake` link are unchanged.
Local source extracts, snapshots and validation logs are in `/tmp/AAR-dlmf678`.
