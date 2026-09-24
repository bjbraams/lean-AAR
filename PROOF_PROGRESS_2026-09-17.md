# Proof progress — 2026-09-17

## Outcome

Replaced **51 `sorry`s** with Lean proofs. The project total went from **757 to 706**
explicit `sorry` occurrences. No axioms were introduced. One theorem statement received an
additional hypothesis (marked in the source, see below); nine statements were found to be
false as stated and were marked with `NOTE` comments but left unchanged.

## Theorems proved

| Theorem | File | DLMF |
| --- | --- | --- |
| `doubleFactorial_odd` | AAR/Gamma/SpecialValues.lean | 5.4.E2 |
| `norm_Gamma_mul_I` | AAR/Gamma/SpecialValues.lean | 5.4.E3 |
| `Gamma_quarter_mul_I` | AAR/Gamma/SpecialValues.lean | 5.4.E5 |
| `trigamma_one_div_two` | AAR/Gamma/SpecialValues.lean | 5.4.E13 |
| `digamma_nat_add_half` | AAR/Gamma/SpecialValues.lean | 5.4.E15 |
| `digamma_mul_I_im` | AAR/Gamma/SpecialValues.lean | 5.4.E16 |
| `digamma_half_add_mul_I_im` | AAR/Gamma/SpecialValues.lean | 5.4.E17 |
| `digamma_one_add_mul_I_im` | AAR/Gamma/SpecialValues.lean | 5.4.E18 |
| `norm_Gamma_add_mul_I_le` | AAR/Gamma/Inequalities.lean | 5.6.E6 |
| `digamma_one_add_mul_I_im_series` | AAR/Gamma/SeriesExpansions.lean | 5.7.E8 |
| `trigamma_nat_sub_half` | AAR/Gamma/Polygamma.lean | 5.15.E4 |
| `polygamma_add_one` | AAR/Gamma/Polygamma.lean | 5.15.E5 |
| `polygamma_reflection` | AAR/Gamma/Polygamma.lean | 5.15.E6 |
| `confluentM_contiguous_a` | AAR/Confluent/Recurrence.lean | 13.3.E1 |
| `confluentM_contiguous_b` | AAR/Confluent/Recurrence.lean | 13.3.E2 |
| `confluentM_contiguous_a_b` | AAR/Confluent/Recurrence.lean | 13.3.E3 |
| `confluentM_contiguous_shift_a` | AAR/Confluent/Recurrence.lean | 13.3.E4 |
| `confluentM_contiguous_mixed` | AAR/Confluent/Recurrence.lean | 13.3.E5 |
| `confluentM_contiguous_down` | AAR/Confluent/Recurrence.lean | 13.3.E6 |
| `confluentM_ode_contiguous` | AAR/Confluent/Recurrence.lean | 13.3.E13 |
| `mulDerivMul_eq_mul_iteratedDeriv` | AAR/Confluent/Recurrence.lean | 13.3.E29 |
| `whittakerM_contiguous_kappa` | AAR/Confluent/Recurrence.lean | 13.15.E1 |
| `whittakerM_contiguous_mu` | AAR/Confluent/Recurrence.lean | 13.15.E2 |
| `whittakerM_contiguous_shift` | AAR/Confluent/Recurrence.lean | 13.15.E3 |
| `whittakerM_contiguous_half` | AAR/Confluent/Recurrence.lean | 13.15.E4 |
| `whittakerM_contiguous_mixed` | AAR/Confluent/Recurrence.lean | 13.15.E5 |
| `whittakerM_contiguous_up` | AAR/Confluent/Recurrence.lean | 13.15.E6 |
| `whittakerM_contiguous_up_shift` | AAR/Confluent/Recurrence.lean | 13.15.E7 |
| `laguerre_recurrence` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.T1 |
| `laguerre_raise_parameter` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.E13 |
| `laguerre_mul_argument` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.E14 |
| `laguerre_continued_fraction` | AAR/OrthogonalPolynomials/ContinuedFractions.lean | 18.13.E4 |
| `chebyshev_geometric_sum` | AAR/OrthogonalPolynomials/Series.lean | 18.18.E31 |
| `chebyshevT_odd_sum` | AAR/OrthogonalPolynomials/Series.lean | 18.18.E33 |
| `chebyshevU_even_sum` | AAR/OrthogonalPolynomials/Series.lean | 18.18.E34 |
| `chebyshevU_odd_sum` | AAR/OrthogonalPolynomials/Series.lean | 18.18.E35 |
| `iterate_mulDerivMul_euler` | AAR/Hypergeometric/Derivatives.lean | 15.5.E5 |
| `iteratedDeriv_euler` | AAR/Hypergeometric/Derivatives.lean | 15.5.E6 |
| `iterate_oneSubMulDerivMul` | AAR/Hypergeometric/Derivatives.lean | 15.5.E7 |
| `iterate_oneSubMulDerivMul_cpow` | AAR/Hypergeometric/Derivatives.lean | 15.5.E8 |
| `iteratedDeriv_two_cpow` | AAR/Hypergeometric/Derivatives.lean | 15.5.E9 |
| `iterate_mulDerivMul_confluentM` | AAR/Confluent/Recurrence.lean | 13.3.E17 |
| `iteratedDeriv_mul_cpow_confluentM` | AAR/Confluent/Recurrence.lean | 13.3.E18 |
| `iterate_mulDerivMul_exp_neg_confluentM` | AAR/Confluent/Recurrence.lean | 13.3.E19 |
| `iteratedDeriv_exp_neg_confluentM` | AAR/Confluent/Recurrence.lean | 13.3.E20 |
| `iteratedDeriv_mul_cpow_exp_neg_confluentM` | AAR/Confluent/Recurrence.lean | 13.3.E21 |
| `iteratedDeriv_exp_mul_whittakerM_neg` | AAR/Confluent/Recurrence.lean | 13.15.E16 |
| `iterate_mulDerivMul_whittakerM` | AAR/Confluent/Recurrence.lean | 13.15.E17 |
| `iteratedDeriv_exp_neg_whittakerM_neg` | AAR/Confluent/Recurrence.lean | 13.15.E19 |
| `iterate_mulDerivMul_exp_neg_whittakerM` | AAR/Confluent/Recurrence.lean | 13.15.E20 |
| `hermitePhys_turan` | AAR/OrthogonalPolynomials/BoundsZeros.lean | 18.14.E13 |

## Proof structure and new supporting lemmas

- **Gamma special values.** Conjugation symmetry of the digamma function (`digamma_conj`,
  from Mathlib's `Gamma_conj` and `deriv_conj_conj`) combined with Euler's reflection formula
  gives the imaginary parts 5.4.16–5.4.18. The modulus formulas use the reflection formula and
  `Gamma_conj`. The trigamma value at `1/2` splits Mathlib's `ζ(2)` sum into even and odd
  terms. New lemmas: `digamma_conj`, `cot_pi_mul_I`, `neg_I_mul_ofReal_im`.
- **Polygamma.** `analyticAt_Gamma` and `analyticAt_digamma` (via
  `analyticAt_iff_eventually_differentiableAt` on the open set `isOpen_not_neg_nat`), the
  trigamma recurrence `trigamma_add_one`, `isOpen_not_int`, and `contDiffAt_cot_pi_mul`.
  The recurrence and reflection formulas differentiate Mathlib's digamma identities `n` times
  using `Filter.EventuallyEq.iteratedDeriv_eq` and the shift lemmas for `iteratedDeriv`.
- **Kummer contiguous relations.** Coefficient identities for `confluentHGCoeff` under unit
  shifts give four derivative relations (`z_mul_deriv_confluentM_eq_shift_a`,
  `…_shift_b_pred`, `…_shift_a_pred`, `deriv_confluentM_eq_shift_b_succ`) by comparing
  everywhere-convergent power series (`hasSum_confluentM`, `hasSum_z_mul_confluentM`, …).
  The six relations 13.3.1–13.3.6 and 13.3.13 are linear combinations of these, except 13.3.4
  and 13.3.13, which are proved directly from coefficient identities. Four further auxiliary
  Kummer relations (`confluentM_contiguous_shift_b_succ`, `…_mixed_b_pred`, `…_up_aux`,
  `…_up_shift_aux`) feed the Whittaker relations.
- **Whittaker `M` contiguous relations.** All seven reduce to Kummer relations after
  unfolding `whittakerM`; the factors `z^(1/2)` are handled with `cpow_add` on the slit plane.
- **Laguerre.** The three-term recurrence and the two parameter shifts are the Kummer
  relations 13.3.1, 13.3.3 and 13.3.4 at `a = -n`, `b = α + 1`. The continued fraction then
  follows the pattern of the Legendre case. `Differential.lean` now imports
  `AAR.Confluent.Recurrence` for this.
- **Chebyshev finite sums.** Induction with Mathlib's `Chebyshev.U_eq_X_mul_U_add_T`,
  `two_mul_T_eq_U_sub_U`, `one_sub_X_sq_mul_U_eq_pol_in_T` and `T_add_two`.
- **5.7.8.** Mathlib's cotangent partial fractions `cot_series_rep'` at `x = i y`, combined
  with 5.4.18.
- **Gauss iterated derivatives 15.5.5–15.5.9.** Each is an induction whose step is a
  first-derivative identity: product rules for `w^s`, `(1-w)^t` and `₂F₁` on the slit plane
  (`deriv_one_sub_cpow_mul_hg`, `deriv_cpow_mul_one_sub_cpow_mul_hg`), combined with
  contiguous derivative relations. Three of these relations are new
  (`one_sub_mul_deriv_eq_shift_a_c`, `mul_one_sub_deriv_eq_shift_down`,
  `mul_one_sub_deriv_eq_shift_down_two`) and follow from `deriv_contiguous_c_succ`,
  `contiguous_c`, `contiguous_shift_b` and the derivative relations in `Contiguous.lean`.
  The five theorems were moved (statements unchanged) to the end of `Derivatives.lean`
  because they use `deriv_contiguous_c_succ`, which is proved later in that file.
- **Kummer iterated derivatives 13.3.17–13.3.21.** The same pattern with the Kummer
  derivative relations proved earlier in this pass and the entire-function derivative
  helpers `hasDerivAt_confluentM`, `deriv_cpow_mul_confluentM`,
  `deriv_exp_neg_mul_confluentM`, `deriv_cpow_mul_exp_neg_mul_confluentM`.
- **Whittaker derivatives 13.15.16, 13.15.17, 13.15.19, 13.15.20.** After unfolding
  `whittakerM`, the exponential and power prefactors collapse on the slit plane and the
  Kummer formulas apply; `iterate_mulDerivMul_congr` transports iterates of the operator
  `z (z f)'` along eventual equality.
- **Turán's inequality for Hermite polynomials.** With `D n := H(n+1)² - H n H(n+2)`, the
  recurrence gives `D (n+1) = 2 (n+1) D n + 2 H(n+1)²`, so `D n ≥ 0` by induction from
  `D 0 = 2`. `BoundsZeros.lean` now imports `AAR.OrthogonalPolynomials.Differential`.

## Changed assumptions

- `AAR.Confluent.mulDerivMul_eq_mul_iteratedDeriv` (13.3.29) received the hypothesis
  `hf : ContDiff ℂ ⊤ f`. The DLMF identity concerns smooth `f`; without smoothness both
  sides involve junk values of `deriv`. The proof reuses the Gauss-side operator identity
  `AAR.Hypergeometric.iterate_mulDerivMul_eq`, so `Recurrence.lean` now imports
  `AAR.Hypergeometric.Derivatives`. A `NOTE` comment marks the change.

## Statements found to be false as stated (unchanged, marked with `NOTE` comments)

All are consequences of Mathlib's `Gamma` vanishing at the nonpositive integers, or of the
principal-branch definitions, which the totalized definitions in this project inherit.

- `AAR/Confluent/Relations.lean`: `confluentU_of_zero_param` (fails at `b = 1`),
  `confluentU_shift_one` (fails at `a = 0`), `confluentU_laguerre` (fails at `α = 0`),
  the two `whittakerW` conjuncts of `whittakerM_exp` (fail at `κ = 1/2`), and
  `whittakerM_exp_neg` (fails at `κ = 0`, where `confluentM 0 0 z = 1`).
- `AAR/Confluent/Whittaker.lean`: `whittakerM_neg_argument` and `whittakerM_continuation`.
  Since `z * exp (2 m π I) = z` and `z * exp (± π I) = -z` exactly, the left sides do not
  encode analytic continuation, while the right sides carry the continuation factors.
- `AAR/Confluent/Recurrence.lean`: `iteratedDeriv_exp_mul_whittakerM` (13.15.15) and
  `iteratedDeriv_exp_neg_whittakerM` (13.15.18) fail at `μ = 0`, `n = 1`, which `hμ` allows:
  the factor `poch (-2μ) n` vanishes while the left side is a nonzero Kummer derivative.
  DLMF reads the product with the regularized function.

Other continuation-type statements (`whittakerW_continuation`,
`confluentU_analytic_continuation`) and the hypothesis-free `confluentU` contiguous and
derivative statements in `Recurrence.lean` are likely affected by the same issues; they were
not analysed in detail.

## Validation

All commands ran from the Lake root.

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3863 jobs.
- `lake env lean` passed for every edited file: `AAR/Gamma/SpecialValues.lean`,
  `AAR/Gamma/Polygamma.lean`, `AAR/Gamma/Inequalities.lean`,
  `AAR/Gamma/SeriesExpansions.lean`, `AAR/Confluent/Recurrence.lean`,
  `AAR/Confluent/Relations.lean`, `AAR/Confluent/Whittaker.lean`,
  `AAR/Hypergeometric/Derivatives.lean`,
  `AAR/OrthogonalPolynomials/Differential.lean`,
  `AAR/OrthogonalPolynomials/ContinuedFractions.lean`,
  `AAR/OrthogonalPolynomials/Series.lean`,
  `AAR/OrthogonalPolynomials/BoundsZeros.lean`.
- `git diff --check`: passed (the Lean files are untracked; the edited files were also
  checked for trailing whitespace directly).
- `rg -n '\bsorry\b' AAR`: 706 occurrences.
- A temporary `Scratch.lean` printed the axioms of all 51 theorems above and of
  `trigamma_add_one`: each depends only on `propext`, `Classical.choice` and `Quot.sound`;
  none depends on `sorryAx`. The file was removed afterwards.

The `.lake` symlink, toolchain and Mathlib revision were preserved. No commits were made.

## Remaining admissions in the edited modules

| Module | Before | After |
| --- | ---: | ---: |
| AAR/Gamma/SpecialValues.lean | 9 | 1 |
| AAR/Gamma/Polygamma.lean | 8 | 5 |
| AAR/Gamma/Inequalities.lean | 9 | 8 |
| AAR/Gamma/SeriesExpansions.lean | 7 | 6 |
| AAR/Confluent/Recurrence.lean | 53 | 29 |
| AAR/Hypergeometric/Derivatives.lean | 5 | 0 |
| AAR/OrthogonalPolynomials/Differential.lean | 19 | 16 |
| AAR/OrthogonalPolynomials/ContinuedFractions.lean | 1 | 0 |
| AAR/OrthogonalPolynomials/Series.lean | 38 | 34 |
| AAR/OrthogonalPolynomials/BoundsZeros.lean | 25 | 24 |

The remaining `sorry` in `SpecialValues.lean` is Gauss's digamma theorem (5.4.19).

## Proof review: replacing first-principles proofs by references

A second pass reviewed the existing proofs (ordered by length) for results that follow from a
more general statement in the project or from Mathlib. Changes (statements unchanged):

| Declaration | File | Before | After | Now proved from |
| --- | --- | ---: | ---: | --- |
| `Real.digamma_eq_re_digamma` (new bridge) | AAR/Gamma/Digamma.lean | – | 18 | Mathlib `Complex.digamma`, `HasDerivAt.real_of_complex`, `deriv_conj_conj` |
| `Real.digamma_add_one` | AAR/Gamma/Digamma.lean | 26 | 6 | bridge + Mathlib `Complex.digamma_apply_add_one` |
| `Real.digamma_one_sub` | AAR/Gamma/Digamma.lean | 45 | 13 | bridge + Mathlib `Complex.digamma_one_sub` |
| `Real.hasDerivAt_log_sin_pi` | AAR/Gamma/Digamma.lean | 62 | 9 | Mathlib chain rule (no longer needed by the reflection formula) |
| `Real.digamma_add_digamma_add_half` | AAR/Gamma/GaussDigamma.lean | 12 | 14 | bridge + Mathlib `Complex.digamma_two_mul` (was: project multiplication formula) |
| `Real.digamma_one_div_two` | AAR/Gamma/GaussDigamma.lean | 12 | 9 | bridge + Mathlib `Complex.digamma_one_half` |
| `AAR.Confluent.confluentM_one_two` | AAR/Confluent/Relations.lean | 35 | 13 | contiguous relation 13.3.4 with `M(1,1,·) = exp`, `M(0,·,·) = 1` |
| `deriv_confluentM_regular` | AAR/OrthogonalPolynomials/Differential.lean | 20 | 1 | `AAR.Confluent.deriv_confluentM` (same statement, 13.3.15) |
| `Gamma_nat_add_half` | AAR/Bessel/Basic.lean | 34 | 18 | Mathlib `Real.Gamma_nat_add_half` |
| `Gamma_nat_add_three_halves` | AAR/Bessel/Basic.lean | 37 | 17 | Mathlib `Real.Gamma_nat_add_one_add_half` |
| `AAR.Gamma.poch_succ_left` | AAR/Gamma/Pochhammer.lean | 2 | 1 | the identical root-level `poch_succ_left` (`Hypergeometric/Series.lean`) |
| `Gamma_half_add_mul_I`, `norm_Gamma_mul_I` | AAR/Gamma/SpecialValues.lean | 31, 24 | 27, 22 | new shared `Gamma_mul_Gamma_conj` |

New imports: `Deriv.Star` and `Complex.RealDeriv` in `Digamma.lean`; `AAR.Confluent.Recurrence`
in `Relations.lean`; `AAR.Hypergeometric.Series` in `Gamma/Pochhammer.lean`.

Reviewed and found already reference-based (no change): the real multiplication formulas
(`Gamma_prod_add_div`, `Gamma_mul_nat` over `ℝ` from the complex ones), `legendreP_recurrence`
and the Legendre continued fraction (from the Gegenbauer recurrence), the Whittaker–Tricomi
conversions, `whittakerM_sinh` (from `confluentM_one_two`), `qGamma_two`, the Stirling file
(from Mathlib's `Stirling.factorial_isEquivalent_stirling`), and `contiguous_a` (from the
derivative relations). Considered but left as is: deriving `euler_transformation` from two
Pfaff transformations (needs extra positivity hypotheses), deriving the Mathlib-`hermite`
generating function from the `hermitePhys` one (needs a complex scaling lemma of similar
length), and `gegenbauer_derivative` from `jacobi_derivative` (Pochhammer bookkeeping of
similar length). The digamma series machinery in `Digamma.lean` has no Mathlib counterpart.

Validation after the review: `lake build` passed (3863 jobs); `rg -n '\bsorry\b' AAR` still
706; `git diff --check` clean; `#print axioms` on all fourteen changed declarations shows only
`propext`, `Classical.choice`, `Quot.sound`.

## Phase 2: analytic continuation in the parameters

Following the agreed strategy (conventions, then a continuation toolkit, then proofs in
"general lemma plus DLMF corollary" form), this phase added the toolkit and used it. The
project total went from **706 to 700** `sorry`s; all new declarations depend only on
`propext`, `Classical.choice`, `Quot.sound`.

### New module `AAR/Hypergeometric/Continuation.lean`

- `eq_of_analyticOnNhd_univ_of_eventuallyEq`, `eq_of_analyticOnNhd_univ_of_eqOn`: the identity
  principle on `ℂ` in the two forms used below.
- `analyticOnNhd_tsum_of_eventually_dominated`: a series of entire functions whose terms are,
  near every point, eventually dominated by a summable sequence is entire (from Mathlib's
  `differentiableOn_tsum_of_summable_norm`).
- `isOpen_not_neg_nat` (moved here from `Polygamma.lean`, which now references it) and
  `eventually_nhdsWithin_ne_neg_nat`.
- Bounds: `ascPochhammer_eval_mono`, `norm_ascPochhammer_eval_le`,
  `factorial_le_norm_ascPochhammer_eval`, and `norm_inv_Gamma_add_nat_le`
  (`‖1/Γ(c+n)‖ ≤ 1/((n-N)! ‖Γ(c+N)‖)` for `n ≥ N` and `Re (c+N) ≥ 1`).
- **`analyticOnNhd_regularizedGaussHGFun_c`, `_a`, `_b`** (DLMF §15.2(ii)): Mathlib's
  regularized Gauss function `𝐅(a,b;c;z)` is an entire function of each parameter for
  `‖z‖ < 1`. The tail of the series is dominated on a neighbourhood by the series with
  parameters `(‖a‖, ‖b‖, 1-N)`, whose summability is Mathlib's `summable_norm_mul_pow`.
- **`regularizedGaussHGFun_contiguous_c`**: the contiguous relation
  `𝐅(a,b;c;z) = (c-a) 𝐅(a,b;c+1;z) + a 𝐅(a+1,b;c+1;z)` with no hypothesis on the parameters,
  obtained from `contiguous_c` off the poles and continuation in `c`. This is the pattern for
  hypothesis-free versions of the other contiguous relations.

The joint statement `entire_regularized_parameters` (analyticity in `(a,b,c)` together) is not
derived from the separate statements; it remains admitted.

### Theorems proved with the toolkit

| Theorem | File | DLMF | Method |
| --- | --- | --- | --- |
| `regularized_at_neg_nat` | AAR/Hypergeometric/AnalyticProperties.lean | 15.2.E3_5 | series tail after the vanishing coefficients |
| `tendsto_regularized_at_neg_nat` | AAR/Hypergeometric/AnalyticProperties.lean | 15.2.E3_5 | continuity in `c` of `𝐅` |
| `jacobi_contiguous_add` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.E4 | disk relation, extension in `x` |
| `jacobi_contiguous_sub` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.E3 | `contiguous_c`, extension in `x` |
| `jacobi_raise_beta` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.E5 | `contiguous_ab`, extension in `x` |
| `gegenbauer_recurrence` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.T1 | normalized recurrence for `Re λ > 0`, continuation in `λ` over `Re λ > -1/2` |

Supporting lemmas in `Differential.lean`: `isOpen_half_shift_disk`, `analyticOnNhd_jacobiP`,
`analyticOnNhd_gegenbauer`, `analyticOnNhd_gegenbauer_param`, `eq_of_eqOn_half_shift_disk`.
The Gauss contiguous relations are only available for `‖z‖ < 1`; the polynomial identities are
proved there and extended by the identity principle, since the polynomials are entire in `x`.

### Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3864 jobs (one new module).
- `lake env lean` passed for `AAR/Hypergeometric/Continuation.lean`,
  `AAR/Hypergeometric/AnalyticProperties.lean`, `AAR/Gamma/Polygamma.lean`,
  `AAR/OrthogonalPolynomials/Differential.lean`; `AAR/Hypergeometric.lean` imports the new module.
- `git diff --check`: passed. `rg -n '\bsorry\b' AAR`: 700 occurrences.
- Axiom audit (temporary `Scratch.lean`, removed): the toolkit theorems and the six theorems
  above depend only on the standard axioms.

### Suggested next steps on this track

1. Hypothesis-free regularized versions of the remaining Gauss contiguous relations, by the
   same three-line pattern as `regularizedGaussHGFun_contiguous_c`.
2. The remaining Jacobi identities in `Differential.lean` (`jacobi_raise_degree_beta`, the two
   derivative relations, `jacobi_recurrence`) by disk relations plus extension in `x`; the
   first needs an extra continuation in `β` at `n + α + β + 1 = 0`.
3. The confluent analogue of the parameter analyticity for `regularizedHGFun {a} {b}`
   (entire in `a` and in `b`, all `z`), which unlocks hypothesis-free Kummer relations.
4. The continued `₂F₁` in the argument (design note first), needed for the Kummer solutions
   and connection formulas.

## Phase 3: regularized statements valid for all parameters

This phase carries out steps 1, 3 and (as a design note) 4 of the list above. No `sorry` was
added or removed: the project total remains **700**. Every new declaration depends only on
`propext`, `Classical.choice`, `Quot.sound`. All new statements are hypothesis-free in the
parameters; the DLMF-form statements with hypotheses are kept unchanged and are the base
cases of the new proofs.

### Gauss: `AAR/Hypergeometric/Continuation.lean` (now about 820 lines)

Toolkit additions:

- `analyticOnNhd_regularizedGaussHGFun_comp`: `w ↦ 𝐅(A w, B w; C w; z)` is entire for entire
  `A B C` and `‖z‖ < 1` (the earlier `_a`, `_b`, `_c` are now corollaries).
- `analyticAt_regularizedGaussHGFun_comp` and `differentiable_regularizedGaussHGFun_comp`, both
  tagged `@[fun_prop]`, so that analyticity of any polynomial expression in shifted `𝐅`'s is
  discharged by `fun_prop (disch := assumption)`.
- `eq_of_eqOn_not_neg_nat`, `eq_of_eqOn_not_neg_nat_sub_one`, `eq_of_eqOn_re_pos`: identity
  principle for entire functions agreeing off the poles of `Γ(c)`, off those of `Γ(c-1)`, or
  on `Re c > 0`.
- `differentiableAt_regularizedGaussHGFun`, `regularizedHGFunCoeff_pair_succ`.

Regularized theorems (all `a b c : ℂ`, `‖z‖ < 1`; each is DLMF's relation divided by the
appropriate `Γ(c + k)`):

| Theorem | DLMF | Statement |
| --- | --- | --- |
| `deriv_regularizedGaussHGFun` | 15.5.1 | `𝐅' = a b 𝐅(a+1,b+1;c+1)` |
| `iteratedDeriv_regularizedGaussHGFun` | 15.5.2 | `𝐅⁽ⁿ⁾ = (a)ₙ(b)ₙ 𝐅(a+n,b+n;c+n)` |
| `regularizedGaussHGFun_contiguous_shift_b` | 15.5.16 | `𝐅 − 𝐅(b+1) = −a z 𝐅(a+1,b+1;c+1)` |
| `regularizedGaussHGFun_contiguous_a` | 15.5.11 | three-term relation in `a` |
| `regularizedGaussHGFun_contiguous_ab` | 15.5.12 | `(b−a)𝐅 + a𝐅(a+1) − b𝐅(b+1) = 0` |
| `regularizedGaussHGFun_contiguous_a_b_pred` | 15.5.13 | |
| `regularizedGaussHGFun_contiguous_c_succ_deriv` | 15.5.21 | `(1−z) a b 𝐅(a+1,b+1;c+1) = (c−a)(c−b)𝐅(c+1) + (a+b−c)𝐅` |
| `regularizedGaussHGFun_contiguous_a_c_succ` | 15.5.14 | |
| `regularizedGaussHGFun_contiguous_a_succ_c_pred` | 15.5.15 | `(c−a−1)𝐅 + a𝐅(a+1) − 𝐅(c−1) = 0` |
| `regularizedGaussHGFun_contiguous_a_pred_c_succ` | 15.5.16 | |
| `regularizedGaussHGFun_contiguous_a_pred_c_pred` | 15.5.17 | |
| `regularizedGaussHGFun_contiguous_c_three` | 15.5.18 | `(z−1)𝐅(c−1) + (c−1−(2c−a−b−1)z)𝐅 + (c−a)(c−b)z𝐅(c+1) = 0` |
| `regularizedGaussHGFun_contiguous_diagonal` | 15.5.19 | |
| `regularizedGaussHGFun_euler` | 15.8.1 | `𝐅(a,b;c;z) = (1−z)^(c−a−b) 𝐅(c−a,c−b;c;z)` |
| `regularizedGaussHGFun_pfaff` | 15.8.1 | `𝐅(a,b;c;z) = (1−z)^(−a) 𝐅(a,c−b;c;z/(z−1))`, with `‖z/(z−1)‖ < 1` |

The contiguous relations follow a uniform pattern: analyticity of both sides in `c` by
`fun_prop`; off the poles rewrite `𝐅 = ₂F₁/Γ(c)` and `Γ(c+1) = cΓ(c)` (or
`Γ(c) = (c−1)Γ(c−1)`), `field_simp`, `linear_combination` of the DLMF relation. Euler and
Pfaff need two continuations: first in `b` on the strip `0 < Re b < Re c` for `Re c > 0`
(where `euler_transformation`/`pfaff_transformation` apply), then in `c` on `Re c > 0`.
The relations with `c − 1` had required `∀ k, c − 1 ≠ −k` in addition to `∀ k, c ≠ −k`; the
regularized forms need neither, and the factor `(c−1)` disappears from the `𝐅(c−1)` term.

### Kummer: new module `AAR/Confluent/Continuation.lean` (registered in `AAR/Confluent.lean`)

Mathlib's regularized Kummer function `𝐌(a,b,z) = regularizedHGFun {a} {b} z` is entire in
`z` (`hasFPowerSeriesOnBall_regularizedConfluent`, radius `⊤`) and entire along entire curves
in `(a, b)` (`analyticOnNhd_regularizedConfluent_comp`, with `_a`, `_b`, `fun_prop`-tagged
`analyticAt_`/`differentiable_` versions). The majorant is `𝐌(‖a‖+1, 1−N, ‖z‖)`, mirroring the
Gauss case. The bridge is `regularizedConfluent_eq_div_Gamma : 𝐌 = M/Γ(b)` off the poles.

Regularized theorems (all `a b z : ℂ`):

| Theorem | DLMF | Statement |
| --- | --- | --- |
| `deriv_regularizedConfluent` | 13.3.15 | `𝐌' = a 𝐌(a+1,b+1)` |
| `iteratedDeriv_regularizedConfluent` | 13.3.15 | `𝐌⁽ⁿ⁾ = (a)ₙ 𝐌(a+n,b+n)` |
| `regularizedConfluent_contiguous_a` | 13.3.1 | |
| `regularizedConfluent_contiguous_b` | 13.3.2 | `𝐌(b−1) + (1−b−z)𝐌 + z(b−a)𝐌(b+1) = 0` |
| `regularizedConfluent_contiguous_a_b` | 13.3.3 | `(a−b+1)𝐌 − a𝐌(a+1) + 𝐌(b−1) = 0` |
| `regularizedConfluent_contiguous_shift_a` | 13.3.4 | `𝐌 − 𝐌(a−1) − z𝐌(b+1) = 0` |
| `regularizedConfluent_contiguous_mixed` | 13.3.5 | |
| `regularizedConfluent_contiguous_down` | 13.3.6 | |
| `regularizedConfluent_contiguous_shift_b_succ` | | `a𝐌(a+1,b+1) = (a−b)𝐌(a,b+1) + 𝐌` |
| `regularizedConfluent_contiguous_mixed_b_pred` | | `(b−1)𝐌 − 𝐌(b−1) + a z 𝐌(a+1,b+1) = 0` |
| `regularizedConfluent_ode_contiguous` | 13.3.13 | `(a+1)z𝐌(a+2,b+2) + (b−z)𝐌(a+1,b+1) − 𝐌 = 0` |
| `regularizedConfluent_kummer_transform` | 13.2.39 | `𝐌(a,b,z) = eᶻ 𝐌(b−a,b,−z)` |

### Design note

`DESIGN_2F1_ARGUMENT_CONTINUATION.md` sets out the definition of `₂F₁` on the cut plane
`ℂ ∖ [1,∞)`. The recommended route is the Euler integral for `Re b > 0`, `Re (c−b) > 0`,
extended to all parameters by well-founded recursion through the two hypothesis-free relations
`regularizedGaussHGFun_contiguous_shift_b` and `regularizedGaussHGFun_contiguous_c`, with the
identity principle on the (star-shaped) cut plane to lift every disk identity. No code was
written for it.

### Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3865 jobs (one new module).
- `lake env lean` passed for `AAR/Hypergeometric/Continuation.lean` and
  `AAR/Confluent/Continuation.lean` with no warnings.
- `git diff --check`: passed. `rg -n '\bsorry\b' -g '*.lean' AAR`: 700 occurrences (unchanged).
- Axiom audit (temporary `Scratch.lean`, removed): the 27 regularized theorems listed above
  depend only on `propext`, `Classical.choice`, `Quot.sound`.

### Not done / next

- `entire_regularized_parameters` (joint analyticity in `(a,b,c)`) is still admitted: Mathlib's
  uniform-limit theorem is for a complex domain of dimension one, so the joint statement needs
  derivative bounds for `hasFDerivAt_tsum_of_isPreconnected` (Cauchy estimates per variable).
- The operator identities 15.5.3–15.5.9 (`mulDerivMul`, `oneSubMulDerivMul`) still carry
  `∀ k, c ≠ −k`; regularized versions need analyticity in `c` of iterated `z`-derivatives,
  available through `iteratedDeriv_regularizedGaussHGFun` plus the Leibniz rule.
- Implement the design note (`AAR/Hypergeometric/ArgumentContinuation.lean`).
- Remaining Jacobi identities in `Differential.lean` as listed under Phase 2.

## Phase 4: `₂F₁` continued to the cut plane

Implements route D of `DESIGN_2F1_ARGUMENT_CONTINUATION.md` in the new module
`AAR/Hypergeometric/ArgumentContinuation.lean` (registered in `AAR/Hypergeometric.lean`;
about 640 lines, 52 declarations, no `sorry`). The project total remains **700** `sorry`s.

### The domain

- `cutPlane := {z | 1 - z ∈ slitPlane}` is `ℂ ∖ [1, ∞)`; `isOpen_cutPlane`,
  `starConvex_zero_cutPlane` (from Mathlib's `starConvex_one_slitPlane`),
  `isPreconnected_cutPlane`, `mem_cutPlane_of_norm_lt_one`.
- `eqOn_cutPlane_of_eventuallyEq`, `eqOn_cutPlane_of_eqOn_ball`, `eqOn_cutPlane_of_eqOn_disk`:
  the identity principle; two functions analytic on the cut plane that agree near `0` agree
  everywhere on it.
- `one_sub_mul_mem_slitPlane`: for `z` in the cut plane and `t ∈ [0,1]`, `1 - z t` is in the
  slit plane, so the Euler integrand is well defined and holomorphic in `z`.

### The Euler integral

- `eulerIntegral a b c z = (Γ(b) Γ(c-b))⁻¹ ∫₀¹ t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a) dt`.
- `eulerIntegral_eq_regularized` (`Re b > 0`, `Re (c-b) > 0`, `‖z‖ < 1`): equals `𝐅`, from
  `ordinaryHypergeometric_eq_integral`.
- `hasDerivAt_integral_eulerKernel`: differentiation under the integral sign, by Mathlib's
  `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the bound `‖t^(b-1)(1-t)^(c-b-1)‖ · C`,
  where `C` bounds the continuous factor `a t (1 - z t)^(-a-1)` on `[0,1] × closedBall z₀ (ε/2)`.
- `analyticOnNhd_eulerIntegral` (`Re b > 0`, `Re (c-b) > 0`): analytic on the cut plane.

### The continuation for all parameters

- Fuel `shiftMeasure b c = shiftB b + shiftC b c` with `shiftB b = ⌈1 - Re b⌉₊` and
  `shiftC b c = ⌈1 + shiftB b - Re (c-b)⌉₊`. The design note's order had to be corrected: a
  `b`-shift lowers `Re (c-b)`, so `c` is raised first, by enough to absorb the later `b`-shifts
  (`shiftMeasure_b_step`, `shiftC_add_one_lt`, `shiftB_add_one_lt`).
- `gaussHGCutAux n a b c z`: structural recursion on the fuel through
  `regularizedGaussHGFun_contiguous_c` and `regularizedGaussHGFun_contiguous_shift_b`, ending
  in `eulerIntegral`. `gaussHGCut a b c z := gaussHGCutAux (shiftMeasure b c) a b c z`.
- **`gaussHGCut_eq_regularized`**: `gaussHGCut a b c z = 𝐅(a,b;c;z)` for `‖z‖ < 1`, all
  parameters.
- **`analyticOnNhd_gaussHGCut`**: analytic on the cut plane, all parameters
  (`analyticAt_gaussHGCut`, `differentiableAt_gaussHGCut` are `@[fun_prop]`).
- **`gaussHGCut_unique`**: any function analytic on the cut plane agreeing with `𝐅` on the disk
  is `gaussHGCut`.
- `ordinaryHypergeometric_eq_Gamma_mul_gaussHGCut`: `₂F₁ = Γ(c) · gaussHGCut` on the disk off
  the poles; `gaussHGCut_symm`.

### Identities lifted to the cut plane (all `a b c : ℂ`, `z ∈ cutPlane`)

`deriv_gaussHGCut` (15.5.1), `iteratedDeriv_gaussHGCut` (15.5.2), the twelve contiguous
relations `gaussHGCut_contiguous_c`, `_shift_b`, `_a`, `_ab`, `_a_b_pred`, `_c_succ_deriv`,
`_a_c_succ`, `_a_succ_c_pred`, `_a_pred_c_succ`, `_a_pred_c_pred`, `_c_three`, `_diagonal`
(15.5.11–15.5.21), `gaussHGCut_euler` and `gaussHGCut_pfaff` (15.8.1, the latter with
`div_sub_one_mem_cutPlane` showing that `z ↦ z/(z-1)` preserves the cut plane). Each proof is
the disk identity plus `eqOn_cutPlane_of_eqOn_disk`, with analyticity by `fun_prop`; the
contiguous relations were generated mechanically from their disk versions.

### Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed, 3866 jobs (one new module).
- `lake env lean AAR/Hypergeometric/ArgumentContinuation.lean`: no errors, no warnings.
- `git diff --check`: passed. `rg -n '\bsorry\b' -g '*.lean' AAR`: 700 occurrences (unchanged).
- Axiom audit (temporary `Scratch.lean`, removed): the 22 main theorems of the module (the
  characterization, uniqueness, Euler-integral analyticity and all lifted identities) depend
  only on `propext`, `Classical.choice`, `Quot.sound`.

### Next

- Restate the DLMF §15.8 connection formulas and §15.4 special values on the cut plane using
  `gaussHGCut`; their proofs remain independent work (Kummer solutions or the Euler integral in
  the other variable).
- Parameter analyticity of `gaussHGCut` for fixed `z` in the cut plane (recursion plus
  dominated differentiation of the Euler integral in `b`, `c`).
- The `Γ(c)`-normalized classical function `F(a,b;c;z) = Γ(c) · gaussHGCut a b c z` can be
  introduced when DLMF statements in classical form are re-stated on the cut plane.

## Phase 5: back to `sorry` removal (700 → 674)

Twenty-six admissions replaced by proofs, concentrated where the continuation toolkit and the
Gauss contiguous relations give the most leverage. No axioms beyond the standard three; no
statement was changed. Three orthogonal-polynomial statements were moved between modules so
that their proofs could use the Jacobi recurrence (see below); their DLMF attributes travel
with them.

### Method: contiguous relations by computer algebra

For each polynomial identity whose hypergeometric form is a linear relation between three
shifted `₂F₁` values, a small sympy script (kept outside the repository) searches for
multipliers `mᵢ` with `target = Σ mᵢ · Rᵢ` over the DLMF relations 15.5.11–15.5.21 at shifted
parameters. The multipliers are read off and become one `linear_combination` call in Lean. The
relations found this way were added to `AAR/Hypergeometric/Derivatives.lean`:

| Theorem | Content |
| --- | --- |
| `contiguous_antidiagonal` | three-term relation along `(a,b) → (a+1,b-1) → (a+2,b-2)`; the Jacobi recurrence 18.9.2 |
| `contiguous_a_pred_b_pred` | `(b-a)(1-z)F(a,b) = (c-a)F(a-1,b) + (b-c)F(a,b-1)`; 18.9.6 |
| `contiguous_c_succ_shift` | 15.5.21 with the derivative eliminated by 15.5.1 |
| `contiguous_c_pair` | `c(b-a)F(a,b;c) = (c-a)bF(a,b+1;c+1) - (c-b)aF(a+1,b;c+1)`; the `α`-raising companion of 18.9.5 |
| `contiguous_gegenbauer_raise`, `_raise_sq` | 18.9.7 and 18.9.8 on the subvariety `b = 2c-1-a` |
| `contiguous_jacobi_lowering`, `_raising` | 18.9.17 and 18.9.18 |
| `ordinaryHypergeometric_symm` | the symmetry `₂F₁ a b c = ₂F₁ b a c`, now public |

The weighted-derivative identities 18.9.16 and 18.9.20 turned out to be exactly `-2` times
15.5.19 (`contiguous_diagonal`), and 18.9.24 is the Kummer relation 13.3.13.

### Theorems proved

| Theorem | File | DLMF |
| --- | --- | --- |
| `jacobi_recurrence` | AAR/OrthogonalPolynomials/Differential.lean | 18.9.2 |
| `jacobi_raise_degree_beta` | Differential.lean | 18.9.6 |
| `jacobi_raise_alpha` (new lemma) | Differential.lean | 18.9.5 companion |
| `gegenbauer_raise_parameter` | Differential.lean | 18.9.7 |
| `gegenbauer_raise_parameter_sq` | Differential.lean | 18.9.8 |
| `chebyshevV_contiguous`, `chebyshevV_mul_one_add` | Differential.lean | 18.9.11, 18.9.12 |
| `chebyshevW_contiguous` (new lemma) | Differential.lean | fourth-kind companion of 18.9.11 |
| `jacobi_lowering_derivative`, `jacobi_raising_derivative` | Differential.lean | 18.9.17, 18.9.18 |
| `jacobi_weighted_derivative` | Differential.lean | 18.9.16 |
| `gegenbauer_weighted_derivative` | Differential.lean | 18.9.20 |
| `chebyshevU_weighted_derivative` | Differential.lean | 18.9.22 (from Mathlib's `add_one_mul_T_eq_poly_in_U`) |
| `laguerre_weighted_derivative` | Differential.lean | 18.9.24 |
| `chebyshevT_hypergeometric` (moved from Explicit.lean) | Differential.lean | 18.5.11 |
| `chebyshevT_eq_jacobi` (moved) | Differential.lean | 18.7.3 |
| `chebyshevV_cos`, `chebyshevW_cos` (moved) | Differential.lean | 18.5.3, 18.5.4 |
| `chebyshevT_quadratic`, `chebyshevU_quadratic` (moved) | Differential.lean | 18.7.18, 18.7.17 |
| `chebyshevV_reflection`, `chebyshevW_reflection` (moved) | Differential.lean | 18.6.T1 |
| `jacobi_reflection`, `gegenbauer_reflection` (moved) | Differential.lean | 18.6.T1 |
| `hermitePhys_even_at_zero` | AAR/OrthogonalPolynomials/Explicit.lean | 18.6.T1 |
| `zero_second_representations` | AAR/Hypergeometric/Kummer.lean | 15.10.12 |
| `one_first_representations` | Kummer.lean | 15.10.13 |
| `one_second_representations` | Kummer.lean | 15.10.14 |

Supporting lemmas: `hasDerivAt_jacobiP`, `hasDerivAt_gegenbauer`, `jacobiP_one_eq`,
`gegenbauer_one_eq`, `jacobiP_half_half`, `gauss_chebyshev_recurrence`, `jacobiP_one_ne_zero`,
`analyticAt_jacobiP`, `analyticAt_gegenbauer` (both `@[fun_prop]`),
`jacobi_weighted_identity`, `gegenbauer_weighted_identity`, `laguerre_weighted_identity`,
`sin_ne_zero_of_cos_ne`, `sin_half_ne_zero_of_cos_ne_one`; in `Continuation.lean`
`euler_transformation_of_ne_neg_nat` and `pfaff_transformation_of_ne_neg_nat` (Euler and Pfaff
for `₂F₁` with no hypothesis on `a`, `b`). `hermitePhys_derivative` moved from
`Differential.lean` to `Classical.lean` so that `Explicit.lean` can use it.

Proof patterns: polynomial identities are proved on the disk `‖(1-x)/2‖ < 1` (or the punctured
disk when a relation carries a factor `z`) and extended in `x` by the identity principle;
denominators are cleared with auxiliary equalities `P · M = (prefactor) · ₂F₁ …` and one
`mul_right_cancel₀`; Chebyshev identities go through `cos θ` with `Complex.cos_surjective` and
Mathlib's `T_complex_cos`, `U_complex_cos`; the real weighted derivatives use
`HasDerivAt.cpow_const`, `HasDerivAt.comp_ofReal` and the complex identities.

### Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed (3866 jobs).
- `git diff --check`: passed. `rg -n '\bsorry\b' -g '*.lean' AAR`: 674 occurrences.
- Axiom audit (temporary `Scratch.lean`, removed): the 28 theorems listed above and the new
  Gauss relations depend only on `propext`, `Classical.choice`, `Quot.sound`.

### Left aside

- `confluentU_*` contiguous relations and `whittakerW_*` in `Confluent/Recurrence.lean`: the
  project's `U` and `W` are Gamma-combinations that degenerate at integer parameters, so the
  hypothesis-free statements are not expected to hold as stated (see the Phase 1 notes).
- `Elementary.lean` (15.4.x): the quadratic-transformation cases need 15.8.15–15.8.18 first.
- The Kummer connection formulas 15.10.15–15.10.28 and the remaining `Explicit.lean` sums.

## Phase 6: Kummer-side and discrete-family admissions (674 → 658)

Sixteen more admissions replaced by proofs; five statements that are false at Mathlib's
`Γ`-poles were annotated instead. No axioms beyond the standard three.

| Theorem | File | DLMF | Method |
| --- | --- | --- | --- |
| `regularizedHGFun_of_neg_nat` | AAR/Confluent/BasicProperties.lean | 13.2.5 | series tail after the vanishing coefficients, as for `₂F₁` |
| `krawtchouk_forward_difference`, `meixner_forward_difference`, `charlier_forward_difference`, `hahn_forward_difference` | AAR/OrthogonalPolynomials/Hahn.lean | 18.22.19–18.22.25 | one generic lemma `terminatingHG_forward_difference` on the finite sum |
| `charlier_difference_equation` | Hahn.lean | 18.22.T2 | forward differences plus `charlier_first_difference` (from `terminatingHG_first_difference`) |
| `meixner_difference_equation` | Hahn.lean | 18.22.T2 | `contiguous_b_neg_nat`: 15.5.11 in `b` for terminating series, valid for all `z` by the identity principle |
| `confluentM_hermite_even`, `confluentM_hermite_odd` | AAR/Confluent/Relations.lean | 13.6.16, 13.6.17 | two-step induction: the Kummer relation 13.3.1 and the Hermite two-step recurrence `hermitePhysEval_two_step` |
| `hermitePhys_even_eq_laguerre`, `hermitePhys_odd_eq_laguerre` | AAR/OrthogonalPolynomials/Explicit.lean | 18.7.19, 18.7.20 | from 13.6.16/17 and `4^n (1/2)_n n! = (2n)!` |
| `gegenbauer_even_at_zero`, `jacobi_symmetric_even_at_zero` (moved to Differential.lean) | Differential.lean | 18.6.T1 | the recurrences at `x = 0` |
| `laguerre_sum` | AAR/OrthogonalPolynomials/Series.lean | 18.18.37 | `laguerre_raise_parameter` for `Re α > 0`, then continuation in `α` (`laguerreExtended` is polynomial in `α`) |
| `krawtchouk_difference_equation` | Hahn.lean | 18.22.T2 | `contiguous_b_neg_nat'`: the terminating relation continued in `c` to the pole `c = -N` (complement of a finite set is connected) |
| `terminating_iterated_parameter_limit` | AAR/Hypergeometric/AnalyticProperties.lean | 15.2.5 | continuity in `a`, then continuity of the terminating series in `c` at `c = -m-l` (`analyticOnNhd_gauss_neg_nat_param`, now in Continuation.lean) |

New supporting lemmas: `terminatingHG_forward_difference`, `terminatingHG_first_difference`,
`poch_neg_succ_sub`, `prod_map_poch_succ`, `charlier_first_difference`, `contiguous_b_neg_nat`,
`meixner_eq_hypergeometric` (Hahn.lean); `hermitePhysEval_eq_aeval`, `hermitePhysEval_succ_succ`,
`hermitePhysEval_two_step`, `hermitePhysEval_even_mul`, `hermitePhysEval_odd_mul` (Relations.lean);
`two_pow_mul_poch_half`, `two_pow_mul_poch_three_half` (Explicit.lean); `poch_succ_succ_mul`
(Differential.lean). New imports: `Explicit.lean` imports `Confluent.Relations`,
`Hahn.lean` and `BasicProperties.lean` import `Hypergeometric.Continuation`.

### Statements found to be false as stated (annotated with `NOTE (2026-09-17)`)

- `tendsto_confluentM_div_Gamma_at_neg_nat` (13.2.5): a limit along `𝓝 (-n)` forces the value at
  `-n`, which is `M/Γ(-n) = 0` in Mathlib; true along `𝓝[≠] (-n)`.
- `confluentU_neg_nat` (13.2.7), `confluentU_neg_nat_nat_denom` (13.2.10), `confluentU_charlier`
  (13.6.20): the project's `U` is a `Γ`-combination that vanishes identically at integer
  parameters where the right-hand sides do not.
- `confluentM_lowerIncompleteGamma` (13.6.5): the first conjunct fails when `a + 1` is a pole of
  `Γ` (`a = -2`, `z = 1`); it needs `∀ k, a + 1 ≠ -k`.

### Validation

- `lake build > /tmp/AAR-build.log 2>&1`: passed (3866 jobs).
- `git diff --check`: passed. `rg -n '\bsorry\b' -g '*.lean' AAR`: 658 occurrences.
- Axiom audit (temporary `Scratch.lean`, removed): the sixteen theorems above depend only on
  `propext`, `Classical.choice`, `Quot.sound`.

### What remains near this material

- `hahn_difference_equation` needs `₃F₂` contiguous relations, which the project lacks.
- `diagonal_parameter_limit` (15.2.6) needs analyticity in `a` of the reindexed series with
  polynomial-in-`k` coefficients; `laguerre_connection` (18.18.18) and
  `monomial_laguerre_expansion` (18.18.19) need a rising-factorial Vandermonde identity.
- The Kummer-solution representations 15.10.15/15.10.16 need branch bookkeeping for
  `(1 - 1/z)^s` versus `(1-z)^s z^{-s}` in the upper half-plane; the ODE and Wronskian
  statements in `Solutions.lean` need second-derivative computations with `cpow`.
