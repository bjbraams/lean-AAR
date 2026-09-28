# Statement audit of admitted results — 27 September 2026

This audit checks whether admitted (`sorry`) statements are true as formalized, before proof
work begins. It covers `AAR/OrthogonalPolynomials` (233 admissions), `AAR/Confluent`
(206 admissions), `AAR/Hypergeometric` (102 admissions), `AAR/Gamma` (76 admissions) and
the small areas Bessel, Selberg, SphericalHarmonics, QSeries, Partitions and Bailey
(29 admissions), following the review in `REVIEW_2026-09-27.md`. Every admitted statement in
the library has now been audited.

Method: every statement was read against the project definitions and the DLMF/AAR source.
Formulas that are not immediate were checked numerically with mpmath at 20–400 digits, using
explicit finite sums for polynomial families and principal-branch evaluation for multivalued
functions, so that the numerical model matches the Lean definitions. Where a statement uses a
Lean totalization (`x / 0 = 0`, `Gamma` at poles, `0 ^ w = 0` for `w ≠ 0`, the integral of a
non-integrable function, the `tsum` of a divergent series), the Lean value was modelled
directly.

## Orthogonal polynomials: no false statements found

All 233 admitted statements were checked. Numerical checks covered orthogonality norms and
transforms (Integrals), generating functions and linearization (Series), all inequalities and
discriminants (BoundsZeros), the associated, exceptional, Pollaczek and Morse families,
the Hahn, Wilson, `q`-families and unit-circle statements, the connection coefficients, and the
Vietoris and Gegenbauer Cesàro positivity results.

Minor observations, not defects:

- `gegenbauer_weighted_generating_function` proves the `(n + 2λ)/(2λ)` variant, whose sum is
  `(1 - xz)/R^{2λ+2}`. It is true; DLMF 18.12.5 prints the `(n + λ)/λ` variant.
- Brafman's generating function and DLMF 18.12.3 are stated where both `₂F₁` arguments lie in
  the unit disk; correctness there rests on that region being connected to `z = 0`.

## Hypergeometric: no false statements found

All 102 admitted statements were checked. Numerically verified:

- all 21 elementary closed forms and special values of DLMF 15.4, including the two
  unit-circle evaluations with their absolute-convergence conditions;
- the connection formulas 15.8.3–5 and 15.8.9–11, the terminating transformations 15.8.6–7,
  the quadratic and cubic transformations 15.8.13–33 and the quadratic connection formulas
  15.8.24–28, each at about 60–120 random points of its hypothesis region;
- the solutions at `0`, `1`, `∞`, their Wronskians, the three logarithmic second solutions
  and the connection formulas 15.10.17–28 among Kummer's solutions (which correctly restrict
  to the upper half-plane);
- Whipple's `₇F₆`, Dixon's and Kummer's sums, Dougall's bilateral sum, the Gauss continued
  fractions, the integral representations 15.6, the Riemann `P`-function solution, and the
  gauge-shift and Möbius-covariance operator identities of 15.11;
- the large-parameter expansion 15.12.5, whose residual scales as `λ^{-2}`.

Checked by reading only: 15.12.2–4, joint analyticity of the regularized function in its
parameters (Mathlib's regularization is by `1 / Γ(c + n)`), the convergence and divergence
statements on the unit circle, and the diagonal parameter limit 15.2.6 (verified from the
coefficient identity `(a)_k / (a - l)_k = (a - l + k)_l / (a - l)_l`).

Unlike Confluent, this area consistently states the convergence disks of every series and
the half-plane restrictions for the `e^{±πi}` factors.

## Small areas: two statements false as stated, now repaired

- `watson_transformation` was false: with its balancing hypothesis `a²q = bcdef` it used the
  argument `aq²/(bcdef) = q/a` and a nonstandard `₄φ₃`, and the two sides differ numerically
  (`1.8 - 1.6i` against `-162 - 6i`). It is restated as the classical terminating
  transformation (`f = q⁻ⁿ`, argument `a²q^{n+2}/(bcde)`, balanced `₄φ₃` at argument `q`),
  with nonvanishing hypotheses for the denominators; this form was checked numerically.
- `bailey_lemma` had no hypotheses on its parameters. At `rho1 = 0` the totalized quotients
  do not give a Bailey pair (the residual is `0.24` in a test); the lemma now assumes
  `rho1, rho2 ≠ 0` and nonvanishing `q`-Pochhammer denominators.

The remaining 27 statements hold. Numerically verified: Nicholson's integral, the Bessel
generating function, Gegenbauer's Bessel addition theorem, Sonine's integral, the monotonicity
of the first Bessel zero, the Jacobi discriminant, the corrected nearly poised `₃F₂`, Siegel's
inequality, Selberg's and Aomoto's integrals for `n = 2`, the finite-field Selberg evaluation
over `F₇`, `F₁₁`, `F₁₃` for `n ≤ 2`, the Gegenbauer addition theorem, the triple product,
Ramanujan's `₁ψ₁` and both Rogers–Ramanujan identities. Checked by reading: Hasse–Davenport,
the spherical-harmonic statements (normalizations of `sphericalHarmonicInner` and
`poissonKernelBall` match), `SU(2) → SO(3)`, the product for `jacobiTheta`, the Ramanujan
congruences and the infinitude of Bessel zeros.

## Gamma: eight statements false as stated, now repaired

The statements repaired after the original review (`polygamma_multiplication`,
`qGamma_mono_right`, `Gamma_ratio_norm_le`, `digamma_half_diff`, the Stirling coefficient
recurrences) were rechecked and are correct; `stirlingRatioG 3 0` gives `1, 3, 2, 0`, as the
exact ratio `t³ + 3t² + 2t` requires. The new defects:

- `barnesG_add_one` was false at `z = 0` (`G(1) = 1`, while the totalized `Γ(0) = 0` makes
  the right side `0`). It now assumes `z ≠ 0`.
- `logGamma_continued_fraction_limit` was false: `logGammaContFractCoeff` sets all partial
  numerators after the seven tabulated ones to zero, so the convergents stabilize at a
  truncation that differs from Binet's function (by `1.5e-7` at `x = 3/2`). The statement was
  removed; stating the limit requires the full coefficient sequence.
- `Gamma_cos`, `Gamma_sin`, `Gamma_cos_pow`, `Gamma_sin_pow` (DLMF 5.9.6–9) converge only
  conditionally, so Lean's integral over `(0, ∞)` is `0`. They are restated as limits of
  integrals over `(0, R)`.
- `Gamma_laplace_power` (5.9.1) allowed complex `μ`; for non-real `μ` the integral diverges.
  It now assumes `μ.im = 0`, matching DLMF's `μ > 0`.
- `sum_alternating_trigamma` (5.16.1) is only conditionally convergent, so the `tsum` over `ℝ`
  is `0`. It is restated with ordered partial sums.

The remaining 68 statements hold. Numerically verified: the Stirling-type expansions,
the inequalities of 5.6 (5.6.7 is an equality at `x = 1/2`), the series of 5.7 including the
principal-branch `log Γ(1 + z)` on the unit disk, Gauss's digamma theorem, the polygamma
values and multiplication formula, the monotonicity of `Γ_q` in `q` on both ranges, the
absolutely convergent integral representations of 5.9, the Beta integrals of 5.12, the
Mellin–Barnes integrals of 5.13, and the Mehta and Dyson integrals for `n = 2`.
Checked by reading only: the Barnes G asymptotics and Glaisher–Kinkelin constant, the
Dirichlet and Selberg–Laguerre integrals, and 5.8.

## Confluent: about 70 statements false or ill-posed as stated

The DLMF formulas are almost always correct. The failures come from transcription into Lean.

1. **Branch transcription (12).** DLMF's `U(a,b,z e^{±πi})` denotes analytic continuation;
   in Lean `exp (±π * I) * z = -z` is evaluated on the principal branch.
   - False everywhere: `confluentM_eq_confluentU_jump`, `confluentU_jump`, `whittakerM_jump`,
     `whittakerW_jump` (DLMF 13.2.43–44, 13.14.34–35).
   - True only on one half-plane per sign: `confluentM_eq_confluentU_connection`,
     `wronskian_regularizedHGFun_kummerU`, `wronskian_confluentU_kummerU`,
     `wronskian_whittakerM_W_neg`, `wronskian_whittakerW_pair`,
     `whittakerM_eq_whittakerW_connection`.
   - Ill-posed at `z > 0` (second function not differentiable):
     `wronskian_confluentU_kummer_neg`, `wronskian_confluentU_kummer_pos`.
2. **Functions of `z²` equated with functions of `z` (7), false for `Re z < 0`:**
   `confluentU_erfcFn`, `confluentU_hermite` (even `n`), `whittakerM_errorFn`,
   `whittakerW_erfcFn`, `whittakerM_hermite_even`, `whittakerM_hermite_odd`,
   `whittakerW_hermite`.
3. **Missing DLMF hypotheses.**
   - `isBigO_confluentU_at_zero_re_ge_two`, `_re_one_to_two`, `_re_nonpos` need `b ≠ 2`,
     `b ≠ 1`, `b ≠ 0` respectively (a `log z` term breaks the bound).
   - Addition theorems DLMF 13.13.2, .6, .7, .8, .10, .12 and 13.26.1, .2, .4, .5, .7, .8,
     .10, .11 need `|y| < |x|`; 13.13.7 and 13.13.10 also lack slit-plane hypotheses. All
     24 formulas are numerically correct inside `|y| < |x|`.
4. **Derivatives without a slit-plane hypothesis (4):** `deriv_confluentU`,
   `iteratedDeriv_confluentU`, `iteratedDeriv_exp_neg_confluentU`, `deriv_confluentU_shift`.
   On the cut `U` is not complex-differentiable and Lean's `deriv` is `0`.
5. **Integrals (10).** `gauss_regularizedHGFun` and `laplace_confluentU` need `0 < Re z`.
   The Bessel-kernel integrals 13.10.13–15 and 13.23.9–11 diverge for non-real `x`, and are
   only conditionally convergent near the edge of the stated parameter ranges.
   `cosine_regularizedHGFun` (for `0 < a ≤ 1/2`) and `cosine_whittakerM` (for
   `-1/2 < κ + μ ≤ 0`) are only conditionally convergent, so the Lean integral is `0`.
6. **Totalization edge cases (about 14):** `whittakerM_lowerIncompleteGamma` at `μ = 0`;
   `whittakerM_product` at `2μ ∈ {1, 2, …}`; `confluentU_integral_besselK` and
   `whittakerW_integral_besselK` at `z = 0`; the Bessel series at `a = 1/2`,
   `b - a = 1/2`, `κ + μ = 0`, `b = 2a`; zero counts with `b` a nonpositive integer;
   `confluentM_large_zeros` when `a` or `b - a` is a nonpositive integer;
   `confluentM_zeros_in_a` at `z = 0`.
7. **Hypothesis on an unused variable (4):** `confluentM_besselI`, `confluentU_besselK`,
   `confluentU_zeros_in_a`, `confluentU_large_a_b` assume `w ∈ slitPlane` for a `w` that
   does not occur; `z` is unconstrained.
8. **Plainly false:** `confluentU_negZeros` (DLMF 13.9.14 as formalized). On the negative
   axis the principal `U` is complex and bounded away from zero in tested cases where the
   statement claims two to four zeros.

About 135 Confluent statements were confirmed, many numerically (all derivative formulas of
13.3.24–28 and 13.15.15–26, the contiguous relations, the continued fractions, the 13.7.4
error bound, the zero counts 13.9.5–6). The uniform and transition expansions 13.8.2,
13.8.6–7, 13.8.17–18, the Barnes integrals and the parabolic zero-free region were checked by
reading only.

## Repairs made on 27 September 2026

All statements in groups 1–8 were repaired; none was used by another declaration. The
repaired statements remain admitted. The admission count fell from 646 to 645 because
`confluentU_negZeros` was removed.

1. Branch transcription: the sign-dependent connection formulas and Wronskians now take
   `hsign : if sign then z.arg ≤ 0 else 0 < z.arg` (strict `<` for Wronskians, which also keeps
   `-z` off the cut). The four jump relations are restated on the logarithmic plane with
   `confluentUOnLog` / `whittakerWOnLog` at `log z ± π * I`, for noninteger `b` or `2μ`;
   these restatements were checked numerically in all quadrants. The two numerically
   satisfactory pair statements and 13.2.37 take `-z ∈ slitPlane`.
2. The seven `z²`-argument identities take `0 < z.re`.
3. `b ≠ 2`, `b ≠ 1`, `b ≠ 0` added to the three small-`z` estimates; `‖y‖ < ‖x‖` added to the
   fourteen addition theorems, with slit-plane hypotheses for 13.13.7 and 13.13.10.
4. The four derivative statements take `z ∈ slitPlane`; the two function-level iterated
   derivative identities are now pointwise.
5. `0 < z.re` added to 13.10.6 and 13.10.7. The Bessel-kernel integrals take real `x`
   (`x.im = 0`) and parameter bounds giving absolute integrability (13.10.13 also `0 < Re b`;
   13.23.11 gains an upper bound on `ν`). The cosine transforms take `1/2 < a` and
   `0 < κ + μ`.
6. Edge exclusions: `μ ≠ 0` (13.18.4); `2μ ∉ ℤ` (13.25.1); `z ≠ 0` (13.4.7, 13.16.8);
   `a ≠ 1/2`, `b - a ≠ 1/2`, `κ + μ ≠ 0`, `b - 2a ≠ 0` (Bessel series); `0 < b` or
   `b ∉ -ℕ` in the zero counts; `a, b - a, b ∉ -ℕ` (13.9.9); `z ≠ 0`, `b ∉ -ℕ` (13.9.10).
7. The unused hypotheses on `w` are replaced by `z ∈ slitPlane`.
8. `confluentU_negZeros` (13.9.14) was removed, with a comment in `Zeros.lean`.
