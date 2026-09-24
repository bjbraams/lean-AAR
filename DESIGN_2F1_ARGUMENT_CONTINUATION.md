# Design note: continuing `₂F₁` in the argument beyond the unit disk

Date: 2026-09-17. Status: implemented the same day as `AAR/Hypergeometric/ArgumentContinuation.lean` (route D below); see the Phase 4 section of `PROOF_PROGRESS_2026-09-17.md`.

## Where we stand

Parameter continuation is done. `AAR/Hypergeometric/Continuation.lean` proves that Mathlib's
regularized function `𝐅(a,b;c;z) = regularizedGaussHGFun a b c z` is entire along any entire
curve in `(a, b, c)` for fixed `‖z‖ < 1`, and uses this to prove every Gauss contiguous
relation, the derivative formulas, and the Euler and Pfaff transformations without any
hypothesis on the parameters. `AAR/Confluent/Continuation.lean` does the same for Kummer's
`𝐌(a,b,z) = regularizedHGFun {a} {b} z`, for all `z`.

What is still missing is continuation in `z`: `𝐅` and `₂F₁` are defined by the series and are
only meaningful for `‖z‖ < 1` (plus the terminating case). DLMF §15.2(i) defines `F(a,b;c;z)`
on the cut plane `ℂ ∖ [1, ∞)` as the analytic continuation of the series; all of §15.8
(connection formulas, quadratic transformations) and most of §15.4, §15.10 and §15.12 live
on that domain.

## Requirements for a definition `gaussHGSlit a b c z`

1. Defined for all parameters `a b c : ℂ` and all `z` with `1 - z ∈ slitPlane`
   (i.e. `z ∉ [1, ∞)`), with no side conditions in the definition.
2. Equal to `𝐅(a,b;c;z)` for `‖z‖ < 1` (the regularized normalization is the right one;
   `₂F₁ = Γ(c) · 𝐅` off the poles of `Γ(c)` by `regularizedGaussHGFun_eq_div_Gamma`).
3. `AnalyticOnNhd ℂ (gaussHGSlit a b c) {z | 1 - z ∈ slitPlane}`, and entire in the
   parameters for fixed `z` in the cut plane.
4. Every identity proved on the disk transfers automatically: the cut plane is open and
   connected (`starConvex_one_slitPlane` translated by `z ↦ 1 - z` gives star-shapedness,
   hence `IsPreconnected`), so `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` extends
   any identity between analytic expressions from the disk to the whole cut plane.

Requirement 4 is the payoff: the contiguous relations, derivative formulas and Euler/Pfaff
transformations already proved for `𝐅` on the disk become theorems on the cut plane with a
five-line proof each, and the same holds for identities still to be proved.

## Options considered

### A. Abstract analytic continuation (`Classical.choose` of an existence theorem)
Rejected. Mathlib has no monodromy theorem, so existence of the continuation is itself the
hard part; and AGENTS.md rules out choice-based definitions.

### B. Barnes (Mellin–Barnes) integral
Valid on the whole cut plane and for all parameters after regularization, but it requires a
contour integral along a vertical line with Gamma-function asymptotics
(`Complex.Gamma` growth estimates in the imaginary direction are not in Mathlib) and
residue calculus to identify it with the series. Too heavy as a first definition.

### C. Patchwork of series (Pfaff for `Re z < 1/2`, `1 - z` connection for the rest)
The `1 - z` connection formula 15.8.4 degenerates when `c - a - b ∈ ℤ` (logarithmic cases
15.8.10–15.8.11 with digamma terms). A definition with that case split is unusable.

### D. Euler integral plus contiguous shifts (recommended)
The Euler integral
`𝐅(a,b;c;z) = (Γ(b) Γ(c-b))⁻¹ ∫₀¹ t^(b-1) (1-t)^(c-b-1) (1 - z t)^(-a) dt`
(`ordinaryHypergeometric_eq_integral` in `EulerIntegral.lean`, currently for `‖z‖ < 1`) is
an analytic function of `z` on the whole cut plane whenever `Re b > 0` and `Re (c - b) > 0`,
for every `a`. The parameter restriction is removed with the hypothesis-free contiguous
relations proved today:

* `regularizedGaussHGFun_contiguous_shift_b`:
  `𝐅(a,b;c) = 𝐅(a,b+1;c) − a z 𝐅(a+1,b+1;c+1)` raises `Re b` by one;
* `regularizedGaussHGFun_contiguous_c`:
  `𝐅(a,b;c) = (c−a) 𝐅(a,b;c+1) + a 𝐅(a+1,b;c+1)` raises `Re (c − b)` by one.

Definition sketch. Note that a `b`-shift lowers `Re (c − b)`, so the two shifts must be
ordered: first raise `c` until `Re (c − b) ≥ 1 + (number of b-shifts still needed)`, then
raise `b`. With `nb = ⌈1 − Re b⌉₊` and `nc = ⌈1 + nb − Re (c − b)⌉₊` the fuel `nb + nc`
decreases in every recursive call (implemented as `shiftB`, `shiftC`, `shiftMeasure`, with a
structural recursion on the fuel rather than well-founded recursion):

```
gaussHGCut a b c z :=
  if 0 < nc then (c − a) · gaussHGCut a b (c+1) z + a · gaussHGCut (a+1) b (c+1) z
  else if 0 < nb then gaussHGCut a (b+1) c z − a z · gaussHGCut (a+1) (b+1) (c+1) z
  else eulerIntegral a b c z
```

Proof obligations, in order:

1. `eulerIntegral_analyticOn`: analyticity in `z` on the cut plane for `Re b > 0`,
   `Re (c-b) > 0`. Tool: `hasDerivAt_integral_of_dominated_loc_of_deriv_le` (differentiation
   under the integral sign), with the bound `‖(1 - z t)^(-a-1)‖ ≤ C` on compact subsets, or
   directly `DifferentiableOn.analyticOnNhd` from `differentiableOn_integral`-style lemmas.
   This is the only genuinely analytic step; about 150 lines.
2. `eulerIntegral_eq_regularized`: equality with `𝐅` on the disk. Direct from
   `ordinaryHypergeometric_eq_integral` and `regularizedGaussHGFun_eq_div_Gamma`
   (`Re c > 0` there, so `Γ(c) ≠ 0`).
3. `gaussHGSlit_eq_regularized`: for `‖z‖ < 1`, `gaussHGSlit a b c z = 𝐅(a,b;c;z)`. By
   induction on `N`, using items 2 and the two regularized contiguous relations. The
   relations are exactly the recursion branches, so each step is `rw` plus `ring`.
4. `analyticOnNhd_gaussHGSlit`: by the same induction, since each branch is a polynomial
   combination of analytic functions.
5. `gaussHGSlit` is independent of the recursion path: not needed as a separate theorem,
   because 3 and 4 together with the identity theorem show any two analytic extensions
   agree.
6. Parameter analyticity of `gaussHGSlit` for fixed `z` in the cut plane: by the same
   recursion, from parameter analyticity of the Euler integral (dominated convergence in the
   parameters) or, cheaper, from Hartogs-free arguments per branch. Can be postponed; not
   needed for requirement 4.

Once 3 and 4 exist, a single helper

```
theorem eq_on_slit_of_eq_on_disk {f g : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f cutPlane) (hg : AnalyticOnNhd ℂ g cutPlane)
    (h : ∀ z, ‖z‖ < 1 → f z = g z) : EqOn f g cutPlane
```

lifts every disk identity. The classical `₂F₁` on the cut plane is then
`Γ(c) · gaussHGSlit a b c z`, and DLMF statements can be written in either form.

### What D does not give for free

The connection formulas 15.8.2–15.8.5 (behaviour at `z = ∞` and `z = 1`) are not
consequences of continuation; they need either Kummer's solutions of the hypergeometric
equation with a Wronskian argument (`AAR/Hypergeometric/Solutions.lean`, still mostly
admitted) or the Euler integral evaluated in the other variable. They remain independent
work, but with D they can at least be stated on their natural domain.

## Recommendation

Implement D in a new module `AAR/Hypergeometric/ArgumentContinuation.lean`, in the order
1 → 2 → 3 → 4, then add the lifting helper and re-state the regularized contiguous relations,
derivative formulas and Euler/Pfaff transformations on the cut plane. The confluent function
does not need this step: `𝐌(a,b,z)` is already entire in `z`.
