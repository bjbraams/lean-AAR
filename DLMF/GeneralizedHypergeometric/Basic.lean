/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Generalized
public import DLMF.Hypergeometric.GeneralizedCalculus
public import DLMF.Hypergeometric.GeneralizedIntegral
public import DLMF.Hypergeometric.ParameterHolomorphy
public import DLMF.Core.Framework

/-!
# Generalized hypergeometric definitions and continuation: DLMF §§16.1–16.2

Mathlib's `regularizedHGFun` is a totalized power-series sum. It is not an analytic
continuation outside its convergence disk. Here `genRegularizedHG` uses a uniquely
normalized principal continuation for `p=q+1`; `genHG` restores the Gamma factors
when lower parameters are regular. Nonprincipal boundary values are kept separately.
For `p>q+1` nonterminating series no analytic value is assigned by this API; contour
values are acquired separately in `Integrals`. `genFiniteHG` handles terminating
expressions whose lower parameters may be exceptional after the final retained term.

Mathlib supplies convergent-series radii and holomorphy. Existing local generalized
calculus supplies differentiation and contiguity; no duplicate proof is introduced.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real ENNReal
noncomputable section
namespace DLMF.Hypergeometric

/-- Vector parameters represented as a multiset; no order-dependent normalization. -/
def genParams {p : ℕ} (a : Fin p → ℂ) : Multiset ℂ := (List.ofFn a : Multiset ℂ)

/-- Product of rising factorials in a parameter multiset (DLMF16.1). -/
def genPoch (a : Multiset ℂ) (n : ℕ) : ℂ := (a.map fun x => poch x n).prod

/-- Product of parameter Gamma factors. -/
def genGamma (a : Multiset ℂ) : ℂ := (a.map Complex.Gamma).prod

/-- The ordinary generalized hypergeometric coefficient (16.2.1). -/
@[dlmf 16.2.E1]
def genCoeff (a b : Multiset ℂ) (n : ℕ) : ℂ :=
  genPoch a n / (genPoch b n * n.factorial)

/-- Lower parameters avoid the nonpositive integers, unless a formula explicitly overrides this. -/
def genDenRegular (b : Multiset ℂ) : Prop := ∀ x ∈ b, ∀ n : ℕ, x ≠ -n

/-- At least one upper parameter terminates the series. -/
def genTerminates (a : Multiset ℂ) : Prop := ∃ x ∈ a, ∃ n : ℕ, x = -n

/-- The formal scalar series, meaningful even where the analytic series diverges. -/
def genFormalSeries (a b : Multiset ℂ) : PowerSeries ℂ := PowerSeries.mk (genCoeff a b)

/-- A finite retained sum; denominator exceptions beyond its degree are permitted. -/
def genFiniteHG (m : ℕ) (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑ n ∈ range (m + 1), genCoeff a b n * z ^ n

/-- Natural-order hypergeometric series convergence; unlike `HasSum`, permits conditional convergence. -/
def genSeriesConvergesTo (a b : Multiset ℂ) (z v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => ∑ n ∈ range N, genCoeff a b n * z ^ n) atTop (𝓝 v)

/-- Absolute convergence of the ordinary coefficient series. -/
def genSeriesAbsolutelyConverges (a b : Multiset ℂ) (z : ℂ) : Prop :=
  Summable (fun n : ℕ => ‖genCoeff a b n * z ^ n‖)

/-- A normalized regularized continuation for `p=q+1`; its existence is acquired explicitly. -/
structure GenPrincipalContinuation (a b : Multiset ℂ) where
  /-- Principal values, with an upper-side cut convention. -/
  value : ℂ → ℂ
  /-- Analytic continuation on the plane cut from one to positive infinity. -/
  analytic : AnalyticOnNhd ℂ value cutPlane
  /-- The original germ on the open unit disk. -/
  germ : ∀ z, ‖z‖ < 1 → value z = Complex.regularizedHGFun a b z
  /-- Upper cut values away from the singular endpoint. -/
  upper_boundary : ∀ x : ℝ, 1 < x →
    Tendsto value (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (value x))
  /-- At the endpoint only the totalized series value is retained; convergence is separate. -/
  one : value 1 = Complex.regularizedHGFun a b 1

/-- Existence of principal continuation for all regularized parameters, including Gamma zeros. -/
theorem genPrincipalContinuation_exists (a b : Multiset ℂ) (h : a.card = b.card + 1) :
    Nonempty (GenPrincipalContinuation a b) := by
  sorry

/-- Uniqueness of the normalized continuation and its declared cut values. -/
theorem genPrincipalContinuation_unique (a b : Multiset ℂ)
    (F G : GenPrincipalContinuation a b) : F.value = G.value := by
  sorry

/-- Regularized principal generalized hypergeometric function.
For `p>q+1` this expression retains only the totalized series; use Barnes values instead. -/
@[dlmf 16.2.E5]
def genRegularizedHG (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  if h : a.card = b.card + 1 then
    (Classical.choice (genPrincipalContinuation_exists a b h)).value z
  else Complex.regularizedHGFun a b z

/-- Ordinary principal generalized hypergeometric values, valid for regular lower parameters. -/
def genHG (a b : Multiset ℂ) (z : ℂ) : ℂ := genGamma b * genRegularizedHG a b z

/-- Lower-side principal cut values; conjugate the parameters as well as the variable. -/
def genHGLower (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  star (genHG (a.map star) (b.map star) (star z))

/-- The unit-circle excess parameter (16.2.2). -/
@[dlmf 16.2.E2]
def genExcess (a b : Multiset ℂ) : ℂ := b.sum - a.sum

/-- Shifting every parameter by the same complex number. -/
def genShift (a : Multiset ℂ) (t : ℂ) : Multiset ℂ := a.map (· + t)

/-- The regularized principal germ agrees with the native power-series germ. -/
theorem genRegularizedHG_eq_series {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    genRegularizedHG a b z = Complex.regularizedHGFun a b z := by
  sorry

/-- Ordinary and regularized coefficients differ by the fixed Gamma product. -/
@[dlmf 16.2.E5]
theorem genCoeff_eq_gamma_mul_regularized {a b : Multiset ℂ} (hb : genDenRegular b)
    (n : ℕ) : genCoeff a b n = genGamma b * Complex.regularizedHGFunCoeff a b n := by
  sorry

/-- The defining series converges to the principal value in its open disk. -/
@[dlmf 16.2.E1]
theorem genHG_hasSum_disk {a b : Multiset ℂ} (h : a.card ≤ b.card + 1)
    (hb : genDenRegular b) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => genCoeff a b n * z ^ n) (genHG a b z) := by
  sorry

/-- Terminating series are the retained polynomial, with the minimum terminating degree. -/
theorem genHG_eq_finite {a b : Multiset ℂ} (hb : genDenRegular b)
    {m : ℕ} (hm : (-m : ℂ) ∈ a) (z : ℂ) :
    genHG a b z = genFiniteHG m a b z := by
  sorry

/-- The terminating inversion formula, with all retained denominator factors nonzero. -/
@[dlmf 16.2.E3]
theorem genFiniteHG_inversion (a b : Multiset ℂ) (m : ℕ) {z : ℂ} (hz : z ≠ 0)
    (ha : genPoch a m ≠ 0) (hb : genPoch b m ≠ 0) :
    genFiniteHG m ((-m : ℂ) ::ₘ a) b z =
      genPoch a m * (-z) ^ m / genPoch b m *
        genFiniteHG m ((-m : ℂ) ::ₘ (b.map fun x => 1 - m - x))
          (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card) / z) := by
  sorry

/-- Every partial sum is a terminating inverted hypergeometric polynomial (16.2.4). -/
@[dlmf 16.2.E4]
theorem genFiniteHG_partial_sum_inversion (a b : Multiset ℂ) (m : ℕ)
    {z : ℂ} (hz : z ≠ 0) (ha : genPoch a m ≠ 0) (hb : genPoch b m ≠ 0) :
    genFiniteHG m a b z = genPoch a m * z ^ m / (genPoch b m * m.factorial) *
      genFiniteHG m ((-m : ℂ) ::ₘ 1 ::ₘ (b.map fun x => 1 - m - x))
        (a.map fun x => 1 - m - x) ((-1 : ℂ) ^ (a.card + b.card + 1) / z) := by
  sorry

/-- Rising factorial at an integer index; negative indices use the reciprocal continuation.
At singular parameters this expression is totalized, so analytic formulas state exclusions. -/
def genIntPoch (a : ℂ) (n : ℤ) : ℂ :=
  if 0 ≤ n then poch a n.toNat else (poch (a + n) (-n).toNat)⁻¹

/-- Formal bilateral hypergeometric coefficient, with no factorial factor (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralCoeff (a b : Multiset ℂ) (n : ℤ) : ℂ :=
  (a.map fun x => genIntPoch x n).prod / (b.map fun x => genIntPoch x n).prod

/-- Totalized bilateral series. Outside an explicitly proved convergence regime this is
only a formal-series interface, not an analytically continued function (16.4.16). -/
@[dlmf 16.4.E16]
def genBilateralHG (a b : Multiset ℂ) (z : ℂ) : ℂ :=
  ∑' n : ℤ, genBilateralCoeff a b n * z ^ n

/-- Mellin–Barnes kernel on the logarithm sheet `w=Log(-z)`. -/
def genBarnesKernelLog (a b : Multiset ℂ) (w s : ℂ) : ℂ :=
  genGamma (genShift a s) / genGamma (genShift b s) * Gamma (-s) * Complex.exp (s * w)

/-- A convergent contour-defined ordinary pFq value, separate from the divergent formal
series. Both contour tails converge separately; the log sheet of `-z` is explicit. -/
def genHasBarnesValueLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w v : ℂ) : Prop :=
  DLMF.HasIntegralWholeLine (fun t => deriv L t * genBarnesKernelLog a b w (L t))
    (2 * Real.pi * I * genGamma a / genGamma b * v)

/-- Totalized value of a Barnes contour. Every mathematical use asserts its separate
convergence with `genHasBarnesValueLog` and excludes poles in the parameter prefactor. -/
def genBarnesHGLog (a b : Multiset ℂ) (L : ℝ → ℂ) (w : ℂ) : ℂ :=
  genGamma b / (2 * Real.pi * I * genGamma a) *
    limUnder atTop (fun T : ℝ =>
      ∫ t in (-T)..T, deriv L t * genBarnesKernelLog a b w (L t))

end DLMF.Hypergeometric
