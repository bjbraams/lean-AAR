/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LogExpBasic
public import DLMF.Gamma.Asymptotics
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Lambert W and Wright omega: DLMF §4.13

Neither Mathlib nor pinned TauCeti has Lambert W. A branch family is characterized
by the inverse equation, analytic continuation, branch indexing at `1`, and upper
boundary limits. Its existence is an explicit admitted acquisition theorem, not an
axiom or an unspecified opaque function. Lower cut values are separate. Nonprincipal
branches at zero are totalized to zero, outside all assertions for those branches.
The Wright omega equation uses DLMF's closed logarithm at its cut values.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- The principal Lambert branch domain with its square-root cut removed. -/
def lambertPrincipalDomain : Set ℂ :=
  {z | -Real.exp (-1) < z.re ∨ z.im ≠ 0}

/-- Analytic and boundary normalization determining every integer Lambert branch. -/
structure LambertBranchFamily where
  /-- Upper-side branch values. -/
  value : ℤ → ℂ → ℂ
  /-- The defining inverse equation. -/
  equation : ∀ k z, z ≠ 0 ∨ k = 0 → value k z * Complex.exp (value k z) = z
  /-- Canonical totalization outside the nonprincipal branch domains. -/
  zero : ∀ k, value k 0 = 0
  /-- Principal-branch holomorphy, including the origin. -/
  principal_analytic : AnalyticOnNhd ℂ (value 0) lambertPrincipalDomain
  /-- Holomorphy of all other branches on the ordinary slit plane. -/
  other_analytic : ∀ k, k ≠ 0 → AnalyticOnNhd ℂ (value k) Complex.slitPlane
  /-- The principal branch is the nonnegative inverse at the positive basepoint. -/
  principal_basepoint : (value 0 1).im = 0 ∧ 0 ≤ (value 0 1).re
  /-- Positive branch indices at the positive basepoint. -/
  positive_basepoint : ∀ k : ℤ, 0 < k →
    (2 * k - 1 : ℝ) * Real.pi < (value k 1).im ∧ (value k 1).im < 2 * k * Real.pi
  /-- Negative branch indices at the positive basepoint. -/
  negative_basepoint : ∀ k : ℤ, k < 0 →
    2 * k * Real.pi < (value k 1).im ∧ (value k 1).im < (2 * k + 1 : ℝ) * Real.pi
  /-- Values on the cut are limits from its upper side. -/
  upper_boundary : ∀ k (x : ℝ), x < 0 →
    Tendsto (value k) (𝓝[{z : ℂ | 0 < z.im}] (x : ℂ)) (𝓝 (value k x))

/-- Existence of the normalized integer branch family (4.13, defining prose). -/
theorem exists_lambertBranchFamily : Nonempty LambertBranchFamily := by
  sorry

/-- Uniqueness of the normalized branches, including the declared totalization. -/
theorem lambertBranchFamily_unique (F G : LambertBranchFamily) : F.value = G.value := by
  sorry

/-- The Lambert W branch with integer index, using the upper-side convention on cuts. -/
def lambertW (k : ℤ) (z : ℂ) : ℂ :=
  (Classical.choice exists_lambertBranchFamily).value k z

/-- Lower-side cut values; away from the cut this agrees with analytic continuation. -/
def lambertWLower (k : ℤ) (z : ℂ) : ℂ := star (lambertW (-k) (star z))

/-- Wright omega with its unwinding-number branch convention. -/
def wrightOmega (z : ℂ) : ℂ :=
  lambertW ⌈(z.im - Real.pi) / (2 * Real.pi)⌉ (Complex.exp z)

/-- The tree T-function on the principal branch. -/
def treeT (z : ℂ) : ℂ := -lambertW 0 (-z)

/-- The Lambert inverse equation on every valid branch. -/
@[dlmf 4.13.E1]
theorem lambertW_equation (k : ℤ) (z : ℂ) (hz : z ≠ 0 ∨ k = 0) :
    lambertW k z * Complex.exp (lambertW k z) = z :=
  (Classical.choice exists_lambertBranchFamily).equation k z hz

/-- The logarithmic sheet used in the branch asymptotics. -/
def lambertXi (k : ℤ) (z : ℂ) : ℂ := Complex.log z + 2 * Real.pi * I * k

/-- Derivative polynomials, given by their full recurrence (4.13.4_2). -/
@[dlmf 4.13.E4_2]
def lambertDerivPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | n + 1 => (1 + Polynomial.X) * (lambertDerivPolynomial n).derivative +
      (1 - Polynomial.C (n + 1 : ℂ) * (Polynomial.X + 3)) * lambertDerivPolynomial n

/-- Coefficients of the logarithmic square-root parameter at the branch point. -/
def lambertC (n : ℕ) : ℝ :=
  if h0 : n = 0 then 1 else if h1 : n = 1 then 1 else
    lambertC (n - 1) / (n + 1) - 1 / 2 *
      ∑ k : Fin (n - 2), lambertC (k.val + 2) * lambertC (n - 1 - k.val)
termination_by n
decreasing_by all_goals omega

/-- Coefficients in the principal Puiseux parameter at the branch point. -/
def lambertD (m : ℕ) : ℝ :=
  if h0 : m = 0 then -1 else if h1 : m = 1 then Real.sqrt 2 else
    (-2 * lambertD (m - 1) + (m - 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 1) * lambertD (m - 2 - k.val)) -
      (m + 1 : ℝ) / 2 *
      (∑ k : Fin (m - 2), lambertD (k.val + 2) * lambertD (m - 1 - k.val))) /
      ((m + 1 : ℝ) * Real.sqrt 2)
termination_by m
decreasing_by all_goals omega

/-- The normalized removable quotient `W₀(z)/z` at zero. -/
def lambertWOver (z : ℂ) : ℂ := if z = 0 then 1 else lambertW 0 z / z

/-- The exact nth outer term of the large-argument Lambert expansion. -/
def lambertAsymptoticTerm (k : ℤ) (z : ℂ) (n : ℕ) : ℂ :=
  (-1 : ℂ) ^ (n + 1) / lambertXi k z ^ (n + 1) *
    ∑ m ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (n + 1 - m) : ℂ) *
      (-Complex.log (lambertXi k z)) ^ (m + 1) / (m + 1).factorial

/-- All integer branches have their normalized leading asymptotic at complex infinity. -/
@[dlmf 4.13.E1_1]
theorem lambertW_leading_asymptotic (k : ℤ) :
    Tendsto (fun z : ℂ => lambertW k z - lambertXi k z + Complex.log (lambertXi k z))
      (Bornology.cobounded ℂ) (𝓝 0) := by
  sorry

/-- The Wright omega equation with the closed logarithm on cut values. -/
@[dlmf 4.13.E1_2]
theorem wrightOmega_equation (z : ℂ) : ∃ l ∈ closedLogValues (wrightOmega z), wrightOmega z + l = z := by
  sorry

/-- The usual principal logarithm form whenever omega lies off its logarithm cut. -/
@[dlmf 4.13.E1_2]
theorem wrightOmega_equation_principal {z : ℂ} (hz : wrightOmega z ∈ Complex.slitPlane) :
    wrightOmega z + Complex.log (wrightOmega z) = z := by
  sorry

/-- The tree T-function satisfies its inverse equation. -/
@[dlmf 4.13.E1_3]
theorem treeT_equation (z : ℂ) : treeT z * Complex.exp (-treeT z) = z := by
  sorry

/-- Exact branch-point, origin and exponential values, including both real lower branches. -/
@[dlmf 4.13.E2]
theorem lambertW_special_values  :
    lambertW 0 (-Real.exp (-1)) = -1 ∧
    lambertWLower 1 (-Real.exp (-1)) = -1 ∧
    lambertW (-1) (-Real.exp (-1)) = -1 ∧
    lambertW 0 0 = 0 ∧ lambertW 0 (Real.exp 1) = 1 := by
  sorry

/-- On the nonnegative axis there is exactly one real solution, increasing and nonnegative. -/
theorem lambertW_real_nonnegative  :
    StrictMonoOn (fun x : ℝ => (lambertW 0 x).re) (Ici 0) ∧
    ∀ x : ℝ, 0 ≤ x → (lambertW 0 x).im = 0 ∧ 0 ≤ (lambertW 0 x).re ∧
      ∀ y : ℝ, y * Real.exp y = x ↔ (y : ℂ) = lambertW 0 x := by
  sorry

/-- The two real branches on the negative interval have opposite monotonicities. -/
theorem lambertW_real_two_solutions  :
    StrictMonoOn (fun x : ℝ => (lambertW 0 x).re) (Ioo (-Real.exp (-1)) 0) ∧
    StrictAntiOn (fun x : ℝ => (lambertW (-1) x).re) (Ioo (-Real.exp (-1)) 0) ∧
    ∀ x : ℝ, x ∈ Ioo (-Real.exp (-1)) 0 →
      (lambertW 0 x).im = 0 ∧ (lambertW (-1) x).im = 0 ∧
      -1 < (lambertW 0 x).re ∧ (lambertW (-1) x).re < -1 ∧
      lambertWLower 1 x = lambertW (-1) x ∧
      ∀ y : ℝ, y * Real.exp y = x ↔
        (y : ℂ) = lambertW 0 x ∨ (y : ℂ) = lambertW (-1) x := by
  sorry

/-- Principal-branch holomorphy on the full square-root slit domain. -/
theorem lambertW_principal_analytic  : AnalyticOnNhd ℂ (lambertW 0) lambertPrincipalDomain := by
  exact (Classical.choice exists_lambertBranchFamily).principal_analytic

/-- Every nonprincipal branch is holomorphic on the logarithm slit plane. -/
theorem lambertW_other_analytic (k : ℤ) (hk : k ≠ 0) : AnalyticOnNhd ℂ (lambertW k) Complex.slitPlane := by
  exact (Classical.choice exists_lambertBranchFamily).other_analytic k hk

/-- The principal branch is real throughout its full real domain. -/
theorem lambertW_principal_real {x : ℝ} (hx : -Real.exp (-1) ≤ x) : (lambertW 0 x).im = 0 := by
  sorry

/-- The principal real inverse is valid through the branch point. -/
@[dlmf 4.13.E3_1]
theorem lambertW_exp_inverse {x : ℝ} (hx : -1 ≤ x) : lambertW 0 (x * Real.exp x) = x := by
  sorry

/-- Both indicated lower-branch cut values invert `x exp x` below minus one. -/
@[dlmf 4.13.E3_2]
theorem lambertW_lower_exp_inverse {x : ℝ} (hx : x < -1) :
    lambertW (-1) (x * Real.exp x) = x ∧ lambertWLower 1 (x * Real.exp x) = x := by
  sorry

/-- Derivative valid on each open analytic branch, including the removable principal origin. -/
@[dlmf 4.13.E4]
theorem lambertW_hasDerivAt (k : ℤ) {z : ℂ}
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (lambertW k)
      (Complex.exp (-lambertW k z) / (1 + lambertW k z)) z := by
  sorry

/-- The equivalent derivative quotient requires a nonzero argument. -/
@[dlmf 4.13.E4]
theorem lambertW_deriv_quotient (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    deriv (lambertW k) z = lambertW k z / (z * (1 + lambertW k z)) := by
  sorry

/-- The nth derivative polynomial has exactly degree n. -/
@[dlmf 4.13.E4_2]
theorem lambertDerivPolynomial_natDegree (n : ℕ) : (lambertDerivPolynomial n).natDegree = n := by
  sorry

/-- Every positive derivative order on every analytic branch. -/
@[dlmf 4.13.E4_1]
theorem lambertW_iteratedDeriv (k n : ℤ) (hn : 1 ≤ n) {z : ℂ}
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    iteratedDeriv n.toNat (lambertW k) z =
      Complex.exp (-n * lambertW k z) *
        (lambertDerivPolynomial (n.toNat - 1)).eval (lambertW k z) /
      (1 + lambertW k z) ^ (2 * n.toNat - 1) := by
  sorry

/-- Maclaurin series with its exact open convergence disk. -/
@[dlmf 4.13.E5]
theorem lambertW_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (-(n + 1) : ℂ) ^ n / (n + 1).factorial * z ^ (n + 1))
      (lambertW 0 z) := by
  sorry

/-- General complex power series, with the n=0 coefficient continued to one for every a. -/
@[dlmf 4.13.E5_1]
theorem lambertW_power_hasSum (a : ℂ) {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    lambertWOver z ^ a = Complex.exp (-a * lambertW 0 z) ∧
    HasSum (fun n : ℕ => (if n = 0 then 1 else a * (n + a) ^ (n - 1) / n.factorial) * (-z) ^ n)
      (Complex.exp (-a * lambertW 0 z)) := by
  sorry

/-- Reciprocal series, including its constant term `0^0=1`. -/
@[dlmf 4.13.E5_2]
theorem lambertW_reciprocal_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n : ℂ) ^ n / n.factorial * z ^ n)
      (1 / (1 + lambertW 0 (-z))) := by
  sorry

/-- Squared-branch series with the negative integer power at n=1 preserved. -/
@[dlmf 4.13.E5_3]
theorem lambertW_square_hasSum {z : ℂ} (hz : ‖z‖ < Real.exp (-1)) :
    HasSum (fun n : ℕ => (n + 1 : ℂ) ^ ((n : ℤ) - 1) / (n + 1).factorial * (-z) ^ (n + 1))
      ((1 - (1 + lambertW 0 z) ^ 2) / 2) := by
  sorry

/-- Exact initial branch-point coefficients. -/
@[dlmf 4.13.E7]
theorem lambertC_initial  :
    lambertC 0 = 1 ∧ lambertC 1 = 1 ∧ lambertC 2 = 1 / 3 ∧
    lambertC 3 = 1 / 36 ∧ lambertC 4 = -1 / 270 := by
  sorry

/-- The coefficient recurrence for every order n≥2. -/
@[dlmf 4.13.E8]
theorem lambertC_recurrence {n : ℕ} (hn : 2 ≤ n) :
    lambertC n = lambertC (n - 1) / (n + 1) - 1 / 2 *
      ∑ k ∈ Finset.Icc 2 (n - 1), lambertC k * lambertC (n + 1 - k) := by
  sorry

/-- The exact relation with the Gamma Stirling coefficients. -/
@[dlmf 4.13.E9]
theorem lambertC_stirling (n : ℕ) :
    (DLMF.oddProduct n) * lambertC (2 * n + 1) = DLMF.Gamma.stirlingG n := by
  sorry

/-- Convergent analytic branch-point parametrization on the full complex t-disk. -/
@[dlmf 4.13.E6]
theorem lambertC_hasSum {t : ℂ} (ht : ‖t‖ < 2 * Real.sqrt Real.pi) :
    ∃ w : ℂ, HasSum (fun n : ℕ => (-1 : ℂ) ^ ((n : ℤ) - 1) * lambertC n * t ^ n) w ∧
      w * Complex.exp w = -Complex.exp (-1 - t ^ 2 / 2) := by
  sorry

/-- The signs of the real parameter select the two real inverse branches. -/
@[dlmf 4.13.E6]
theorem lambertC_real_branches {t : ℝ} (ht : |t| < 2 * Real.sqrt Real.pi) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ ((n : ℤ) - 1) * lambertC n * (t : ℂ) ^ n)
      (if 0 ≤ t then lambertW 0 (-Real.exp (-1 - t ^ 2 / 2))
       else lambertW (-1) (-Real.exp (-1 - t ^ 2 / 2))) := by
  sorry

/-- Exact initial Puiseux coefficients. -/
@[dlmf 4.13.E9_2]
theorem lambertD_initial  :
    lambertD 0 = -1 ∧ lambertD 1 = Real.sqrt 2 ∧ lambertD 2 = -2 / 3 ∧
    lambertD 3 = 11 / 36 * Real.sqrt 2 ∧ lambertD 4 = -43 / 135 := by
  sorry

/-- The full Puiseux-coefficient recurrence. -/
@[dlmf 4.13.E9_2]
theorem lambertD_recurrence {n : ℕ} (hn : 1 ≤ n) :
    (n + 2 : ℝ) * lambertD 1 * lambertD (n + 1) = -2 * lambertD n +
      (n : ℝ) / 2 * (∑ k ∈ Finset.Icc 1 (n - 1), lambertD k * lambertD (n - k)) -
      (n + 2 : ℝ) / 2 * (∑ k ∈ Finset.Icc 1 (n - 1), lambertD (k + 1) * lambertD (n - k + 1)) := by
  sorry

/-- Principal Puiseux series with the exact disk and branch exclusion. -/
@[dlmf 4.13.E9_1]
theorem lambertW_puiseux_hasSum {z : ℂ} (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) :
    HasSum (fun n : ℕ => (lambertD n : ℂ) * ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2))
      (lambertW 0 z) := by
  sorry

/-- All orders of the large-argument expansion, with a next-term logarithmic remainder. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic (k : ℤ) (N : ℕ) :
    Asymptotics.IsBigO (Bornology.cobounded ℂ)
      (fun z => lambertW k z - lambertXi k z + Complex.log (lambertXi k z) -
        ∑ n ∈ range N, lambertAsymptoticTerm k z n)
      (fun z => (Complex.log (lambertXi k z)) ^ (N + 1) / lambertXi k z ^ (N + 1)) := by
  sorry

/-- The large-argument series is eventually absolutely convergent to the branch. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic_converges (k : ℤ) :
    ∀ᶠ z : ℂ in Bornology.cobounded ℂ,
      Summable (fun n => ‖lambertAsymptoticTerm k z n‖) ∧
      HasSum (lambertAsymptoticTerm k z)
        (lambertW k z - lambertXi k z + Complex.log (lambertXi k z)) := by
  sorry

/-- For the real principal branch convergence already holds at e. -/
@[dlmf 4.13.E10]
theorem lambertW_asymptotic_real_converges {x : ℝ} (hx : Real.exp 1 ≤ x) :
    Summable (fun n => ‖lambertAsymptoticTerm 0 x n‖) ∧
    HasSum (lambertAsymptoticTerm 0 x)
      (lambertW 0 x - lambertXi 0 x + Complex.log (lambertXi 0 x)) := by
  sorry

/-- All orders for both real lower cut branches at zero from below. -/
@[dlmf 4.13.E11]
theorem lambertW_lower_asymptotic (N : ℕ) :
    Asymptotics.IsBigO (𝓝[<] (0 : ℝ))
      (fun x => lambertW (-1) x + Real.log (-1 / x) +
        Real.log (Real.log (-1 / x)) -
        ∑ n ∈ range N, (1 : ℂ) / (Real.log (-1 / x) : ℂ) ^ (n + 1) *
          ∑ m ∈ range (n + 1), (Nat.stirlingFirst (n + 1) (n + 1 - m) : ℂ) *
            (-Real.log (Real.log (-1 / x)) : ℂ) ^ (m + 1) / (m + 1).factorial)
      (fun x => (Real.log (Real.log (-1 / x)) : ℂ) ^ (N + 1) /
        (Real.log (-1 / x) : ℂ) ^ (N + 1)) := by
  sorry

/-- An antiderivative on each analytic branch away from zero. -/
@[dlmf 4.13.E12]
theorem lambertW_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z / lambertW k z + z * lambertW k z - z) (lambertW k z) z := by
  sorry

/-- An antiderivative of W(z)/z. -/
@[dlmf 4.13.E13]
theorem lambertW_div_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => (lambertW k z) ^ 2 / 2 + lambertW k z) (lambertW k z / z) z := by
  sorry

/-- The sine-of-W antiderivative on every branch. -/
@[dlmf 4.13.E14]
theorem sin_lambertW_primitive (k : ℤ) {z : ℂ} (hne : z ≠ 0)
    (hz : if k = 0 then z ∈ lambertPrincipalDomain else z ∈ Complex.slitPlane) :
    HasDerivAt (fun z : ℂ => z * (1 + 1 / lambertW k z) * Complex.sin (lambertW k z) -
      z * Complex.cos (lambertW k z)) (2 * Complex.sin (lambertW k z)) z := by
  sorry

/-- Rational integral representation on the full principal slit domain. -/
@[dlmf 4.13.E15]
theorem lambertW_integral_rational {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    lambertW 0 z = z / Real.pi * ∫ t in (0 : ℝ)..Real.pi,
      (((1 - t * Real.cos t / Real.sin t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t) := by
  sorry

/-- Logarithmic integral representation on the full principal slit domain. -/
@[dlmf 4.13.E16]
theorem lambertW_integral_log {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    lambertW 0 z = 1 / Real.pi * ∫ t in (0 : ℝ)..Real.pi,
      Complex.log (1 + z * (Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t) : ℝ)) := by
  sorry

/-- Nonprincipal branches have a logarithmic singularity at zero (4.13, prose). -/
theorem lambertW_other_norm_tendsto_zero (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun z : ℂ => ‖lambertW k z‖)
      (𝓝[Complex.slitPlane] 0) atTop := by
  sorry

/-- The rational principal-branch integral is convergent on the stated domain. -/
@[dlmf 4.13.E15]
theorem lambertW_integral_rational_integrable {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    IntervalIntegrable (fun t : ℝ =>
      (((1 - t * Real.cos t / Real.sin t) ^ 2 + t ^ 2 : ℝ) : ℂ) /
        (z + t * Real.exp (-t * Real.cos t / Real.sin t) / Real.sin t))
      MeasureTheory.volume 0 Real.pi := by
  sorry

/-- The logarithmic principal-branch integral is convergent on the stated domain. -/
@[dlmf 4.13.E16]
theorem lambertW_integral_log_integrable {z : ℂ} (hz : z ∈ lambertPrincipalDomain) :
    IntervalIntegrable (fun t : ℝ =>
      Complex.log (1 + z * (Real.sin t / t * Real.exp (t * Real.cos t / Real.sin t) : ℝ)))
      MeasureTheory.volume 0 Real.pi := by
  sorry

/-- Puiseux expansion of the decreasing real branch continued into the upper half-plane.
Together with its nonzero first coefficient this records its square-root branch point. -/
@[dlmf 4.13.E9_1]
theorem lambertW_minus_one_puiseux_hasSum {z : ℂ}
    (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) (him : 0 ≤ z.im) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * lambertD n *
      ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2)) (lambertW (-1) z) := by
  sorry

/-- Lower-side counterpart of the real-branch Puiseux expansion. -/
@[dlmf 4.13.E9_1]
theorem lambertW_one_lower_puiseux_hasSum {z : ℂ}
    (hz : ‖(Real.exp 1 : ℂ) * z + 1‖ < 1)
    (harg : |(z + (Real.exp (-1) : ℂ)).arg| < Real.pi) (him : z.im ≤ 0) :
    HasSum (fun n : ℕ => (-1 : ℂ) ^ n * lambertD n *
      ((Real.exp 1 : ℂ) * z + 1) ^ ((n : ℂ) / 2)) (lambertWLower 1 z) := by
  sorry

/-- The singular growth of a nonprincipal branch at zero is logarithmic. -/
theorem lambertW_other_logarithmic_growth (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun z : ℂ => ‖lambertW k z‖ / |Real.log ‖z‖|)
      (𝓝[Complex.slitPlane] 0) (𝓝 1) := by
  sorry

/-- Differential of the inverse substitution `z=w exp w` used in Lambert integrals. -/
theorem lambert_forward_hasDerivAt (w : ℂ) :
    HasDerivAt (fun w : ℂ => w * Complex.exp w) ((w + 1) * Complex.exp w) w := by
  simpa only [id_eq, Pi.mul_apply, one_mul, add_mul, add_comm] using
    (hasDerivAt_id w).fun_mul (Complex.hasDerivAt_exp w)

end DLMF.Elementary
