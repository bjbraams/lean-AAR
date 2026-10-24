/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Elementary.LogExpBasic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Logarithms, exponentials and powers: DLMF §§4.4–4.8

Exact special values, complex-parameter limits, inequalities, boundary-convergent
series, differential equations, and multivalued identities. Decimal approximations
are omitted. The strict bounds in 4.5.3 and 4.5.14 require a strict endpoint; their
exact positive cutoffs are defined below and equality is retained there.
The additive constant printed in 4.7.13 is corrected to a multiplicative constant.
The independent-set interpretation of 4.8.5 is corrected by retaining all integer
logarithm shifts rather than only multiples of the exponent.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- Both exact logarithm values at `-1`. -/
@[dlmf 4.4.E2]
theorem closedLogValues_neg_one  : closedLogValues (-1) = {Real.pi * I, -Real.pi * I} := by
  sorry

/-- The two exact sixth-root exponential values. -/
@[dlmf 4.4.E8]
theorem exp_pi_div_three (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * Real.pi / 3 * I) = 1 / 2 + ε * I * (Real.sqrt 3 / 2) := by
  sorry

/-- The two exact third-root exponential values. -/
@[dlmf 4.4.E9]
theorem exp_two_pi_div_three (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * 2 * Real.pi / 3 * I) = -1 / 2 + ε * I * (Real.sqrt 3 / 2) := by
  sorry

/-- The two exact eighth-root exponential values. -/
@[dlmf 4.4.E10]
theorem exp_pi_div_four (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * Real.pi / 4 * I) = 1 / (Real.sqrt 2 : ℂ) + ε * I / Real.sqrt 2 := by
  sorry

/-- The two exact remaining eighth-root exponential values. -/
@[dlmf 4.4.E11]
theorem exp_three_pi_div_four (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    Complex.exp (ε * 3 * Real.pi / 4 * I) = -1 / (Real.sqrt 2 : ℂ) + ε * I / Real.sqrt 2 := by
  sorry

/-- The principal imaginary powers of `I`. -/
@[dlmf 4.4.E12]
theorem I_cpow_I (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    I ^ (ε * I) = (Real.exp (-ε * Real.pi / 2) : ℂ) := by
  sorry

/-- Logarithmic growth is smaller than every power with positive real part. -/
@[dlmf 4.4.E13]
theorem tendsto_cpow_neg_mul_log {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ (-a) * Real.log x) atTop (𝓝 0) := by
  sorry

/-- Complex positive-real-part powers suppress the logarithm at zero. -/
@[dlmf 4.4.E14]
theorem tendsto_cpow_mul_log_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  sorry

/-- Real-axis exponential decay for every complex power. -/
@[dlmf 4.4.E15]
theorem tendsto_cpow_mul_exp_neg (a : ℂ) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ a * Complex.exp (-x)) atTop (𝓝 0) := by
  sorry

/-- Uniform exponential decay in each closed proper right half-sector. -/
@[dlmf 4.4.E16]
theorem tendsto_cpow_mul_exp_neg_sector (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi / 2) :
    Tendsto (fun z : ℂ => z ^ a * Complex.exp (-z))
      (DLMF.sector (Real.pi / 2 - δ)) (𝓝 0) := by
  sorry

/-- Exact positive cutoff for the logarithm inequality, without a decimal approximation. -/
def logInequalityCutoff : ℝ := sSup {x : ℝ | 0 < x ∧ x < 1 ∧ -Real.log (1 - x) ≤ 3 * x / 2}

/-- The cutoff is the nonzero root of the equality case. -/
theorem logInequalityCutoff_spec  :
    0 < logInequalityCutoff ∧ logInequalityCutoff < 1 ∧
    -Real.log (1 - logInequalityCutoff) = 3 * logInequalityCutoff / 2 := by
  sorry

/-- Both sharp first-order logarithmic inequalities. -/
@[dlmf 4.5.E1]
theorem log_one_add_bounds {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) :
    x / (1 + x) < Real.log (1 + x) ∧ Real.log (1 + x) < x := by
  sorry

/-- The equivalent logarithmic inequalities below one. -/
@[dlmf 4.5.E2]
theorem neg_log_one_sub_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    x < -Real.log (1 - x) ∧ -Real.log (1 - x) < x / (1 - x) := by
  sorry

/-- Strict form inside the exact cutoff; the printed closed endpoint has equality. -/
@[dlmf 4.5.E3]
theorem abs_log_one_sub_lt {x : ℝ} (hx : 0 < x) (hr : x < logInequalityCutoff) :
    |Real.log (1 - x)| < 3 * x / 2 := by
  sorry

/-- Weak form through the exact cutoff. -/
@[dlmf 4.5.E3]
theorem abs_log_one_sub_le {x : ℝ} (hx : 0 < x) (hr : x ≤ logInequalityCutoff) :
    |Real.log (1 - x)| ≤ 3 * x / 2 := by
  sorry

/-- The positive-parameter power bound for the logarithm. -/
@[dlmf 4.5.E5]
theorem log_le_rpow_sub_one {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    Real.log x ≤ a * (x ^ (1 / a) - 1) := by
  sorry

/-- The complex logarithm bound with full unit-disk range. -/
@[dlmf 4.5.E6]
theorem norm_log_one_add_le {z : ℂ} (hz : ‖z‖ < 1) :
    ‖Complex.log (1 + z)‖ ≤ -Real.log (1 - ‖z‖) := by
  sorry

/-- Exponential bounds for `1-x`. -/
@[dlmf 4.5.E7]
theorem exp_one_sub_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    Real.exp (-x / (1 - x)) < 1 - x ∧ 1 - x < Real.exp (-x) := by
  sorry

/-- The exponential upper bound below one. -/
@[dlmf 4.5.E9]
theorem exp_lt_one_div {x : ℝ} (hx : x < 1) (hne : x ≠ 0) : Real.exp x < 1 / (1 - x) := by
  sorry

/-- Bounds for `1-exp(-x)`. -/
@[dlmf 4.5.E10]
theorem one_sub_exp_neg_bounds {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) :
    x / (1 + x) < 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) < x := by
  sorry

/-- Bounds for `exp x-1`. -/
@[dlmf 4.5.E11]
theorem exp_sub_one_bounds {x : ℝ} (hx : x < 1) (hne : x ≠ 0) :
    x < Real.exp x - 1 ∧ Real.exp x - 1 < x / (1 - x) := by
  sorry

/-- Exponential lower approximation to `1+x`. -/
@[dlmf 4.5.E12]
theorem exp_div_one_add_lt {x : ℝ} (hx : -1 < x) (hne : x ≠ 0) : Real.exp (x / (1 + x)) < 1 + x := by
  sorry

/-- Two-parameter exponential bounds, with both parameters positive. -/
@[dlmf 4.5.E13]
theorem rpow_one_add_bounds {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.exp (x * y / (x + y)) < (1 + x / y) ^ y ∧
    (1 + x / y) ^ y < Real.exp x := by
  sorry

/-- Exact nonzero cutoff for the linear exponential upper bound. -/
def expInequalityCutoff : ℝ := sSup {x : ℝ | 0 < x ∧ Real.exp (-x) ≤ 1 - x / 2}

/-- The exponential cutoff and its exact equality case. -/
theorem expInequalityCutoff_spec  :
    0 < expInequalityCutoff ∧ expInequalityCutoff < 2 ∧
    Real.exp (-expInequalityCutoff) = 1 - expInequalityCutoff / 2 := by
  sorry

/-- Strict form inside the exact cutoff. -/
@[dlmf 4.5.E14]
theorem exp_neg_lt_linear {x : ℝ} (hx : 0 < x) (hr : x < expInequalityCutoff) :
    Real.exp (-x) < 1 - x / 2 := by
  sorry

/-- Weak form through the exact cutoff. -/
@[dlmf 4.5.E14]
theorem exp_neg_le_linear {x : ℝ} (hx : 0 < x) (hr : x ≤ expInequalityCutoff) :
    Real.exp (-x) ≤ 1 - x / 2 := by
  sorry

/-- Two-sided complex exponential estimate on the punctured unit disk. -/
@[dlmf 4.5.E15]
theorem norm_exp_sub_one_bounds {z : ℂ} (hz : 0 < ‖z‖) (hz1 : ‖z‖ < 1) :
    ‖z‖ / 4 < ‖Complex.exp z - 1‖ ∧ ‖Complex.exp z - 1‖ < 7 * ‖z‖ / 4 := by
  sorry

/-- Global complex exponential estimate. -/
@[dlmf 4.5.E16]
theorem norm_exp_sub_one_le (z : ℂ) :
    ‖Complex.exp z - 1‖ ≤ Real.exp ‖z‖ - 1 ∧
    Real.exp ‖z‖ - 1 ≤ ‖z‖ * Real.exp ‖z‖ := by
  sorry

/-- Logarithm Taylor series with all convergent boundary points. -/
@[dlmf 4.6.E1]
theorem log_one_add_hasSum_closed {z : ℂ} (hz : ‖z‖ ≤ 1) (hne : z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n * z ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log (1 + z))) := by
  sorry

/-- The reciprocal-transformed logarithm series, including the boundary line. -/
@[dlmf 4.6.E2]
theorem log_hasSum_halfplane {z : ℂ} (hz : 1 / 2 ≤ z.re) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, ((z - 1) / z) ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log z)) := by
  sorry

/-- The logarithm Taylor series about one with its full boundary. -/
@[dlmf 4.6.E3]
theorem log_hasSum_center_one {z : ℂ} (hz : ‖z - 1‖ ≤ 1) (hne : z ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, (-1 : ℂ) ^ n * (z - 1) ^ (n + 1) / (n + 1))
      atTop (𝓝 (Complex.log z)) := by
  sorry

/-- The odd Cayley-transform series, including the imaginary-axis boundary. -/
@[dlmf 4.6.E4]
theorem log_hasSum_odd {z : ℂ} (hz : 0 ≤ z.re) (hne : z ≠ 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 * ((z - 1) / (z + 1)) ^ (2 * n + 1) / (2 * n + 1))
      atTop (𝓝 (Complex.log z)) := by
  sorry

/-- The reciprocal odd series, including all admissible unit-circle points. -/
@[dlmf 4.6.E5]
theorem log_ratio_hasSum_odd {z : ℂ} (hz : 1 ≤ ‖z‖) (hp : z ≠ 1) (hm : z ≠ -1) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 / ((2 * n + 1 : ℂ) * z ^ (2 * n + 1)))
      atTop (𝓝 (Complex.log ((z + 1) / (z - 1)))) := by
  sorry

/-- The shifted odd logarithm series with a positive real shift. -/
@[dlmf 4.6.E6]
theorem log_add_hasSum_odd {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : -a ≤ z.re) (hne : z ≠ -a) :
    Tendsto (fun N : ℕ => ∑ n ∈ range N, 2 * (z / (2 * a + z)) ^ (2 * n + 1) / (2 * n + 1))
      atTop (𝓝 (Complex.log (z + a) - Complex.log a)) := by
  sorry

/-- The complex falling factorial, including its empty product. -/
def fallingPower (a : ℂ) (n : ℕ) : ℂ := ∏ j ∈ range n, (a - j)

/-- The complex binomial series on its full open disk. -/
@[dlmf 4.6.E7]
theorem binomial_hasSum (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => fallingPower a n / n.factorial * z ^ n) ((1 + z) ^ a) := by
  sorry

/-- Nonnegative integer exponents terminate and allow unrestricted arguments. -/
@[dlmf 4.6.E7]
theorem binomial_nat_hasSum (m : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => fallingPower (m : ℂ) n / n.factorial * z ^ n) ((1 + z) ^ m) := by
  sorry

/-- Every logarithm sheet has the same derivative on the slit plane. -/
@[dlmf 4.7.E2]
theorem logSheet_hasDerivAt (k : ℤ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    HasDerivAt (logSheet k) z⁻¹ z := by
  change HasDerivAt (fun z => Complex.log z + k * (2 * Real.pi * I)) z⁻¹ z
  exact (Complex.hasDerivAt_log hz).add_const _

/-- Every logarithm sheet has the displayed derivatives of all positive orders. -/
@[dlmf 4.7.E4]
theorem iteratedDeriv_logSheet (k : ℤ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv (n + 1) (logSheet k) z =
      (-1 : ℂ) ^ n * n.factorial * z ^ (-(n : ℤ) - 1) := by
  sorry

/-- General logarithmic ODE solution on a connected open domain with a selected analytic logarithm. -/
@[dlmf 4.7.E5, dlmf 4.7.E6]
theorem logarithmic_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    (f f' L w : ℂ → ℂ)
    (hf : ∀ z ∈ s, HasDerivAt f (f' z) z)
    (hn : ∀ z ∈ s, f z ≠ 0)
    (hL : ∀ z ∈ s, Complex.exp (L z) = f z)
    (hLd : DifferentiableOn ℂ L s) :
    (∀ z ∈ s, HasDerivAt w (f' z / f z) z) ↔
      ∃ C : ℂ, ∀ z ∈ s, w z = L z + C := by
  sorry

/-- Derivative of an exponential with an arbitrary complex slope. -/
@[dlmf 4.7.E8]
theorem exp_mul_hasDerivAt (a z : ℂ) : HasDerivAt (fun z : ℂ => Complex.exp (a * z))
    (a * Complex.exp (a * z)) z := by
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using
    (Complex.hasDerivAt_exp (a * z)).comp z ((hasDerivAt_id z).const_mul a)

/-- A general power uses the logarithm sheet from its definition. -/
@[dlmf 4.7.E9]
theorem powerSheet_hasDerivAt (a : ℂ) (k : ℤ) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (z * logSheet k a))
      (Complex.exp (z * logSheet k a) * logSheet k a) z := by
  simpa only [Function.comp_def, id_eq, mul_one, one_mul, mul_comm] using
    (Complex.hasDerivAt_exp (z * logSheet k a)).comp z
      ((hasDerivAt_id z).mul_const (logSheet k a))

/-- All higher power derivatives retain the full complex exponent. -/
@[dlmf 4.7.E11]
theorem iteratedDeriv_cpow (a : ℂ) (n : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun z : ℂ => z ^ a) z = fallingPower a n * z ^ (a - n) := by
  sorry

/-- Corrected general linear ODE solution: the arbitrary constant multiplies the exponential. -/
@[dlmf 4.7.E12, dlmf 4.7.E13]
theorem linear_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    (f F w : ℂ → ℂ) (hF : ∀ z ∈ s, HasDerivAt F (f z) z) :
    (∀ z ∈ s, HasDerivAt w (f z * w z) z) ↔
      ∃ C : ℂ, ∀ z ∈ s, w z = C * Complex.exp (F z) := by
  sorry

/-- General second-order constant-coefficient ODE solution, including both arbitrary constants. -/
@[dlmf 4.7.E14, dlmf 4.7.E15]
theorem second_order_ode_solution {s : Set ℂ} (hs : IsOpen s) (hc : IsPreconnected s)
    {a : ℂ} (ha : a ≠ 0) (w : ℂ → ℂ) :
    (∀ z ∈ s, HasDerivAt w (deriv w z) z ∧ HasDerivAt (deriv w) (a * w z) z) ↔
      ∃ A B : ℂ, ∀ z ∈ s,
        w z = A * Complex.exp ((a ^ (1 / 2 : ℂ)) * z) + B * Complex.exp (-(a ^ (1 / 2 : ℂ)) * z) := by
  sorry

/-- Product identity as equality of full multivalued logarithm sets. -/
@[dlmf 4.8.E1]
theorem generalLogValues_mul {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    generalLogValues (x * y) = {w | ∃ u ∈ generalLogValues x, ∃ v ∈ generalLogValues y, w = u + v} := by
  sorry

/-- Quotient identity as equality of full multivalued logarithm sets. -/
@[dlmf 4.8.E3]
theorem generalLogValues_div {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    generalLogValues (x / y) = {w | ∃ u ∈ generalLogValues x, ∃ v ∈ generalLogValues y, w = u - v} := by
  sorry

/-- All branches of the integer-power logarithm; shifts remain arbitrary, including at exponent zero. -/
@[dlmf 4.8.E5]
theorem generalLogValues_zpow {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    generalLogValues (z ^ n) = {w | ∃ k : ℤ, w = n * Complex.log z + k * (2 * Real.pi * I)} := by
  sorry

/-- Principal integer-power identity with the half-open Mathlib strip. -/
@[dlmf 4.8.E6]
theorem log_zpow_strip {z : ℂ} (hz : z ≠ 0) (n : ℤ)
    (hlo : -Real.pi < n * z.arg) (hhi : n * z.arg ≤ Real.pi) :
    Complex.log (z ^ n) = n * Complex.log z := by
  sorry

/-- Every logarithm of an exponential differs by an integer period. -/
@[dlmf 4.8.E8]
theorem generalLogValues_exp (z : ℂ) : generalLogValues (Complex.exp z) =
    {w | ∃ k : ℤ, w = z + k * (2 * Real.pi * I)} := by
  sorry

/-- Logarithms of a selected general power acquire an independent integer shift. -/
@[dlmf 4.8.E11]
theorem generalLogValues_power {a : ℂ} (ha : a ≠ 0) (z : ℂ) (j : ℤ) :
    generalLogValues (Complex.exp (z * logSheet j a)) =
      {w | ∃ k : ℤ, w = z * logSheet j a + k * (2 * Real.pi * I)} := by
  sorry

/-- Principal logarithm of a principal power with the unique half-open strip correction. -/
@[dlmf 4.8.E12]
theorem log_cpow_sheet {a : ℂ} (ha : a ≠ 0) (z : ℂ) :
    ∃ k : ℤ, Complex.log (a ^ z) = z * Complex.log a + k * (2 * Real.pi * I) ∧
      -Real.pi < (z * Complex.log a + k * (2 * Real.pi * I)).im ∧
      (z * Complex.log a + k * (2 * Real.pi * I)).im ≤ Real.pi := by
  sorry

/-- Exponentiating twice uses the principal strip, with the lower edge excluded. -/
@[dlmf 4.8.E17]
theorem exp_cpow_strip {z : ℂ} (hlo : -Real.pi < z.im) (hhi : z.im ≤ Real.pi) (a : ℂ) :
    (Complex.exp z) ^ a = Complex.exp (z * a) := by
  sorry

/-- Integer outer exponents remove the strip restriction entirely. -/
@[dlmf 4.8.E17]
theorem exp_cpow_int (z : ℂ) (n : ℤ) : (Complex.exp z) ^ n = Complex.exp (z * n) := by
  sorry

/-- The closed principal product identity retains both valid strip edges (4.8.2). -/
@[dlmf 4.8.E2]
theorem closedLog_mul {x y u v : ℂ} (hu : u ∈ closedLogValues x)
    (hv : v ∈ closedLogValues y) (hstrip : |(u + v).im| ≤ Real.pi) :
    u + v ∈ closedLogValues (x * y) := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_add, hu.1, hv.1], hstrip⟩

/-- The closed principal quotient identity retains both valid strip edges (4.8.4). -/
@[dlmf 4.8.E4]
theorem closedLog_div {x y u v : ℂ} (hu : u ∈ closedLogValues x)
    (hv : v ∈ closedLogValues y) (hstrip : |(u - v).im| ≤ Real.pi) :
    u - v ∈ closedLogValues (x / y) := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_sub, hu.1, hv.1], hstrip⟩

/-- The closed integer-power identity retains both strip edges (4.8.6). -/
@[dlmf 4.8.E6]
theorem closedLog_zpow {z l : ℂ} (hl : l ∈ closedLogValues z) (n : ℤ)
    (hstrip : |(n * l).im| ≤ Real.pi) :
    n * l ∈ closedLogValues (z ^ n) := by
  sorry

/-- Inversion exchanges the two sides of the cut (4.8.7). -/
@[dlmf 4.8.E7]
theorem closedLog_inv {z l : ℂ} (hl : l ∈ closedLogValues z) :
    -l ∈ closedLogValues z⁻¹ := by
  simp only [closedLogValues, mem_setOf_eq] at *
  exact ⟨by rw [Complex.exp_neg, hl.1], by simpa using hl.2⟩

/-- The closed logarithm of an exponential includes both edges (4.8.9). -/
@[dlmf 4.8.E9]
theorem closedLog_exp {z : ℂ} (hstrip : |z.im| ≤ Real.pi) :
    z ∈ closedLogValues (Complex.exp z) := ⟨rfl, hstrip⟩

/-- Compatible principal logarithms give compatible principal products of powers (4.8.15). -/
@[dlmf 4.8.E15]
theorem closedPower_mul {a b u v : ℂ} (hu : u ∈ closedLogValues a)
    (hv : v ∈ closedLogValues b) (hstrip : |(u + v).im| ≤ Real.pi) (z : ℂ) :
    Complex.exp (z * u) * Complex.exp (z * v) ∈ closedPowerValues (a * b) z := by
  refine ⟨u + v, closedLog_mul hu hv hstrip, ?_⟩
  rw [← Complex.exp_add]; congr 1; ring

/-- The zero-limit holds even on every complex approach, including both cut sides. -/
@[dlmf 4.4.E14]
theorem tendsto_cpow_mul_log_complex_zero {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun z : ℂ => z ^ a * Complex.log z) (𝓝[≠] 0) (𝓝 0) := by
  sorry

end DLMF.Elementary
