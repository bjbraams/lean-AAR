/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous

/-!
# Logarithms, exponentials and powers: DLMF §§4.2–4.3

Mathlib supplies the principal logarithm with argument in `(-π,π]`. DLMF also uses a
closed principal value with two values on the negative axis. `closedLogValues` retains
both values; `generalLogValues` retains every logarithm. Thus a boundary value is never
silently identified with Mathlib's upper-side convention. Upstream declarations are
indexed in `MathlibCoverage`; only missing statements and adapters occur here.
-/

@[expose] public section

open Complex Filter Set
open scoped Topology Real
noncomputable section
namespace DLMF.Elementary

/-- Every value of the complex logarithm, as an inverse relation of `exp` (4.2.25). -/
@[dlmf 4.2.E25]
def generalLogValues (z : ℂ) : Set ℂ := {w | Complex.exp w = z}

/-- The closed principal logarithm, retaining both sides of the negative-axis cut. -/
def closedLogValues (z : ℂ) : Set ℂ :=
  {w | Complex.exp w = z ∧ |w.im| ≤ Real.pi}

/-- A specified sheet of the general logarithm (4.2.6). -/
@[dlmf 4.2.E6]
def logSheet (k : ℤ) (z : ℂ) : ℂ := Complex.log z + k * (2 * Real.pi * I)

/-- All general logarithms are the integer translates of the principal logarithm. -/
@[dlmf 4.2.E6]
theorem mem_generalLogValues_iff {z w : ℂ} (hz : z ≠ 0) :
    w ∈ generalLogValues z ↔ ∃ k : ℤ, w = logSheet k z := by
  simpa [generalLogValues, logSheet, Complex.exp_log hz] using
    (Complex.exp_eq_exp_iff_exists_int (x := w) (y := Complex.log z))

/-- The negative real axis used as the logarithm branch cut (4.2.4). -/
@[dlmf 4.2.E4]
def logBranchCut : Set ℂ := {z | z.im = 0 ∧ z.re < 0}

/-- The two closed logarithm values on the cut (4.2.7). -/
@[dlmf 4.2.E7]
theorem closedLogValues_neg {x : ℝ} (hx : x < 0) :
    closedLogValues (x : ℂ) =
      {((Real.log |x| : ℝ) : ℂ) + Real.pi * I,
       ((Real.log |x| : ℝ) : ℂ) - Real.pi * I} := by
  sorry

/-- The principal logarithm is the integral of `dt/t` along any absolutely
continuous path in the slit plane from `1` to `z` (4.2.2). -/
@[dlmf 4.2.E2]
theorem log_eq_path_integral {z : ℂ} (γ : ℝ → ℂ)
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ Complex.slitPlane)
    (h0 : γ 0 = 1) (h1 : γ 1 = z) :
    Complex.log z = ∫ t in (0 : ℝ)..1, deriv γ t / γ t := by
  sorry

/-- Every path integral avoiding zero gives a general logarithm (4.2.1).
Absolute continuity includes all piecewise continuously differentiable paths. -/
@[dlmf 4.2.E1]
theorem path_integral_mem_generalLogValues {z : ℂ} (γ : ℝ → ℂ)
    (hγ : AbsolutelyContinuousOnInterval γ 0 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0)
    (h0 : γ 0 = 1) (h1 : γ 1 = z) :
    (∫ t in (0 : ℝ)..1, deriv γ t / γ t) ∈ generalLogValues z := by
  sorry

/-- Conversely every logarithm value is attained by a path integral (4.2.1). -/
@[dlmf 4.2.E1]
theorem generalLogValues_eq_pathIntegrals (z : ℂ) :
    generalLogValues z = {w | ∃ γ : ℝ → ℂ,
      AbsolutelyContinuousOnInterval γ 0 1 ∧ γ 0 = 1 ∧ γ 1 = z ∧
      (∀ t ∈ Icc (0 : ℝ) 1, γ t ≠ 0) ∧
      w = ∫ t in (0 : ℝ)..1, deriv γ t / γ t} := by
  sorry

/-- The only zero of the principal logarithm on its nonzero domain (4.2(i), prose). -/
theorem log_eq_zero_iff {z : ℂ} (hz : z ≠ 0) : Complex.log z = 0 ↔ z = 1 := by
  constructor
  · intro h
    simpa [h] using (Complex.exp_log hz).symm
  · rintro rfl; exact Complex.log_one

/-- Complex logarithm to an arbitrary base, using principal logarithms (4.2.8). -/
@[dlmf 4.2.E8]
def complexLogb (a z : ℂ) : ℂ := Complex.log z / Complex.log a

/-- Complex change of logarithm base; both bases are nonzero and different from one. -/
@[dlmf 4.2.E9]
theorem complexLogb_change_base {a b z : ℂ}
    (ha : a ≠ 0) (ha1 : a ≠ 1) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    complexLogb a z = complexLogb b z / complexLogb b a := by
  have hb' : Complex.log b ≠ 0 := by simpa [log_eq_zero_iff hb] using hb1
  simp only [complexLogb]
  field_simp

/-- Reciprocal change of base (4.2.10). -/
@[dlmf 4.2.E10]
theorem complexLogb_reciprocal (a b : ℂ) :
    complexLogb a b = 1 / complexLogb b a := by
  simp [complexLogb, div_div]

/-- Natural logarithms have base `exp 1` (4.2.14). -/
@[dlmf 4.2.E14]
theorem complexLogb_exp_one (z : ℂ) : complexLogb (Complex.exp 1) z = Complex.log z := by
  rw [complexLogb, Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  simp

/-- Common logarithms as a multiple of the natural logarithm (4.2.15). -/
@[dlmf 4.2.E15]
theorem complexLogb_ten (z : ℂ) :
    complexLogb 10 z = Complex.log z / Complex.log 10 ∧
    complexLogb 10 z = complexLogb 10 (Complex.exp 1) * Complex.log z := by
  rw [complexLogb, complexLogb, Complex.log_exp (by simp [Real.pi_pos])
    (by simp [Real.pi_pos.le])]
  constructor <;> ring

/-- Recovery of the natural logarithm from the common logarithm (4.2.16). -/
@[dlmf 4.2.E16]
theorem log_eq_log_ten_mul_logb (z : ℂ) :
    Complex.log z = Complex.log 10 * complexLogb 10 z := by
  have h : Complex.log (10 : ℂ) ≠ 0 := by
    intro h; have := (log_eq_zero_iff (by norm_num : (10 : ℂ) ≠ 0)).mp h; norm_num at this
  simp only [complexLogb]
  field_simp

/-- General powers, retaining all sheets of the base logarithm (4.2.26). -/
@[dlmf 4.2.E26]
def generalPowerValues (z a : ℂ) : Set ℂ :=
  {w | ∃ l ∈ generalLogValues z, w = Complex.exp (a * l)}

/-- Closed principal powers, retaining the two cut values. -/
def closedPowerValues (z a : ℂ) : Set ℂ :=
  {w | ∃ l ∈ closedLogValues z, w = Complex.exp (a * l)}

/-- Magnitude of a power on any logarithm sheet; this includes both closed cut values. -/
@[dlmf 4.2.E29]
theorem norm_power_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℂ) :
    ‖Complex.exp (a * l)‖ = ‖z‖ ^ a.re * Real.exp (-a.im * l.im) := by
  have hr : l.re = Real.log ‖z‖ := by
    simpa only [Complex.norm_exp, Real.log_exp] using
      congrArg (fun w : ℂ => Real.log ‖w‖) (show Complex.exp l = z from hl)
  rw [Complex.norm_exp, Complex.mul_re, hr,
    Real.rpow_def_of_pos (norm_pos_iff.mpr hz), ← Real.exp_add]
  congr 1
  ring

/-- Unreduced phase on every logarithm sheet, with no principal argument restriction. -/
@[dlmf 4.2.E30]
theorem power_phase_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℂ) :
    Complex.exp (a * l) = (‖z‖ ^ a.re * Real.exp (-a.im * l.im) : ℝ) *
      Complex.exp ((a.re * l.im + a.im * Real.log ‖z‖) * I) := by
  have hr : l.re = Real.log ‖z‖ := by
    simpa only [Complex.norm_exp, Real.log_exp] using
      congrArg (fun w : ℂ => Real.log ‖w‖) (show Complex.exp l = z from hl)
  have he : Real.exp (a * l).re = ‖z‖ ^ a.re * Real.exp (-a.im * l.im) := by
    simpa only [Complex.norm_exp] using norm_power_of_logValue hz hl a
  calc
    Complex.exp (a * l) = Complex.exp ((a * l).re + (a * l).im * I) := by
      rw [Complex.re_add_im]
    _ = (Real.exp (a * l).re : ℂ) * Complex.exp ((a * l).im * I) := by
      rw [Complex.exp_add, Complex.ofReal_exp]
    _ = _ := by
      rw [he]
      simp only [Complex.mul_im, hr, Complex.ofReal_add, Complex.ofReal_mul]

/-- Magnitude and unreduced phase of a real power on every logarithm sheet. -/
@[dlmf 4.2.E31]
theorem real_power_of_logValue {z l : ℂ} (hz : z ≠ 0) (hl : l ∈ generalLogValues z)
    (a : ℝ) :
    ‖Complex.exp (a * l)‖ = ‖z‖ ^ a ∧
      Complex.exp (a * l) = (‖z‖ ^ a : ℝ) * Complex.exp ((a * l.im : ℝ) * I) := by
  constructor
  · simpa using norm_power_of_logValue hz hl (a : ℂ)
  · simpa using power_phase_of_logValue hz hl (a : ℂ)


/-- The unreduced phase of a power, before reduction modulo `2π` (4.2.30). -/
@[dlmf 4.2.E30]
theorem power_phase {z a : ℂ} (hz : z ≠ 0) :
    z ^ a = (‖z‖ ^ a.re * Real.exp (-a.im * z.arg) : ℝ) *
      Complex.exp ((a.re * z.arg + a.im * Real.log ‖z‖) * I) := by
  rw [Complex.cpow_def_of_ne_zero hz, mul_comm]
  simpa only [Complex.log_im] using
    power_phase_of_logValue hz (Complex.exp_log hz) a

/-- General powers of `e`, in addition to its principal power (4.2.33). -/
@[dlmf 4.2.E33]
theorem generalPowerValues_exp_one (a : ℂ) :
    generalPowerValues (Complex.exp 1) a =
      {w | ∃ k : ℤ, w = Complex.exp a * Complex.exp (2 * k * a * Real.pi * I)} := by
  sorry

/-- Inversion of the full general power relation (4.2.35). -/
@[dlmf 4.2.E35]
theorem mem_generalPowerValues_iff {z a w : ℂ} (hz : z ≠ 0) (ha : a ≠ 0)
    (hw : w ≠ 0) :
    w ∈ generalPowerValues z a ↔
      ∃ l ∈ generalLogValues w, z = Complex.exp (l / a) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    refine ⟨a * l, rfl, ?_⟩
    have hdiv : a * l / a = l := by field_simp
    rw [hdiv]
    exact hl.symm
  · rintro ⟨l, hl, hzl⟩
    refine ⟨l / a, hzl.symm, ?_⟩
    have hmul : a * (l / a) = l := by field_simp
    rw [hmul]
    exact hl.symm

/-- Principal-power inversion uses exactly those logarithms whose divided imaginary
part lies in the principal strip (4.2.36); both edges are retained. -/
@[dlmf 4.2.E36]
theorem mem_closedPowerValues_iff {z a w : ℂ} (hz : z ≠ 0) (ha : a ≠ 0)
    (hw : w ≠ 0) :
    w ∈ closedPowerValues z a ↔
      ∃ l ∈ generalLogValues w, |(l / a).im| ≤ Real.pi ∧ z = Complex.exp (l / a) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hdiv : a * l / a = l := by field_simp
    refine ⟨a * l, rfl, ?_, ?_⟩
    · simpa only [hdiv] using hl.2
    · rw [hdiv]; exact hl.1.symm
  · rintro ⟨l, hl, hstrip, hzl⟩
    refine ⟨l / a, ⟨hzl.symm, hstrip⟩, ?_⟩
    have hmul : a * (l / a) = l := by field_simp
    rw [hmul]
    exact hl.symm

/-- Closed square-root values at `z²` on the right half-plane (4.2.37). -/
@[dlmf 4.2.E37]
theorem sqrt_sq_closed_right {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ closedPowerValues (z ^ 2) (1 / 2) := by
  refine ⟨2 * Complex.log z, ⟨?_, ?_⟩, ?_⟩
  · simpa using (Complex.exp_nat_mul (Complex.log z) 2)
      |>.trans (by rw [Complex.exp_log hz])
  · have harg := (Complex.abs_arg_le_pi_div_two_iff).mpr hr
    have hi : (2 * Complex.log z).im = 2 * z.arg := by simp [Complex.mul_im, Complex.log_im]
    rw [hi, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    linarith
  · have heq : (1 / 2 : ℂ) * (2 * Complex.log z) = Complex.log z := by ring
    rw [heq, Complex.exp_log hz]

/-- Closed square-root values at `z²` on the left half-plane (4.2.37). -/
@[dlmf 4.2.E37]
theorem sqrt_sq_closed_left {z : ℂ} (hz : z ≠ 0) (hr : z.re ≤ 0) :
    -z ∈ closedPowerValues (z ^ 2) (1 / 2) := by
  have h := sqrt_sq_closed_right (z := -z) (neg_ne_zero.mpr hz) (by simpa using neg_nonneg.mpr hr)
  simpa only [neg_sq] using h

/-- The exponential maps horizontal lines to rays (4.3(ii), mathematical prose). -/
theorem exp_horizontal_image (y : ℝ) :
    (fun x : ℝ => Complex.exp (x + y * I)) '' univ =
      {w | ∃ r : ℝ, 0 < r ∧ w = r * Complex.exp (y * I)} := by
  ext w
  constructor
  · rintro ⟨x, _, rfl⟩
    refine ⟨Real.exp x, Real.exp_pos x, ?_⟩
    change Complex.exp ((x : ℂ) + (y : ℂ) * I) = _
    rw [Complex.exp_add, Complex.ofReal_exp]
  · rintro ⟨r, hr, rfl⟩
    refine ⟨Real.log r, Set.mem_univ _, ?_⟩
    change Complex.exp ((Real.log r : ℂ) + (y : ℂ) * I) = _
    rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hr]

/-- The exponential maps vertical lines to circles (4.3(ii), mathematical prose). -/
theorem exp_vertical_image (x : ℝ) :
    (fun y : ℝ => Complex.exp (x + y * I)) '' univ = Metric.sphere 0 (Real.exp x) := by
  ext w
  constructor
  · rintro ⟨y, _, rfl⟩
    simp only [Metric.mem_sphere, dist_zero_right, Complex.norm_exp]
    congr 1
    simp
  · intro hw
    have hn : ‖w‖ = Real.exp x := by simpa only [Metric.mem_sphere, dist_zero_right] using hw
    have hw0 : w ≠ 0 := by
      intro h; simpa [h] using hn.trans_gt (Real.exp_pos x)
    have hr : Real.log ‖w‖ = x := by rw [hn, Real.log_exp]
    refine ⟨w.arg, Set.mem_univ _, ?_⟩
    change Complex.exp ((x : ℂ) + (w.arg : ℂ) * I) = w
    calc
      Complex.exp ((x : ℂ) + (w.arg : ℂ) * I) = Complex.exp (Complex.log w) := by
        congr 1
        apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, hr]
      _ = w := Complex.exp_log hw0

/-- Principal powers of `e` are the complex exponential (4.2.32). -/
@[dlmf 4.2.E32]
theorem exp_one_cpow (a : ℂ) : (Complex.exp 1) ^ a = Complex.exp a := by
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
    Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le]), one_mul]

/-- The general power has one value exactly for integer exponents (4.2(iv), prose).
This records the nontrivial monodromy around the origin for every other exponent. -/
theorem generalPowerValues_subsingleton_iff {z : ℂ} (hz : z ≠ 0) (a : ℂ) :
    (generalPowerValues z a).Subsingleton ↔ ∃ n : ℤ, a = n := by
  sorry

/-- Every value of a logarithm exponentiates back to its argument (4.8.10). -/
@[dlmf 4.8.E10]
theorem exp_generalLog {z l : ℂ} (hl : l ∈ generalLogValues z) : Complex.exp l = z := hl

/-- General integer powers are single-valued, including exponent zero and negative integers. -/
@[dlmf 4.2.E27]
theorem generalPowerValues_int {z : ℂ} (hz : z ≠ 0) (n : ℤ) :
    generalPowerValues z (n : ℂ) = {z ^ n} := by
  ext w
  constructor
  · rintro ⟨l, hl, rfl⟩
    simp only [Set.mem_singleton_iff]
    rw [Complex.exp_int_mul, show Complex.exp l = z from hl]
  · intro hw
    have hw' : w = z ^ n := hw
    refine ⟨Complex.log z, Complex.exp_log hz, ?_⟩
    rw [Complex.exp_int_mul, Complex.exp_log hz]
    exact hw'


end DLMF.Elementary
