/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Contiguous
public import AAR.Hypergeometric.Continuation
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Elementary evaluations and special arguments (DLMF §15.4)

These are statement acquisitions; proofs marked `sorry` remain to be supplied.
Existing evaluations are in `Basic`, `DiffEq`, `EulerIntegral`, and `Identities`.
Powers use the principal complex logarithm. Trigonometric substitutions are stated
for real arguments, so their transformed arguments stay in the convergence disk.
Equations with removable quotients (E2, E5, E9, E10, E15, E16) are multiplied
through by their elementary denominators; thus they also hold at the removable points.
The unit-circle evaluations E33–E34 assume absolute convergence and exclude poles
of numerator Gamma factors; DLMF's broader continuation/limit interpretations are
not the totalized series definition in Mathlib.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology Nat

noncomputable section

namespace AAR.Hypergeometric

@[dlmf 15.4.E2]
theorem log_ratio {z : ℂ} (hz : ‖z‖ < 1) :
    2 * z * ₂F₁ (1 / 2 : ℂ) 1 (3 / 2) (z ^ 2) =
      log ((1 + z) / (1 - z)) := by
  have h := arctan_eq_ordinaryHypergeometric (x := -I * z) (by simpa using hz)
  have hi : -I * z * I = z := by
    calc
      _ = -(I * I) * z := by ring
      _ = z := by simp
  have hs : -((-I * z) ^ 2) = z ^ 2 := by simp [mul_pow, I_sq]
  rw [Complex.arctan, hi, hs] at h
  have hh := congrArg (fun w : ℂ => 2 * I * w) h
  ring_nf at hh
  simp only [I_sq] at hh
  convert hh.symm using 1 <;> ring

@[dlmf 15.4.E5]
theorem log_add_sqrt {z : ℂ} (hz : ‖z‖ < 1) :
    z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-z ^ 2) =
      log (z + (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  sorry

/-- Duplication for rising factorials: `(2a)_{2m} = 4^m (a)_m (a + 1/2)_m`. -/
lemma poch_two_mul_two_mul (a : ℂ) (m : ℕ) :
    poch (2 * a) (2 * m) = 4 ^ m * poch a m * poch (a + 1 / 2) m := by
  induction m with
  | zero => simp [poch_zero]
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ a,
      poch_succ (a + 1 / 2), pow_succ]
    push_cast
    ring

/-- Even part of a series: if `f` vanishes at odd indices, sum over even indices. -/
lemma hasSum_even_of_odd_eq_zero {f : ℕ → ℂ} {s : ℂ} (hf : HasSum f s)
    (hodd : ∀ m, f (2 * m + 1) = 0) : HasSum (fun m => f (2 * m)) s := by
  refine ((mul_right_injective₀ (two_ne_zero' ℕ)).hasSum_iff fun n hn => ?_).mpr hf
  obtain ⟨m, h | h⟩ := Nat.even_or_odd' n
  · exact absurd ⟨m, h.symm⟩ hn
  · rw [h]; exact hodd m

/-- Odd part of a series: if `f` vanishes at even indices, sum over odd indices. -/
lemma hasSum_odd_of_even_eq_zero {f : ℕ → ℂ} {s : ℂ} (hf : HasSum f s)
    (heven : ∀ m, f (2 * m) = 0) : HasSum (fun m => f (2 * m + 1)) s := by
  refine ((show Function.Injective (fun m : ℕ => 2 * m + 1) from fun a b h => by
    simp only at h; omega).hasSum_iff fun n hn => ?_).mpr hf
  obtain ⟨m, h | h⟩ := Nat.even_or_odd' n
  · rw [h]; exact heven m
  · exact absurd ⟨m, h.symm⟩ hn

@[dlmf 15.4.E7]
theorem even_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (z ^ 2) =
      ((1 + z) ^ (-2 * a) + (1 - z) ^ (-2 * a)) / 2 := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hf := hasSum_poch_div_factorial (β := 2 * a) hz
  have hg := hasSum_poch_div_factorial (β := 2 * a) hz'
  have hh := ((hf.add hg).div_const 2)
  have heven := hasSum_even_of_odd_eq_zero hh fun m => by
    rw [Odd.neg_pow ⟨m, rfl⟩]; ring
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hF := (hasFPowerSeriesOnBall_ordinaryHypergeometric a (a + 1 / 2) (1 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz2)
  have hfac : ∀ m : ℕ, ((2 * m) ! : ℂ) = 4 ^ m * poch (1 / 2) m * m ! := by
    intro m
    have := poch_two_mul_two_mul (1 / 2 : ℂ) m
    rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
      poch_nat_one, poch_nat_one] at this
    exact_mod_cast this
  refine hF.unique (heven.congr_fun fun m => ?_) |>.trans ?_
  · have h1 : ((2 * m) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : poch (1 / 2 : ℂ) m ≠ 0 := by
      intro h; apply h1; rw [hfac, h]; simp
    have h3 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    unfold gaussHGCoeff
    rw [Even.neg_pow ⟨m, by ring⟩, poch_two_mul_two_mul, hfac, pow_mul]
    field_simp
    ring
  · rw [sub_neg_eq_add, neg_mul]
    ring

/-- `|tan x| < 1` for `|x| < π/4`. -/
lemma abs_tan_lt_one {x : ℝ} (hx : |x| < π / 4) : |Real.tan x| < 1 := by
  have hpi := Real.pi_pos
  rw [abs_lt] at hx ⊢
  constructor
  · have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := -(π / 4)) (y := x) (by linarith)
      (by linarith) hx.1
    rwa [Real.tan_neg, Real.tan_pi_div_four] at this
  · have := Real.tan_lt_tan_of_lt_of_lt_pi_div_two (x := x) (y := π / 4) (by linarith)
      (by linarith) hx.2
    rwa [Real.tan_pi_div_four] at this

/-- For `|x| < π/2`, `(1 ± i tan x)^w = cos^{-w} x · e^{± i w x}`. -/
lemma one_add_I_tan_cpow {x : ℝ} (hx : |x| < π / 2) (s : ℝ) (hs : s = 1 ∨ s = -1) (w : ℂ) :
    (1 + s * I * Real.tan x) ^ w = (Real.cos x : ℂ) ^ (-w) * exp (s * I * x * w) := by
  have hpi := Real.pi_pos
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1],
    (abs_lt.mp hx).2⟩
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hcC : Complex.cos (x : ℂ) ≠ 0 := by rw [← ofReal_cos]; exact hc'
  have hlog : log (Real.cos x : ℂ) = Real.log (Real.cos x) := (ofReal_log hc.le).symm
  have key : (1 : ℂ) + s * I * Real.tan x = exp (s * I * x - Real.log (Real.cos x)) := by
    rw [exp_sub, ← hlog, exp_log hc', Real.tan_eq_sin_div_cos]
    rcases hs with rfl | rfl
    · rw [show ((1 : ℝ) : ℂ) * I * x = x * I by push_cast; ring, exp_mul_I]
      push_cast; field_simp
    · rw [show ((-1 : ℝ) : ℂ) * I * x = (-x : ℂ) * I by push_cast; ring, exp_mul_I, cos_neg,
        sin_neg]
      push_cast; field_simp
  have him : (s * I * x - Real.log (Real.cos x) : ℂ).im = s * x := by simp
  rw [key, cpow_def_of_ne_zero (exp_ne_zero _), log_exp, cpow_def_of_ne_zero hc', hlog,
    ← exp_add]
  · congr 1; ring
  · rw [him]; rcases hs with rfl | rfl <;> simp <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]
  · rw [him]; rcases hs with rfl | rfl <;> simp <;> linarith [(abs_lt.mp hx).1, (abs_lt.mp hx).2]

@[dlmf 15.4.E8]
theorem tan_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    ₂F₁ a (a + 1 / 2) (1 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * cos (2 * a * x) := by
  have hx2 : |x| < π / 2 := by linarith [Real.pi_pos]
  have hz : ‖I * Real.tan x‖ < 1 := by
    rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]; exact abs_tan_lt_one hx
  have h := even_binomial a hz
  rw [mul_pow, I_sq, neg_one_mul] at h
  rw [h, show (1 : ℂ) + I * Real.tan x = 1 + ((1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    show (1 : ℂ) - I * Real.tan x = 1 + ((-1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    one_add_I_tan_cpow hx2 1 (Or.inl rfl), one_add_I_tan_cpow hx2 (-1) (Or.inr rfl),
    Complex.cos]
  push_cast
  ring_nf

@[dlmf 15.4.E9]
theorem odd_binomial (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (a + 1 / 2) (3 / 2) (z ^ 2) =
      (1 + z) ^ (1 - 2 * a) - (1 - z) ^ (1 - 2 * a) := by
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hf := hasSum_poch_div_factorial (β := 2 * a - 1) hz
  have hg := hasSum_poch_div_factorial (β := 2 * a - 1) hz'
  have hh := hg.sub hf
  have hodd := hasSum_odd_of_even_eq_zero hh fun m => by
    rw [Even.neg_pow ⟨m, by ring⟩]; ring
  have hz2 : ‖z ^ 2‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg z) hz (by norm_num)
  have hF := ((hasFPowerSeriesOnBall_ordinaryHypergeometric a (a + 1 / 2) (3 / 2)).hasSum_mul_pow
    (mem_eball_one_of_norm_lt_one hz2)).mul_left ((2 - 4 * a) * z)
  have hfac : ∀ m : ℕ, ((2 * m + 1) ! : ℂ) = 4 ^ m * poch (3 / 2) m * m ! := by
    intro m
    have := poch_two_mul_two_mul (1 : ℂ) m
    rw [mul_one, poch_nat_two, show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num, poch_nat_one] at this
    linear_combination this
  refine hF.unique (hodd.congr_fun fun m => ?_) |>.trans ?_
  · have h1 : ((2 * m + 1) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h2 : poch (3 / 2 : ℂ) m ≠ 0 := by
      intro h; apply h1; rw [hfac, h]; simp
    have h3 : (m ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    unfold gaussHGCoeff
    rw [Odd.neg_pow ⟨m, rfl⟩, show 2 * m + 1 = 1 + 2 * m by ring, poch_add, poch_one,
      show 2 * a - 1 + (1 : ℕ) = 2 * a by push_cast; ring, poch_two_mul_two_mul,
      show 1 + 2 * m = 2 * m + 1 by ring, hfac, pow_succ z (2 * m), pow_mul z 2 m]
    field_simp
    ring
  · rw [sub_neg_eq_add, show -(2 * a - 1) = 1 - 2 * a by ring]

@[dlmf 15.4.E10]
theorem tan_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 4) :
    (1 - 2 * a) * (Real.sin x : ℂ) * ₂F₁ a (a + 1 / 2) (3 / 2) (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2 * a) * x) := by
  have hpi := Real.pi_pos
  have hx2 : |x| < π / 2 := by linarith
  have hc : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx2).1],
    (abs_lt.mp hx2).2⟩
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hc.ne'
  have hz : ‖I * Real.tan x‖ < 1 := by
    rw [norm_mul, norm_I, one_mul, norm_real, Real.norm_eq_abs]; exact abs_tan_lt_one hx
  have h := odd_binomial a hz
  rw [mul_pow, I_sq, neg_one_mul,
    show (1 : ℂ) + I * Real.tan x = 1 + ((1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    show (1 : ℂ) - I * Real.tan x = 1 + ((-1 : ℝ) : ℂ) * I * Real.tan x by push_cast; ring,
    one_add_I_tan_cpow hx2 1 (Or.inl rfl), one_add_I_tan_cpow hx2 (-1) (Or.inr rfl)] at h
  have hpow : (Real.cos x : ℂ) ^ (2 * a) = (Real.cos x : ℂ) ^ (-(1 - 2 * a)) * Real.cos x := by
    have := cpow_add (x := (Real.cos x : ℂ)) (-(1 - 2 * a)) 1 hc'
    rwa [cpow_one, show -(1 - 2 * a) + 1 = 2 * a by ring] at this
  have ht : (Real.sin x : ℂ) = Real.tan x * Real.cos x := by
    have hcC : Complex.cos (x : ℂ) ≠ 0 := by rw [← ofReal_cos]; exact hc'
    rw [Real.tan_eq_sin_div_cos]; push_cast; field_simp
  rw [show ((1 : ℝ) : ℂ) * I * x * (1 - 2 * a) = (1 - 2 * a) * x * I by push_cast; ring,
    show ((-1 : ℝ) : ℂ) * I * x * (1 - 2 * a) = -((1 - 2 * a) * x) * I by push_cast; ring] at h
  rw [hpow, ht, Complex.sin]
  linear_combination ((Real.cos x : ℂ) * (-I) / 2) * h +
    ((1 - 2 * a) * Real.tan x * Real.cos x * ₂F₁ a (a + 1 / 2) (3 / 2) (-(Real.tan x : ℂ) ^ 2)) *
      I_sq

@[dlmf 15.4.E11]
theorem opposite_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ (-a) a (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a)) / 2 := by
  sorry

/-- Restriction of a complex-analytic function to the real line is real-analytic. -/
lemma analyticAt_comp_ofReal {f : ℂ → ℂ} {x0 : ℝ} (hf : AnalyticAt ℂ f x0) :
    AnalyticAt ℝ (fun x : ℝ => f x) x0 :=
  (hf.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt x0)

/-- `x ↦ ₂F₁(a,b;c;sin² x)` is real-analytic on `(-π/2, π/2)`. -/
lemma analyticAt_ordinaryHypergeometric_sin_sq (a b c : ℂ) {x0 : ℝ} (hx : |x0| < π / 2) :
    AnalyticAt ℝ (fun x : ℝ => ₂F₁ a b c ((Real.sin x : ℂ) ^ 2)) x0 := by
  have h : ‖((Real.sin x0 : ℂ)) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x0]
    have : 0 < Real.cos x0 := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1],
      (abs_lt.mp hx).2⟩
    nlinarith
  have hF : AnalyticAt ℂ (₂F₁ a b c) (sin (x0 : ℂ) ^ 2) :=
    (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).analyticAt_of_mem
      (by rw [← ofReal_sin]; simpa using mem_eball_one_of_norm_lt_one h)
  have hG : AnalyticAt ℂ (fun w : ℂ => ₂F₁ a b c (sin w ^ 2)) x0 :=
    hF.comp (f := fun w : ℂ => sin w ^ 2) (by fun_prop)
  simpa [ofReal_sin] using analyticAt_comp_ofReal hG

/-- Positive real bases: `r^w = exp (log r * w)`. -/
lemma ofReal_cpow_eq_exp {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (r : ℂ) ^ w = exp ((Real.log r : ℂ) * w) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr.ne'), ofReal_log hr.le]

/-- Extension from `|x| < π/4` to `|x| < π/2` of an identity between real-analytic
functions. -/
lemma eq_of_analytic_of_abs_lt_pi_div_four {f g : ℝ → ℂ}
    (hf : ∀ x, |x| < π / 2 → AnalyticAt ℝ f x) (hg : ∀ x, |x| < π / 2 → AnalyticAt ℝ g x)
    (h : ∀ x, |x| < π / 4 → f x = g x) {x : ℝ} (hx : |x| < π / 2) : f x = g x := by
  have hpi := Real.pi_pos
  have hU : ∀ y ∈ Set.Ioo (-(π / 2)) (π / 2), |y| < π / 2 := fun y hy => abs_lt.mpr hy
  have hfg : AnalyticOnNhd ℝ (f - g) (Set.Ioo (-(π / 2)) (π / 2)) := fun y hy =>
    (hf y (hU y hy)).sub (hg y (hU y hy))
  have h0 : (f - g) =ᶠ[𝓝 0] 0 := by
    filter_upwards [Ioo_mem_nhds (show -(π / 4) < 0 by linarith) (show (0 : ℝ) < π / 4 by
      linarith)] with y hy
    simp [h y (abs_lt.mpr hy)]
  have := hfg.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Ioo
    ⟨by linarith, by linarith⟩ h0 (abs_lt.mp hx)
  simpa [sub_eq_zero] using this

/-- Pfaff's transformation at `z = -tan² x`: for `|x| < π/4`,
`₂F₁(a,b;c;-tan² x) = cos^{2a} x · ₂F₁(a,c-b;c;sin² x)`. -/
lemma ordinaryHypergeometric_neg_tan_sq (a b : ℂ) {c : ℂ} (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) {x : ℝ}
    (hx : |x| < π / 4) :
    ₂F₁ a b c (-((Real.tan x : ℂ) ^ 2)) =
      (Real.cos x : ℂ) ^ (2 * a) * ₂F₁ a (c - b) c ((Real.sin x : ℂ) ^ 2) := by
  have hpi := Real.pi_pos
  have hx2 : |x| < π / 2 := by linarith
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx2).1],
    (abs_lt.mp hx2).2⟩
  have ht := abs_tan_lt_one hx
  have hz : ‖-((Real.tan x : ℂ) ^ 2)‖ < 1 := by
    rw [norm_neg, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
    exact (sq_lt_one_iff_abs_lt_one _).mpr ht
  have hsin : -((Real.tan x : ℂ) ^ 2) / (-((Real.tan x : ℂ) ^ 2) - 1) =
      (Real.sin x : ℂ) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcx.ne'
    have hsum : (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq x
    have hd : -((Real.sin x : ℂ) / Real.cos x) ^ 2 - 1 ≠ 0 := by
      rw [div_pow]; field_simp
      rw [show -(Real.sin x : ℂ) ^ 2 - (Real.cos x : ℂ) ^ 2 = -1 by linear_combination -hsum]
      exact div_ne_zero (by norm_num) (pow_ne_zero 2 hc')
    rw [ofReal_div, div_eq_iff hd]
    field_simp
    linear_combination (Real.sin x : ℂ) ^ 2 * hsum
  have hzt : ‖-((Real.tan x : ℂ) ^ 2) / (-((Real.tan x : ℂ) ^ 2) - 1)‖ < 1 := by
    rw [hsin, norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x]
    nlinarith
  have hP := pfaff_transformation_of_ne_neg_nat (a := a) (b := b) hc hz hzt
  rw [hsin] at hP
  have h1t : (1 : ℂ) - -((Real.tan x : ℂ) ^ 2) = ((1 + Real.tan x ^ 2 : ℝ) : ℂ) := by
    push_cast; ring
  have hpos : 0 < 1 + Real.tan x ^ 2 := by positivity
  have hcos : (Real.cos x : ℂ) ^ (2 * a) = ((1 + Real.tan x ^ 2 : ℝ) : ℂ) ^ (-a) := by
    rw [ofReal_cpow_eq_exp hcx, ofReal_cpow_eq_exp hpos, ← inv_inv (1 + Real.tan x ^ 2),
      Real.inv_one_add_tan_sq hcx.ne', Real.log_inv, Real.log_pow]
    push_cast; ring_nf
  rw [hP, h1t, hcos]

@[dlmf 15.4.E12]
theorem sin_sq_cos (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ (-a) a (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos (2 * a * x) := by
  refine eq_of_analytic_of_abs_lt_pi_div_four (f := fun x : ℝ => ₂F₁ (-a) a (1 / 2)
    ((Real.sin x : ℂ) ^ 2)) (g := fun x : ℝ => cos (2 * a * x))
    (fun x hx => analyticAt_ordinaryHypergeometric_sin_sq _ _ _ hx)
    (fun x _ => analyticAt_comp_ofReal (f := fun w => cos (2 * a * w)) (by fun_prop))
    (fun x hx => ?_) hx
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hP := ordinaryHypergeometric_neg_tan_sq a (a + 1 / 2) hc hx
  rw [tan_cos a hx, show (1 / 2 : ℂ) - (a + 1 / 2) = -a by ring,
    ordinaryHypergeometric_symm] at hP
  exact (mul_left_cancel₀ (by rw [ofReal_cpow_eq_exp hcx]; exact exp_ne_zero _) hP).symm

@[dlmf 15.4.E13]
theorem complementary_parameters_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    ₂F₁ a (1 - a) (1 / 2) (-z ^ 2) =
      (((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (2 * a - 1) + ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (2 * a - 1)) / (2 *
        (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  sorry

@[dlmf 15.4.E14]
theorem sin_sq_cos_quotient (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    ₂F₁ a (1 - a) (1 / 2) ((Real.sin x : ℂ) ^ 2) =
      cos ((2 * a - 1) * x) / (Real.cos x : ℂ) := by
  have hc : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hz : ‖(Real.sin x : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, norm_real, Real.norm_eq_abs, sq_abs, ← Real.cos_sq_add_sin_sq x]
    nlinarith
  rw [euler_transformation_of_ne_neg_nat hc hz, show (1 / 2 : ℂ) - a = -(a - 1 / 2) by ring,
    show (1 / 2 : ℂ) - (1 - a) = a - 1 / 2 by ring, sin_sq_cos (a - 1 / 2) hx,
    show -(a - 1 / 2) - (1 - a) = -(1 / 2 : ℂ) by ring,
    show 2 * (a - 1 / 2) = 2 * a - 1 by ring,
    show (1 : ℂ) - (Real.sin x : ℂ) ^ 2 = ((Real.cos x ^ 2 : ℝ) : ℂ) by
      rw [ofReal_pow]; linear_combination -(by exact_mod_cast Real.sin_sq_add_cos_sq x :
        (Real.sin x : ℂ) ^ 2 + (Real.cos x : ℂ) ^ 2 = 1),
    ofReal_cpow_eq_exp (by positivity), Real.log_pow]
  have hc' : (Real.cos x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hcx.ne'
  rw [show ((((2 : ℕ) : ℝ) * Real.log (Real.cos x) : ℝ) : ℂ) * -(1 / 2) =
    -(Real.log (Real.cos x) : ℂ) by push_cast; ring, exp_neg, ofReal_log hcx.le,
    exp_log hc']
  ring

@[dlmf 15.4.E15]
theorem complementary_parameters_odd_sqrt (a : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    (2 - 4 * a) * z * ₂F₁ a (1 - a) (3 / 2) (-z ^ 2) =
      ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ (1 - 2 * a) - ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ (1 - 2 * a) := by
  sorry

@[dlmf 15.4.E16]
theorem sin_sq_sin (a : ℂ) {x : ℝ} (hx : |x| < Real.pi / 2) :
    (2 * a - 1) * (Real.sin x : ℂ) * ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2) =
      sin ((2 * a - 1) * x) := by
  have hsinA : ∀ x : ℝ, AnalyticAt ℝ (fun x : ℝ => (Real.sin x : ℂ)) x := fun x => by
    simpa [ofReal_sin] using analyticAt_comp_ofReal (f := Complex.sin) (x0 := x) (by fun_prop)
  refine eq_of_analytic_of_abs_lt_pi_div_four (f := fun x : ℝ => (2 * a - 1) * (Real.sin x : ℂ) *
    ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2)) (g := fun x : ℝ => sin ((2 * a - 1) * x))
    (fun x hx => (analyticAt_const.mul (hsinA x)).mul
      (analyticAt_ordinaryHypergeometric_sin_sq _ _ _ hx))
    (fun x _ => analyticAt_comp_ofReal (f := fun w => sin ((2 * a - 1) * w)) (by fun_prop))
    (fun x hx => ?_) hx
  have hc : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hcx : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [(abs_lt.mp hx).1,
    Real.pi_pos], by linarith [(abs_lt.mp hx).2, Real.pi_pos]⟩
  have hP := ordinaryHypergeometric_neg_tan_sq a (a + 1 / 2) hc hx
  have hT := tan_sin a hx
  rw [hP, show (3 / 2 : ℂ) - (a + 1 / 2) = 1 - a by ring] at hT
  have hne : (Real.cos x : ℂ) ^ (2 * a) ≠ 0 := by
    rw [ofReal_cpow_eq_exp hcx]; exact exp_ne_zero _
  have h := mul_left_cancel₀ hne (show (Real.cos x : ℂ) ^ (2 * a) *
    ((1 - 2 * a) * (Real.sin x : ℂ) * ₂F₁ a (1 - a) (3 / 2) ((Real.sin x : ℂ) ^ 2)) =
    (Real.cos x : ℂ) ^ (2 * a) * sin ((1 - 2 * a) * x) by rw [← hT]; ring)
  rw [show (2 * a - 1) * (x : ℂ) = -((1 - 2 * a) * x) by ring, Complex.sin_neg]
  linear_combination -h

@[dlmf 15.4.E17]
theorem quadratic_binomial {a z : ℂ} (hc : ∀ k : ℕ, 1 + 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (1 + 2 * a) z =
      ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (-2 * a) := by
  sorry

@[dlmf 15.4.E18]
theorem quadratic_binomial_derivative {a z : ℂ} (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (2 * a) z =
      (1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (1 - 2 * a) := by
  sorry

@[dlmf 15.4.E19]
theorem successor_binomial {a b z : ℂ} (ha : ∀ k : ℕ, a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ (a + 1) b a z =
      (1 - (1 - b / a) * z) * (1 - z) ^ (-1 - b) := by
  have ha0 : a ≠ 0 := by simpa using ha 0
  have ha1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := by simpa using not_neg_nat_add_nat ha 1
  have h := contiguous_shift_b (a := b) (b := a) ha hz
  have hsymm : ₂F₁ b (a + 1) a z = ₂F₁ (a + 1) b a z := by
    unfold ordinaryHypergeometric
    rw [ordinaryHypergeometricSeries_symm]
  rw [hsymm, ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha k (neg_eq_iff_eq_neg.mp hk.symm)) hz,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk => ha1 k (neg_eq_iff_eq_neg.mp hk.symm)) hz] at h
  have hz1 : z ≠ 1 := by intro he; simp [he] at hz
  have hp : (1 - z) ^ (-b) = (1 - z) * (1 - z) ^ (-1 - b) := by
    calc
      _ = (1 - z) ^ ((1 : ℂ) + (-1 - b)) := by congr 1; ring
      _ = _ := by rw [cpow_add _ _ (sub_ne_zero.mpr hz1.symm), cpow_one]
  rw [hp, show -(b + 1) = -1 - b by ring] at h
  apply mul_left_cancel₀ ha0
  field_simp [ha0]
  linear_combination -h

@[dlmf 15.4.E28]
theorem gauss_second_summation {a b : ℂ} (hc : ∀ k : ℕ, (a + b + 1) / 2 ≠ -(k : ℂ)) :
    ₂F₁ a b ((a + b + 1) / 2) (1 / 2) =
      (Real.sqrt Real.pi : ℂ) * Gamma ((a + b + 1) / 2) / (Gamma ((a + 1) / 2) * Gamma ((b + 1) / 2)) := by
  sorry

@[dlmf 15.4.E29]
theorem gauss_second_summation_contiguous
    {a b : ℂ}
    (hc : ∀ k : ℕ,
    (a + b) / 2 + 1 ≠ -(k : ℂ))
    (hab : a ≠ b) :
    ₂F₁ a b ((a + b) / 2 + 1) (1 / 2) =
      2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma ((a + b) / 2 + 1) * (1 / (Gamma (a / 2) * Gamma ((b + 1)
        / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) := by
  sorry

@[dlmf 15.4.E30]
theorem bailey_summation {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) :
    ₂F₁ a (1 - a) b (1 / 2) =
      (2 : ℂ) ^ (1 - b) * (Real.sqrt Real.pi : ℂ) * Gamma b / (Gamma ((a + b) / 2) * Gamma ((b - a + 1) /
        2)) := by
  sorry

@[dlmf 15.4.E31]
theorem value_neg_one_third {a : ℂ} (hc : ∀ k : ℕ, 3 / 2 - 2 * a ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (3 / 2 - 2 * a) (-1 / 3) =
      (8 / 9 : ℂ) ^ (-2 * a) * Gamma (4 / 3) * Gamma (3 / 2 - 2 * a) / (Gamma (3 / 2) * Gamma (4 / 3 - 2 *
        a)) := by
  sorry

@[dlmf 15.4.E32]
theorem value_one_ninth {a : ℂ} (hc : ∀ k : ℕ, 5 / 6 + 2 * a / 3 ≠ -(k : ℂ)) :
    ₂F₁ a (a + 1 / 2) (5 / 6 + 2 * a / 3) (1 / 9) =
      (Real.sqrt Real.pi : ℂ) * (3 / 4 : ℂ) ^ a * Gamma (5 / 6 + 2 * a / 3) / (Gamma (1 / 2 + a / 3) * Gamma
        (5 / 6 + a / 3)) := by
  sorry

@[dlmf 15.4.E33]
theorem value_sixth_root
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 / 3 + 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 1 / 6)
    (hg : ∀ k : ℕ, 5 / 6 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) (1 / 3 + a) (2 / 3 + 2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (16 / 27 : ℂ) ^ ((3 * a + 1) / 6) * Gamma (5 / 6
        + a) / (Gamma (2 / 3 + a) * Gamma (2 / 3)) := by
  sorry

@[dlmf 15.4.E34]
theorem value_sixth_root_contiguous
    {a : ℂ}
    (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ))
    (hconv : a.re < 0)
    (hg : ∀ k : ℕ, 1 / 2 + a ≠ -(k : ℂ)) :
    ₂F₁ (3 * a) a (2 * a) (exp (I * Real.pi / 3)) =
      (Real.sqrt Real.pi : ℂ) * exp (I * Real.pi * a / 2) * (2 : ℂ) ^ (2 * a) * Gamma (1 / 2 + a) / (3 : ℂ)
        ^ ((3 * a + 1) / 2) * (1 / (Gamma (1 / 3 + a) * Gamma (2 / 3)) + 1 / (Gamma (2 / 3 + a) * Gamma (1 /
        3))) := by
  sorry

@[dlmf 15.4.E27]
theorem half_argument_digamma {a : ℂ} (ha : 0 < a.re) :
    (2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2) =
      a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) := by
  sorry

/-- Ordered partial sums are essential here: the series is only conditionally convergent. -/
@[dlmf 15.4.E27]
theorem alternating_digamma {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k) atTop
      (𝓝 (a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)))) := by
  sorry

end AAR.Hypergeometric
