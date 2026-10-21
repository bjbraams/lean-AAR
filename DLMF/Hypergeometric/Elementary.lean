/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Hypergeometric.Contiguous
public import DLMF.Hypergeometric.Continuation
public import DLMF.Hypergeometric.FurtherTransformations
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import DLMF.Gamma.Digamma
public import DLMF.Gamma.SpecialValues

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
open scoped Real Topology Nat ComplexConjugate

noncomputable section

namespace DLMF.Hypergeometric

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

/-- Principal powers of right-half-plane numbers are multiplicative. -/
lemma cpow_mul_cpow_of_re_pos {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) (s : ℂ) :
    x ^ s * y ^ s = (x * y) ^ s := by
  have hx0 : x ≠ 0 := by rintro rfl; simp at hx
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy
  have hax := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hx))
  have hay := abs_lt.mp (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hy))
  rw [cpow_def_of_ne_zero hx0, cpow_def_of_ne_zero hy0, cpow_def_of_ne_zero (mul_ne_zero hx0 hy0),
    log_mul hx0 hy0 ⟨by linarith, by linarith⟩, ← exp_add]
  ring_nf

/-- The square root `r = √(1+z²)` on the unit disk, with `u = r + z`, `v = r - z`, `uv = 1`. -/
lemma sqrt_one_add_sq_data {z : ℂ} (hz : ‖z‖ < 1) :
    0 < (1 + z ^ 2).re ∧ 0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ)).re ∧
      ((1 + z ^ 2) ^ (1 / 2 : ℂ)) ^ 2 = 1 + z ^ 2 ∧
      ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z) * ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z) = 1 ∧
      0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ) + z).re ∧ 0 < ((1 + z ^ 2) ^ (1 / 2 : ℂ) - z).re := by
  have hw : 0 < (1 + z ^ 2).re := by
    have h1 := neg_le_of_abs_le (abs_re_le_norm (z ^ 2))
    rw [norm_pow] at h1
    have h2 : ‖z‖ ^ 2 < 1 := by nlinarith [norm_nonneg z]
    simp only [add_re, one_re]; linarith
  have hw0 : 1 + z ^ 2 ≠ 0 := by intro h; rw [h] at hw; simp at hw
  set r := (1 + z ^ 2) ^ (1 / 2 : ℂ) with hr
  have hrre : 0 < r.re := re_cpow_half_pos hw
  have hrsq : r ^ 2 = 1 + z ^ 2 := cpow_half_sq hw0
  have huv : (r + z) * (r - z) = 1 := by linear_combination hrsq
  have hu0 : r + z ≠ 0 := by intro h; rw [h, zero_mul] at huv; exact zero_ne_one huv
  have hv : r - z = (r + z)⁻¹ := eq_inv_of_mul_eq_one_right huv
  have hsum : (r + z).re + (r - z).re = 2 * r.re := by simp; ring
  have hns : 0 < normSq (r + z) := normSq_pos.mpr hu0
  have hvre : (r - z).re = (r + z).re / normSq (r + z) := by rw [hv, inv_re]
  have hure : 0 < (r + z).re := by
    by_contra h
    push Not at h
    have : (r - z).re ≤ 0 := by rw [hvre]; exact div_nonpos_of_nonpos_of_nonneg h hns.le
    linarith
  exact ⟨hw, hrre, hrsq, huv, hure, by rw [hvre]; positivity⟩

@[dlmf 15.4.E5]
theorem log_add_sqrt {z : ℂ} (hz : ‖z‖ < 1) :
    z * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-z ^ 2) =
      log (z + (1 + z ^ 2) ^ (1 / 2 : ℂ)) := by
  have hc32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set f : ℂ → ℂ := fun w => w * ₂F₁ (1 / 2 : ℂ) (1 / 2) (3 / 2) (-w ^ 2) with hf
  set g : ℂ → ℂ := fun w => log (w + (1 + w ^ 2) ^ (1 / 2 : ℂ)) with hg
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  have hfd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt f ((1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
    intro w hw
    have hF := hasDerivAt_ordinaryHypergeometric (a := (1 / 2 : ℂ)) (b := 1 / 2) hc32 (hdisk w hw)
    have hsq : HasDerivAt (fun w : ℂ => -w ^ 2) (-(2 * w)) w :=
      (hasDerivAt_pow 2 w).neg.congr_deriv (by simp)
    refine ((hasDerivAt_id w).mul (hF.comp w hsq)).congr_deriv ?_
    have hid := ordinaryHypergeometric_arcsin_ident (hdisk w hw)
    rw [show (1 : ℂ) - -w ^ 2 = 1 + w ^ 2 by ring] at hid
    rw [← hid, show (1 / 2 + 1 : ℂ) = 3 / 2 by norm_num, show (3 / 2 + 1 : ℂ) = 5 / 2 by norm_num]
    simp only [id, Function.comp_apply, ordinaryHypergeometric]
    ring
  have hgd : ∀ w : ℂ, ‖w‖ < 1 → HasDerivAt g ((1 + w ^ 2) ^ (-(1 / 2 : ℂ))) w := by
    intro w hw
    obtain ⟨hre, hrre, -, -, hu, -⟩ := sqrt_one_add_sq_data hw
    have hslit : 1 + w ^ 2 ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl hre)
    have hr0 : (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    have hu0 : w + (1 + w ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by
      intro h; rw [add_comm] at h; rw [h] at hu; simp at hu
    have hr := ((hasDerivAt_const w (1 : ℂ)).add ((hasDerivAt_id w).pow 2)).cpow_const
      (c := (1 / 2 : ℂ)) hslit
    have hu' := ((hasDerivAt_id w).add hr).clog
      (by rw [add_comm]; exact mem_slitPlane_iff.mpr (Or.inl hu))
    refine hu'.congr_deriv ?_
    simp only [id, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl,
      pow_one, zero_add]
    rw [show (1 / 2 : ℂ) - 1 = -(1 / 2) by norm_num, cpow_neg]
    field_simp
    ring
  have hdiff : DifferentiableOn ℂ (fun w => f w - g w) (Metric.ball 0 1) := fun w hw =>
    (((hfd w (by simpa using hw)).sub (hgd w (by simpa using hw))).differentiableAt).differentiableWithinAt
  have hderiv : Set.EqOn (deriv (fun w => f w - g w)) 0 (Metric.ball 0 1) := by
    intro w hw
    have hw' : ‖w‖ < 1 := by simpa using hw
    have h' : HasDerivAt (fun w => f w - g w) _ w := (hfd w hw').sub (hgd w hw')
    rw [h'.deriv, sub_self, Pi.zero_apply]
  have h0 := Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) 1).isPreconnected
    hdiff hderiv (x := z) (y := 0) (by simpa using hz) (by simp)
  simp only [hf, hg, zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, one_cpow, log_one, sub_zero] at h0
  exact sub_eq_zero.mp h0

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
  set r : ℂ → ℂ := fun z => (1 + z ^ 2) ^ (1 / 2 : ℂ) with hrdef
  have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  -- Near the origin: Pfaff's transformation and the even binomial evaluation.
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 2), ₂F₁ (-a) a (1 / 2) (-w ^ 2) =
      ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2 := by
    intro w hw
    have hw' : ‖w‖ < 1 / 2 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    obtain ⟨hre, hrre, hrsq, -, -, -⟩ := sqrt_one_add_sq_data hw1
    show _ = (((1 + w ^ 2) ^ (1 / 2 : ℂ) + w) ^ (2 * a) +
      ((1 + w ^ 2) ^ (1 / 2 : ℂ) - w) ^ (2 * a)) / 2
    set R := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hR
    have hr0 : R ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    set t := w / R with htdef
    have h1w2 : 1 + w ^ 2 ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have ht2 : t ^ 2 = w ^ 2 / (1 + w ^ 2) := by rw [htdef, div_pow, hrsq]
    have hn1 : 3 / 4 ≤ ‖1 + w ^ 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(w ^ 2))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this
      nlinarith [norm_nonneg w]
    have ht2n : ‖t ^ 2‖ < 1 := by
      rw [ht2, norm_div, norm_pow, div_lt_one (by linarith)]
      nlinarith [norm_nonneg w]
    have htn : ‖t‖ < 1 := by
      rw [norm_pow] at ht2n
      nlinarith [norm_nonneg t]
    have hpf : -w ^ 2 / (-w ^ 2 - 1) = t ^ 2 := by
      rw [ht2]
      have : -w ^ 2 - 1 = -(1 + w ^ 2) := by ring
      rw [this]; field_simp
    have h1p : 0 < (1 + t).re := by
      have := neg_le_of_abs_le (abs_re_le_norm t); simp; linarith
    have h1m : 0 < (1 - t).re := by
      have := re_le_norm t; simp; linarith
    rw [pfaff_transformation_of_ne_neg_nat hc12 (hdisk w hw1) (by rw [hpf]; exact ht2n), hpf,
      show (1 / 2 : ℂ) - a = -a + 1 / 2 by ring, even_binomial (-a) htn,
      show -(-a) = a by ring, show -2 * -a = 2 * a by ring,
      show (1 : ℂ) - -w ^ 2 = R ^ 2 by rw [hrsq]; ring, sq_cpow hrre]
    have e1 : R ^ (2 * a) * (1 + t) ^ (2 * a) = (R + w) ^ (2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1p, htdef]; congr 1; field_simp
    have e2 : R ^ (2 * a) * (1 - t) ^ (2 * a) = (R - w) ^ (2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1m, htdef]; congr 1; field_simp
    rw [← e1, ← e2]
    ring
  -- Continuation over the unit disk.
  have hLan : AnalyticOnNhd ℂ (fun w : ℂ => ₂F₁ (-a) a (1 / 2) (-w ^ 2)) (Metric.ball 0 1) :=
    fun w hw => (analyticAt_ordinaryHypergeometric (hdisk w (by simpa using hw))).comp
      (f := fun w : ℂ => -w ^ 2) (analyticAt_id.pow 2).neg
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2)
      (Metric.ball 0 1) := by
    intro w hw
    obtain ⟨hre, -, -, -, hu, hv⟩ := sqrt_one_add_sq_data (by simpa using hw : ‖w‖ < 1)
    have hra : AnalyticAt ℂ r w :=
      (analyticAt_const.add (analyticAt_id.pow 2)).cpow analyticAt_const
        (mem_slitPlane_iff.mpr (Or.inl hre))
    exact (((hra.add analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hu))).add
      ((hra.sub analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hv)))).div
      analyticAt_const two_ne_zero
  have hev : (fun w : ℂ => ₂F₁ (-a) a (1 / 2) (-w ^ 2)) =ᶠ[𝓝 0]
      fun w => ((r w + w) ^ (2 * a) + (r w - w) ^ (2 * a)) / 2 := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan (convex_ball 0 1).isPreconnected
    (by simp) hev (by simpa using hz)

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
  have hc12 : ∀ k : ℕ, (1 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hx : ‖-z ^ 2‖ < 1 := by rw [norm_neg, norm_pow]; nlinarith [norm_nonneg z]
  obtain ⟨hre, hrre, -, -, -, -⟩ := sqrt_one_add_sq_data hz
  have hr0 : (1 + z ^ 2) ^ (1 / 2 : ℂ) ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
  have h := opposite_parameters_sqrt (a - 1 / 2) hz
  rw [show -(a - 1 / 2) = 1 / 2 - a by ring, show 2 * (a - 1 / 2) = 2 * a - 1 by ring] at h
  rw [euler_transformation_of_ne_neg_nat hc12 hx, show (1 / 2 : ℂ) - a - (1 - a) = -(1 / 2) by ring,
    show (1 / 2 : ℂ) - (1 - a) = a - 1 / 2 by ring, h, show (1 : ℂ) - -z ^ 2 = 1 + z ^ 2 by ring,
    cpow_neg]
  field_simp

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
  set r : ℂ → ℂ := fun z => (1 + z ^ 2) ^ (1 / 2 : ℂ) with hrdef
  have hc32 : ∀ k : ℕ, (3 / 2 : ℂ) ≠ -(k : ℂ) := fun k h => by
    have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hdisk : ∀ w : ℂ, ‖w‖ < 1 → ‖-w ^ 2‖ < 1 := fun w hw => by
    rw [norm_neg, norm_pow]; nlinarith [norm_nonneg w]
  have hball : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 2), (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2) =
      (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a) := by
    intro w hw
    have hw' : ‖w‖ < 1 / 2 := by simpa using hw
    have hw1 : ‖w‖ < 1 := by linarith
    obtain ⟨hre, hrre, hrsq, -, -, -⟩ := sqrt_one_add_sq_data hw1
    show _ = ((1 + w ^ 2) ^ (1 / 2 : ℂ) + w) ^ (1 - 2 * a) -
      ((1 + w ^ 2) ^ (1 / 2 : ℂ) - w) ^ (1 - 2 * a)
    set R := (1 + w ^ 2) ^ (1 / 2 : ℂ) with hR
    have hr0 : R ≠ 0 := by intro h; rw [h] at hrre; simp at hrre
    set t := w / R with htdef
    have h1w2 : 1 + w ^ 2 ≠ 0 := by intro h; rw [h] at hre; simp at hre
    have ht2 : t ^ 2 = w ^ 2 / (1 + w ^ 2) := by rw [htdef, div_pow, hrsq]
    have hn1 : 3 / 4 ≤ ‖1 + w ^ 2‖ := by
      have := norm_sub_norm_le (1 : ℂ) (-(w ^ 2))
      rw [norm_one, norm_neg, norm_pow, sub_neg_eq_add] at this
      nlinarith [norm_nonneg w]
    have ht2n : ‖t ^ 2‖ < 1 := by
      rw [ht2, norm_div, norm_pow, div_lt_one (by linarith)]
      nlinarith [norm_nonneg w]
    have htn : ‖t‖ < 1 := by
      rw [norm_pow] at ht2n
      nlinarith [norm_nonneg t]
    have hpf : -w ^ 2 / (-w ^ 2 - 1) = t ^ 2 := by
      rw [ht2]
      have : -w ^ 2 - 1 = -(1 + w ^ 2) := by ring
      rw [this]; field_simp
    have h1p : 0 < (1 + t).re := by
      have := neg_le_of_abs_le (abs_re_le_norm t); simp; linarith
    have h1m : 0 < (1 - t).re := by
      have := re_le_norm t; simp; linarith
    have hwt : w = R * t := by rw [htdef]; field_simp
    have hodd := odd_binomial a htn
    rw [pfaff_transformation_of_ne_neg_nat hc32 (hdisk w hw1) (by rw [hpf]; exact ht2n), hpf,
      show (3 / 2 : ℂ) - (1 - a) = a + 1 / 2 by ring,
      show (1 : ℂ) - -w ^ 2 = R ^ 2 by rw [hrsq]; ring, sq_cpow hrre]
    have e1 : R ^ (1 - 2 * a) * (1 + t) ^ (1 - 2 * a) = (R + w) ^ (1 - 2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1p]; congr 1; rw [hwt]; ring
    have e2 : R ^ (1 - 2 * a) * (1 - t) ^ (1 - 2 * a) = (R - w) ^ (1 - 2 * a) := by
      rw [cpow_mul_cpow_of_re_pos hrre h1m]; congr 1; rw [hwt]; ring
    have e3 : R ^ (1 - 2 * a) = R * R ^ (2 * -a) := by
      rw [show 1 - 2 * a = 1 + 2 * -a by ring, cpow_add _ _ hr0, cpow_one]
    rw [← e1, ← e2, e3]
    conv_lhs => rw [hwt]
    linear_combination (R * R ^ (2 * -a)) * hodd
  have hLan : AnalyticOnNhd ℂ (fun w : ℂ => (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2))
      (Metric.ball 0 1) :=
    fun w hw => (analyticAt_const.mul analyticAt_id).mul
      ((analyticAt_ordinaryHypergeometric (hdisk w (by simpa using hw))).comp
        (f := fun w : ℂ => -w ^ 2) (analyticAt_id.pow 2).neg)
  have hRan : AnalyticOnNhd ℂ (fun w : ℂ => (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a))
      (Metric.ball 0 1) := by
    intro w hw
    obtain ⟨hre, -, -, -, hu, hv⟩ := sqrt_one_add_sq_data (by simpa using hw : ‖w‖ < 1)
    have hra : AnalyticAt ℂ r w :=
      (analyticAt_const.add (analyticAt_id.pow 2)).cpow analyticAt_const
        (mem_slitPlane_iff.mpr (Or.inl hre))
    exact ((hra.add analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hu))).sub
      ((hra.sub analyticAt_id).cpow analyticAt_const (mem_slitPlane_iff.mpr (Or.inl hv)))
  have hev : (fun w : ℂ => (2 - 4 * a) * w * ₂F₁ a (1 - a) (3 / 2) (-w ^ 2)) =ᶠ[𝓝 0]
      fun w => (r w + w) ^ (1 - 2 * a) - (r w - w) ^ (1 - 2 * a) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    exact hball w hw
  exact hLan.eqOn_of_preconnected_of_eventuallyEq hRan (convex_ball 0 1).isPreconnected
    (by simp) hev (by simpa using hz)

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
  obtain ⟨h1, -, -, -⟩ := quadratic_lobe_of_mem_ball hz
  have hk := kummer_quadratic (a := a) (b := a + 1 / 2)
    (by rw [show a + (a + 1 / 2) + 1 / 2 = 1 + 2 * a by ring]; exact hc) hz
  rw [show a + (a + 1 / 2) + 1 / 2 = 1 + 2 * a by ring,
    show 2 * (a + 1 / 2) = 1 + 2 * a by ring] at hk
  rw [hk, ordinaryHypergeometric_eq_one_sub_neg_cpow
    (fun k hk' => hc k (neg_eq_iff_eq_neg.mp hk'.symm)) h1]
  congr 1 <;> ring_nf

@[dlmf 15.4.E18]
theorem quadratic_binomial_derivative {a z : ℂ} (hc : ∀ k : ℕ, 2 * a ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    ₂F₁ a (a + 1 / 2) (2 * a) z =
      (1 - z) ^ (-(1 / 2 : ℂ)) * ((1 + (1 - z) ^ (1 / 2 : ℂ)) / 2) ^ (1 - 2 * a) := by
  obtain ⟨h1, -, -, -⟩ := quadratic_lobe_of_mem_ball hz
  have hk := kummer_quadratic (a := a) (b := a - 1 / 2)
    (by rw [show a + (a - 1 / 2) + 1 / 2 = 2 * a by ring]; exact hc) hz
  rw [show a + (a - 1 / 2) + 1 / 2 = 2 * a by ring,
    show 2 * (a - 1 / 2) = 2 * a - 1 by ring, ordinaryHypergeometric_symm (2 * a)] at hk
  rw [euler_transformation_of_ne_neg_nat hc hz, show 2 * a - a - (a + 1 / 2) = -(1 / 2) by ring,
    show 2 * a - a = a by ring, show 2 * a - (a + 1 / 2) = a - 1 / 2 by ring, hk,
    ordinaryHypergeometric_eq_one_sub_neg_cpow (fun k hk' => hc k (neg_eq_iff_eq_neg.mp hk'.symm)) h1]
  congr 2 <;> ring_nf

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
  set C := (a + b + 1) / 2 with hC
  have hC' : ∀ k : ℕ, a / 2 + b / 2 + 1 / 2 ≠ -(k : ℂ) := by
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring]; exact hc
  have hre : 0 < (C - a / 2 - b / 2).re := by
    rw [show C - a / 2 - b / 2 = 1 / 2 by rw [hC]; ring]; norm_num
  -- Along real `x → 1/2⁻`, Gauss's quadratic transformation relates both sides.
  have hL : Tendsto (fun x : ℝ => ₂F₁ a b C (x : ℂ)) (𝓝[<] (1 / 2)) (𝓝 (₂F₁ a b C (1 / 2))) := by
    have hc0 := (continuous_ofReal.tendsto (1 / 2 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Iio (1 / 2 : ℝ)))
    rw [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by push_cast; ring] at hc0
    exact (analyticAt_ordinaryHypergeometric (a := a) (b := b) (c := C)
      (show ‖(1 / 2 : ℂ)‖ < 1 by norm_num)).continuousAt.tendsto.comp hc0
  have hmap : Tendsto (fun x : ℝ => 4 * x * (1 - x)) (𝓝[<] (1 / 2)) (𝓝[<] 1) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := ((show Continuous (fun x : ℝ => 4 * x * (1 - x)) by fun_prop).tendsto (1 / 2)).mono_left
        (nhdsWithin_le_nhds (s := Set.Iio (1 / 2 : ℝ)))
      rw [show (4 : ℝ) * (1 / 2) * (1 - 1 / 2) = 1 by norm_num] at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx ⊢
      nlinarith [sq_nonneg (1 - 2 * x)]
  have hR := (tendsto_ordinaryHypergeometric_left_one (a := a / 2) (b := b / 2) hre).comp hmap
  have heq : ∀ᶠ x : ℝ in 𝓝[<] (1 / 2), ₂F₁ a b C (x : ℂ) =
      ₂F₁ (a / 2) (b / 2) C ((4 * x * (1 - x) : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 / 2 by norm_num)] with x hx
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]; linarith [hx.2]
    have hyn : ‖4 * (x : ℂ) * (1 - x)‖ < 1 := by
      rw [show 4 * (x : ℂ) * (1 - x) = ((4 * x * (1 - x) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by nlinarith [hx.1, hx.2])]
      nlinarith [sq_nonneg (1 - 2 * x), hx.2]
    have hq := gauss_quadratic (a := a / 2) (b := b / 2) hC' hxn hyn (by simpa using hx.2)
    rw [show a / 2 + b / 2 + 1 / 2 = C by rw [hC]; ring, show 2 * (a / 2) = a by ring,
      show 2 * (b / 2) = b by ring] at hq
    rw [hq]
    push_cast
    ring_nf
  have hlim := tendsto_nhds_unique hL (hR.congr' (by
    filter_upwards [heq] with x hx
    simp only [Function.comp_apply]
    rw [hx]))
  rw [hlim, gauss_summation (a := a / 2) (b := b / 2) (fun k => hc k) hre,
    show C - a / 2 - b / 2 = 1 / 2 by rw [hC]; ring, show C - a / 2 = (b + 1) / 2 by rw [hC]; ring,
    show C - b / 2 = (a + 1) / 2 by rw [hC]; ring, Complex.Gamma_one_half_eq,
    show (Real.sqrt Real.pi : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) by
      rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf]
  ring_nf

@[dlmf 15.4.E29]
theorem gauss_second_summation_contiguous
    {a b : ℂ}
    (hc : ∀ k : ℕ,
    (a + b) / 2 + 1 ≠ -(k : ℂ))
    (hab : a ≠ b) :
    ₂F₁ a b ((a + b) / 2 + 1) (1 / 2) =
      2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma ((a + b) / 2 + 1) * (1 / (Gamma (a / 2) * Gamma ((b + 1)
        / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) := by
  set c := (a + b) / 2 + 1 with hcdef
  have h12 : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hcon := contiguous_ab (a := a) (b := b) hc h12
  have h1 := gauss_second_summation (a := a + 1) (b := b)
    (by rw [show (a + 1 + b + 1) / 2 = c by rw [hcdef]; ring]; exact hc)
  have h2 := gauss_second_summation (a := a) (b := b + 1)
    (by rw [show (a + (b + 1) + 1) / 2 = c by rw [hcdef]; ring]; exact hc)
  rw [show (a + 1 + b + 1) / 2 = c by rw [hcdef]; ring, show (a + 1 + 1) / 2 = a / 2 + 1 by ring]
    at h1
  rw [show (a + (b + 1) + 1) / 2 = c by rw [hcdef]; ring, show (b + 1 + 1) / 2 = b / 2 + 1 by ring]
    at h2
  have hG (x : ℂ) : x * (Gamma (x / 2 + 1))⁻¹ = 2 * (Gamma (x / 2))⁻¹ := by
    by_cases hx : x = 0
    · subst hx; simp [Complex.Gamma_zero]
    · rw [Complex.Gamma_add_one _ (by simpa using hx), mul_inv]
      field_simp
  have hab' : a - b ≠ 0 := sub_ne_zero.mpr hab
  have key : (a - b) * ₂F₁ a b c (1 / 2) = a * ₂F₁ (a + 1) b c (1 / 2) - b * ₂F₁ a (b + 1) c (1 / 2) := by
    linear_combination -hcon
  rw [h1, h2] at key
  apply mul_left_cancel₀ hab'
  rw [key, show (a - b) * (2 * (Real.sqrt Real.pi : ℂ) / (a - b) * Gamma c *
      (1 / (Gamma (a / 2) * Gamma ((b + 1) / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2)))) =
      2 * (Real.sqrt Real.pi : ℂ) * Gamma c *
      (1 / (Gamma (a / 2) * Gamma ((b + 1) / 2)) - 1 / (Gamma ((a + 1) / 2) * Gamma (b / 2))) by
    field_simp]
  linear_combination ((Real.sqrt Real.pi : ℂ) * Gamma c * (Gamma ((b + 1) / 2))⁻¹) * hG a -
    ((Real.sqrt Real.pi : ℂ) * Gamma c * (Gamma ((a + 1) / 2))⁻¹) * hG b

@[dlmf 15.4.E30]
theorem bailey_summation {a b : ℂ} (hb : ∀ k : ℕ, b ≠ -(k : ℂ)) :
    ₂F₁ a (1 - a) b (1 / 2) =
      (2 : ℂ) ^ (1 - b) * (Real.sqrt Real.pi : ℂ) * Gamma b / (Gamma ((a + b) / 2) * Gamma ((b - a + 1) /
        2)) := by
  have h12 : ‖(1 / 2 : ℂ)‖ < 1 := by norm_num
  have hg := gauss_second_summation (a := b - a) (b := b + a - 1)
    (by rw [show (b - a + (b + a - 1) + 1) / 2 = b by ring]; exact hb)
  rw [show (b - a + (b + a - 1) + 1) / 2 = b by ring, show (b + a - 1 + 1) / 2 = (a + b) / 2 by ring]
    at hg
  have harg2 : (2 : ℂ).arg ≠ Real.pi := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, arg_ofReal_of_nonneg (by norm_num)]
    exact Real.pi_pos.ne
  rw [euler_transformation_of_ne_neg_nat hb h12, show b - a - (1 - a) = b - 1 by ring,
    show b - (1 - a) = b + a - 1 by ring, hg,
    show (1 : ℂ) - 1 / 2 = (2 : ℂ)⁻¹ by norm_num, inv_cpow _ _ harg2, ← cpow_neg,
    show -(b - 1) = 1 - b by ring]
  ring

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

/-- The paired terms of the alternating series `∑ (-1)^k a/(a+k)`. -/
def altPair (a : ℂ) (j : ℕ) : ℂ := a / (a + 2 * j) - a / (a + 2 * j + 1)

lemma altPair_eq (a : ℂ) (j : ℕ) (h1 : a + 2 * j ≠ 0) (h2 : a + 2 * j + 1 ≠ 0) :
    altPair a j = a / ((a + 2 * j) * (a + 2 * j + 1)) := by
  unfold altPair; field_simp; ring

/-- Complex digamma at a positive real is the real digamma. -/
lemma digamma_ofReal_eq {x : ℝ} (hx : 0 < x) : Complex.digamma x = (Real.digamma x : ℂ) := by
  apply Complex.ext
  · simp [Real.digamma_eq_re_digamma hx]
  · have h := DLMF.Gamma.digamma_conj (x : ℂ)
    rw [Complex.conj_ofReal] at h
    have := congrArg Complex.im h
    simp at this
    simp; linarith

/-- The real case: `∑ⱼ (x/(x+2j) - x/(x+2j+1)) = (x/2)(ψ((x+1)/2) - ψ(x/2))`. -/
lemma hasSum_altPair_ofReal {x : ℝ} (hx : 0 < x) :
    HasSum (altPair x) ((x / 2 : ℂ) * (Complex.digamma ((x + 1) / 2) - Complex.digamma (x / 2))) := by
  have h1 := Real.tendsto_deriv_log_GammaSeq (x := (x + 1) / 2) (by positivity)
  have h2 := Real.tendsto_deriv_log_GammaSeq (x := x / 2) (by positivity)
  have hd := (h1.sub h2).const_mul (x / 2)
  have hpartial : ∀ n : ℕ, x / 2 * ((Real.log n - ∑ k ∈ Finset.range (n + 1), ((x + 1) / 2 + k)⁻¹) -
      (Real.log n - ∑ k ∈ Finset.range (n + 1), (x / 2 + k)⁻¹)) =
      ∑ k ∈ Finset.range (n + 1), (x / (x + 2 * k) - x / (x + 2 * k + 1)) := by
    intro n
    rw [sub_sub_sub_cancel_left, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    field_simp
    ring
  simp_rw [hpartial] at hd
  have hreal : HasSum (fun j : ℕ => x / (x + 2 * j) - x / (x + 2 * j + 1))
      (x / 2 * (Real.digamma ((x + 1) / 2) - Real.digamma (x / 2))) := by
    rw [hasSum_iff_tendsto_nat_of_nonneg]
    · exact (hd.comp (tendsto_sub_atTop_nat 1)).congr' (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        simp only [Function.comp_apply, Nat.sub_add_cancel hn])
    · intro j
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      rw [sub_nonneg]
      exact div_le_div_of_nonneg_left hx.le (by positivity) (by linarith)
  have hc := (Complex.ofRealCLM.hasSum hreal)
  simp only [ofRealCLM_apply] at hc
  convert hc using 1
  · funext j; simp [altPair]
  · rw [show ((x : ℂ) + 1) / 2 = (((x + 1) / 2 : ℝ) : ℂ) by push_cast; ring,
      show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      digamma_ofReal_eq (by positivity), digamma_ofReal_eq (by positivity)]
    push_cast; ring

/-- `ψ` is analytic away from the nonpositive integers. -/
lemma analyticAt_digamma_of_not_neg_nat {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.digamma s := by
  have hG : AnalyticAt ℂ Complex.Gamma s := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [isOpen_not_neg_nat.mem_nhds hs] with w hw
    exact Complex.differentiableAt_Gamma w hw
  rw [show Complex.digamma = fun s => deriv Complex.Gamma s / Complex.Gamma s from
    funext fun s => by rw [Complex.digamma_def, logDeriv_apply]]
  exact hG.deriv.div hG (Complex.Gamma_ne_zero hs)

lemma forall_ne_neg_nat_of_re_pos {s : ℂ} (hs : 0 < s.re) : ∀ m : ℕ, s ≠ -(m : ℂ) := by
  intro m h
  have := congrArg re h
  simp at this
  linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The paired alternating series for `Re a > 0`. -/
theorem hasSum_altPair {a : ℂ} (ha : 0 < a.re) :
    HasSum (altPair a) (a / 2 * (Complex.digamma ((a + 1) / 2) - Complex.digamma (a / 2))) := by
  set U : Set ℂ := {a : ℂ | 0 < a.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const continuous_re
  have hden : ∀ b : ℂ, 0 < b.re → ∀ j : ℕ, b + 2 * j ≠ 0 ∧ b + 2 * j + 1 ≠ 0 := by
    intro b hb j
    constructor <;> intro h <;> have := congrArg re h <;> simp at this <;>
      linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- local domination of the paired series
  have hdom : ∀ a₀ ∈ U, ∃ V : Set ℂ, IsOpen V ∧ a₀ ∈ V ∧ V ⊆ U ∧ ∃ u : ℕ → ℝ, Summable u ∧
      ∀ j, ∀ b ∈ V, ‖altPair b j‖ ≤ u j := by
    intro a₀ ha₀
    set δ := a₀.re / 2 with hδ
    have hδ0 : 0 < δ := by simp only [hδ]; have : 0 < a₀.re := ha₀; linarith
    set m := min δ 1 with hm
    have hm0 : 0 < m := lt_min hδ0 one_pos
    set R := ‖a₀‖ + δ with hR
    refine ⟨Metric.ball a₀ δ, Metric.isOpen_ball, Metric.mem_ball_self hδ0, ?_, ?_⟩
    · intro b hb
      have := (abs_re_le_norm (b - a₀)).trans_lt (by simpa [dist_eq_norm] using hb)
      rw [abs_lt] at this
      simp only [sub_re] at this
      show 0 < b.re
      have : 0 < a₀.re := ha₀
      linarith
    refine ⟨fun j => R / (m ^ 2 * ((j : ℝ) + 1) ^ 2), ?_, ?_⟩
    · have h2 := (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr one_lt_two)
      refine (h2.mul_left (R / m ^ 2)).congr fun j => ?_
      push_cast
      field_simp
    · intro j b hb
      have hbd : ‖b - a₀‖ < δ := by simpa [dist_eq_norm] using hb
      have hre : δ < b.re := by
        have hlt := (abs_re_le_norm (b - a₀)).trans_lt hbd
        rw [abs_lt, sub_re] at hlt
        have h2 : a₀.re = 2 * δ := by simp only [hδ]; ring
        linarith [hlt.1]
      have hbR : ‖b‖ ≤ R := by
        have h3 : ‖b‖ ≤ ‖a₀‖ + ‖b - a₀‖ := by
          have := norm_add_le a₀ (b - a₀); rwa [add_sub_cancel] at this
        simp only [hR]; linarith
      obtain ⟨h1, h2⟩ := hden b (by linarith) j
      rw [altPair_eq b j h1 h2, norm_div, norm_mul]
      have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hmδ : m ≤ δ := min_le_left _ _
      have hm1 : m ≤ 1 := min_le_right _ _
      have hA : m * ((j : ℝ) + 1) ≤ ‖b + 2 * j‖ := by
        refine le_trans ?_ (re_le_norm _)
        simp; nlinarith
      have hB : m * ((j : ℝ) + 1) ≤ ‖b + 2 * j + 1‖ := by
        refine le_trans ?_ (re_le_norm _)
        simp; nlinarith
      have hpos : 0 < m * ((j : ℝ) + 1) := by positivity
      rw [div_le_div_iff₀ (mul_pos (hpos.trans_le hA) (hpos.trans_le hB)) (by positivity)]
      calc ‖b‖ * (m ^ 2 * ((j : ℝ) + 1) ^ 2) = ‖b‖ * ((m * ((j : ℝ) + 1)) * (m * ((j : ℝ) + 1))) := by
            ring
        _ ≤ R * (‖b + 2 * j‖ * ‖b + 2 * j + 1‖) := by
            gcongr
  have hsum : ∀ b ∈ U, Summable (altPair b) := by
    intro b hb
    obtain ⟨V, -, hbV, -, u, hu, hle⟩ := hdom b hb
    exact Summable.of_norm_bounded hu fun j => hle j b hbV
  have hPan : AnalyticOnNhd ℂ (fun b => ∑' j, altPair b j) U := by
    intro a₀ ha₀
    obtain ⟨V, hVo, ha₀V, hVU, u, hu, hle⟩ := hdom a₀ ha₀
    have hdiff : DifferentiableOn ℂ (fun b => ∑' j, altPair b j) V := by
      refine differentiableOn_tsum_of_summable_norm hu (fun j => ?_) hVo hle
      intro b hb
      obtain ⟨h1, h2⟩ := hden b (hVU hb) j
      have hd : DifferentiableAt ℂ (fun b : ℂ => b / (b + 2 * j) - b / (b + 2 * j + 1)) b := by
        fun_prop (disch := assumption)
      exact hd.differentiableWithinAt
    exact hdiff.analyticAt (hVo.mem_nhds ha₀V)
  have hfan : AnalyticOnNhd ℂ (fun b => b / 2 * (Complex.digamma ((b + 1) / 2) -
      Complex.digamma (b / 2))) U := by
    intro b hb
    have hb' : 0 < b.re := hb
    have h1 : 0 < ((b + 1) / 2).re := by simp; linarith
    have h2 : 0 < (b / 2).re := by simp; linarith
    have hA1 : AnalyticAt ℂ (fun b : ℂ => (b + 1) / 2) b := by fun_prop
    have hA2 : AnalyticAt ℂ (fun b : ℂ => b / 2) b := by fun_prop
    have hD1 := (analyticAt_digamma_of_not_neg_nat (forall_ne_neg_nat_of_re_pos h1)).comp
      (f := fun b : ℂ => (b + 1) / 2) hA1
    have hD2 := (analyticAt_digamma_of_not_neg_nat (forall_ne_neg_nat_of_re_pos h2)).comp
      (f := fun b : ℂ => b / 2) hA2
    exact hA2.mul (hD1.sub hD2)
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 0).isPreconnected
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ b in 𝓝[≠] (1 : ℂ), (∑' j, altPair b j) =
      b / 2 * (Complex.digamma ((b + 1) / 2) - Complex.digamma (b / 2)) := by
    have hseq : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝[≠] (1 : ℂ)) := by
      have hr0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
        refine h.congr fun n => ?_
        simp only [Function.comp_apply]; push_cast; ring
      have hr1 : Tendsto (fun n : ℕ => (1 : ℝ) + 1 / ((n : ℝ) + 2)) atTop (𝓝 1) := by
        simpa using hr0.const_add 1
      have hc : Tendsto (fun n : ℕ => ((1 + 1 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop (𝓝 (1 : ℂ)) := by
        have := (continuous_ofReal.tendsto (1 : ℝ)).comp hr1
        simpa [Function.comp_def] using this
      refine tendsto_nhdsWithin_iff.mpr ⟨hc, Eventually.of_forall fun n => ?_⟩
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
      intro h
      have : (1 + 1 / ((n : ℝ) + 2) : ℝ) = 1 := by exact_mod_cast h
      linarith
    refine hseq.frequently (Frequently.of_forall fun n => ?_)
    have hx : (0 : ℝ) < 1 + 1 / ((n : ℝ) + 2) := by positivity
    have h := hasSum_altPair_ofReal hx
    rw [h.tsum_eq]
  have heq := hPan.eqOn_of_preconnected_of_frequently_eq hfan hUc h1U hfreq (show a ∈ U from ha)
  have := (hsum a ha).hasSum
  simp only at heq
  rwa [heq] at this

lemma gaussHGCoeff_one_self_add_one {a : ℂ} (ha : 0 < a.re) (k : ℕ) :
    gaussHGCoeff 1 a (a + 1) k = a / (a + k) := by
  have hp : poch (a + 1) k ≠ 0 :=
    poch_ne_zero_of_not_neg_nat (forall_ne_neg_nat_of_re_pos (by simp; linarith)) k
  have hak : a + k ≠ 0 := by
    intro h; have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have e1 := poch_succ a k
  have e2 := poch_succ_left a k
  rw [gaussHGCoeff, poch_nat_one, div_eq_div_iff (mul_ne_zero hp hf) hak]
  linear_combination (k.factorial : ℂ) * (e1.symm.trans e2)

/-- Ordered partial sums are essential here: the series is only conditionally convergent. -/
@[dlmf 15.4.E27]
theorem alternating_digamma {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n,
      gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k) atTop
      (𝓝 (a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)))) := by
  set t : ℕ → ℂ := fun k => gaussHGCoeff 1 a (a + 1) k * (-1 : ℂ) ^ k with ht
  have htk : ∀ k : ℕ, t k = (-1) ^ k * (a / (a + k)) := fun k => by
    simp only [ht]; rw [gaussHGCoeff_one_self_add_one ha]; ring
  have h2N : ∀ N : ℕ, ∑ k ∈ Finset.range (2 * N), t k = ∑ j ∈ Finset.range N, altPair a j := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [show 2 * (N + 1) = 2 * N + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
        ih, Finset.sum_range_succ, htk, htk, altPair, pow_succ, pow_mul]
      push_cast
      ring
  have hdecomp : ∀ n : ℕ, ∑ k ∈ Finset.range n, t k = ∑ j ∈ Finset.range (n / 2), altPair a j +
      (if n % 2 = 1 then a / (a + (2 * (n / 2) : ℕ)) else 0) := by
    intro n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : n = 2 * (n / 2) := by omega
      rw [ite_eq_right_iff.mpr (fun h' => absurd h' (by omega)), add_zero]
      conv_lhs => rw [this]
      exact h2N _
    · have : n = 2 * (n / 2) + 1 := by omega
      rw [ite_eq_left_iff.mpr (fun h' => absurd h h')]
      conv_lhs => rw [this]
      rw [Finset.sum_range_succ, h2N, htk, pow_mul]
      simp
  simp_rw [hdecomp]
  rw [show a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) =
    a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) + 0 by ring]
  refine Tendsto.add ((hasSum_altPair ha).tendsto_sum_nat.comp (Nat.tendsto_div_const_atTop
    (by norm_num))) ?_
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hb : Tendsto (fun n : ℕ => ‖a‖ / (2 * ((n / 2 : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (2 * ((n / 2 : ℕ) : ℝ))) atTop atTop :=
      (tendsto_natCast_atTop_atTop.comp (Nat.tendsto_div_const_atTop (by norm_num))).const_mul_atTop
        (by norm_num)
    have := h1.inv_tendsto_atTop.const_mul ‖a‖
    rw [mul_zero] at this
    exact this.congr fun n => by rw [div_eq_mul_inv]; rfl
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hb
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hm : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by
    have : 1 ≤ n / 2 := by omega
    exact_mod_cast this
  split_ifs
  · rw [norm_div]
    have hre : 2 * ((n / 2 : ℕ) : ℝ) ≤ ‖a + ((2 * (n / 2) : ℕ) : ℂ)‖ := by
      refine le_trans ?_ (re_le_norm _)
      simp; linarith
    gcongr
  · simp; positivity

@[dlmf 15.4.E27]
theorem half_argument_digamma {a : ℂ} (ha : 0 < a.re) :
    (2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2) =
      a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) := by
  set L := a / 2 * (digamma ((a + 1) / 2) - digamma (a / 2)) with hL
  have hc : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := forall_ne_neg_nat_of_re_pos (by simp; linarith)
  -- Abel's theorem for `∑ (-1)^k a/(a+k) x^k`
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt (alternating_digamma ha)
  rw [tendsto_map'_iff] at habel
  -- the same function through Pfaff's transformation
  have hF : ∀ x : ℝ, 0 < x → x < 1 →
      ((fun z : ℂ => ∑' n, gaussHGCoeff 1 a (a + 1) n * (-1 : ℂ) ^ n * z ^ n) ∘ ofReal) x =
        (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)) := by
    intro x hx0 hx1
    have hxn : ‖-(x : ℂ)‖ < 1 := by
      rw [norm_neg, norm_real, Real.norm_eq_abs, abs_of_pos hx0]; exact hx1
    have hq : -(x : ℂ) / (-(x : ℂ) - 1) = (x : ℂ) / (1 + x) := by
      have h1 : (1 : ℂ) + x ≠ 0 := by exact_mod_cast (show (1 + x : ℝ) ≠ 0 by linarith)
      have h2 : -(x : ℂ) - 1 ≠ 0 := by
        rw [show -(x : ℂ) - 1 = -(1 + x) by ring]; exact neg_ne_zero.mpr h1
      rw [div_eq_div_iff h2 h1]; ring
    have hqn : ‖-(x : ℂ) / (-(x : ℂ) - 1)‖ < 1 := by
      rw [hq, show (x : ℂ) / (1 + x) = ((x / (1 + x) : ℝ) : ℂ) by push_cast; ring, norm_real,
        Real.norm_eq_abs, abs_of_pos (by positivity), div_lt_one (by linarith)]
      linarith
    have hP := pfaff_transformation_of_ne_neg_nat (a := a) (b := 1) (c := a + 1) hc hxn hqn
    rw [ordinaryHypergeometric_symm, hq, show a + 1 - 1 = a by ring, sub_neg_eq_add] at hP
    simp only [Function.comp_apply]
    rw [← hP, ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    refine tsum_congr fun n => ?_
    simp [gaussHGCoeff, poch, div_eq_mul_inv]
    ring
  have hlim : Tendsto (fun x : ℝ => (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)))
      (𝓝[<] 1) (𝓝 ((2 : ℂ) ^ (-a) * ₂F₁ a a (a + 1) (1 / 2))) := by
    have h1 : Tendsto (fun x : ℝ => (1 + (x : ℂ))) (𝓝[<] 1) (𝓝 2) := by
      have : Tendsto (fun x : ℝ => (1 + (x : ℂ))) (𝓝 1) (𝓝 (1 + ((1 : ℝ) : ℂ))) :=
        (continuous_const.add continuous_ofReal).tendsto 1
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun x : ℝ => (x : ℂ) / (1 + x)) (𝓝[<] 1) (𝓝 (1 / 2)) := by
      have : Tendsto (fun x : ℝ => (x : ℂ) / (1 + x)) (𝓝 1) (𝓝 (((1 : ℝ) : ℂ) / (1 + ((1 : ℝ) : ℂ)))) :=
        (continuous_ofReal.tendsto 1).div ((continuous_const.add continuous_ofReal).tendsto 1)
          (by norm_num)
      norm_num at this
      exact this.mono_left nhdsWithin_le_nhds
    have hcp : ContinuousAt (fun w : ℂ => w ^ (-a)) 2 :=
      continuousAt_cpow_const (by simp)
    have hFc : ContinuousAt (₂F₁ a a (a + 1) : ℂ → ℂ) (1 / 2) :=
      (analyticAt_ordinaryHypergeometric (by norm_num)).continuousAt
    exact (hcp.tendsto.comp h1).mul (hFc.tendsto.comp h2)
  have hev : ∀ᶠ x : ℝ in 𝓝[<] 1, x ∈ Set.Ioo (0 : ℝ) 1 := Ioo_mem_nhdsLT (by norm_num)
  have habel' : Tendsto (fun x : ℝ => (1 + (x : ℂ)) ^ (-a) * ₂F₁ a a (a + 1) ((x : ℂ) / (1 + x)))
      (𝓝[<] 1) (𝓝 L) := by
    refine habel.congr' ?_
    filter_upwards [hev] with x hx
    exact hF x hx.1 hx.2
  exact tendsto_nhds_unique hlim habel'

end DLMF.Hypergeometric
