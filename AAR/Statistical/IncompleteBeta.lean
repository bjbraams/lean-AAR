/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Derivatives
public import AAR.Hypergeometric.EulerIntegral
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.Binomial.Tail

/-!
# Incomplete Beta functions with complex parameters (Temme §11.3; DLMF §8.17)

For complex `a, b` with positive real parts and `0 ≤ x ≤ 1`,

`B_x(a,b) = ∫₀ˣ t^{a-1} (1-t)^{b-1} dt`,  `I_x(a,b) = B_x(a,b) / B(a,b)`,

where `B(a,b)` is Mathlib's `Complex.betaIntegral` (DLMF 8.17.1–8.17.2). TauCeti treats the real
case; `regIncompleteBeta_ofReal` identifies the two.

## Main results

* `incompleteBeta_one`, `regIncompleteBeta_one`: `B_1(a,b) = B(a,b)`, `I_1(a,b) = 1`.
* `incompleteBeta_add_incompleteBeta_one_sub`, `regIncompleteBeta_symm`:
  `I_x(a,b) + I_{1-x}(b,a) = 1` (DLMF 8.17.4).
* `incompleteBeta_one_right`, `regIncompleteBeta_one_right`: `I_x(a,1) = x^a`.
* `incompleteBeta_eq_add`: `B_x(a,b) = B_x(a+1,b) + B_x(a,b+1)`.
* `incompleteBeta_parts`: `a B_x(a,b+1) - b B_x(a+1,b) = x^a (1-x)^b`.
* `regIncompleteBeta_add_one_left`, `regIncompleteBeta_add_one_right`: the recurrences
  DLMF 8.17.20–8.17.21.
* `regIncompleteBeta_nat`: the binomial sum `I_p(m, n-m+1) = ∑_{j=m}^n C(n,j) p^j (1-p)^{n-j}`
  (DLMF 8.17.5).
* `incompleteBeta_eq_ordinaryHypergeometric`: `B_x(a,b) = xᵃ/a · F(a, 1-b; a+1; x)` for
  `0 < x < 1` (DLMF 8.17.7), from Euler's integral.
-/

@[expose] public section

open Complex Set MeasureTheory intervalIntegral
open scoped Real

noncomputable section

namespace AAR.Statistical

/-- The incomplete Beta function `B_x(a,b) = ∫₀ˣ t^{a-1} (1-t)^{b-1} dt` (DLMF 8.17.1). -/
@[dlmf 8.17.E1]
def incompleteBeta (a b : ℂ) (x : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)

/-- The regularized incomplete Beta function `I_x(a,b) = B_x(a,b)/B(a,b)` (DLMF 8.17.2). -/
@[dlmf 8.17.E2]
def regIncompleteBeta (a b : ℂ) (x : ℝ) : ℂ := incompleteBeta a b x / betaIntegral a b

/-- The Beta integrand is integrable on every subinterval of `[0, 1]`. -/
lemma intervalIntegrable_beta {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) 1) (hv : v ∈ Icc (0 : ℝ) 1) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) volume u v :=
  (betaIntegral_convergent ha hb).mono_set (uIcc_subset_uIcc (by simpa using hu)
    (by simpa using hv))

/-- `B(a,b) ≠ 0` for positive real parts. -/
lemma betaIntegral_ne_zero {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) : betaIntegral a b ≠ 0 := by
  intro h
  have := Gamma_mul_Gamma_eq_betaIntegral ha hb
  rw [h, mul_zero] at this
  exact mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hb) this

/-- `B_1(a,b) = B(a,b)`. -/
theorem incompleteBeta_one (a b : ℂ) : incompleteBeta a b 1 = betaIntegral a b := rfl

/-- `I_1(a,b) = 1`. -/
theorem regIncompleteBeta_one {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    regIncompleteBeta a b 1 = 1 := by
  rw [regIncompleteBeta, incompleteBeta_one, div_self (betaIntegral_ne_zero ha hb)]

/-- `B_0(a,b) = 0`. -/
@[simp]
theorem incompleteBeta_zero (a b : ℂ) : incompleteBeta a b 0 = 0 := by
  simp [incompleteBeta]

/-- `B_x(a,b) + B_{1-x}(b,a) = B(a,b)` for `0 ≤ x ≤ 1`. -/
theorem incompleteBeta_add_incompleteBeta_one_sub {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    incompleteBeta a b x + incompleteBeta b a (1 - x) = betaIntegral a b := by
  have h := intervalIntegral.integral_comp_sub_left (a := 0) (b := 1 - x)
    (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) 1
  simp only [sub_sub_cancel, sub_zero] at h
  have h' : incompleteBeta b a (1 - x) =
      ∫ t in x..1, (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1) := by
    rw [incompleteBeta, ← h]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast
    rw [sub_sub_cancel]
    ring
  rw [h', incompleteBeta, intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_beta ha hb ⟨le_rfl, zero_le_one⟩ hx)
    (intervalIntegrable_beta ha hb hx ⟨zero_le_one, le_rfl⟩)]
  rfl

/-- **Symmetry** `I_x(a,b) + I_{1-x}(b,a) = 1` (DLMF 8.17.4). -/
@[dlmf 8.17.E4]
theorem regIncompleteBeta_symm {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regIncompleteBeta a b x + regIncompleteBeta b a (1 - x) = 1 := by
  rw [regIncompleteBeta, regIncompleteBeta, betaIntegral_symm a b, ← add_div,
    incompleteBeta_add_incompleteBeta_one_sub ha hb hx,
    div_self (betaIntegral_ne_zero ha hb)]

/-- `B_x(a,1) = x^a / a`. -/
theorem incompleteBeta_one_right {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    incompleteBeta a 1 x = (x : ℂ) ^ a / a := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [incompleteBeta]
  simp only [sub_self, cpow_zero, mul_one]
  rw [integral_cpow (Or.inl (by simp; linarith)), sub_add_cancel, ofReal_zero,
    zero_cpow ha0, sub_zero]

/-- `I_x(a,1) = x^a`. -/
theorem regIncompleteBeta_one_right {a : ℂ} (ha : 0 < a.re) (x : ℝ) :
    regIncompleteBeta a 1 x = (x : ℂ) ^ a := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  rw [regIncompleteBeta, incompleteBeta_one_right ha x, betaIntegral_eval_one_right ha]
  field_simp

/-- `t^a = t^{a-1} t` for `a ≠ 0`, including `t = 0`. -/
lemma cpow_eq_cpow_sub_one_mul {a : ℂ} (ha : a ≠ 0) (t : ℂ) : t ^ a = t ^ (a - 1) * t := by
  by_cases ht : t = 0
  · rw [ht, zero_cpow ha, mul_zero]
  · rw [cpow_sub _ _ ht, cpow_one, div_mul_cancel₀ _ ht]

lemma re_add_one_pos {a : ℂ} (ha : 0 < a.re) : 0 < (a + 1).re := by simp; linarith

/-- `B_x(a,b) = B_x(a+1,b) + B_x(a,b+1)`, from `t + (1 - t) = 1`. -/
theorem incompleteBeta_eq_add {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    incompleteBeta a b x = incompleteBeta (a + 1) b x + incompleteBeta a (b + 1) x := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  rw [incompleteBeta, incompleteBeta, incompleteBeta, ← intervalIntegral.integral_add
    (intervalIntegrable_beta (re_add_one_pos ha) hb h0 hx)
    (intervalIntegrable_beta ha (re_add_one_pos hb) h0 hx)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [add_sub_cancel_right]
  rw [cpow_eq_cpow_sub_one_mul ha0 (t : ℂ), cpow_eq_cpow_sub_one_mul hb0 (1 - (t : ℂ))]
  ring

/-- Integration by parts: `a B_x(a,b+1) - b B_x(a+1,b) = x^a (1-x)^b` for `0 ≤ x ≤ 1`. -/
theorem incompleteBeta_parts {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    a * incompleteBeta a (b + 1) x - b * incompleteBeta (a + 1) b x =
      (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  set F : ℝ → ℂ := fun t => (t : ℂ) ^ a * (1 - (t : ℂ)) ^ b with hF
  have hcont : ContinuousOn F (Icc 0 x) := by
    intro t ht
    have ht1 : t ≤ 1 := ht.2.trans hx.2
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact (continuousAt_cpow_const_of_re_pos (Or.inl (by simpa using ht.1)) ha).comp
        continuous_ofReal.continuousAt
    · exact (continuousAt_cpow_const_of_re_pos (Or.inl (by simp; linarith)) hb).comp
        (by fun_prop : Continuous fun t : ℝ => 1 - (t : ℂ)).continuousAt
  have hderiv : ∀ t ∈ Ioo 0 x, HasDerivAt F
      (a * ((t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b + 1 - 1)) -
        b * ((t : ℂ) ^ (a + 1 - 1) * (1 - (t : ℂ)) ^ (b - 1))) t := by
    intro t ht
    have ht1 : t < 1 := ht.2.trans_le hx.2
    have hs1 : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr ht.1
    have hs2 : (1 - (t : ℂ)) ∈ slitPlane := by
      rw [show (1 : ℂ) - t = ((1 - t : ℝ) : ℂ) by push_cast; ring]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have h := (((hasDerivAt_id (t : ℂ)).cpow_const (c := a) hs1).mul
      (((hasDerivAt_id (t : ℂ)).const_sub 1).cpow_const (c := b) hs2)).comp_ofReal
    refine h.congr_deriv ?_
    simp only [id, add_sub_cancel_right]
    rw [cpow_eq_cpow_sub_one_mul ha0 (t : ℂ)]
    have hb0 : b ≠ 0 := fun h => by simp [h] at hb
    rw [cpow_eq_cpow_sub_one_mul hb0 (1 - (t : ℂ))]
    ring
  have hint : IntervalIntegrable (fun t : ℝ =>
      a * ((t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b + 1 - 1)) -
        b * ((t : ℂ) ^ (a + 1 - 1) * (1 - (t : ℂ)) ^ (b - 1))) volume 0 x :=
    ((intervalIntegrable_beta ha (re_add_one_pos hb) h0 hx).const_mul a).sub
      ((intervalIntegrable_beta (re_add_one_pos ha) hb h0 hx).const_mul b)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 hcont hderiv hint
  rw [intervalIntegral.integral_sub
    ((intervalIntegrable_beta ha (re_add_one_pos hb) h0 hx).const_mul a)
    ((intervalIntegrable_beta (re_add_one_pos ha) hb h0 hx).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hftc
  rw [incompleteBeta, incompleteBeta, hftc]
  simp [hF, zero_cpow ha0]

/-- **Recurrence in `a`** (DLMF 8.17.20): `I_x(a+1,b) = I_x(a,b) - x^a (1-x)^b / (a B(a,b))`. -/
@[dlmf 8.17.E20]
theorem regIncompleteBeta_add_one_left {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regIncompleteBeta (a + 1) b x =
      regIncompleteBeta a b x - (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b / (a * betaIntegral a b) := by
  have ha0 : a ≠ 0 := fun h => by simp [h] at ha
  have hS := incompleteBeta_eq_add ha hb hx
  have hR := incompleteBeta_parts ha hb hx
  have hB := incompleteBeta_eq_add ha hb ⟨zero_le_one, le_rfl⟩
  have hrec := betaIntegral_recurrence ha hb
  have hp := betaIntegral_ne_zero (re_add_one_pos ha) hb
  have hB0 := betaIntegral_ne_zero ha hb
  simp only [incompleteBeta_one] at hB
  rw [regIncompleteBeta, regIncompleteBeta]
  generalize incompleteBeta (a + 1) b x = U at *
  generalize incompleteBeta a (b + 1) x = V at *
  generalize incompleteBeta a b x = S at *
  generalize betaIntegral (a + 1) b = P at *
  generalize betaIntegral a (b + 1) = Q at *
  generalize betaIntegral a b = B at *
  generalize (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b = R at *
  field_simp
  linear_combination (a * U) * hB - (a * P) * hS - P * hR + U * hrec

/-- **Recurrence in `b`** (DLMF 8.17.21): `I_x(a,b+1) = I_x(a,b) + x^a (1-x)^b / (b B(a,b))`. -/
@[dlmf 8.17.E21]
theorem regIncompleteBeta_add_one_right {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regIncompleteBeta a (b + 1) x =
      regIncompleteBeta a b x + (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b / (b * betaIntegral a b) := by
  have hb0 : b ≠ 0 := fun h => by simp [h] at hb
  have hS := incompleteBeta_eq_add ha hb hx
  have hR := incompleteBeta_parts ha hb hx
  have hB := incompleteBeta_eq_add ha hb ⟨zero_le_one, le_rfl⟩
  have hrec := betaIntegral_recurrence ha hb
  have hq := betaIntegral_ne_zero ha (re_add_one_pos hb)
  have hB0 := betaIntegral_ne_zero ha hb
  simp only [incompleteBeta_one] at hB
  rw [regIncompleteBeta, regIncompleteBeta]
  generalize incompleteBeta (a + 1) b x = U at *
  generalize incompleteBeta a (b + 1) x = V at *
  generalize incompleteBeta a b x = S at *
  generalize betaIntegral (a + 1) b = P at *
  generalize betaIntegral a (b + 1) = Q at *
  generalize betaIntegral a b = B at *
  generalize (x : ℂ) ^ a * (1 - (x : ℂ)) ^ b = R at *
  field_simp
  linear_combination (b * V) * hB - (b * Q) * hS + Q * hR - V * hrec

/-- For real positive parameters, `B(a,b)` is the real Beta function. -/
lemma betaIntegral_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    betaIntegral a b = (ProbabilityTheory.beta a b : ℂ) := by
  have h := Gamma_mul_Gamma_eq_betaIntegral (s := (a : ℂ)) (t := b) (by simpa) (by simpa)
  have hG : Gamma ((a : ℂ) + b) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  rw [ProbabilityTheory.beta, ofReal_div, ofReal_mul, ← Gamma_ofReal, ← Gamma_ofReal,
    ← Gamma_ofReal, ofReal_add, h]
  field_simp

/-- For real positive parameters and `0 ≤ x ≤ 1`, `I_x(a,b)` is TauCeti's
`regularizedIncompleteBeta`. -/
theorem regIncompleteBeta_ofReal {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ}
    (hx : x ∈ Icc (0 : ℝ) 1) :
    regIncompleteBeta a b x = (TauCeti.regularizedIncompleteBeta a b x : ℂ) := by
  rw [TauCeti.regularizedIncompleteBeta_def_of_mem_Icc ha hb hx, ofReal_div,
    ← betaIntegral_ofReal ha hb, regIncompleteBeta, incompleteBeta,
    ← intervalIntegral.integral_ofReal]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hx.1] at ht
  have ht1 : 0 ≤ 1 - t := by linarith [ht.2, hx.2]
  rw [ofReal_mul, ofReal_cpow ht.1, ofReal_cpow ht1]
  push_cast
  ring_nf

/-- **The binomial sum** (DLMF 8.17.5): for `1 ≤ m ≤ n` and `0 ≤ p ≤ 1`,
`I_p(m, n-m+1) = ∑_{j=m}^n C(n,j) p^j (1-p)^{n-j}`. -/
@[dlmf 8.17.E5]
theorem regIncompleteBeta_nat {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) {p : ℝ}
    (hp : p ∈ Icc (0 : ℝ) 1) :
    regIncompleteBeta m ((n : ℂ) - m + 1) p =
      ∑ k ∈ Finset.Icc m n, (n.choose k : ℂ) * (p : ℂ) ^ k * (1 - (p : ℂ)) ^ (n - k) := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hb : (0 : ℝ) < (n : ℝ) - m + 1 := by
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    linarith
  have h := TauCeti.Probability.sum_Icc_choose_mul_pow_eq_regularizedIncompleteBeta hmn ⟨p, hp⟩
  rw [show regIncompleteBeta (m : ℂ) ((n : ℂ) - m + 1) p =
      regIncompleteBeta ((m : ℝ) : ℂ) (((n : ℝ) - m + 1 : ℝ) : ℂ) p by push_cast; rfl,
    regIncompleteBeta_ofReal hm' hb hp, ← h]
  push_cast
  rfl

/-- The hypergeometric form `B_x(a,b) = xᵃ/a · F(a, 1-b; a+1; x)` for `0 < x < 1`
(DLMF 8.17.7), from Euler's integral after the substitution `t = xs`. -/
@[dlmf 8.17.E7]
theorem incompleteBeta_eq_ordinaryHypergeometric {a : ℂ} (ha : 0 < a.re) (b : ℂ) {x : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) :
    incompleteBeta a b x = (x : ℂ) ^ a / a * ₂F₁ a (1 - b) (a + 1) (x : ℂ) := by
  have ha0 : a ≠ 0 := fun h => by rw [h] at ha; simp at ha
  have hxn : ‖(x : ℂ)‖ < 1 := by rw [norm_real, Real.norm_of_nonneg hx0.le]; exact hx1
  have hE := ordinaryHypergeometric_eq_integral (a := 1 - b) (b := a) (c := a + 1)
    ha (by simp) hxn
  rw [show a + 1 - a = 1 by ring, Gamma_one, mul_one, Gamma_add_one a ha0] at hE
  have hsub : incompleteBeta a b x = (x : ℂ) * ∫ s in (0 : ℝ)..1,
      ((x * s : ℝ) : ℂ) ^ (a - 1) * (1 - ((x * s : ℝ) : ℂ)) ^ (b - 1) := by
    have h := intervalIntegral.integral_comp_mul_left
      (fun t : ℝ => (t : ℂ) ^ (a - 1) * (1 - (t : ℂ)) ^ (b - 1)) (a := 0) (b := 1) hx0.ne'
    rw [mul_zero, mul_one] at h
    rw [incompleteBeta, h, real_smul, ← mul_assoc, ← ofReal_mul, mul_inv_cancel₀ hx0.ne',
      ofReal_one, one_mul]
  have hΓ : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  rw [hsub, AAR.Hypergeometric.ordinaryHypergeometric_symm, hE, mul_div_assoc, div_self hΓ,
    mul_one]
  have hcongr : ∫ s in (0 : ℝ)..1, ((x * s : ℝ) : ℂ) ^ (a - 1) * (1 - ((x * s : ℝ) : ℂ)) ^ (b - 1) =
      ∫ s in (0 : ℝ)..1, (x : ℂ) ^ (a - 1) * ((s : ℂ) ^ (a - 1) * (1 - (s : ℂ)) ^ ((1 : ℂ) - 1) *
        (1 - (x : ℂ) * s) ^ (-(1 - b))) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    have hs0 : 0 ≤ s := by rw [uIcc_of_le zero_le_one] at hs; exact hs.1
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hx0.le hs0, sub_self, cpow_zero, mul_one,
      show -(1 - b) = b - 1 by ring]
    ring
  rw [hcongr, intervalIntegral.integral_const_mul]
  have hx : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx0.ne'
  rw [show (x : ℂ) ^ a = (x : ℂ) ^ (a - 1) * x by
    rw [cpow_sub _ _ hx, cpow_one]; field_simp]
  field_simp

end AAR.Statistical
