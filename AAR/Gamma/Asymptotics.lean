/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Stirling
public import AAR.Gamma.Digamma
public import AAR.Hypergeometric.Basic
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Asymptotic expansions (DLMF §5.11)

Stirling's formula for `Γ(n+1)` is already `Gamma_nat_succ_isEquivalent_stirlingGamma`
in `Stirling.lean`. Poincaré expansions below are stated along the positive real
axis. Remainder estimates 5.11.10–5.11.11 with `sec(ph z)` are deferred except
for the real-axis form of 5.11.3.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Scaled Gamma `Γ*(z)` in DLMF 5.11.3. -/
@[dlmf 5.11.E3]
def scaledGamma (z : ℂ) : ℂ :=
  Complex.Gamma z / (Complex.exp (-z) * z ^ z * (2 * π / z) ^ (1 / 2 : ℂ))

@[dlmf 5.11.E1]
theorem log_Gamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.log (Real.Gamma (t + x)) -
        ((t + x - 1 / 2) * Real.log (t + x) - (t + x) + (1 / 2) * Real.log (2 * π) +
          ∑ k ∈ Finset.Icc 1 n,
            bernoulli (2 * k) / ((2 * k) * (2 * k - 1) * (t + x) ^ (2 * k - 1))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 1)) := by
  sorry

@[dlmf 5.11.E2]
theorem digamma_stirling (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Real.digamma (t + x) -
        (Real.log (t + x) - 1 / (2 * (t + x)) -
          ∑ k ∈ Finset.Icc 1 n, bernoulli (2 * k) / ((2 * k) * (t + x) ^ (2 * k))))
      (fun t : ℝ => (t : ℝ) ^ (-(2 * n : ℝ) - 2)) := by
  sorry

/-- Stirling coefficients, obtained by exponentiating the Bernoulli expansion
of the logarithm of the scaled Gamma function. This recurrence specifies every order. -/
@[dlmf 5.11.E4]
def stirlingG : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (bernoulli (k.val + 2) : ℂ) / (k.val + 2) * stirlingG (n - k.val)) / (n + 1)
termination_by n => n

@[dlmf 5.11.E7]
theorem Gamma_linear_argument {a : ℝ} (ha : 0 < a) {b : ℂ} :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (a * t + b) /
        (Real.sqrt (2 * π) * Complex.exp (-(a : ℂ) * t) *
          (a * t : ℂ) ^ (a * t + b - 1 / 2)))
      (fun _ : ℝ => (1 : ℂ)) := by
  sorry

@[dlmf 5.11.E9]
theorem norm_Gamma_imag_large {x : ℝ} :
    Asymptotics.IsEquivalent atTop
      (fun y : ℝ => ‖Complex.Gamma (x + I * y)‖)
      (fun y : ℝ => Real.sqrt (2 * π) * |y| ^ (x - 1 / 2) * Real.exp (-π * |y| / 2)) := by
  sorry

/-- Helper lemma for `Gamma_ratio_power`: the substitution `u = x / t` in the Beta integral
`B(a, t+1)`. -/
lemma cpow_mul_betaIntegral_add_one_eq {a : ℂ} {t : ℝ} (ht : 0 < t) :
    (t : ℂ) ^ a * betaIntegral a (t + 1) =
      ∫ x : ℝ in 0..t, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) := by
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hcomp := intervalIntegral.integral_comp_div (a := 0) (b := t)
    (fun u : ℝ => (((1 - u) ^ t : ℝ) : ℂ) * ((u * t : ℝ) : ℂ) ^ (a - 1)) ht.ne'
  simp only [zero_div, div_self ht.ne', div_mul_cancel₀ _ ht.ne'] at hcomp
  rw [hcomp, betaIntegral, real_smul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  simp_rw [intervalIntegral.integral_of_le zero_le_one]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have h1 : (1 - (u : ℂ)) ^ ((t : ℂ) + 1 - 1) = (((1 - u) ^ t : ℝ) : ℂ) := by
    rw [add_sub_cancel_right, ofReal_cpow (by linarith [hu.2])]
    push_cast
    rfl
  have h2 : ((u * t : ℝ) : ℂ) ^ (a - 1) = (u : ℂ) ^ (a - 1) * (t : ℂ) ^ (a - 1) := by
    push_cast
    exact mul_cpow_ofReal_nonneg hu.1.le ht.le _
  have h3 : (t : ℂ) ^ a = (t : ℂ) ^ (a - 1) * t := by
    conv_lhs => rw [show a = a - 1 + 1 by ring, cpow_add _ _ htC, cpow_one]
  rw [h1, h2, h3]
  ring

/-- Helper lemma for `Gamma_ratio_power`: `t^a B(a, t+1) → Γ(a)` along real `t → ∞`,
by dominated convergence against the Gamma integrand. -/
lemma tendsto_approx_Gamma_integral_rpow {a : ℂ} (ha : 0 < a.re) :
    Tendsto (fun t : ℝ => ∫ x : ℝ in 0..t, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1))
      atTop (𝓝 (Complex.Gamma a)) := by
  rw [Gamma_eq_integral ha, GammaIntegral]
  let f : ℝ → ℝ → ℂ := fun t =>
    Set.indicator (Set.Ioc 0 t) fun x : ℝ => (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1)
  have hcont (t : ℝ) (ht : 0 < t) :
      Continuous fun x : ℝ => (((1 - x / t) ^ t : ℝ) : ℂ) := by
    have : Continuous fun x : ℝ => (1 - x / t) ^ t :=
      (Real.continuous_rpow_const ht.le).comp (by fun_prop)
    exact continuous_ofReal.comp this
  have f_ible (t : ℝ) (ht : 0 < t) :
      MeasureTheory.Integrable (f t) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
    rw [MeasureTheory.integrable_indicator_iff measurableSet_Ioc, MeasureTheory.IntegrableOn,
      MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self,
      ← MeasureTheory.IntegrableOn,
      ← intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    apply IntervalIntegrable.continuousOn_mul
    · refine intervalIntegral.intervalIntegrable_cpow' ?_
      rwa [sub_re, one_re, ← zero_sub, sub_lt_sub_iff_right]
    · exact (hcont t ht).continuousOn
  have f_tends : ∀ x : ℝ, x ∈ Set.Ioi (0 : ℝ) →
      Tendsto (fun t : ℝ => f t x) atTop
        (𝓝 <| ((Real.exp (-x) : ℝ) : ℂ) * (x : ℂ) ^ (a - 1)) := by
    intro x hx
    apply Tendsto.congr'
    · change ∀ᶠ t : ℝ in atTop, (((1 - x / t) ^ t : ℝ) : ℂ) * (x : ℂ) ^ (a - 1) = f t x
      filter_upwards [eventually_ge_atTop x] with t hxt
      simp only [f]
      rw [Set.indicator_of_mem]
      exact ⟨hx, hxt⟩
    · refine (Tendsto.comp (continuous_ofReal.tendsto _) ?_).mul_const _
      convert Real.tendsto_one_add_div_rpow_exp (-x) using 2 with t
      rw [neg_div, ← sub_eq_add_neg]
  have hbound : ∀ᶠ t : ℝ in atTop, ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ‖f t x‖ ≤ Real.exp (-x) * x ^ (a.re - 1) := by
    filter_upwards [Ioi_mem_atTop 0] with t ht
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    simp only [Set.mem_Ioi, f] at hx ⊢
    rcases lt_or_ge t x with hxt | hxt
    · rw [Set.indicator_of_notMem (Set.notMem_Ioc_of_gt hxt), norm_zero]
      positivity
    · have h0 : 0 ≤ 1 - x / t := sub_nonneg.mpr (div_le_one_of_le₀ hxt ht.le)
      rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx, hxt⟩), norm_mul,
        Complex.norm_of_nonneg (Real.rpow_nonneg h0 _),
        norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
      gcongr
      calc (1 - x / t) ^ t ≤ Real.exp (-x / t) ^ t := by
            have hle : 1 - x / t ≤ Real.exp (-x / t) := by
              rw [neg_div]
              linarith [Real.add_one_le_exp (-(x / t))]
            exact Real.rpow_le_rpow h0 hle (le_of_lt ht)
        _ = Real.exp (-x) := by
            rw [← Real.exp_mul, div_mul_cancel₀ _ ht.ne']
  refine (MeasureTheory.tendsto_integral_filter_of_dominated_convergence _
    (Filter.eventually_of_mem (Ioi_mem_atTop 0) fun t ht => (f_ible t ht).1)
    hbound (Real.GammaIntegral_convergent ha)
    ((MeasureTheory.ae_restrict_iff' measurableSet_Ioi).mpr
      (MeasureTheory.ae_of_all _ f_tends))).congr' ?_
  filter_upwards [Ioi_mem_atTop 0] with t ht
  rw [MeasureTheory.integral_indicator measurableSet_Ioc,
    intervalIntegral.integral_of_le (le_of_lt ht),
    MeasureTheory.Measure.restrict_restrict_of_subset Set.Ioc_subset_Ioi_self]

/-- Helper lemma for `Gamma_ratio_power`: `Γ(t+a)/(Γ(t) t^a) → 1` for `Re a > 1`. -/
lemma tendsto_Gamma_add_div_Gamma_mul_cpow_of_one_lt_re {a : ℂ} (ha : 1 < a.re) :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
      atTop (𝓝 1) := by
  have ha' : 0 < (a - 1).re := by simp; linarith
  have hG : Complex.Gamma (a - 1) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha'
  have hlim := (tendsto_approx_Gamma_integral_rpow ha').inv₀ hG |>.const_mul (Complex.Gamma (a - 1))
  rw [mul_inv_cancel₀ hG] at hlim
  apply hlim.congr'
  filter_upwards [Ioi_mem_atTop 0] with t ht
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have ht1 : 0 < ((t : ℂ) + 1).re := by simp; linarith [Set.mem_Ioi.mp ht]
  have hB := Complex.Gamma_mul_Gamma_eq_betaIntegral ha' ht1
  have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
  have hGt1 : Complex.Gamma ((t : ℂ) + 1) = t * Complex.Gamma t := Complex.Gamma_add_one _ htC
  rw [← cpow_mul_betaIntegral_add_one_eq ht]
  have hsum : a - 1 + ((t : ℂ) + 1) = t + a := by ring
  rw [hsum, hGt1] at hB
  have hpow : (t : ℂ) ^ a = (t : ℂ) ^ (a - 1) * t := by
    conv_lhs => rw [show a = a - 1 + 1 by ring, cpow_add _ _ htC, cpow_one]
  have hpow0 : (t : ℂ) ^ (a - 1) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  have hBne : betaIntegral (a - 1) ((t : ℂ) + 1) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hB
    exact mul_ne_zero hG (mul_ne_zero htC hGt) hB
  rw [hpow]
  field_simp
  linear_combination hB

/-- Helper lemma for `Gamma_ratio_power`: `Γ(t+a)/(Γ(t) t^a) → 1` along real `t → ∞`. -/
lemma tendsto_Gamma_add_div_Gamma_mul_cpow (a : ℂ) :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
      atTop (𝓝 1) := by
  suffices h : ∀ n : ℕ, ∀ a : ℂ, 1 < a.re + n →
      Tendsto (fun t : ℝ => Complex.Gamma (t + a) / (Complex.Gamma t * (t : ℂ) ^ a))
        atTop (𝓝 1) by
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - a.re)
    exact h n a (by linarith)
  intro n
  induction n with
  | zero =>
    intro a ha
    exact tendsto_Gamma_add_div_Gamma_mul_cpow_of_one_lt_re (by simpa using ha)
  | succ n ih =>
    intro a ha
    have h1 := ih (a + 1) (by simp; push_cast at ha; linarith)
    have h2 : Tendsto (fun t : ℝ => (1 + a / (t : ℂ))⁻¹) atTop (𝓝 1) := by
      have : Tendsto (fun t : ℝ => a / (t : ℂ)) atTop (𝓝 0) := by
        have := (tendsto_inv_atTop_zero (𝕜 := ℝ)).ofReal.const_mul a
        simpa [div_eq_mul_inv] using this
      simpa using (this.const_add 1).inv₀ (by norm_num)
    have := h1.mul h2
    rw [one_mul] at this
    apply this.congr'
    filter_upwards [Ioi_mem_atTop (max 0 (-a.re))] with t ht
    have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht
    have hta : 0 < t + a.re := by linarith [lt_of_le_of_lt (le_max_right _ _) (Set.mem_Ioi.mp ht)]
    have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have htaC : (t : ℂ) + a ≠ 0 := by
      intro h0
      have := congrArg re h0
      simp at this
      linarith
    have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht0)
    have hpow0 : (t : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
    rw [show (t : ℂ) + (a + 1) = (t + a) + 1 by ring, Complex.Gamma_add_one _ htaC,
      cpow_add _ _ htC, cpow_one]
    field_simp

@[dlmf 5.11.E12]
theorem Gamma_ratio_power {a b : ℂ} :
    Tendsto (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) /
      ((t : ℂ) ^ (a - b))) atTop (𝓝 1) := by
  have h := (tendsto_Gamma_add_div_Gamma_mul_cpow a).div
    (tendsto_Gamma_add_div_Gamma_mul_cpow b) one_ne_zero
  rw [div_one] at h
  apply h.congr'
  filter_upwards [Ioi_mem_atTop 0] with t ht
  have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  have hGt : Complex.Gamma t ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by simpa using ht)
  have hpa : (t : ℂ) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  have hpb : (t : ℂ) ^ b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl htC)
  simp only [Pi.div_apply]
  rw [cpow_sub _ _ htC]
  field_simp

/-- Gamma-ratio coefficients, obtained by exponentiating the difference of
Bernoulli-polynomial expansions of `log Γ(z+a)` and `log Γ(z+b)`.
The recurrence defines all orders, including the higher coefficients needed in remainders. -/
@[dlmf 5.11.E15]
def stirlingRatioG (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | n + 1 => (∑ k : Fin (n + 1),
      (-1 : ℂ) ^ k.val *
        (Polynomial.aeval a (Polynomial.bernoulli (k.val + 2)) -
          Polynomial.aeval b (Polynomial.bernoulli (k.val + 2))) / (k.val + 2) *
        stirlingRatioG a b (n - k.val)) / (n + 1)
termination_by n => n

/-- The all-order positive-ray Gamma-ratio expansion with its order-dependent remainder. -/
@[dlmf 5.11.E13]
theorem Gamma_ratio_expansion (a b : ℂ) (n : ℕ) {x : ℝ} (hx : 1 < x) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) / Complex.Gamma (t + b) -
        (t : ℂ) ^ (a - b) * ∑ k ∈ Finset.range n, stirlingRatioG a b k / (t : ℂ) ^ k)
      (fun t : ℝ => (t : ℂ) ^ (a - b - n)) := by
  sorry

/-- The inverse-factorial Gamma-ratio expansion. The remainder retains the
parameter-dependent leading power `a + b - c`, which cannot be omitted. -/
@[dlmf 5.11.E19]
theorem Gamma_ratio_three {a b c : ℂ} {x : ℝ} (hx : 1 < x) (n : ℕ) :
    Asymptotics.IsBigO atTop
      (fun t : ℝ => Complex.Gamma (t + a) * Complex.Gamma (t + b) / Complex.Gamma (t + c) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * poch (c - a) k * poch (c - b) k / k.factorial *
            Complex.Gamma (a + b - c + t - k))
      (fun t : ℝ => Complex.Gamma t * (t : ℂ) ^ (a + b - c - n)) := by
  sorry

end AAR.Gamma
