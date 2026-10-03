/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Hypergeometric.EulerIntegral
public import AAR.Hypergeometric.Transformations
public import AAR.Hypergeometric.FurtherTransformations
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Summation identities and Chapter 3 transformations (AAR §§2.7–2.8, 3.3–3.5)

Kummer's theorem, Dixon's theorem, Whipple's `₇F₆` transformation, and Dougall's bilateral
sum are the main closed-form identities of AAR Chapter 3 that are absent from Mathlib.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

/-- Kummer's theorem:
`₂F₁(a,b;1+a-b;-1) = Γ(1+a-b) Γ(1+a/2) / (Γ(1+a) Γ(1+a/2-b))`. -/
@[dlmf 15.4.E26]
theorem kummer_theorem {a b : ℂ}
    (h : ∀ k : ℕ, (1 + a - b : ℂ) ≠ -k)
    (ha : ∀ k : ℕ, (1 + a / 2 : ℂ) ≠ -k) (hb : b.re < 1 / 2) :
    ₂F₁ a b (1 + a - b) (-1 : ℂ) =
      Gamma (1 + a - b) * Gamma (1 + a / 2) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b)) := by
  set C := 1 + a - b with hCdef
  have hC' : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ) := by
    rw [show a - b + 1 = C by rw [hCdef]; ring]; exact h
  have hre : 0 < (C - a - b).re := by
    rw [show C - a - b = 1 - 2 * b by rw [hCdef]; ring]; simp; linarith
  have hre' : 0 < (C - a / 2 - (a / 2 - b + 1 / 2)).re := by
    rw [show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring]; norm_num
  -- The series as a power series with coefficients multiplied by `(-1)^n`.
  have htsum : ∀ x : ℂ, ₂F₁ a b C x = ∑' n, gaussHGCoeff a b C n * x ^ n := by
    intro x
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul]
    congr 1
    funext n
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  have hsum : Summable fun n => gaussHGCoeff a b C n * (-1 : ℂ) ^ n :=
    ordinaryHypergeometric_summable_of_mem_sphere (z := -1) (by simp) hre
  have habel := Complex.tendsto_tsum_powerSeries_nhdsWithin_lt
    (f := fun n => gaussHGCoeff a b C n * (-1 : ℂ) ^ n) hsum.hasSum.tendsto_sum_nat
  rw [Filter.tendsto_map'_iff] at habel
  have hneg : Filter.Tendsto (fun x : ℝ => -x) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhdsWithin 1 (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have := (continuous_neg.tendsto (-1 : ℝ)).mono_left
        (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio, Set.mem_Ioi] at hx ⊢; linarith
  have hL : Filter.Tendsto (fun x : ℝ => ₂F₁ a b C (x : ℂ)) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhds (₂F₁ a b C (-1))) := by
    rw [htsum (-1)]
    refine (habel.comp hneg).congr fun x => ?_
    simp only [Function.comp_apply]
    rw [htsum]
    refine tsum_congr fun n => ?_
    push_cast
    rw [neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  -- The right-hand side of 15.8.16 along `x → -1⁺`.
  have hv : Filter.Tendsto (fun x : ℝ => -4 * x / (1 - x) ^ 2) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhdsWithin 1 (Set.Iio 1)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hcont : ContinuousAt (fun x : ℝ => -4 * x / (1 - x) ^ 2) (-1) :=
        ((continuousAt_const.mul continuousAt_id).div
          ((continuousAt_const.sub continuousAt_id).pow 2) (by norm_num))
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
      norm_num at this ⊢
      exact this
    · filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)] with x hx
      simp only [Set.mem_Iio]
      have h1x : 0 < (1 - x) ^ 2 := by nlinarith [hx.2]
      rw [div_lt_one h1x]
      nlinarith [hx.1, hx.2]
  have hR1 := (AAR.Hypergeometric.tendsto_ordinaryHypergeometric_left_one
    (a := a / 2) (b := a / 2 - b + 1 / 2) (c := C) hre').comp hv
  have hR2 : Filter.Tendsto (fun x : ℝ => (1 - (x : ℂ)) ^ (-a)) (nhdsWithin (-1) (Set.Ioi (-1)))
      (nhds ((2 : ℂ) ^ (-a))) := by
    have h2 : (2 : ℂ) ∈ slitPlane := by simp
    have h1 := ((show Continuous (fun x : ℝ => (1 : ℂ) - x) by fun_prop).tendsto (-1 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (-1 : ℝ)))
    rw [show (1 : ℂ) - ((-1 : ℝ) : ℂ) = 2 by push_cast; ring] at h1
    exact (continuousAt_cpow_const (b := -a) h2).tendsto.comp h1
  have heq : ∀ᶠ x : ℝ in nhdsWithin (-1) (Set.Ioi (-1)), ₂F₁ a b C (x : ℂ) =
      (1 - (x : ℂ)) ^ (-a) * ₂F₁ (a / 2) (a / 2 - b + 1 / 2) C ((-4 * x / (1 - x) ^ 2 : ℝ) : ℂ) := by
    filter_upwards [Ioo_mem_nhdsGT (show (-1 : ℝ) < 0 by norm_num)] with x hx
    have hxn : ‖(x : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_lt]; constructor <;> linarith [hx.1, hx.2]
    have hvn : ‖-4 * (x : ℂ) / (1 - x) ^ 2‖ < 1 := by
      rw [show -4 * (x : ℂ) / (1 - x) ^ 2 = ((-4 * x / (1 - x) ^ 2 : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
      have h1x : 0 < (1 - x) ^ 2 := by nlinarith [hx.2]
      rw [abs_of_pos (div_pos (by nlinarith [hx.2]) h1x), div_lt_one h1x]
      nlinarith [hx.1, hx.2]
    have hq := AAR.Hypergeometric.quadratic_well_poised_minus (a := a) (b := b) hC' hxn hvn
    rw [show a - b + 1 = C by rw [hCdef]; ring] at hq
    rw [hq]
    push_cast
    ring_nf
  have hlim := tendsto_nhds_unique hL ((hR2.mul hR1).congr' (by
    filter_upwards [heq] with x hx
    rw [hx]; rfl))
  rw [hlim, gauss_summation (a := a / 2) (b := a / 2 - b + 1 / 2) h hre',
    show C - a / 2 - (a / 2 - b + 1 / 2) = 1 / 2 by rw [hCdef]; ring,
    show C - a / 2 = 1 + a / 2 - b by rw [hCdef]; ring,
    show C - (a / 2 - b + 1 / 2) = a / 2 + 1 / 2 by rw [hCdef]; ring, Gamma_one_half_eq]
  -- Duplication formula at `s = (a+1)/2`.
  have hdup := Complex.Gamma_mul_Gamma_add_half (a / 2 + 1 / 2)
  rw [show a / 2 + 1 / 2 + 1 / 2 = 1 + a / 2 by ring, show 1 - 2 * (a / 2 + 1 / 2) = -a by ring,
    show 2 * (a / 2 + 1 / 2) = 1 + a by ring] at hdup
  have hsq : ((Real.sqrt Real.pi : ℝ) : ℂ) = (Real.pi : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; ring_nf
  rw [hsq] at hdup
  have hG2 : Gamma (1 + a / 2) ≠ 0 := Complex.Gamma_ne_zero ha
  have h2a : (2 : ℂ) ^ (-a) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl two_ne_zero)
  have hπ : (Real.pi : ℂ) ^ (1 / 2 : ℂ) ≠ 0 :=
    cpow_ne_zero_iff.mpr (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  by_cases hG1 : Gamma (a / 2 + 1 / 2) = 0
  · have : Gamma (1 + a) = 0 := by
      rw [hG1, zero_mul] at hdup
      rcases mul_eq_zero.mp (mul_eq_zero.mp hdup.symm |>.resolve_right hπ) with h' | h'
      · exact h'
      · exact absurd h' h2a
    rw [hG1, this]
    simp
  · have hG3 : Gamma (1 + a) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_mul] at hdup
      exact mul_ne_zero hG1 hG2 hdup
    by_cases hG4 : Gamma (1 + a / 2 - b) = 0
    · rw [hG4]; simp
    · rw [← mul_div_assoc, div_eq_div_iff (mul_ne_zero hG4 hG1) (mul_ne_zero hG3 hG4)]
      linear_combination (-(Gamma C * Gamma (1 + a / 2 - b))) * hdup

/-- Dixon's well-poised `₃F₂(1)` evaluation (AAR Theorem 3.4.1). -/
theorem dixon_sum {a b c : ℂ}
    (h : 0 < (1 + a / 2 - b - c).re)
    (ha : ∀ k : ℕ, (1 + a / 2 : ℂ) ≠ -k)
    (hb : ∀ k : ℕ, (1 + a - b : ℂ) ≠ -k)
    (hc : ∀ k : ℕ, (1 + a - c : ℂ) ≠ -k) :
    (∑' n : ℕ, poch a n * poch b n * poch c n /
        (poch (1 + a - b) n * poch (1 + a - c) n *
          (n.factorial : ℂ))) =
      Gamma (1 + a / 2) * Gamma (1 + a - b) * Gamma (1 + a - c) *
        Gamma (1 + a / 2 - b - c) /
        (Gamma (1 + a) * Gamma (1 + a / 2 - b) * Gamma (1 + a / 2 - c) *
          Gamma (1 + a - b - c)) := by
  sorry

/-- Whipple's terminating very well-poised `₇F₆(1)` transformation into a balanced
`₄F₃(1)`, AAR Theorem 3.4.4. -/
theorem whipple_7F6 {a b c d e : ℂ} (m : ℕ)
    (hden : ∀ z ∈ [a / 2, a - b + 1, a - c + 1, a - d + 1,
      a - e + 1, a + m + 1, d + e - a - m], ∀ k : ℕ, z ≠ -k) :
    (∑ n ∈ Finset.range (m + 1),
      poch a n * poch (a / 2 + 1) n * poch b n * poch c n * poch d n * poch e n *
        poch (-m : ℂ) n /
        (poch (a / 2) n * poch (a - b + 1) n * poch (a - c + 1) n *
          poch (a - d + 1) n * poch (a - e + 1) n * poch (a + m + 1) n * n.factorial)) =
      poch (a + 1) m * poch (a - d - e + 1) m /
        (poch (a - d + 1) m * poch (a - e + 1) m) *
      (∑ n ∈ Finset.range (m + 1),
        poch (a - b - c + 1) n * poch d n * poch e n * poch (-m : ℂ) n /
          (poch (a - b + 1) n * poch (a - c + 1) n *
            poch (d + e - a - m) n * n.factorial)) := by
  sorry

/-- Dougall's bilateral `₂H₂` sum, in Gamma form (AAR Theorem 2.8.2). -/
@[dlmf 15.4.E25]
theorem dougall_bilateral {a b c d : ℂ}
    (ha : ∀ k : ℤ, a ≠ k) (hb : ∀ k : ℤ, b ≠ k)
    (hconv : 1 + (a + b).re < (c + d).re) :
    (∑' n : ℤ, Gamma (a + n) * Gamma (b + n) /
      (Gamma (c + n) * Gamma (d + n))) =
      π ^ 2 * Gamma (c + d - a - b - 1) /
        (sin (π * a) * sin (π * b) * Gamma (c - a) * Gamma (d - a) *
          Gamma (c - b) * Gamma (d - b)) := by
  sorry

/-- The complete elliptic integral of the first kind, defined as the hypergeometric
function of AAR §3.2. -/
@[dlmf 19.5.E1]
def completeEllipticK (k : ℂ) : ℂ :=
  (π / 2) * ₂F₁ (1 / 2 : ℂ) (1 / 2) 1 (k ^ 2)

/-- The inverse square root of the square of a positive real number. -/
lemma cpow_sq_neg_half {x : ℝ} (hx : 0 < x) :
    ((x : ℂ) ^ 2) ^ (-(1 / 2 : ℂ)) = (x : ℂ)⁻¹ := by
  have hh : ((x : ℂ) ^ 2) ^ (1 / 2 : ℂ) = (x : ℂ) := by
    rw [← ofReal_pow, show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      ← ofReal_cpow (sq_nonneg x), ← Real.sqrt_eq_rpow, Real.sqrt_sq hx.le]
  rw [cpow_neg, hh]

/-- The substitution `t = sin² θ` for the beta weight with parameters `1/2, 1/2`. -/
lemma integral_beta_half_weight (f : ℝ → ℂ) :
    (∫ t : ℝ in (0 : ℝ)..1,
      (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t) =
      2 * ∫ θ : ℝ in (0 : ℝ)..(π / 2), f (Real.sin θ ^ 2) := by
  let g : ℝ → ℂ := fun t =>
    (t : ℂ) ^ (-(1 / 2 : ℂ)) * (1 - (t : ℂ)) ^ (-(1 / 2 : ℂ)) * f t
  have hd (θ : ℝ) : HasDerivAt (fun u : ℝ => Real.sin u ^ 2)
      (2 * Real.sin θ * Real.cos θ) θ := by
    convert! (Real.hasDerivAt_sin θ).pow 2 using 1
    simp
  have hnonneg {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
      0 ≤ 2 * Real.sin θ * Real.cos θ := by
    have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
    have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    positivity
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := (0 : ℝ)) (b := π / 2) (g := g)
    (show ContinuousOn (fun θ : ℝ => Real.sin θ ^ 2) (Set.uIcc 0 (π / 2)) by fun_prop)
    (fun θ _ => hd θ) (fun θ hθ => hnonneg (by
      simpa [min_eq_left Real.pi_div_two_pos.le, max_eq_right Real.pi_div_two_pos.le] using hθ))
  simp only [Real.sin_zero, zero_pow (by decide : 2 ≠ 0), Real.sin_pi_div_two,
    one_pow] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_div_two_pos.le
  intro θ hθ
  have hs := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsq : 1 - (Real.sin θ : ℂ) ^ 2 = (Real.cos θ : ℂ) ^ 2 := by
    exact_mod_cast (by nlinarith [Real.sin_sq_add_cos_sq θ] :
      1 - Real.sin θ ^ 2 = Real.cos θ ^ 2)
  simp only [Function.comp_apply, g, real_smul, ofReal_mul, ofReal_ofNat, ofReal_pow]
  rw [hsq, cpow_sq_neg_half hs, cpow_sq_neg_half hc]
  field_simp [ofReal_ne_zero.mpr hs.ne', ofReal_ne_zero.mpr hc.ne']
  apply (div_eq_iff (mul_ne_zero (ofReal_ne_zero.mpr hs.ne')
    (ofReal_ne_zero.mpr hc.ne'))).2
  ring

/-- AAR §3.2: `K(k) = (π/2) ₂F₁(1/2,1/2;1;k²)` is the definition above; the equivalent
integral `∫_0^{π/2} (1-k² sin²θ)^{-1/2} dθ` follows by `t = sin² θ` in Euler's integral. -/
@[dlmf 19.2.E4]
theorem completeEllipticK_eq_integral {k : ℝ} (hk : |k| < 1) :
    completeEllipticK k =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2), (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
  have hhalf : (0 : ℝ) < (1 / 2 : ℂ).re := by norm_num
  have hsub : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  have hz : ‖(k : ℂ) ^ 2‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
    exact pow_lt_one₀ (abs_nonneg k) hk (by decide)
  have hgamma : Gamma (1 / 2 : ℂ) * Gamma (1 / 2) = (π : ℂ) := by
    have h := Gamma_mul_Gamma_one_sub (1 / 2)
    rw [hsub, show (π : ℂ) * (1 / 2) = π / 2 by ring, sin_pi_div_two, div_one] at h
    exact h
  unfold completeEllipticK
  rw [ordinaryHypergeometric_eq_integral hhalf (by rwa [hsub]) hz,
    hsub, Gamma_one, hgamma]
  have hexp : (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) := by ring
  simp only [hexp]
  rw [integral_beta_half_weight]
  have hpi : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hi : (∫ θ : ℝ in (0 : ℝ)..(π / 2),
      (1 - (k : ℂ) ^ 2 * ((Real.sin θ ^ 2 : ℝ) : ℂ)) ^ (-(1 / 2 : ℂ))) =
      ∫ θ : ℝ in (0 : ℝ)..(π / 2),
        (1 - (k : ℂ) ^ 2 * sin θ ^ 2) ^ (-(1 / 2 : ℂ)) := by
    simp only [ofReal_pow, ofReal_sin]
  rw [hi]
  field [hpi]
