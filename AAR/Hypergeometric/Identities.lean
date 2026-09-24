/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import AAR.Hypergeometric.EulerIntegral
public import AAR.Hypergeometric.Transformations
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
  sorry

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
