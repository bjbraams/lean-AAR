/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.IncompleteGamma

/-!
# Parabolic cylinder functions (Temme §7.3.3; DLMF Chapter 12)

Weber's function `U(a,z)` is the solution of `w'' = (z²/4 + a) w` that is recessive as
`z → +∞`. We define it, following DLMF 12.4.1, through the even and odd Kummer solutions
`u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` and `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)`
with the initial values 12.2.6 and 12.2.7. This makes `U(a, ·)` entire for every `a`.

## Main results

* `hasDerivAt_pcfU`, `hasDerivAt_pcfUDeriv`, `deriv_deriv_pcfU`: Weber's equation 12.2.2.
* `pcfU_zero`, `pcfUDeriv_zero`: the initial values.
* `pcfU_neg_half`: `U(-1/2, z) = e^{-z²/4}`.
* `pcfU_eq_kummerU`: `U(a,z) = 2^{-1/4-a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)` for `re z > 0`.
* `hasAsymptoticExpansion_pcfU`: `U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s}/(s! (2x²)^s)`.

Whittaker's `D_ν(z) = U(-ν - 1/2, z)` is `pcfD`. The second solution `V(a,z)`, the Wronskians
12.2.10–12.2.12 and the Hermite specializations 12.7.2 are not yet formalized.
-/

@[expose] public section

open Complex Filter MeasureTheory Asymptotics Set
open scoped Real Topology Nat
open AAR.Hypergeometric

noncomputable section

namespace AAR.Confluent

/-- The even solution `u₁(a,z) = e^{-z²/4} M(a/2 + 1/4, 1/2, z²/2)` (DLMF 12.7.12). -/
@[dlmf 12.7.E12]
def pcfEven (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2)

/-- The odd solution `u₂(a,z) = z e^{-z²/4} M(a/2 + 3/4, 3/2, z²/2)` (DLMF 12.7.13). -/
@[dlmf 12.7.E13]
def pcfOdd (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2)

lemma five_halves_ne_neg_nat : ∀ k : ℕ, (5 / 2 : ℂ) ≠ -k := fun k h => by
  have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

lemma hasDerivAt_kummerM_half_sq {α b : ℂ} (hb : ∀ k : ℕ, b ≠ -k) (z : ℂ) :
    HasDerivAt (fun z : ℂ => kummerM α b (z ^ 2 / 2))
      (z * (α / b * kummerM (α + 1) (b + 1) (z ^ 2 / 2))) z := by
  have h := (hasDerivAt_kummerM_shift (a := α) hb (z ^ 2 / 2)).comp z
    (((hasDerivAt_pow 2 z).div_const 2))
  exact h.congr_deriv (by push_cast; ring)

lemma hasDerivAt_exp_neg_sq_div_four (z : ℂ) :
    HasDerivAt (fun z : ℂ => exp (-z ^ 2 / 4)) (-z / 2 * exp (-z ^ 2 / 4)) z := by
  have h := (((hasDerivAt_pow 2 z).neg).div_const 4).cexp
  exact h.congr_deriv (by simp only [Pi.neg_apply]; push_cast; ring)

/-- The derivative of `u₁`. -/
def pcfEvenDeriv (a z : ℂ) : ℂ :=
  z * exp (-z ^ 2 / 4) * (-(1 / 2) * kummerM (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) +
    (a + 1 / 2) * kummerM (a / 2 + 1 / 4 + 1) (1 / 2 + 1) (z ^ 2 / 2))

theorem hasDerivAt_pcfEven (a z : ℂ) : HasDerivAt (pcfEven a) (pcfEvenDeriv a z) z := by
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) half_ne_neg_nat z)
  exact h.congr_deriv (by unfold pcfEvenDeriv; ring)

theorem hasDerivAt_pcfEvenDeriv (a z : ℂ) :
    HasDerivAt (pcfEvenDeriv a) ((z ^ 2 / 4 + a) * pcfEven a z) z := by
  have hb1 : ∀ k : ℕ, (1 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact three_half_ne_neg_nat
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4) half_ne_neg_nat z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 1 / 4 + 1) hb1 z
  have h := (((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    ((h0.const_mul (-(1 / 2))).add (h1.const_mul (a + 1 / 2))))
  have hc := kummerM_ode_contiguous (a := a / 2 + 1 / 4) (b := 1 / 2) half_ne_neg_nat
    (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold pcfEven
  simp only [id, Pi.add_apply, Pi.mul_apply]
  rw [show a / 2 + 1 / 4 + 1 + 1 = a / 2 + 1 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 1 / 4) / 3)) * hc

/-- The derivative of `u₂`. -/
def pcfOddDeriv (a z : ℂ) : ℂ :=
  exp (-z ^ 2 / 4) * ((1 - z ^ 2 / 2) * kummerM (a / 2 + 3 / 4) (3 / 2) (z ^ 2 / 2) +
    (a + 3 / 2) / 3 * z ^ 2 * kummerM (a / 2 + 3 / 4 + 1) (3 / 2 + 1) (z ^ 2 / 2))

theorem hasDerivAt_pcfOdd (a z : ℂ) : HasDerivAt (pcfOdd a) (pcfOddDeriv a z) z := by
  have h := ((hasDerivAt_id z).mul (hasDerivAt_exp_neg_sq_div_four z)).mul
    (hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) three_half_ne_neg_nat z)
  exact h.congr_deriv (by unfold pcfOddDeriv; simp only [id, Pi.mul_apply]; ring)

theorem hasDerivAt_pcfOddDeriv (a z : ℂ) :
    HasDerivAt (pcfOddDeriv a) ((z ^ 2 / 4 + a) * pcfOdd a z) z := by
  have hb1 : ∀ k : ℕ, (3 / 2 + 1 : ℂ) ≠ -k := by
    norm_num; exact five_halves_ne_neg_nat
  have h0 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4) three_half_ne_neg_nat z
  have h1 := hasDerivAt_kummerM_half_sq (α := a / 2 + 3 / 4 + 1) hb1 z
  have h := (hasDerivAt_exp_neg_sq_div_four z).mul
    ((((hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_pow 2 z).div_const 2)).mul h0).add
      (((hasDerivAt_pow 2 z).const_mul ((a + 3 / 2) / 3)).mul h1))
  have hc := kummerM_ode_contiguous (a := a / 2 + 3 / 4) (b := 3 / 2)
    three_half_ne_neg_nat (z := z ^ 2 / 2)
  refine h.congr_deriv ?_
  unfold pcfOdd
  rw [show a / 2 + 3 / 4 + 1 + 1 = a / 2 + 3 / 4 + 2 by ring]
  norm_num at hc ⊢
  linear_combination (exp (-z ^ 2 / 4) * (8 * (a / 2 + 3 / 4) * z / 15)) * hc

/-- **Weber's parabolic cylinder function** `U(a,z)`, the entire solution of
`w'' = (z²/4 + a) w` fixed by its initial values (DLMF 12.2.6, 12.2.7, 12.4.1):
`U(a,z) = U(a,0) u₁(a,z) + U'(a,0) u₂(a,z)`. The reciprocal Gamma factors vanish at the
poles, as for the entire function `1/Γ`. -/
@[dlmf 12.4.E1]
def pcfU (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ * pcfEven a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOdd a z

/-- The derivative `U'(a,z)`. -/
def pcfUDeriv (a z : ℂ) : ℂ :=
  (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 + 1 / 4)) * (Gamma (3 / 4 + a / 2))⁻¹ *
      pcfEvenDeriv a z -
    (Real.sqrt π : ℂ) * (2 : ℂ) ^ (-(a / 2 - 1 / 4)) * (Gamma (1 / 4 + a / 2))⁻¹ * pcfOddDeriv a z

/-- Whittaker's notation `D_ν(z) = U(-ν - 1/2, z)` (DLMF 12.2.5). -/
@[dlmf 12.2.E5]
def pcfD (ν z : ℂ) : ℂ := pcfU (-ν - 1 / 2) z

theorem hasDerivAt_pcfU (a z : ℂ) : HasDerivAt (pcfU a) (pcfUDeriv a z) z :=
  ((hasDerivAt_pcfEven a z).const_mul _).sub ((hasDerivAt_pcfOdd a z).const_mul _)

/-- **Weber's equation** (DLMF 12.2.2): `U''(a,z) = (z²/4 + a) U(a,z)`. -/
@[dlmf 12.2.E2]
theorem hasDerivAt_pcfUDeriv (a z : ℂ) :
    HasDerivAt (pcfUDeriv a) ((z ^ 2 / 4 + a) * pcfU a z) z := by
  refine (((hasDerivAt_pcfEvenDeriv a z).const_mul _).sub
    ((hasDerivAt_pcfOddDeriv a z).const_mul _)).congr_deriv ?_
  rw [pcfU]
  ring

/-- Weber's equation in `deriv` form. -/
theorem deriv_deriv_pcfU (a z : ℂ) :
    deriv (deriv (pcfU a)) z = (z ^ 2 / 4 + a) * pcfU a z := by
  have : deriv (pcfU a) = pcfUDeriv a := funext fun w => (hasDerivAt_pcfU a w).deriv
  rw [this, (hasDerivAt_pcfUDeriv a z).deriv]

/-- `U(a,0)` (DLMF 12.2.6). -/
@[dlmf 12.2.E6]
theorem pcfU_zero (a : ℂ) :
    pcfU a 0 = (Real.sqrt π : ℂ) / ((2 : ℂ) ^ (a / 2 + 1 / 4) * Gamma (3 / 4 + a / 2)) := by
  simp only [pcfU, pcfEven, pcfOdd, zero_pow two_ne_zero, zero_div, neg_zero, Complex.exp_zero,
    kummerM_zero, mul_zero, sub_zero, mul_one, Complex.cpow_neg]
  field_simp

/-- `U'(a,0)` (DLMF 12.2.7). -/
@[dlmf 12.2.E7]
theorem pcfUDeriv_zero (a : ℂ) :
    pcfUDeriv a 0 = -(Real.sqrt π : ℂ) / ((2 : ℂ) ^ (a / 2 - 1 / 4) * Gamma (1 / 4 + a / 2)) := by
  simp only [pcfUDeriv, pcfEvenDeriv, pcfOddDeriv, zero_pow two_ne_zero, zero_div, neg_zero,
    Complex.exp_zero, kummerM_zero, zero_mul, mul_zero, sub_zero, mul_one, add_zero,
    zero_sub, Complex.cpow_neg]
  field_simp

/-- `U(-1/2, z) = D_0(z) = e^{-z²/4}` (DLMF 12.7.1). -/
@[dlmf 12.7.E1]
theorem pcfU_neg_half (z : ℂ) : pcfU (-1 / 2) z = exp (-z ^ 2 / 4) := by
  have h1 : (3 / 4 + -1 / 2 / 2 : ℂ) = 1 / 2 := by ring
  have h2 : (1 / 4 + -1 / 2 / 2 : ℂ) = 0 := by ring
  have h3 : (-1 / 2 / 2 + 1 / 4 : ℂ) = 0 := by ring
  rw [pcfU, pcfEven, h1, h2, h3, Complex.Gamma_zero, inv_zero, Gamma_one_half_eq_sqrt,
    kummerM_of_zero_param, neg_zero, Complex.cpow_zero]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  field_simp
  ring

lemma two_cpow_half : (2 : ℂ) ^ (1 / 2 : ℂ) = (Real.sqrt 2 : ℂ) := by
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (by norm_num)]
  norm_num

/-- **`U(a,z)` through Tricomi's function** (DLMF 12.7.14), for `re z > 0`:
`U(a,z) = 2^{-1/4 - a/2} e^{-z²/4} U(a/2 + 1/4, 1/2, z²/2)`. -/
@[dlmf 12.7.E14]
theorem pcfU_eq_kummerU (a : ℂ) {z : ℂ} (hre : 0 < z.re) :
    pcfU a z = (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-z ^ 2 / 4) *
      kummerU (a / 2 + 1 / 4) (1 / 2) (z ^ 2 / 2) := by
  have hb : ∀ k : ℤ, (1 / 2 : ℂ) ≠ k := fun k h => by
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 : ℝ) * k = 1 := by linarith
    have : (2 : ℤ) * k = 1 := by exact_mod_cast h2
    omega
  set s2 : ℂ := (Real.sqrt 2 : ℂ) with hs2
  have hs2sq : s2 * s2 = 2 := by
    rw [hs2, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hs20 : s2 ≠ 0 := by intro h; rw [h, zero_mul] at hs2sq; norm_num at hs2sq
  have hy : z ^ 2 / 2 = (z / s2) ^ 2 := by
    rw [div_pow, sq s2, hs2sq]
  have hre' : 0 < (z / s2).re := by
    rw [hs2, Complex.div_ofReal_re]
    exact div_pos hre (Real.sqrt_pos.mpr (by norm_num))
  have hsqrt : (z ^ 2 / 2) ^ (1 / 2 : ℂ) = z / s2 := by
    rw [hy, sq_cpow_of_re_pos hre', show (2 : ℂ) * (1 / 2) = 1 by norm_num, Complex.cpow_one]
  have hGm : Gamma (-1 / 2 : ℂ) = -2 * (Real.sqrt π : ℂ) := by
    have h := Complex.Gamma_add_one (-1 / 2 : ℂ) (by norm_num)
    rw [show (-1 / 2 : ℂ) + 1 = 1 / 2 by ring, Gamma_one_half_eq_sqrt] at h
    linear_combination 2 * h
  have h2pow : (2 : ℂ) ^ (-(a / 2 - 1 / 4)) = (2 : ℂ) ^ (-(1 / 4) - a / 2) * s2 := by
    rw [hs2, ← two_cpow_half, ← Complex.cpow_add _ _ two_ne_zero]
    ring_nf
  rw [kummerU_eq_connection _ _ _ hb, kummerUConnection, pcfU, pcfEven, pcfOdd,
    show (1 : ℂ) - 1 / 2 = 1 / 2 by ring, show a / 2 + 1 / 4 - 1 / 2 + 1 = 3 / 4 + a / 2 by ring,
    show (1 / 2 : ℂ) - 1 = -1 / 2 by ring, show (2 : ℂ) - 1 / 2 = 3 / 2 by ring,
    show a / 2 + 3 / 4 = 3 / 4 + a / 2 by ring, show a / 2 + 1 / 4 = 1 / 4 + a / 2 by ring,
    hsqrt, hGm, Gamma_one_half_eq_sqrt, h2pow, show -(1 / 4 + a / 2) = -(1 / 4) - a / 2 by ring]
  have hπ : (Real.sqrt π : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  generalize kummerM (3 / 4 + a / 2) (3 / 2) (z ^ 2 / 2) = N
  generalize kummerM (1 / 4 + a / 2) (1 / 2) (z ^ 2 / 2) = M
  generalize Gamma (1 / 4 + a / 2) = G1
  generalize Gamma (3 / 4 + a / 2) = G3
  field_simp
  linear_combination (-(z * N * G1⁻¹)) * hs2sq

/-- Legendre duplication for Pochhammer symbols: `(2c)_{2s} = 4^s (c)_s (c + 1/2)_s`. -/
lemma poch_two_mul (c : ℂ) (s : ℕ) :
    poch (2 * c) (2 * s) = 4 ^ s * poch c s * poch (c + 1 / 2) s := by
  induction s with
  | zero => simp [poch_zero]
  | succ s ih =>
    rw [show 2 * (s + 1) = 2 * s + 1 + 1 by ring, poch_succ, poch_succ, ih, poch_succ c,
      poch_succ (c + 1 / 2), pow_succ]
    push_cast
    ring

/-- **Asymptotic expansion of `U(a,x)`** (DLMF 12.9.1, Temme §7.3.3):
`U(a,x) ~ e^{-x²/4} x^{-a-1/2} ∑ (-1)^s (a + 1/2)_{2s} / (s! (2x²)^s)` as `x → +∞`. -/
@[dlmf 12.9.E1]
theorem hasAsymptoticExpansion_pcfU (a : ℂ) :
    HasAsymptoticExpansion atTop
      (fun (s : ℕ) (x : ℝ) => exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)))
      (fun s => (-1) ^ s * poch (a + 1 / 2) (2 * s) / (2 ^ s * s.factorial))
      (fun x : ℝ => pcfU a x) := by
  set α : ℂ := a / 2 + 1 / 4 with hα
  have hsq : Tendsto (fun x : ℝ => x ^ 2 / 2) atTop atTop :=
    (tendsto_pow_atTop two_ne_zero).atTop_div_const two_pos
  have h := (((hasAsymptoticExpansion_kummerU α (1 / 2)).comp_tendsto hsq).mul_left
    (fun x : ℝ => (2 : ℂ) ^ (-(1 / 4) - a / 2) * exp (-(x : ℂ) ^ 2 / 4))).smul_scale
    (κ := fun s => (2 : ℂ) ^ s) (ψ := fun (s : ℕ) (x : ℝ) =>
      exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) (fun s => ?_)
  · refine (h.congr' ?_).congr_coeff ?_
    · filter_upwards [eventually_gt_atTop 0] with x hx
      simp only [Function.comp_apply, smul_eq_mul]
      rw [pcfU_eq_kummerU a (by simpa using hx)]
      push_cast
      ring
    · funext s
      rw [tricomiCoeff, show α - 1 / 2 + 1 = α + 1 / 2 by ring, smul_eq_mul,
        show a + 1 / 2 = 2 * α by rw [hα]; ring, poch_two_mul]
      have hf : (s.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
      rw [show (4 : ℂ) ^ s = 2 ^ s * 2 ^ s by rw [← mul_pow]; norm_num]
      field_simp
  · filter_upwards [eventually_gt_atTop 0] with x hx
    have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
    have hxy : (((x ^ 2 / 2 : ℝ)) : ℂ) ^ (-((s : ℂ) + α)) =
        (x : ℂ) ^ (2 * (-((s : ℂ) + α))) * (2 : ℂ) ^ ((s : ℂ) + α) := by
      rw [show (x ^ 2 / 2 : ℝ) = x ^ 2 * (1 / 2) by ring, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (by positivity) (by norm_num), Complex.ofReal_pow,
        sq_cpow_of_re_pos (by simpa using hx), one_div, Complex.ofReal_inv,
        Complex.inv_cpow _ _ (by norm_num [Complex.arg_ofReal_of_nonneg, Real.pi_pos.ne]),
        ← Complex.cpow_neg]
      push_cast
      ring_nf
    rw [hxy]
    have h2 : (2 : ℂ) ^ (-(1 / 4) - a / 2) * (2 : ℂ) ^ ((s : ℂ) + α) = 2 ^ s := by
      rw [← Complex.cpow_add _ _ two_ne_zero, hα,
        show -(1 / 4) - a / 2 + ((s : ℂ) + (a / 2 + 1 / 4)) = (s : ℂ) by ring,
        Complex.cpow_natCast]
    rw [show (x : ℂ) ^ (2 * (-((s : ℂ) + α))) = (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ)) by
      rw [hα]; ring_nf]
    linear_combination (exp (-(x : ℂ) ^ 2 / 4) * (x : ℂ) ^ (-a - 1 / 2 - 2 * (s : ℂ))) * h2

end AAR.Confluent
