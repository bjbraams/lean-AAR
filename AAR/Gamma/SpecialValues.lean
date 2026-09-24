/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import AAR.Gamma.GaussDigamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Special values and extrema (DLMF §5.4)

`Γ(1) = 1` and `Γ(n+1) = n!` are Mathlib. `Γ(1/2) = √π` is Mathlib
`Gamma_one_half_eq`. `ψ(1) = -γ` and `ψ(1/2) = -γ - 2 log 2` are already
tagged in `Digamma` and `GaussDigamma`. Decimal expansions 5.4.7–5.4.10 are
not transcribed. The large-`n` extrema expansion 5.4.20 is deferred.
-/

@[expose] public section

open Complex
open scoped Real ComplexConjugate

noncomputable section

namespace AAR.Gamma

/-- Double factorial via Gamma, even case. -/
@[dlmf 5.4.E2]
theorem doubleFactorial_even (n : ℕ) :
    ((2 * n).doubleFactorial : ℂ) =
      (2 : ℂ) ^ n * Complex.Gamma (n + 1) := by
  simp [Nat.doubleFactorial_two_mul, Complex.Gamma_nat_eq_factorial]

@[dlmf 5.4.E2]
theorem doubleFactorial_odd (n : ℕ) :
    ((2 * n + 1).doubleFactorial : ℂ) =
      (π : ℂ) ^ (-(1 / 2 : ℂ)) * (2 : ℂ) ^ ((2 * n + 1 : ℂ) / 2 + 1 / 2) *
        Complex.Gamma ((2 * n + 1 : ℂ) / 2 + 1) := by
  have hexp : ((2 * n + 1 : ℂ) / 2 + 1 / 2) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
  have harg : ((2 * n + 1 : ℂ) / 2 + 1) = ((((n + 1 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) := by
    push_cast; ring
  have h2 : (2 * (n + 1) - 1 : ℕ) = 2 * n + 1 := by omega
  rw [hexp, harg, cpow_natCast, Complex.Gamma_ofReal, Real.Gamma_nat_add_half, h2]
  have hsqrt : ((Real.sqrt π : ℝ) : ℂ) = (π : ℂ) ^ (1 / 2 : ℂ) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow Real.pi_nonneg]; push_cast; rfl
  have hpi : (π : ℂ) ^ (-(1 / 2 : ℂ)) * (π : ℂ) ^ (1 / 2 : ℂ) = 1 := by
    rw [← cpow_add _ _ (ofReal_ne_zero.mpr Real.pi_ne_zero)]; simp
  rw [ofReal_div, ofReal_mul, ofReal_pow, ofReal_natCast, ofReal_ofNat, hsqrt]
  have h2ne : (2 : ℂ) ^ (n + 1) ≠ 0 := pow_ne_zero _ two_ne_zero
  field_simp
  linear_combination (-((2 * n + 1).doubleFactorial : ℂ)) * hpi

/-- `Γ(z) Γ(z̄) = |Γ(z)|²`. -/
lemma Gamma_mul_Gamma_conj (z : ℂ) :
    Complex.Gamma z * Complex.Gamma (conj z) = (‖Complex.Gamma z‖ : ℂ) ^ 2 := by
  rw [Complex.Gamma_conj, mul_conj, Complex.normSq_eq_norm_sq, ofReal_pow]

@[dlmf 5.4.E3]
theorem norm_Gamma_mul_I (y : ℝ) (hy : y ≠ 0) :
    ‖Complex.Gamma (I * y)‖ = Real.sqrt (π / (y * Real.sinh (π * y))) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hz : I * (y : ℂ) ≠ 0 := mul_ne_zero I_ne_zero hy'
  have hconj : conj (I * (y : ℂ)) = -(I * y) := by simp [neg_mul]
  have hnorm : Complex.Gamma (I * y) * Complex.Gamma (-(I * y)) =
      ‖Complex.Gamma (I * y)‖ ^ 2 := by
    rw [← hconj]; exact Gamma_mul_Gamma_conj _
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (I * y)
  have h1 : Complex.Gamma (1 - I * y) = -(I * y) * Complex.Gamma (-(I * y)) := by
    have := Complex.Gamma_add_one (-(I * y)) (neg_ne_zero.mpr hz)
    rw [← this]; ring_nf
  have hsin : sin (π * (I * y)) = I * Real.sinh (π * y) := by
    have hsplit : (π : ℂ) * (I * y) = (0 : ℂ) + ((π * y : ℝ) : ℂ) * I := by push_cast; ring
    rw [hsplit, sin_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_sinh]
    ring
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  rw [h1, hsin, eq_div_iff (mul_ne_zero I_ne_zero hsinh)] at hrefl
  have hsq : (‖Complex.Gamma (I * y)‖ ^ 2 : ℂ) = ((π / (y * Real.sinh (π * y)) : ℝ) : ℂ) := by
    rw [← hnorm, ofReal_div, ofReal_mul, eq_div_iff (mul_ne_zero hy' hsinh)]
    linear_combination hrefl +
      Complex.Gamma (I * y) * Complex.Gamma (-(I * y)) * Real.sinh (π * y) * y * I_sq
  have hsq' : ‖Complex.Gamma (I * y)‖ ^ 2 = π / (y * Real.sinh (π * y)) := by exact_mod_cast hsq
  rw [← hsq', Real.sqrt_sq (norm_nonneg _)]

@[dlmf 5.4.E4]
theorem Gamma_half_add_mul_I (y : ℝ) :
    Complex.Gamma (1 / 2 + I * y) * Complex.Gamma (1 / 2 - I * y) =
      ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 ∧
    ‖Complex.Gamma (1 / 2 + I * y)‖ ^ 2 = π / Real.cosh (π * y) := by
  let z : ℂ := 1 / 2 + I * y
  have hstar : star z = 1 / 2 - I * y := by
    simp [z, star_add, star_mul]
    ring
  have harg : (1 : ℂ) - z = 1 / 2 - I * y := by
    simp [z]
    ring
  have hprod :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) = π / sin (π * z) := by
    simpa [harg] using Complex.Gamma_mul_Gamma_one_sub z
  have hnorm :
      Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) =
        ‖Complex.Gamma z‖ ^ 2 := by
    rw [← hstar]; exact Gamma_mul_Gamma_conj z
  have hsin : sin (π * z) = Real.cosh (π * y) := by
    have hsplit : (π : ℂ) * z = (π / 2 : ℂ) + (↑(π * y) : ℂ) * I := by
      simp [z, mul_add]
      ring
    rw [hsplit, sin_add_mul_I]
    simp [Complex.sin_pi_div_two, Complex.cos_pi_div_two, Complex.ofReal_cosh]
  refine ⟨hnorm, ?_⟩
  have hℂ : (‖Complex.Gamma z‖ ^ 2 : ℂ) = (π / Real.cosh (π * y) : ℂ) := by
    calc
      (‖Complex.Gamma z‖ ^ 2 : ℂ) =
          Complex.Gamma z * Complex.Gamma (1 / 2 - I * y) := hnorm.symm
      _ = π / sin (π * z) := hprod
      _ = π / Real.cosh (π * y) := by rw [hsin]
  exact_mod_cast hℂ

@[dlmf 5.4.E5]
theorem Gamma_quarter_mul_I (y : ℝ) :
    Complex.Gamma (1 / 4 + I * y) * Complex.Gamma (3 / 4 - I * y) =
      π * (Real.sqrt 2 : ℂ) / (Real.cosh (π * y) + I * Real.sinh (π * y)) := by
  have harg : (1 : ℂ) - (1 / 4 + I * y) = 3 / 4 - I * y := by ring
  rw [← harg, Complex.Gamma_mul_Gamma_one_sub]
  have hsplit : (π : ℂ) * (1 / 4 + I * y) = ((π / 4 : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [hsplit, sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, Real.sin_pi_div_four,
    Real.cos_pi_div_four, ← ofReal_cosh, ← ofReal_sinh]
  have hden : (Real.cosh (π * y) : ℂ) + I * Real.sinh (π * y) ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.zero_re] at this
    linarith [Real.cosh_pos (π * y)]
  have hs2 : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hsq : (Real.sqrt 2 : ℂ) * Real.sqrt 2 = 2 := by
    exact_mod_cast Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hden' : ((Real.sqrt 2 : ℂ) / 2) * Real.cosh (π * y) +
      ((Real.sqrt 2 : ℂ) / 2) * Real.sinh (π * y) * I ≠ 0 := by
    have : ((Real.sqrt 2 : ℂ) / 2) * Real.cosh (π * y) +
        ((Real.sqrt 2 : ℂ) / 2) * Real.sinh (π * y) * I =
        (Real.sqrt 2 / 2) * (Real.cosh (π * y) + I * Real.sinh (π * y)) := by ring
    rw [this]
    exact mul_ne_zero (div_ne_zero hs2 two_ne_zero) hden
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [div_eq_div_iff hden' hden]
  linear_combination (-((π : ℂ) * (Real.cosh (π * y) + I * Real.sinh (π * y)) / 2)) * hsq

@[dlmf 5.4.E11]
theorem deriv_Gamma_one : deriv Complex.Gamma 1 = -Real.eulerMascheroniConstant := by
  exact Complex.hasDerivAt_Gamma_one.deriv

@[dlmf 5.4.E12]
theorem trigamma_one : Real.trigamma 1 = π ^ 2 / 6 := by
  rw [Real.trigamma_eq_tsum (by positivity : (0 : ℝ) < 1)]
  have hshift : HasSum (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℝ) ^ 2)) (π ^ 2 / 6) := by
    have hiff :=
      hasSum_nat_add_iff' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) (g := π ^ 2 / 6) 1
    simpa using (hiff.mpr hasSum_zeta_two)
  refine (tsum_congr fun n => ?_).trans hshift.tsum_eq
  simp [inv_pow, add_comm]

@[dlmf 5.4.E13]
theorem trigamma_one_div_two : Real.trigamma (1 / 2) = π ^ 2 / 2 := by
  rw [Real.trigamma_eq_tsum (by positivity : (0 : ℝ) < 1 / 2)]
  set f : ℕ → ℝ := fun n => (1 : ℝ) / (n : ℝ) ^ 2 with hf
  have hall : HasSum f (π ^ 2 / 6) := hasSum_zeta_two
  have heven : HasSum (fun k : ℕ => f (2 * k)) (π ^ 2 / 24) := by
    have h := hall.mul_left (1 / 4)
    convert h using 1
    · funext k
      simp only [hf]
      push_cast
      ring
    · ring
  have hodd_s : Summable (fun k : ℕ => f (2 * k + 1)) :=
    hall.summable.comp_injective
      ((add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' ℕ)))
  have hsum := heven.even_add_odd hodd_s.hasSum
  have hodd : ∑' k : ℕ, f (2 * k + 1) = π ^ 2 / 8 := by
    have := hall.unique hsum
    linarith
  have hterm : ∀ n : ℕ, ((1 / 2 : ℝ) + n)⁻¹ ^ 2 = 4 * f (2 * n + 1) := by
    intro n
    simp only [hf]
    push_cast
    field_simp
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, hodd]
  ring

@[dlmf 5.4.E15]
theorem digamma_nat_add_half (n : ℕ) (hn : 0 < n) :
    Real.digamma (n + 1 / 2) =
      -Real.eulerMascheroniConstant - 2 * Real.log 2 +
        2 * ∑ k ∈ Finset.range n, (1 / (2 * (k : ℝ) + 1)) := by
  have h := Real.digamma_add_nat (by norm_num : (0 : ℝ) < 1 / 2) n
  rw [add_comm (1 / 2 : ℝ), Real.digamma_one_div_two] at h
  rw [h, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  field_simp
  ring

/-- The digamma function commutes with complex conjugation. -/
lemma digamma_conj (s : ℂ) : Complex.digamma (conj s) = conj (Complex.digamma s) := by
  have hfun : (conj ∘ Complex.Gamma ∘ conj) = Complex.Gamma := by
    funext z
    simp [Function.comp_def, Complex.Gamma_conj]
  have hderiv : deriv Complex.Gamma (conj s) = conj (deriv Complex.Gamma s) := by
    have h := congrFun (deriv_conj_conj (f := Complex.Gamma)) s
    rw [hfun] at h
    simp only [Function.comp_def] at h
    rw [h, Complex.conj_conj]
  simp only [Complex.digamma_def, logDeriv_apply, hderiv, Complex.Gamma_conj, map_div₀]

lemma neg_I_mul_ofReal_im (r : ℝ) : (-I * (r : ℂ)).im = -r := by
  simp

lemma cot_pi_mul_I (y : ℝ) (hy : y ≠ 0) :
    cot ((π : ℂ) * (I * y)) = -I * (Real.cosh (π * y) / Real.sinh (π * y)) := by
  have hsplit : (π : ℂ) * (I * y) = (0 : ℂ) + ((π * y : ℝ) : ℂ) * I := by push_cast; ring
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hc : cos ((π : ℂ) * (I * y)) = Real.cosh (π * y) := by
    rw [hsplit, cos_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_cosh, ← ofReal_sinh]
    ring
  have hs : sin ((π : ℂ) * (I * y)) = I * Real.sinh (π * y) := by
    rw [hsplit, sin_add_mul_I]
    simp only [Complex.sin_zero, Complex.cos_zero, ← ofReal_cosh, ← ofReal_sinh]
    ring
  rw [Complex.cot, hc, hs, div_eq_iff (mul_ne_zero I_ne_zero hsinh)]
  field_simp
  linear_combination (Real.cosh (π * y) : ℂ) * I_sq

@[dlmf 5.4.E16]
theorem digamma_mul_I_im (y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma (I * y)).im =
      1 / (2 * y) + π / 2 * Real.cosh (π * y) / Real.sinh (π * y) := by
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hint : ∀ n : ℤ, I * (y : ℂ) ≠ n := fun n h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have hneg : ∀ m : ℕ, -(I * (y : ℂ)) ≠ -(m : ℂ) := fun m h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have hconj : conj (I * (y : ℂ)) = -(I * y) := by simp [neg_mul]
  have h1 := Complex.digamma_one_sub hint
  have h2 := Complex.digamma_apply_add_one (-(I * (y : ℂ))) hneg
  rw [show -(I * (y : ℂ)) + 1 = 1 - I * y by ring] at h2
  have h3 : Complex.digamma (-(I * (y : ℂ))) = conj (Complex.digamma (I * y)) := by
    rw [← hconj, digamma_conj]
  have hcot := cot_pi_mul_I y hy
  have hinv : (-(I * (y : ℂ)))⁻¹ = I / y := by
    field_simp
    linear_combination (-1 : ℂ) * I_sq
  have hkey : conj (Complex.digamma (I * (y : ℂ))) - Complex.digamma (I * y) =
      -I * ((π * (Real.cosh (π * y) / Real.sinh (π * y)) + 1 / y : ℝ) : ℂ) := by
    rw [← h3]
    simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one]
    linear_combination h1 - h2 + (π : ℂ) * hcot - hinv
  have him := congrArg Complex.im hkey
  rw [Complex.sub_im, Complex.conj_im, neg_I_mul_ofReal_im] at him
  have hsinh : Real.sinh (π * y) ≠ 0 := Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hval : (Complex.digamma (I * y)).im =
      (π * (Real.cosh (π * y) / Real.sinh (π * y)) + 1 / y) / 2 := by linarith
  rw [hval]
  field_simp
  ring

@[dlmf 5.4.E17]
theorem digamma_half_add_mul_I_im (y : ℝ) :
    (Complex.digamma (1 / 2 + I * y)).im = π / 2 * Real.tanh (π * y) := by
  have hint : ∀ n : ℤ, (1 / 2 + I * (y : ℂ)) ≠ n := by
    intro n h
    have := congrArg Complex.re h
    simp at this
    have h2 : (2 * n : ℤ) = 1 := by exact_mod_cast (by linarith : (2 : ℝ) * n = 1)
    omega
  have hconj : conj (1 / 2 + I * (y : ℂ)) = 1 - (1 / 2 + I * y) := by
    simp only [map_add, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_I,
      Complex.conj_ofReal]
    ring
  have h1 := Complex.digamma_one_sub hint
  rw [← hconj, digamma_conj] at h1
  have hcot : cot ((π : ℂ) * (1 / 2 + I * y)) = -I * Real.tanh (π * y) := by
    have hsplit : (π : ℂ) * (1 / 2 + I * y) = ((π / 2 : ℝ) : ℂ) + ((π * y : ℝ) : ℂ) * I := by
      push_cast; ring
    have hcosh : (Real.cosh (π * y) : ℂ) ≠ 0 := by exact_mod_cast (Real.cosh_pos _).ne'
    rw [Complex.cot, hsplit, sin_add_mul_I, cos_add_mul_I, ← ofReal_sin, ← ofReal_cos,
      Real.sin_pi_div_two, Real.cos_pi_div_two, ← ofReal_cosh, ← ofReal_sinh,
      Real.tanh_eq_sinh_div_cosh, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_zero]
    have hden : (1 : ℂ) * Real.cosh (π * y) + 0 * Real.sinh (π * y) * I ≠ 0 := by
      simpa using hcosh
    rw [div_eq_iff hden]
    field_simp
    ring
  have hkey : conj (Complex.digamma (1 / 2 + I * (y : ℂ))) - Complex.digamma (1 / 2 + I * y) =
      -I * ((π * Real.tanh (π * y) : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
    linear_combination h1 + (π : ℂ) * hcot
  have him := congrArg Complex.im hkey
  rw [Complex.sub_im, Complex.conj_im, neg_I_mul_ofReal_im] at him
  linarith

@[dlmf 5.4.E18]
theorem digamma_one_add_mul_I_im (y : ℝ) (hy : y ≠ 0) :
    (Complex.digamma (1 + I * y)).im =
      -1 / (2 * y) + π / 2 * Real.cosh (π * y) / Real.sinh (π * y) := by
  have hneg : ∀ m : ℕ, I * (y : ℂ) ≠ -(m : ℂ) := fun m h =>
    hy (by have := congrArg Complex.im h; simpa using this)
  have h := Complex.digamma_apply_add_one (I * y) hneg
  rw [add_comm] at h
  rw [h, Complex.add_im, digamma_mul_I_im y hy]
  have hinv : (I * (y : ℂ))⁻¹ = -I * ((1 / y : ℝ) : ℂ) := by
    have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
    rw [Complex.ofReal_div, Complex.ofReal_one]
    field_simp
    linear_combination I_sq
  rw [hinv, neg_I_mul_ofReal_im]
  ring

@[dlmf 5.4.E19]
theorem digamma_rat (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    Real.digamma (p / q) =
      -Real.eulerMascheroniConstant - Real.log q -
        π / 2 * Real.cot (π * p / q) +
        (1 / 2) * ∑ k ∈ Finset.Icc 1 (q - 1),
          Real.cos (2 * π * k * p / q) *
            Real.log (2 - 2 * Real.cos (2 * π * k / q)) := by
  sorry

end AAR.Gamma
