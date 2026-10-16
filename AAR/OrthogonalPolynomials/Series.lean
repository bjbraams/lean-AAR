/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Explicit
public import AAR.Bessel.Basic
public import AAR.OrthogonalPolynomials.Differential
public import AAR.OrthogonalPolynomials.GegenbauerSeries
public import AAR.OrthogonalPolynomials.LaguerreSeries
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
/-!
# Generating functions, connection formulas, and linearization

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

/-- Recover a scalar power series from its sums on the unit disk. -/
lemma scalarSeries_unique {c d : ℕ → ℂ} {f : ℂ → ℂ}
    (hc : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => c n * z ^ n) (f z))
    (hd : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => d n * z ^ n) (f z)) : c = d := by
  have series {e : ℕ → ℂ}
      (he : ∀ z : ℂ, ‖z‖ < 1 → HasSum (fun n => e n * z ^ n) (f z)) :
      HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars ℂ e) 0
        ((1 / 2 : NNReal) : ENNReal) := by
    refine ⟨?_, by norm_num, ?_⟩
    · apply FormalMultilinearSeries.le_radius_of_summable_norm
      simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using
        (he (1 / 2) (by norm_num)).summable.norm
    · intro z hz
      have hzNN : ‖z‖₊ < (1 / 2 : NNReal) := by
        simpa only [Metric.mem_eball, edist_zero_right, enorm_lt_coe] using hz
      have hz' : ‖z‖ < (1 / 2 : ℝ) := by exact_mod_cast hzNN
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
        he z (by linarith)
  exact FormalMultilinearSeries.ofScalars_series_injective ℂ ℂ
    ((series hc).hasFPowerSeriesAt.eq_formalMultilinearSeries (series hd).hasFPowerSeriesAt)

/-- Cauchy product of scalar series, written as a coefficient convolution. -/
lemma hasSum_scalar_convolution {c d : ℕ → ℂ} {z u v : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u)
    (hd : HasSum (fun n => d n * z ^ n) v) :
    HasSum (fun n => (∑ k ∈ Finset.range (n + 1), c k * d (n - k)) * z ^ n) (u * v) := by
  have h := hasSum_sum_range_mul_of_summable_norm hc.summable.norm hd.summable.norm
  rw [hc.tsum_eq, hd.tsum_eq] at h
  refine h.congr_fun fun n => ?_
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by simpa using Finset.mem_range.mp hk
  have hp : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hk']
  rw [hp]
  ring


/-- Insert zero odd coefficients into the exponential series. -/
lemma hasSum_exp_quadratic (q z : ℂ) :
    HasSum (fun n : ℕ => (if n % 2 = 0 then q ^ (n / 2) / (n / 2)! else 0) * z ^ n)
      (exp (q * z ^ 2)) := by
  have hinj : Function.Injective (fun k : ℕ => 2 * k) := by intro i j h; dsimp at h; omega
  apply (hinj.hasSum_iff (fun n hn => ?_)).mp
  · convert NormedSpace.expSeries_div_hasSum_exp (q * z ^ 2) using 1
    · funext k
      simp only [Function.comp_apply, Nat.mul_mod_right, ↓reduceIte, Nat.mul_div_cancel_left,
        Nat.ofNat_pos, mul_pow, pow_mul]
      ring
    · simp only [Complex.exp_eq_exp_ℂ]
  · have hodd : n % 2 ≠ 0 := by
      intro he
      exact hn ⟨n / 2, by dsimp; omega⟩
    simp [hodd]

/-- Sum the even-indexed terms of a finite interval. -/
lemma sum_even_range (f : ℕ → ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k % 2 = 0 then f k else 0) =
      ∑ k ∈ Finset.range (n / 2 + 1), f (2 * k) := by
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun k _ => 2 * k)
  · intro k hk
    simp only [Finset.mem_range, Finset.mem_filter] at hk ⊢
    omega
  · intro i hi j hj he
    omega
  · intro k hk
    simp only [Finset.mem_filter, Finset.mem_range] at hk
    refine ⟨k / 2, Finset.mem_range.mpr (by omega), by omega⟩
  · intro k hk
    rfl

/-- A quadratic exponential times the Hermite generating function. -/
lemma hasSum_exp_quadratic_mul_hermite (q lam x z : ℂ) :
    HasSum (fun n : ℕ => (∑ k ∈ Finset.range (n / 2 + 1),
      q ^ k / k ! * ((aeval x (hermitePhys (n - 2 * k)) : ℂ) / (n - 2 * k)! *
        lam ^ (n - 2 * k))) * z ^ n)
      (exp (q * z ^ 2 + (2 * x * (lam * z) - (lam * z) ^ 2))) := by
  have hh : HasSum (fun n => ((aeval x (hermitePhys n) : ℂ) / n ! * lam ^ n) * z ^ n)
      (exp (2 * x * (lam * z) - (lam * z) ^ 2)) := by
    convert hasSum_hermitePhys_generating_function x (lam * z) using 1
    funext n; rw [mul_pow]; ring
  have h := hasSum_scalar_convolution (hasSum_exp_quadratic q z) hh
  rw [← exp_add] at h
  convert h using 1
  funext n
  congr 1
  simp_rw [ite_mul, zero_mul]
  rw [sum_even_range]
  simp

/-- The factorial ratio in the even-indexed Hermite formulas. -/
lemma poch_neg_nat_even_mul_factorial {n k : ℕ} (hk : 2 * k ≤ n) :
    poch (-(n : ℂ)) (2 * k) * ((n - 2 * k)! : ℂ) = n ! := by
  have h := poch_neg_nat_mul_factorial hk
  simpa [pow_mul] using h


@[dlmf 18.12.E1]
theorem jacobi_generating_function {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => jacobiP α β n x * z ^ n)
      ((2 : ℂ) ^ (α + β) / ((1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) ^ α *
        (1 + (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) ^ β)) := by
  sorry

@[dlmf 18.12.E4]
theorem gegenbauer_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => gegenbauer lam n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-lam)) := by
  have h := hasSum_coeff_gegenbauerSeries_mul_pow lam (Real.arccos x) hz
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at h
  refine h.congr_fun fun n => ?_
  rw [ofReal_eq_half_add_inv_of_abs_le_one hx,
    gegenbauer_eq_coeff_gegenbauerSeries hlam (Complex.exp_ne_zero _)]

@[dlmf 18.12.E5]
theorem gegenbauer_weighted_generating_function {lam : ℂ} (hlam : -1 / 2 < lam.re) (hlam0 : lam ≠ 0)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (n + 2 * lam) / (2 * lam) * gegenbauer lam n x * z ^ n)
      ((1 - x * z) / (1 - 2 * x * z + z ^ 2) ^ (lam + 1)) := by
  set w := exp (Real.arccos x * I)
  have hw : w ≠ 0 := Complex.exp_ne_zero _
  have hQ := hasSum_coeff_gegenbauerSeries_mul_pow (lam + 1) (Real.arccos x) hz
  rw [Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2] at hQ
  have h := hasSum_coeff_one_sub_mul hQ ((w + w⁻¹) / 2)
  rw [← weightedGegenbauerSeries_eq hlam0 hw, ← ofReal_eq_half_add_inv_of_abs_le_one hx] at h
  rw [div_eq_mul_inv, ← Complex.cpow_neg]
  refine h.congr_fun fun n => ?_
  rw [coeff_weightedGegenbauerSeries hlam0, ofReal_eq_half_add_inv_of_abs_le_one hx,
    gegenbauer_eq_coeff_gegenbauerSeries hlam hw]

/-- Generating function of a sequence with constant-coefficient three-term recurrence. -/
lemma hasSum_of_three_term {a : ℕ → ℂ} {p q z : ℂ}
    (hrec : ∀ n, a (n + 2) = p * a (n + 1) + q * a n) (hs : Summable fun n => a n * z ^ n)
    (hD : 1 - p * z - q * z ^ 2 ≠ 0) :
    HasSum (fun n => a n * z ^ n) ((a 0 + (a 1 - p * a 0) * z) / (1 - p * z - q * z ^ 2)) := by
  set S := ∑' n, a n * z ^ n
  have h0 := hs.hasSum
  have h1 := (hasSum_nat_add_iff' 1).mpr h0
  have h2 := (hasSum_nat_add_iff' 2).mpr h0
  have h2' : HasSum (fun n => a (n + 2) * z ^ (n + 2))
      (p * z * (S - ∑ i ∈ Finset.range 1, a i * z ^ i) + q * z ^ 2 * S) := by
    have := (h1.mul_left (p * z)).add (h0.mul_left (q * z ^ 2))
    refine this.congr_fun fun n => ?_
    simp only [hrec]
    ring
  have heq := h2.unique h2'
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one,
    pow_one] at heq
  convert h0 using 1
  rw [div_eq_iff hD]
  linear_combination -heq

/-- `1 - 2xz + z²` does not vanish for `|x| ≤ 1` and `‖z‖ < 1`. -/
lemma one_sub_two_mul_add_sq_ne_zero {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    1 - 2 * x * z + z ^ 2 ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [sq] at hre him
  have hn : z.re ^ 2 + z.im ^ 2 < 1 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    nlinarith [norm_nonneg z]
  have hx2 : x ^ 2 ≤ 1 := by nlinarith [abs_nonneg x, sq_abs x]
  rcases mul_eq_zero.mp (show z.im * (z.re - x) = 0 by linarith) with hb | ha
  · rw [hb] at hre hn
    nlinarith [sq_nonneg (z.re - x)]
  · have : z.re = x := by linarith
    rw [this] at hre hn
    nlinarith

/-- Chebyshev polynomials at a real point are real. -/
lemma chebyshevT_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.T ℂ n).eval (x : ℂ) = ((Chebyshev.T ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_T (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- Chebyshev polynomials of the second kind at a real point are real. -/
lemma chebyshevU_eval_ofReal (n : ℤ) (x : ℝ) :
    (Chebyshev.U ℂ n).eval (x : ℂ) = ((Chebyshev.U ℝ n).eval x : ℝ) := by
  rw [← Chebyshev.map_U (algebraMap ℝ ℂ), eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) x

/-- `|Uₙ(x)| ≤ n + 1` on `[-1, 1]`. -/
lemma abs_eval_U_real_le {x : ℝ} (hx : |x| ≤ 1) (n : ℕ) :
    |(Chebyshev.U ℝ n).eval x| ≤ n + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := Chebyshev.U_eq_X_mul_U_add_T ℝ (n : ℤ)
    rw [show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring] at h
    rw [h, eval_add, eval_mul, eval_X]
    have hT := Chebyshev.abs_eval_T_real_le_one ((n + 1 : ℕ) : ℤ) hx
    calc |x * (Chebyshev.U ℝ n).eval x + (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x|
        ≤ |x| * |(Chebyshev.U ℝ n).eval x| + 1 := by
          rw [← abs_mul]; exact (abs_add_le _ _).trans (by linarith)
      _ ≤ 1 * (n + 1) + 1 := by gcongr
      _ = ((n + 1 : ℕ) : ℝ) + 1 := by push_cast; ring

@[dlmf 18.12.E8]
theorem chebyshevT_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n) ((1 - x * z) / (1 - 2 * x * z + z ^ 2)) := by
  have hs : Summable fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg z) hz) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevT_eval_ofReal, norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (by positivity) (Chebyshev.abs_eval_T_real_le_one _ hx)
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.T ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.T_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  · simp; ring
  · ring

/-- `1 - z e^{iθ}` lies in the right half-plane for `‖z‖ < 1`. -/
lemma one_sub_mul_exp_re_pos {z : ℂ} (hz : ‖z‖ < 1) (θ : ℝ) :
    0 < (1 - z * exp (θ * I)).re := by
  have h : ‖z * exp (θ * I)‖ < 1 := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hz
  have := Complex.re_le_norm (z * exp (θ * I))
  simp only [sub_re, one_re]
  linarith

@[dlmf 18.12.E9]
theorem chebyshevT_log_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) / (n + 1) * z ^ (n + 1))
      (-log (1 - 2 * x * z + z ^ 2)) := by
  set θ := Real.arccos x with hθ
  have hcos : Real.cos θ = x := Real.cos_arccos (abs_le.mp hx).1 (abs_le.mp hx).2
  set u := z * exp (θ * I) with hu
  set v := z * exp (-θ * I) with hv
  have hun : ‖u‖ < 1 := by rw [hu, norm_mul, norm_exp_ofReal_mul_I, mul_one]; exact hz
  have hvn : ‖v‖ < 1 := by
    rw [hv, norm_mul, show -(θ : ℂ) * I = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
      norm_exp_ofReal_mul_I, mul_one]; exact hz
  have h := (Complex.hasSum_taylorSeries_neg_log' hun).add (Complex.hasSum_taylorSeries_neg_log' hvn)
  have hprod : (1 - u) * (1 - v) = 1 - 2 * x * z + z ^ 2 := by
    rw [← hcos, ofReal_cos, Complex.cos, hu, hv]
    have : exp (θ * I) * exp (-θ * I) = 1 := by rw [← exp_add]; ring_nf; simp
    linear_combination z ^ 2 * this
  have hre1 : 0 < (1 - u).re := one_sub_mul_exp_re_pos hz θ
  have hre2 : 0 < (1 - v).re := by
    have := one_sub_mul_exp_re_pos hz (-θ); push_cast at this; exact this
  have harg1 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre1)
  have harg2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre2)
  have hne1 : 1 - u ≠ 0 := fun h => by rw [h] at hre1; simp at hre1
  have hne2 : 1 - v ≠ 0 := fun h => by rw [h] at hre2; simp at hre2
  have hlog : log ((1 - u) * (1 - v)) = log (1 - u) + log (1 - v) := by
    apply Complex.log_mul hne1 hne2
    constructor <;> linarith [abs_lt.mp harg1, abs_lt.mp harg2, Real.pi_pos]
  rw [← hprod, hlog, neg_add]
  refine h.congr_fun fun n => ?_
  have hT : (Chebyshev.T ℂ ((n + 1 : ℕ) : ℤ)).eval (x : ℂ) = cos ((n + 1 : ℕ) * (θ : ℂ)) := by
    rw [← hcos, ofReal_cos, Chebyshev.T_complex_cos]; push_cast; ring_nf
  push_cast at hT ⊢
  have e1 : exp (θ * I) ^ (n + 1) = exp (((n : ℂ) + 1) * θ * I) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have e2 : exp (-θ * I) ^ (n + 1) = exp (-(((n : ℂ) + 1) * θ * I)) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  rw [hT, Complex.cos, hu, hv, mul_pow, mul_pow, e1, e2]
  field_simp

@[dlmf 18.12.E10]
theorem chebyshevU_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n) ((1 - 2 * x * z + z ^ 2)⁻¹) := by
  have hs : Summable fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded (((summable_pow_mul_geometric_of_norm_lt_one 1
      (show ‖‖z‖‖ < 1 by simpa using hz)).add
      (summable_geometric_of_lt_one (norm_nonneg z) hz))) fun n => ?_
    rw [norm_mul, norm_pow, chebyshevU_eval_ofReal, norm_real, Real.norm_eq_abs, pow_one]
    have := abs_eval_U_real_le hx n
    nlinarith [pow_nonneg (norm_nonneg z) n]
  have h := hasSum_of_three_term (a := fun n : ℕ => (Chebyshev.U ℂ n).eval (x : ℂ))
    (p := 2 * x) (q := -1) (fun n => by
      have := Chebyshev.U_add_two ℂ (n : ℤ)
      rw [show ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 by push_cast; ring,
        show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by push_cast; ring, this]
      simp; ring) hs (by
        have := one_sub_two_mul_add_sq_ne_zero hx hz
        convert this using 1; ring)
  convert h using 2
  simp

@[dlmf 18.12.E11]
theorem legendre_generating_function {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => legendreP n x * z ^ n) ((1 - 2 * x * z + z ^ 2) ^ (-1 / 2 : ℂ)) := by
  simp_rw [legendre_eq_gegenbauer]
  rw [show (-1 / 2 : ℂ) = -(1 / 2) by ring]
  exact gegenbauer_generating_function (by norm_num) hx hz

@[dlmf 18.12.E16]
theorem hermite_generating_function (x z : ℂ) :
    HasSum (fun n : ℕ => aeval x (hermite n) / (n.factorial : ℂ) * z ^ n)
      (exp (x * z - z ^ 2 / 2)) := by
  have hf : Differentiable ℂ (fun y : ℂ => exp (-(y ^ 2 / 2))) := by fun_prop
  have hne : exp (-(x ^ 2 / 2)) ≠ 0 := exp_ne_zero _
  have hderiv (n : ℕ) (y : ℂ) :
      iteratedDeriv n (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
        (-1 : ℂ) ^ n * (aeval y (hermite n) : ℂ) * exp (-(y ^ 2 / 2)) := by
    rw [iteratedDeriv_eq_iterate, mul_assoc]
    induction n generalizing y with
    | zero => simp [hermite_zero]
    | succ n ih =>
      replace ih : deriv^[n] _ = _ := funext ih
      have hgaussian : deriv (fun t : ℂ => exp (-(t ^ 2 / 2))) y =
          -y * exp (-(y ^ 2 / 2)) := by
        rw [deriv_cexp (by fun_prop)]
        simp [pow_two]
        ring
      rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
        pow_succ, hgaussian, hermite_succ, map_sub, map_mul, aeval_X,
        Polynomial.deriv_aeval]
      · ring
      · apply Polynomial.differentiable_aeval
      · fun_prop
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - z)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - z) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => exp (-(y ^ 2 / 2))) x) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [hderiv, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2 / 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermite n) : ℂ) * z ^ n / n ! * exp (-(x ^ 2 / 2)) *
        (exp (-(x ^ 2 / 2)))⁻¹) =
      fun n => (aeval x (hermite n) : ℂ) * z ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - z) ^ 2 / 2)) * (exp (-(x ^ 2 / 2)))⁻¹ =
      exp (x * z - z ^ 2 / 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  rw [hval] at hs'
  convert hs' using 1
  funext n
  ring

/-- The exponential generating function with an arbitrary starting degree. -/
lemma hasSum_hermitePhys_shifted (m : ℕ) (x t : ℂ) :
    HasSum (fun n : ℕ => (aeval x (hermitePhys (m + n)) : ℂ) * t ^ n / n !)
      ((aeval (x - t) (hermitePhys m) : ℂ) * exp (2 * x * t - t ^ 2)) := by
  have hderiv (n : ℕ) (y : ℂ) :
      iteratedDeriv n (fun v : ℂ => (aeval v (hermitePhys m) : ℂ) * exp (-(v ^ 2))) y =
        (-1 : ℂ) ^ n * (aeval y (hermitePhys (m + n)) : ℂ) * exp (-(y ^ 2)) := by
    rw [iteratedDeriv_eq_iterate, mul_assoc]
    induction n generalizing y with
    | zero => simp
    | succ n ih =>
      replace ih := funext ih
      have hg : deriv (fun v : ℂ => exp (-(v ^ 2))) y = -(2 * y) * exp (-(y ^ 2)) := by
        rw [deriv_cexp (by fun_prop)]
        simp [pow_two]; ring
      rw [Function.iterate_succ_apply', ih, deriv_const_mul_field, deriv_fun_mul,
        pow_succ, hg, show m + (n + 1) = (m + n) + 1 by omega, hermitePhys_succ,
        map_sub, map_mul, map_mul, map_ofNat, aeval_X, Polynomial.deriv_aeval]
      · ring
      · apply Polynomial.differentiable_aeval
      · fun_prop
  have hf : Differentiable ℂ (fun y : ℂ => (aeval y (hermitePhys m) : ℂ) * exp (-(y ^ 2))) := by
    apply Differentiable.mul
    · apply Polynomial.differentiable_aeval
    · fun_prop
  have hne : exp (-(x ^ 2)) ≠ 0 := exp_ne_zero _
  have hs := Complex.hasSum_taylorSeries_of_entire (E := ℂ) hf x (x - t)
  have hterm : (fun n : ℕ =>
      (n ! : ℂ)⁻¹ • ((x - t) - x) ^ n •
        iteratedDeriv n (fun y : ℂ => (aeval y (hermitePhys m) : ℂ) * exp (-(y ^ 2))) x) =
      fun n => (aeval x (hermitePhys (m + n)) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) := by
    funext n
    simp only [sub_sub_cancel_left, smul_eq_mul]
    rw [hderiv, neg_pow]
    ring_nf
    rw [mul_comm n 2, pow_mul, neg_one_sq, one_pow]
    ring
  rw [hterm] at hs
  have hs' := hs.mul_right (exp (-(x ^ 2)))⁻¹
  have hsimp : (fun n : ℕ =>
      (aeval x (hermitePhys (m + n)) : ℂ) * t ^ n / n ! * exp (-(x ^ 2)) *
        (exp (-(x ^ 2)))⁻¹) =
      fun n => (aeval x (hermitePhys (m + n)) : ℂ) * t ^ n / n ! := by
    funext n
    field [hne]
  rw [hsimp] at hs'
  have hval : exp (-((x - t) ^ 2)) * (exp (-(x ^ 2)))⁻¹ =
      exp (2 * x * t - t ^ 2) := by
    rw [← div_eq_mul_inv, div_eq_iff hne, ← exp_add]
    congr 1
    ring
  simpa only [mul_assoc, hval] using hs'


/-- Translation of a Hermite polynomial by an arbitrary complex number. -/
lemma hermitePhys_translation (m : ℕ) (x y : ℂ) :
    (aeval (x + y) (hermitePhys m) : ℂ) =
      ∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (2 * y) ^ k *
        aeval x (hermitePhys (m - k)) := by
  have hc := scalarSeries_unique
    (c := fun n => (aeval (x + y) (hermitePhys n) : ℂ) / n !)
    (d := fun n => ∑ k ∈ Finset.range (n + 1),
      ((2 * y) ^ k / k !) * ((aeval x (hermitePhys (n - k)) : ℂ) / (n - k)!))
    (f := fun z => exp (2 * (x + y) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePhys_generating_function _ z).congr_fun (by intro n; ring))
    (fun z _ => by
      have he : HasSum (fun k : ℕ => ((2 * y) ^ k / k !) * z ^ k) (exp (2 * y * z)) := by
        convert NormedSpace.expSeries_div_hasSum_exp (2 * y * z) using 1
        · funext k; rw [mul_pow]; ring
        · simp only [Complex.exp_eq_exp_ℂ]
      have hh : HasSum (fun k => ((aeval x (hermitePhys k) : ℂ) / k !) * z ^ k)
          (exp (2 * x * z - z ^ 2)) :=
        (hasSum_hermitePhys_generating_function x z).congr_fun (by intro k; ring)
      convert hasSum_scalar_convolution he hh using 1
      rw [← exp_add]; congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c m * m !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr m.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have he : (m.choose k : ℂ) * k ! * (m - k)! = m ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using Finset.mem_range.mp hk)
  rw [← he]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - k))]

/-- Multiplication of a power series by a monomial inserts a zero prefix. -/
lemma hasSum_scalar_shift {c : ℕ → ℂ} {z u : ℂ}
    (hc : HasSum (fun n => c n * z ^ n) u) (k : ℕ) :
    HasSum (fun n => (if k ≤ n then c (n - k) else 0) * z ^ n) (z ^ k * u) := by
  apply (hasSum_nat_add_iff' k).mp
  have hzero : ∑ n ∈ Finset.range k, (if k ≤ n then c (n - k) else 0) * z ^ n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp [show ¬k ≤ n by have := Finset.mem_range.mp hn; omega]
  rw [hzero, sub_zero]
  convert hc.mul_left (z ^ k) using 1
  funext n
  simp only [Nat.le_add_left, ↓reduceIte, Nat.add_sub_cancel, pow_add]
  ring

/-- The probabilists' Hermite polynomial as a finite monomial sum. -/
lemma hermite_finite_sum (n : ℕ) (x : ℂ) :
    (aeval x (hermite n) : ℂ) = ∑ k ∈ Finset.range (n / 2 + 1),
      (-1 : ℂ) ^ k * n.factorial /
        (2 ^ k * (k.factorial : ℂ) * (n - 2 * k).factorial) * x ^ (n - 2 * k) := by
  have hc := scalarSeries_unique
    (c := fun j => (aeval x (hermite j) : ℂ) / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (-1 / 2 : ℂ) ^ k / k ! * (x ^ (j - 2 * k) / (j - 2 * k)!))
    (f := fun z => exp (x * z - z ^ 2 / 2))
    (fun z _ => hermite_generating_function x z)
    (fun z _ => by
      have he : HasSum (fun j : ℕ => (x ^ j / j !) * z ^ j) (exp (x * z)) := by
        convert NormedSpace.expSeries_div_hasSum_exp (x * z) using 1
        · funext j; rw [mul_pow]; ring
        · simp only [Complex.exp_eq_exp_ℂ]
      have h := hasSum_scalar_convolution (hasSum_exp_quadratic (-1 / 2) z) he
      rw [← exp_add, show (-1 / 2 : ℂ) * z ^ 2 + x * z = x * z - z ^ 2 / 2 by ring] at h
      convert h using 1
      funext j
      congr 1
      simp_rw [ite_mul, zero_mul]
      rw [sum_even_range]
      simp)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k _
  rw [div_pow]
  ring

@[dlmf 18.18.E10, dlmf 18.18.E38]
theorem laguerre_addition (α β x y : ℂ) (n : ℕ) :
    laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
  have hdiffL : ∀ β : ℂ, Differentiable ℂ fun α : ℂ => laguerreExtended (α + β + 1) n (x + y) :=
    fun β => (differentiable_laguerreExtended n (x + y)).comp
      ((differentiable_id.add_const _).add_const _)
  have hstep : ∀ β : ℂ, -1 < β.re → ∀ α : ℂ, laguerreExtended (α + β + 1) n (x + y) =
      ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x * laguerreExtended β (n - k) y := by
    intro β hβ
    refine eq_of_differentiable_of_re_gt (hdiffL β) ?_
      fun α hα => laguerre_addition_of_re hα hβ x y n
    exact Differentiable.fun_sum fun k _ =>
      (differentiable_laguerreExtended k x).mul (differentiable_const _)
  refine eq_of_differentiable_of_re_gt (f := fun β => laguerreExtended (α + β + 1) n (x + y))
    (g := fun β => ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x *
      laguerreExtended β (n - k) y) ?_ ?_ (fun β hβ => hstep β hβ α) β
  · exact (differentiable_laguerreExtended n (x + y)).comp
      ((differentiable_const _).add differentiable_id |>.add_const _)
  · exact Differentiable.fun_sum fun k _ =>
      (differentiable_const _).mul (differentiable_laguerreExtended (n - k) y)

@[dlmf 18.18.E11, dlmf 18.18.E39]
theorem hermitePhys_addition (a b x y : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (n : ℕ) :
    (aeval (a * x + b * y) (hermitePhys n) : ℝ) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ k * b ^ (n - k) *
        aeval x (hermitePhys k) * aeval y (hermitePhys (n - k)) := by
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hcoeff := scalarSeries_unique
    (c := fun n => (aeval ((a : ℂ) * x + b * y) (hermitePhys n) : ℂ) / n !)
    (d := fun n => ∑ k ∈ Finset.range (n + 1),
      ((aeval (x : ℂ) (hermitePhys k) : ℂ) / k ! * (a : ℂ) ^ k) *
      ((aeval (y : ℂ) (hermitePhys (n - k)) : ℂ) / (n - k) ! * (b : ℂ) ^ (n - k)))
    (f := fun z => exp (2 * ((a : ℂ) * x + b * y) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePhys_generating_function _ z).congr_fun (by intro k; ring))
    (fun z _ => ?_)
  · have h := congrArg (fun c : ℕ → ℂ => c n * n !) hcoeff
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
    have ht (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
        ((aeval (x : ℂ) (hermitePhys k) : ℂ) / k ! * (a : ℂ) ^ k *
          ((aeval (y : ℂ) (hermitePhys (n - k)) : ℂ) / (n - k) ! * (b : ℂ) ^ (n - k))) * n ! =
        (n.choose k : ℂ) * a ^ k * b ^ (n - k) *
          aeval (x : ℂ) (hermitePhys k) * aeval (y : ℂ) (hermitePhys (n - k)) := by
      have he : (n.choose k : ℂ) * k ! * (n - k) ! = n ! := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial (by simpa using Finset.mem_range.mp hk)
      rw [← he]
      field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]
    rw [Finset.sum_congr rfl ht] at h
    have castH (t : ℝ) (j : ℕ) :
        (aeval (t : ℂ) (hermitePhys j) : ℂ) = ((aeval t (hermitePhys j) : ℝ) : ℂ) :=
      aeval_algHom_apply (IsScalarTower.toAlgHom ℤ ℝ ℂ) t (hermitePhys j)
    rw [show (a : ℂ) * x + b * y = ((a * x + b * y : ℝ) : ℂ) by push_cast; rfl] at h
    simp_rw [castH] at h
    exact_mod_cast h
  · have h1 : HasSum (fun k => ((aeval (x : ℂ) (hermitePhys k) : ℂ) / k ! *
        (a : ℂ) ^ k) * z ^ k) (exp (2 * x * (a * z) - (a * z) ^ 2)) := by
      convert hasSum_hermitePhys_generating_function (x : ℂ) (a * z) using 1
      funext k; rw [mul_pow]; ring
    have h2 : HasSum (fun k => ((aeval (y : ℂ) (hermitePhys k) : ℂ) / k ! *
        (b : ℂ) ^ k) * z ^ k) (exp (2 * y * (b * z) - (b * z) ^ 2)) := by
      convert hasSum_hermitePhys_generating_function (y : ℂ) (b * z) using 1
      funext k; rw [mul_pow]; ring
    convert hasSum_scalar_convolution h1 h2 using 1
    rw [← exp_add]
    congr 1
    linear_combination z ^ 2 * hab'

@[dlmf 18.18.E12]
theorem laguerre_multiplication {α : ℂ} (hα : -1 < α.re) (lam x : ℂ) (n : ℕ) :
    laguerre α n (lam * x) / laguerre α n 0 = ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℂ) * lam ^ k * (1 - lam) ^ (n - k) * laguerre α k x / laguerre α k 0 := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  have hL : ∀ m ≤ n, ∀ y, laguerre α m y / laguerre α m 0 =
      ∑ j ∈ Finset.range (n + 1), poch (-(m : ℂ)) j / (poch (α + 1) j * j !) * y ^ j := by
    intro m hm y
    have hp : poch (α + 1) m / m ! ≠ 0 :=
      div_ne_zero (hpk m) (Nat.cast_ne_zero.mpr m.factorial_ne_zero)
    unfold laguerre
    rw [confluentM_zero, mul_one, mul_div_cancel_left₀ _ hp, confluentM_eq_sum_neg_nat]
    refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) fun j _ hj => ?_
    rw [poch_neg_nat_eq_zero (by simpa using hj)]; simp
  rw [hL n le_rfl]
  simp_rw [mul_div_assoc _ (laguerre α _ x)]
  conv_rhs => rw [Finset.sum_congr rfl fun k hk => by
    rw [hL k (by simpa [Nat.lt_succ_iff] using hk) x]]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  have hb := sum_choose_mul_poch_neg_nat_mul_pow hjn lam (1 - lam)
  rw [add_sub_cancel, one_pow, mul_one] at hb
  rw [Finset.sum_congr rfl (g := fun k => (n.choose k : ℂ) * poch (-(k : ℂ)) j * lam ^ k *
    (1 - lam) ^ (n - k) * (x ^ j / (poch (α + 1) j * j !))) (fun k _ => by ring),
    ← Finset.sum_mul, hb, mul_pow]
  ring

@[dlmf 18.18.E13]
theorem hermitePhys_multiplication (lam x : ℂ) (n : ℕ) :
    aeval (lam * x) (hermitePhys n) = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * lam ^ (n - 2 * k) * (lam ^ 2 - 1) ^ k *
        aeval x (hermitePhys (n - 2 * k)) := by
  have hc := scalarSeries_unique
    (c := fun j => (aeval (lam * x) (hermitePhys j) : ℂ) / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (lam ^ 2 - 1) ^ k / k ! *
        ((aeval x (hermitePhys (j - 2 * k)) : ℂ) / (j - 2 * k)! * lam ^ (j - 2 * k)))
    (f := fun z => exp (2 * (lam * x) * z - z ^ 2))
    (fun z _ => (hasSum_hermitePhys_generating_function _ z).congr_fun (by intro j; ring))
    (fun z _ => by
      convert hasSum_exp_quadratic_mul_hermite (lam ^ 2 - 1) lam x z using 1
      congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [← poch_neg_nat_even_mul_factorial hk']
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 2 * k))]

@[dlmf 18.18.E16]
theorem gegenbauer_connection {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : -1 / 2 < μ.re) (n : ℕ) (x : ℂ) :
    gegenbauer μ n x = ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam * poch μ (n - k) / poch (lam + 1) (n - k) *
      (poch (μ - lam) k / k.factorial) * gegenbauer lam (n - 2 * k) x := by
  sorry

@[dlmf 18.18.E17]
theorem monomial_gegenbauer_expansion {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = n.factorial * ∑ k ∈ Finset.range (n / 2 + 1),
      (lam + n - 2 * k) / lam / (poch (lam + 1) (n - k) * k.factorial) * gegenbauer lam (n - 2 * k) x := by
  sorry

@[dlmf 18.18.E18]
theorem laguerre_connection (α β : ℂ) (n : ℕ) (x : ℂ) :
    laguerreExtended β n x = ∑ k ∈ Finset.range (n + 1),
      poch (β - α) (n - k) / (n - k).factorial * laguerreExtended α k x := by
  unfold laguerreExtended
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by simp at hj; omega
  rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
  have hv := poch_add_eq_sum (α + j + 1) (β - α) (n - j)
  rw [show α + j + 1 + (β - α) = β + j + 1 by ring] at hv
  rw [hv, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmN : m ≤ n - j := by simp at hm; omega
  rw [show n - (j + m) = n - j - m by omega, show j + m - j = m by omega,
    Nat.cast_choose ℂ hmN]
  have h1 : ((n - j - m).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : ((n - j).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  field_simp

@[dlmf 18.18.E19]
theorem monomial_laguerre_expansion {α : ℂ} (hα : -1 < α.re) (n : ℕ) (x : ℂ) :
    x ^ n = poch (α + 1) n * ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k / poch (α + 1) k * laguerre α k x := by
  have hc : ∀ k : ℕ, α + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  have hpk : ∀ k, poch (α + 1) k ≠ 0 := poch_ne_zero_of_not_neg_nat hc
  simp_rw [laguerre_eq_sum hc, Finset.mul_sum]
  rw [Finset.sum_comm' (t' := Finset.range (n + 1)) (s' := fun j => Finset.Ico j (n + 1))
    (by intro k j; simp only [Finset.mem_range, Finset.mem_Ico]; omega)]
  have hterm : ∀ j ∈ Finset.range (n + 1), ∑ k ∈ Finset.Ico j (n + 1),
      poch (α + 1) n * (poch (-(n : ℂ)) k / poch (α + 1) k *
        (poch (α + 1 + j) (k - j) / ((k - j).factorial * j.factorial : ℂ) * (-x) ^ j)) =
      poch (α + 1) n * (-x) ^ j * poch (-(n : ℂ)) j / (poch (α + 1) j * j.factorial) *
        0 ^ (n - j) := by
    intro j hj
    have hjn : j ≤ n := by simp at hj; omega
    rw [Finset.sum_Ico_eq_sum_range, show n + 1 - j = (n - j) + 1 by omega]
    have hs := sum_poch_neg_nat_div_factorial_mul_pow (n - j) 1
    rw [sub_self] at hs
    rw [← hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [show j + m - j = m by omega, poch_add (α + 1) j m, poch_add (-(n : ℂ)) j m,
      show -(n : ℂ) + j = -((n - j : ℕ) : ℂ) by push_cast [Nat.cast_sub hjn]; ring]
    have h1 := hpk j
    have h2 : poch (α + 1 + j) m ≠ 0 := by
      have := hpk (j + m); rw [poch_add] at this; exact right_ne_zero_of_mul this
    have h3 : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h4 : (j.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_eq_single n]
  · rw [Nat.sub_self, pow_zero, mul_one, poch_neg_coe_nat, Nat.descFactorial_self, neg_pow]
    have h4 : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    field_simp [hpk n]
    rw [← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow, mul_one]
  · intro j hj hjn
    have : 0 < n - j := by simp at hj; omega
    simp [zero_pow this.ne']
  · simp

@[dlmf 18.18.E20]
theorem monomial_hermitePhys_expansion (n : ℕ) (x : ℂ) :
    (2 * x) ^ n = ∑ k ∈ Finset.range (n / 2 + 1),
      poch (-(n : ℂ)) (2 * k) / k.factorial * aeval x (hermitePhys (n - 2 * k)) := by
  have hc := scalarSeries_unique
    (c := fun j => (2 * x) ^ j / j !)
    (d := fun j => ∑ k ∈ Finset.range (j / 2 + 1),
      (1 : ℂ) ^ k / k ! * ((aeval x (hermitePhys (j - 2 * k)) : ℂ) / (j - 2 * k)! *
        (1 : ℂ) ^ (j - 2 * k)))
    (f := fun z => exp (2 * x * z))
    (fun z _ => by
      convert NormedSpace.expSeries_div_hasSum_exp (2 * x * z) using 1
      · funext j; rw [mul_pow]; ring
      · simp only [Complex.exp_eq_exp_ℂ])
    (fun z _ => by
      convert hasSum_exp_quadratic_mul_hermite 1 1 x z using 1
      congr 1; ring)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 2 * k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [← poch_neg_nat_even_mul_factorial hk']
  simp only [one_pow, mul_one, one_div]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k),
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - 2 * k))]

@[dlmf 18.18.E23]
theorem hermitePhys_linearization (m n : ℕ) (x : ℂ) :
    (aeval x (hermitePhys m) : ℂ) * aeval x (hermitePhys n) =
      ∑ k ∈ Finset.range (min m n + 1), (m.choose k : ℂ) * n.choose k * 2 ^ k * k.factorial *
        aeval x (hermitePhys (m + n - 2 * k)) := by
  have hc := scalarSeries_unique
    (c := fun j => (aeval x (hermitePhys m) : ℂ) * aeval x (hermitePhys j) / j !)
    (d := fun j => ∑ k ∈ Finset.range (m + 1),
      (m.choose k : ℂ) * 2 ^ k *
        (if k ≤ j then (aeval x (hermitePhys (m - k + (j - k))) : ℂ) / (j - k)! else 0))
    (f := fun z => (aeval x (hermitePhys m) : ℂ) * exp (2 * x * z - z ^ 2))
    (fun z _ => ((hasSum_hermitePhys_generating_function x z).mul_left
      (aeval x (hermitePhys m) : ℂ)).congr_fun (by intro j; ring))
    (fun z _ => by
      have hs (k : ℕ) := (hasSum_scalar_shift
        (c := fun j => (aeval x (hermitePhys (m - k + j)) : ℂ) / j !) (z := z)
        ((hasSum_hermitePhys_shifted (m - k) x z).congr_fun (by intro j; ring)) k).mul_left
          ((m.choose k : ℂ) * 2 ^ k)
      have h := hasSum_sum (s := Finset.range (m + 1)) (fun k _ => hs k)
      have hv : (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
          (z ^ k * ((aeval (x - z) (hermitePhys (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
          (aeval x (hermitePhys m) : ℂ) * exp (2 * x * z - z ^ 2) := by
        rw [show (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * 2 ^ k *
            (z ^ k * ((aeval (x - z) (hermitePhys (m - k)) : ℂ) * exp (2 * x * z - z ^ 2)))) =
            (∑ k ∈ Finset.range (m + 1), (m.choose k : ℂ) * (2 * z) ^ k *
              aeval (x - z) (hermitePhys (m - k))) * exp (2 * x * z - z ^ 2) by
          rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro k _; rw [mul_pow]; ring]
        rw [← hermitePhys_translation, sub_add_cancel]
      rw [hv] at h
      simpa only [Finset.sum_mul, mul_assoc] using h)
  have h := congrArg (fun c : ℕ → ℂ => c n * n !) hc
  rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), Finset.sum_mul] at h
  rw [h]
  have hsub : Finset.range (min m n + 1) ⊆ Finset.range (m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub (by
    intro k hk hkn
    have hnk : ¬ k ≤ n := by
      simp only [Finset.mem_range] at hk hkn; omega
    simp [hnk])]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  have hkn : k ≤ n := by have := Finset.mem_range.mp hk; omega
  rw [if_pos hkn, show m - k + (n - k) = m + n - 2 * k by omega]
  have he : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
    exact_mod_cast Nat.choose_mul_factorial_mul_factorial hkn
  rw [← he]
  field_simp [Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (n - k))]

@[dlmf 18.18.E28]
theorem mehler_formula (x y : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (aeval (x : ℂ) (hermitePhys n) : ℂ) * aeval (y : ℂ) (hermitePhys n) /
      (2 ^ n * (n.factorial : ℂ)) * z ^ n)
      ((1 - z ^ 2) ^ (-1 / 2 : ℂ) * exp ((2 * x * y * z - (x ^ 2 + y ^ 2) * z ^ 2) / (1 - z ^ 2))) := by
  sorry


@[dlmf 18.18.E9]
theorem legendre_addition (n : ℕ) (θ ψ phi : ℝ) :
    legendreP n (Real.cos θ * Real.cos ψ + Real.sin θ * Real.sin ψ * Real.cos phi) =
      legendreP n (Real.cos θ) * legendreP n (Real.cos ψ) +
      2 * ∑ k ∈ Finset.Icc 1 n, ((n - k).factorial : ℂ) * (n + k).factorial /
        (2 ^ (2 * k) * (n.factorial : ℂ) ^ 2) * (Real.sin θ : ℂ) ^ k *
        jacobiP k k (n - k) (Real.cos θ) * (Real.sin ψ : ℂ) ^ k *
        jacobiP k k (n - k) (Real.cos ψ) * Real.cos (k * phi) := by
  sorry

@[dlmf 18.18.E22]
theorem gegenbauer_linearization {lam : ℝ} (hlam : 0 < lam) (m n : ℕ) (x : ℂ) :
    gegenbauer lam m x * gegenbauer lam n x = ∑ k ∈ Finset.range (min m n + 1),
      (m + n + (lam : ℂ) - 2 * k) * (m + n - 2 * k).factorial /
      ((m + n + lam - k) * k.factorial * (m - k).factorial * (n - k).factorial) *
      (poch lam k * poch lam (m - k) * poch lam (n - k) * poch (2 * lam) (m + n - k) /
       (poch lam (m + n - k) * poch (2 * lam) (m + n - 2 * k))) * gegenbauer lam (m + n - 2 * k) x := by
  sorry


@[dlmf 18.18.E29]
theorem gegenbauer_convolution {lam μ : ℂ} (hlam : 0 < lam.re) (hμ : 0 < μ.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), gegenbauer lam k x * gegenbauer μ (n - k) x = gegenbauer (lam + μ) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_inv x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < μ.re := by linarith
  have h3 : -1 / 2 < (lam + μ).re := by rw [Complex.add_re]; linarith
  simp_rw [gegenbauer_eq_coeff_gegenbauerSeries h1 hw, gegenbauer_eq_coeff_gegenbauerSeries h2 hw,
    gegenbauer_eq_coeff_gegenbauerSeries h3 hw]
  exact sum_coeff_mul_coeff_gegenbauerSeries lam μ w n

@[dlmf 18.18.E30]
theorem gegenbauer_geometric_convolution {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (k + 2 * lam) / (2 * lam) * gegenbauer lam k x * x ^ (n - k) =
      gegenbauer (lam + 1) n x := by
  obtain ⟨w, hw, rfl⟩ := exists_eq_half_add_inv x
  have h1 : -1 / 2 < lam.re := by linarith
  have h2 : -1 / 2 < (lam + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  simp_rw [gegenbauer_eq_coeff_gegenbauerSeries h1 hw, gegenbauer_eq_coeff_gegenbauerSeries h2 hw]
  exact sum_weighted_coeff_gegenbauerSeries hlam0 hw n

/-- `U_{n+2} = 2 T_{n+2} + U_n`. -/
lemma chebyshevU_eq_two_T_add_U (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (n + 2)).eval x =
      2 * (Chebyshev.T ℂ (n + 2)).eval x + (Chebyshev.U ℂ n).eval x := by
  have hT := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.T_eq_X_mul_U_sub_U (R := ℂ) n)
  have hU := congrArg (fun p : ℂ[X] => p.eval x)
    (Chebyshev.U_add_two (R := ℂ) n)
  simp only [eval_sub, eval_mul, eval_X, eval_ofNat] at hT hU
  linear_combination hU - 2 * hT

@[dlmf 18.18.E31]
theorem chebyshev_geometric_sum (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) =
      (Chebyshev.U ℂ n).eval x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one]
    have hsum : ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n + 1 - k) =
        x * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ k).eval x * x ^ (n - k) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
      ring
    rw [hsum, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.U_eq_X_mul_U_add_T ℂ n)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X] at h
    push_cast
    linear_combination -h

@[dlmf 18.18.E32]
theorem chebyshevT_even_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k)).eval x =
      1 + (Chebyshev.U ℂ (2 * n)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_zero, Chebyshev.U_zero]
    norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hU := chebyshevU_eq_two_T_add_U (2 * n) x
    have hU' : (Chebyshev.U ℂ (2 * (n + 1))).eval x =
        2 * (Chebyshev.T ℂ (2 * (n + 1))).eval x + (Chebyshev.U ℂ (2 * n)).eval x := by
      convert hU <;> (push_cast; ring)
    simp only [Nat.cast_succ] at hU' ⊢
    rw [hU']
    ring

@[dlmf 18.18.E33]
theorem chebyshevT_odd_sum (n : ℕ) (x : ℂ) :
    2 * ∑ k ∈ Finset.range (n + 1), (Chebyshev.T ℂ (2 * k + 1)).eval x =
      (Chebyshev.U ℂ (2 * n + 1)).eval x := by
  induction n with
  | zero => simp [Chebyshev.T_one, Chebyshev.U_one]
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h := congrArg (Polynomial.eval x) (Chebyshev.two_mul_T_eq_U_sub_U ℂ (2 * n + 1))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_ofNat] at h
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 1 + 2 by push_cast; ring]
    linear_combination h

@[dlmf 18.18.E34]
theorem chebyshevU_even_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k)).eval x =
      1 - (Chebyshev.T ℂ (2 * n + 2)).eval x := by
  induction n with
  | zero =>
    simp [Chebyshev.T_two]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 2))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 2))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) = 2 * (n : ℤ) + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E35]
theorem chebyshevU_odd_sum (n : ℕ) (x : ℂ) :
    2 * (1 - x ^ 2) * ∑ k ∈ Finset.range (n + 1), (Chebyshev.U ℂ (2 * k + 1)).eval x =
      x - (Chebyshev.T ℂ (2 * n + 3)).eval x := by
  induction n with
  | zero =>
    have h := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ 1)
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h
    norm_num [Chebyshev.T_two, Chebyshev.T_one] at h
    simp [Chebyshev.U_one]
    rw [h]
    ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 := congrArg (Polynomial.eval x)
      (Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T ℂ (2 * n + 3))
    have h2 := congrArg (Polynomial.eval x) (Chebyshev.T_add_two ℂ (2 * n + 3))
    simp only [Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_ofNat] at h1 h2
    rw [show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 1 = 2 * (n : ℤ) + 3 by push_cast; ring,
      show (2 : ℤ) * ((n + 1 : ℕ) : ℤ) + 3 = 2 * (n : ℤ) + 3 + 2 by push_cast; ring]
    linear_combination 2 * h1 - h2

@[dlmf 18.18.E36]
theorem legendre_convolution (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), legendreP k x * legendreP (n - k) x = (Chebyshev.U ℂ n).eval x := by
  simp_rw [legendre_eq_gegenbauer]
  rw [gegenbauer_convolution (by norm_num) (by norm_num), eval_U_eq_gegenbauer]
  norm_num

@[dlmf 18.18.E37]
theorem laguerre_sum (α : ℂ) (n : ℕ) (x : ℂ) :
    ∑ k ∈ Finset.range (n + 1), laguerreExtended α k x = laguerreExtended (α + 1) n x := by
  -- the polynomial identity in `α` is proved for `Re α > 0` and extended by analyticity
  have hana : ∀ m : ℕ, AnalyticOnNhd ℂ (fun a : ℂ => laguerreExtended a m x) Set.univ := by
    intro m a _
    unfold laguerreExtended
    refine Finset.analyticAt_fun_sum (Finset.range (m + 1)) fun k _ => ?_
    have h : AnalyticAt ℂ (fun a : ℂ => poch (a + k + 1) (m - k)) a :=
      (((Polynomial.differentiable (ascPochhammer ℂ (m - k))).comp
        ((differentiable_id.add_const _).add_const _))).analyticAt a
    exact (h.div_const).mul analyticAt_const
  have key : (fun a : ℂ => ∑ k ∈ Finset.range (n + 1), laguerreExtended a k x) =
      fun a => laguerreExtended (a + 1) n x := by
    refine AAR.Hypergeometric.eq_of_eqOn_re_pos ?_ ?_ ?_
    · intro a _
      exact Finset.analyticAt_fun_sum (Finset.range (n + 1)) fun k _ => hana k a (Set.mem_univ a)
    · intro a _
      exact ((hana n) (a + 1) (Set.mem_univ _)).comp (f := fun a : ℂ => a + 1) (by fun_prop)
    intro a ha
    have h1 : ∀ k : ℕ, a + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have h2 : ∀ k : ℕ, a + 1 + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re]
      linarith)
    have ha' : -1 < a.re := by linarith
    simp only [laguerreExtended_eq h1, laguerreExtended_eq h2]
    induction n with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_range_succ, ih, laguerre_raise_parameter ha']
      ring
  exact congrFun key α

@[dlmf 18.18.E40]
theorem hermitePhys_even_convolution (n : ℕ) (x y : ℂ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℂ) * (aeval x (hermitePhys (2 * k)) : ℂ) *
      aeval y (hermitePhys (2 * n - 2 * k)) = (-1 : ℂ) ^ n * 2 ^ (2 * n) * n.factorial * laguerre 0 n (x ^ 2 + y ^ 2) := by
  have hc : ∀ k : ℕ, (-1 / 2 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hc0 : ∀ k : ℕ, (0 : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by norm_num)
  have hadd := laguerre_addition (-1 / 2) (-1 / 2) (x ^ 2) (y ^ 2) n
  rw [show (-1 / 2 : ℂ) + -1 / 2 + 1 = 0 by ring, laguerreExtended_eq hc0] at hadd
  rw [hadd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [show 2 * n - 2 * k = 2 * (n - k) by omega, hermitePhys_even_eq_laguerre,
    hermitePhys_even_eq_laguerre, laguerreExtended_eq hc, laguerreExtended_eq hc,
    Nat.cast_choose ℂ hkn]
  have h1 : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h2 : ((n - k).factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hpow1 : (-1 : ℂ) ^ n = (-1) ^ k * (-1) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  have hpow2 : (2 : ℂ) ^ (2 * n) = 2 ^ (2 * k) * 2 ^ (2 * (n - k)) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow1, hpow2]
  field_simp



/-- The regularized `₀F₁` series converges absolutely everywhere. -/
lemma summable_norm_regularized0F1 (c w : ℂ) :
    Summable fun n : ℕ => ‖regularizedHGFunCoeff (∅ : Multiset ℂ) {c} n * w ^ n‖ := by
  have hr : (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).radius = ⊤ :=
    top_le_iff.mp (hasFPowerSeriesOnBall_regularized0F1 c).r_le
  have := (FormalMultilinearSeries.ofScalars ℂ (regularizedHGFunCoeff ∅ {c})).summable_norm_mul_pow
    (r := ‖w‖₊) (by rw [hr]; exact ENNReal.coe_lt_top)
  simpa [FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow] using this


/-- `(a)ₖ / Γ(a + k) = 1 / Γ(a)` away from the poles of `Γ`. -/
lemma poch_div_Gamma_add_nat {a : ℂ} (ha : ∀ k : ℕ, a ≠ -k) (k : ℕ) :
    poch a k / Complex.Gamma (a + k) = 1 / Complex.Gamma a := by
  have h := Complex.Gamma_add_nat_div_Gamma_eq (n := k) a ha
  have hG : Complex.Gamma a ≠ 0 := Complex.Gamma_ne_zero ha
  rw [poch, ← h]
  have hGk : Complex.Gamma (a + k) ≠ 0 := Complex.Gamma_ne_zero fun m hm =>
    ha (m + k) (by push_cast; linear_combination hm)
  field_simp


@[dlmf 18.12.E2]
theorem jacobi_regularized_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (x z : ℂ) :
    HasSum (fun n : ℕ => jacobiP α β n x / (Gamma (n + α + 1) * Gamma (n + β + 1)) * z ^ n)
      (regularizedHGFun (∅ : Multiset ℂ) {α + 1} ((x - 1) * z / 2) *
       regularizedHGFun (∅ : Multiset ℂ) {β + 1} ((x + 1) * z / 2)) := by
  set u := (x - 1) * z / 2
  set v := (x + 1) * z / 2
  have hu := summable_norm_regularized0F1 (α + 1) u
  have hv := summable_norm_regularized0F1 (β + 1) v
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hv hu
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hv hu).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (β + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq] at hsum
  rw [mul_comm]
  refine hsum.congr_fun fun n => ?_
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, jacobi_binomial_sum hα, Finset.mul_sum,
    Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hA : poch (α + n - k + 1) k / Gamma (n + α + 1) = 1 / Gamma (α + 1 + (n - k : ℕ)) := by
    have := poch_div_Gamma_add_nat (a := α + 1 + (n - k : ℕ)) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) (n - k))])) k
    rw [← this]
    congr 1
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  have hB : poch (β + k + 1) (n - k) / Gamma (n + β + 1) = 1 / Gamma (β + 1 + k) := by
    have := poch_div_Gamma_add_nat (a := β + 1 + k) (not_neg_nat_of_re_pos (by
      simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
      linarith [(Nat.cast_nonneg (α := ℝ) k)])) (n - k)
    rw [← this]
    congr 1
    · congr 1; ring
    · congr 1; push_cast [Nat.cast_sub hkn]; ring
  simp only [regularizedHGFunCoeff_empty]
  have hGA : Gamma (n + α + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  have hGB : Gamma (n + β + 1) ≠ 0 := Complex.Gamma_ne_zero (not_neg_nat_of_re_pos (by
    simp only [Complex.add_re, Complex.one_re, Complex.natCast_re]
    linarith [(Nat.cast_nonneg (α := ℝ) n)]))
  rw [div_eq_iff hGA] at hA
  rw [div_eq_iff hGB] at hB
  have hzn : z ^ n = z ^ k * z ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  have h2n : (2 : ℂ) ^ n = 2 ^ k * 2 ^ (n - k) := by rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [hA, hB, hzn, h2n]
  simp only [u, v, div_pow, mul_pow]
  field_simp

@[dlmf 18.12.E2_5]
theorem jacobi_brafman_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) (γ : ℂ) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2‖ < 1)
    (hv : ‖(1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2‖ < 1) :
    HasSum (fun n : ℕ => poch γ n * poch (α + β + 1 - γ) n /
      (poch (α + 1) n * poch (β + 1) n) * jacobiP α β n x * z ^ n)
      (₂F₁ γ (α + β + 1 - γ) (α + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) - z) / 2) *
       ₂F₁ γ (α + β + 1 - γ) (β + 1) ((1 - (1 - 2 * x * z + z ^ 2) ^ (1 / 2 : ℂ) + z) / 2)) := by
  sorry

@[dlmf 18.12.E3]
theorem jacobi_weighted_generating_function {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hu : ‖2 * (x + 1 : ℂ) * z / (1 + z) ^ 2‖ < 1) :
    HasSum (fun n : ℕ => poch (α + β + 1) n / poch (β + 1) n * jacobiP α β n x * z ^ n)
      ((1 + z) ^ (-α - β - 1) * ₂F₁ ((α + β + 1) / 2) ((α + β + 2) / 2)
        (β + 1) (2 * (x + 1 : ℂ) * z / (1 + z) ^ 2)) := by
  sorry

@[dlmf 18.12.E3_5]
theorem jacobi_adjacent_generating_function {β : ℂ} (hβ : -1 < β.re)
    {x : ℝ} (hx : |x| ≤ 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch (2 * β + 2) n / poch (β + 1) n * jacobiP (β + 1) β n x * z ^ n)
      ((1 + z) / (1 - 2 * x * z + z ^ 2) ^ (β + 3 / 2)) := by
  sorry

@[dlmf 18.12.E6]
theorem gegenbauer_bessel_generating_function {lam : ℝ} (hlam : 0 < lam)
    {θ z : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) (hz : 0 < z) :
    HasSum (fun n : ℕ => gegenbauer lam n (Real.cos θ) / poch (2 * lam) n * (z : ℂ) ^ n)
      (Gamma (lam + 1 / 2 : ℂ) * exp (z * Real.cos θ : ℂ) *
        (z * Real.sin θ / 2 : ℂ) ^ (1 / 2 - lam : ℂ) * besselJ (lam - 1 / 2) (z * Real.sin θ)) := by
  sorry

@[dlmf 18.12.E7]
theorem chebyshevT_poisson_generating_function {x : ℝ} (hx : |x| ≤ 1)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => 2 * (Chebyshev.T ℂ (n + 1)).eval (x : ℂ) * z ^ (n + 1))
      ((1 - z ^ 2) / (1 - 2 * x * z + z ^ 2) - 1) := by
  have hD := one_sub_two_mul_add_sq_ne_zero hx hz
  have h := ((hasSum_nat_add_iff' 1).mpr (chebyshevT_generating_function hx hz)).mul_left 2
  convert h using 1
  · funext n; push_cast; ring
  · simp only [Finset.sum_range_one, pow_zero, mul_one, Nat.cast_zero, Chebyshev.T_zero, eval_one]
    rw [div_sub_one hD, div_sub_one hD, ← mul_div_assoc]
    congr 1
    ring

/-- The exponential series in `ℂ`. -/
lemma hasSum_cexp (z : ℂ) : HasSum (fun n : ℕ => z ^ n / (n.factorial : ℂ)) (exp z) := by
  rw [Complex.exp_eq_exp_ℂ]
  exact NormedSpace.expSeries_div_hasSum_exp z

/-- The exponential series converges absolutely. -/
lemma summable_norm_pow_div_factorial (z : ℂ) :
    Summable fun n : ℕ => ‖z ^ n / (n.factorial : ℂ)‖ := by
  simpa [norm_div, norm_pow] using Real.summable_pow_div_factorial ‖z‖

@[dlmf 18.12.E14]
theorem laguerre_bessel_generating_function {α : ℝ} (hα : -1 < α)
    {x z : ℝ} (hx : 0 < x) (hz : 0 < z) :
    HasSum (fun n : ℕ => laguerre α n x / poch (α + 1) n * (z : ℂ) ^ n)
      (Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
        besselJ α (2 * Real.sqrt (x * z))) := by
  have hc : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := not_neg_nat_of_re_pos (by simp; linarith)
  set w : ℂ := -((x : ℂ) * z)
  have hf := summable_norm_regularized0F1 (α + 1) w
  have hg := summable_norm_pow_div_factorial (z : ℂ)
  have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hf hg
  have hsum := (summable_norm_sum_mul_antidiagonal_of_summable_norm hf hg).of_norm.hasSum
  rw [← hprod, ((hasFPowerSeriesOnBall_regularized0F1 (α + 1)).hasSum_mul_pow
      (by simp)).tsum_eq, (hasSum_cexp _).tsum_eq] at hsum
  -- the Bessel prefactor
  have hxz : (0 : ℝ) < x * z := mul_pos hx hz
  have hbes : (x * z : ℂ) ^ (-α / 2 : ℂ) * besselJ α (2 * Real.sqrt (x * z)) =
      regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w := by
    set t := x * z
    have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt hxz.le
    unfold besselJ
    have harg : -((2 * (Real.sqrt t : ℂ)) ^ 2 / 4) = w := by
      simp only [w, t]
      rw [mul_pow, ← Complex.ofReal_pow, hsq]
      simp only [t]; push_cast; ring
    rw [harg, ← mul_assoc]
    convert one_mul _ using 2
    rw [show 2 * (Real.sqrt t : ℂ) / 2 = (Real.sqrt t : ℂ) by ring,
      show (x : ℂ) * z = (t : ℂ) by simp only [t]; push_cast; ring,
      show (-(α : ℂ) / 2) = ((-α / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hxz.le, ← Complex.ofReal_cpow (Real.sqrt_nonneg t),
      ← Complex.ofReal_mul, Real.sqrt_eq_rpow, ← Real.rpow_mul hxz.le, ← Real.rpow_add hxz,
      show -α / 2 + 1 / 2 * α = 0 by ring, Real.rpow_zero, Complex.ofReal_one]
  have hval : Gamma (α + 1 : ℂ) * (x * z : ℂ) ^ (-α / 2 : ℂ) * exp z *
      besselJ α (2 * Real.sqrt (x * z)) =
      Gamma (α + 1 : ℂ) * (regularizedHGFun (∅ : Multiset ℂ) {(α : ℂ) + 1} w * exp z) := by
    rw [← hbes]; ring
  rw [hval]
  refine (hsum.mul_left (Gamma (α + 1 : ℂ))).congr_fun fun n => ?_
  have hpos : 0 < ((α : ℂ) + 1).re := by simp; linarith
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, ← laguerreExtended_eq hc, laguerreExtended,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hsplit : poch ((α : ℂ) + 1) n = poch ((α : ℂ) + 1) k * poch ((α : ℂ) + 1 + k) (n - k) := by
    rw [← poch_add, Nat.add_sub_cancel' hkn]
  have hG : Gamma ((α : ℂ) + 1 + k) = Gamma ((α : ℂ) + 1) * poch ((α : ℂ) + 1) k := by
    have := Complex.Gamma_add_nat_div_Gamma_eq (n := k) ((α : ℂ) + 1) hc
    rw [div_eq_iff (Complex.Gamma_ne_zero hc)] at this
    rw [this, poch]; ring
  have h1 : poch ((α : ℂ) + 1) k ≠ 0 := poch_ne_zero_of_re_pos hpos k
  have h2 : poch ((α : ℂ) + 1 + k) (n - k) ≠ 0 := poch_ne_zero_of_re_pos (by
    simp only [Complex.add_re, Complex.natCast_re] at hpos ⊢; positivity) (n - k)
  have h3 : Gamma ((α : ℂ) + 1) ≠ 0 := Complex.Gamma_ne_zero hc
  have hzn : (z : ℂ) ^ n = (z : ℂ) ^ k * (z : ℂ) ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_cancel' hkn]
  rw [regularizedHGFunCoeff_empty, hG, hsplit, hzn, show (α : ℂ) + k + 1 = α + 1 + k by ring]
  have hw : w ^ k = (-1) ^ k * (x : ℂ) ^ k * (z : ℂ) ^ k := by
    simp only [w]; rw [neg_pow, mul_pow]; ring
  rw [hw, neg_pow (x : ℂ) k]
  field_simp

/-- The Laguerre generating function as a `HasSum`. -/
lemma hasSum_laguerre_generating_function {α x t : ℂ} (hα : ∀ k : ℕ, α + 1 ≠ -(k : ℂ))
    (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => laguerre α n x * t ^ n) ((1 - t) ^ (-α - 1) * exp (-x * t / (1 - t))) := by
  have h := laguerre_generating_function (x := x) hα ht
  have h1t : (1 : ℂ) - t ≠ 0 := by
    intro h0
    have : t = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have hne : (1 - t) ^ (-α - 1) * exp (-x * t / (1 - t)) ≠ 0 := by
    refine mul_ne_zero ?_ (exp_ne_zero _)
    rw [cpow_def_of_ne_zero h1t]; exact exp_ne_zero _
  have hs : Summable fun n : ℕ => laguerre α n x * t ^ n := by
    by_contra hns
    rw [tsum_eq_zero_of_not_summable hns] at h
    exact hne h
  rw [h]; exact hs.hasSum


/-- DLMF 18.12.17 prints the incorrect convergence condition `|z| < 1`
(checked 2026-09-16). The disk is `|z| < 1/2`: already at `x = 0`,
the even coefficients are `(-1)^k * (2*k)! / (k!)²`, with radius `1/2`. -/
@[dlmf 18.12.E17]
theorem hermitePhys_half_factorial_generating_function (x : ℂ) {z : ℂ} (hz : ‖z‖ < 1 / 2) :
    HasSum (fun n : ℕ => aeval x (hermitePhys n) / ((n / 2).factorial : ℂ) * z ^ n)
      ((1 + 2 * x * z + 4 * z ^ 2) / (1 + 4 * z ^ 2) ^ (3 / 2 : ℂ) *
        exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))) := by
  have ht : ‖-4 * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_neg, norm_pow]
    have := norm_nonneg z
    norm_num; nlinarith
  have hw : (1 : ℂ) + 4 * z ^ 2 ≠ 0 := by
    intro h0
    have : -4 * z ^ 2 = 1 := by linear_combination -h0
    rw [this, norm_one] at ht; exact lt_irrefl _ ht
  have he := hasSum_laguerre_generating_function (α := -1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht
  have ho := (hasSum_laguerre_generating_function (α := 1 / 2) (x := x ^ 2)
    (not_neg_nat_of_re_pos (by norm_num)) ht).mul_left (2 * x * z)
  set E := exp (4 * x ^ 2 * z ^ 2 / (1 + 4 * z ^ 2))
  have hE : exp (-x ^ 2 * (-4 * z ^ 2) / (1 + 4 * z ^ 2)) = E := by
    congr 1; ring_nf
  rw [show (1 : ℂ) - -4 * z ^ 2 = 1 + 4 * z ^ 2 by ring, hE] at he ho
  set f : ℕ → ℂ := fun n => aeval x (hermitePhys n) / ((n / 2).factorial : ℂ) * z ^ n with hf
  have hev : HasSum (fun m => f (2 * m))
      ((1 + 4 * z ^ 2) ^ (-(-1 / 2) - 1 : ℂ) * E) := by
    refine he.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show 2 * m / 2 = m by omega]
    rw [hermitePhys_even_eq_laguerre, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m) = (z ^ 2) ^ m by rw [pow_mul],
      show (2 : ℂ) ^ (2 * m) = 4 ^ m by rw [pow_mul]; norm_num]
    field_simp
  have hod : HasSum (fun m => f (2 * m + 1))
      (2 * x * z * ((1 + 4 * z ^ 2) ^ (-(1 / 2) - 1 : ℂ) * E)) := by
    refine ho.congr_fun fun m => ?_
    have hm : (m.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    simp only [hf, show (2 * m + 1) / 2 = m by omega]
    rw [hermitePhys_odd_eq_laguerre, mul_pow, neg_pow (4 : ℂ),
      show z ^ (2 * m + 1) = z * (z ^ 2) ^ m by rw [pow_succ, pow_mul]; ring,
      show (2 : ℂ) ^ (2 * m + 1) = 2 * 4 ^ m by rw [pow_succ, pow_mul]; norm_num; ring]
    field_simp
  have hsum := hev.even_add_odd hod
  convert hsum using 1
  set w := (1 : ℂ) + 4 * z ^ 2
  have h1 : w ^ (-(-1 / 2) - 1 : ℂ) = w * (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg, show (-(-1 / 2) - 1 : ℂ) = 1 + -(3 / 2) by norm_num, cpow_add _ _ hw, cpow_one]
  have h2 : w ^ (-(1 / 2) - 1 : ℂ) = (w ^ (3 / 2 : ℂ))⁻¹ := by
    rw [← cpow_neg]; norm_num
  rw [h1, h2]
  ring

end AAR.OrthogonalPolynomials
