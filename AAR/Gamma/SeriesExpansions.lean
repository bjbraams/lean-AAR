/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.Complex.TaylorSeries
public import AAR.Gamma.Digamma
public import AAR.Gamma.SpecialValues
public import AAR.Gamma.Polygamma
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Cotangent
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Series expansions (DLMF §5.7)

The Weierstrass/digamma series 5.7.6 is `digamma_eq_tsum` in `Digamma.lean` (real) and
`digamma_eq_cDigammaSeries` in `Polygamma.lean` (complex); the expansions below use the
complex form.
The Taylor coefficients of `1/Γ` and the ζ-expansions of `log Γ` and `ψ` are
described here. The reciprocal Gamma Taylor series converges on all of `ℂ`;
the logarithmic and digamma expansions retain their disk and pole restrictions.
The alternating half-argument digamma series is grouped into absolutely summable pairs.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- Taylor coefficients of `1/Γ` at zero, DLMF 5.7.1. -/
@[dlmf 5.7.E1]
def invGammaCoeff (k : ℕ) : ℂ :=
  iteratedDeriv k (fun z : ℂ => (Complex.Gamma z)⁻¹) 0 / k.factorial

/-- The reciprocal Gamma Taylor series at zero converges at every complex argument. -/
@[dlmf 5.7.E1]
theorem hasSum_invGammaCoeff (z : ℂ) :
    HasSum (fun k : ℕ => invGammaCoeff k * z ^ k) (Complex.Gamma z)⁻¹ := by
  simpa [invGammaCoeff, div_eq_mul_inv, smul_eq_mul,
    mul_comm, mul_left_comm, mul_assoc] using
    Complex.hasSum_taylorSeries_of_entire Complex.differentiable_one_div_Gamma 0 z

@[dlmf 5.7.E2]
theorem invGammaCoeff_recurrence {k : ℕ} (hk : 1 < k) :
    (k - 1 : ℂ) * invGammaCoeff k =
      Real.eulerMascheroniConstant * invGammaCoeff (k - 1) -
        ∑ j ∈ Finset.Icc 2 (k - 1),
          (-1 : ℂ) ^ j * (riemannZeta j) * invGammaCoeff (k - j) := by
  sorry

@[dlmf 5.7.E3]
theorem log_Gamma_one_add {z : ℂ} (hz : ‖z‖ < 1) :
    log (Complex.Gamma (1 + z)) =
      -log (1 + z) + z * (1 - Real.eulerMascheroniConstant) +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * (riemannZeta (k + 2) - 1) * z ^ (k + 2) / (k + 2) := by
  sorry

/-- The ζ-expansion of `ψ(1+z) + γ` as a `HasSum`, from the complex digamma series
`digamma_eq_cDigammaSeries` by expanding each term geometrically and summing by columns. -/
theorem hasSum_digamma_one_add_zeta {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1))
      (Complex.digamma (1 + z) + Real.eulerMascheroniConstant) := by
  have hre : -1 < z.re := by
    have := Complex.abs_re_le_norm z
    linarith [neg_abs_le z.re]
  have hU : 1 + z ∈ notNegNat := fun m h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  rw [digamma_eq_cDigammaSeries hU, cDigammaSeries, neg_add_cancel_comm]
  set a : ℕ → ℕ → ℂ := fun n k => (-1 : ℂ) ^ k * z ^ (k + 1) / ((n : ℂ) + 1) ^ (k + 2)
    with ha
  have hn1 : ∀ n : ℕ, ((n : ℂ) + 1) ≠ 0 := fun n => by exact_mod_cast Nat.succ_ne_zero n
  have hnorm1 : ∀ n : ℕ, (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := fun n => by
    rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos n
  -- summability of the double series
  have hsum : Summable (Function.uncurry a) := by
    have hg : Summable fun p : ℕ × ℕ =>
        (1 / ((p.1 : ℝ) + 1) ^ 2) * ‖z‖ ^ (p.2 + 1) := by
      have h1 : Summable fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2 := by
        exact_mod_cast (summable_nat_add_iff 1).mpr
          (Real.summable_one_div_nat_pow.mpr one_lt_two)
      have h2 : Summable fun k : ℕ => ‖z‖ ^ (k + 1) := by
        simpa [pow_succ] using
          (summable_geometric_of_lt_one (norm_nonneg z) hz).mul_right ‖z‖
      exact h1.mul_of_nonneg h2 (fun _ => by positivity) (fun _ => by positivity)
    refine hg.of_norm_bounded fun ⟨n, k⟩ => ?_
    simp only [Function.uncurry_apply_pair, ha, norm_div, norm_mul, norm_pow, norm_neg,
      norm_one, one_pow, one_mul]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := hnorm1 n
    rw [div_le_iff₀ (by positivity)]
    have hnn : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      push_cast; ring
    rw [hnn] at hn ⊢
    calc ‖z‖ ^ (k + 1) = 1 / ((n : ℝ) + 1) ^ 2 * ‖z‖ ^ (k + 1) * ((n : ℝ) + 1) ^ 2 := by
          field_simp
      _ ≤ 1 / ((n : ℝ) + 1) ^ 2 * ‖z‖ ^ (k + 1) * ((n : ℝ) + 1) ^ (k + 2) := by
          gcongr
          omega
  -- inner sums over `k`
  have hinner : ∀ n : ℕ, ∑' k : ℕ, a n k = cDigammaTerm n (1 + z) := by
    intro n
    have hq : ‖-z / ((n : ℂ) + 1)‖ < 1 := by
      rw [norm_div, norm_neg, div_lt_one (by linarith [hnorm1 n])]
      linarith [hnorm1 n]
    have hgeo := tsum_geometric_of_norm_lt_one hq
    have hz1 : 1 + z + n ≠ 0 := add_nat_ne_zero_of_not_neg_nat hU n
    have hne : (1 : ℂ) - -z / ((n : ℂ) + 1) = (1 + z + n) / ((n : ℂ) + 1) := by
      field_simp; ring
    have hterm : ∀ k : ℕ, a n k = z / ((n : ℂ) + 1) ^ 2 * (-z / ((n : ℂ) + 1)) ^ k := by
      intro k
      simp only [ha, div_pow, neg_pow z]
      field_simp
      ring
    simp_rw [hterm]
    rw [tsum_mul_left, hgeo, hne, cDigammaTerm]
    have := hn1 n
    field_simp
    ring
  have hrow : ∀ k : ℕ, ∑' n : ℕ, a n k =
      (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) := by
    intro k
    rw [show ((k : ℂ) + 2) = ((k + 2 : ℕ) : ℂ) by push_cast; ring,
      riemannZeta_nat_eq_tsum_succ (by omega), ← tsum_mul_left, ← tsum_mul_right]
    congr 1; funext n
    simp only [ha, pow_add (-1 : ℂ) k 2]
    ring
  have hcol : Summable fun k : ℕ => ∑' n : ℕ, a n k := by
    simpa using hsum.prod_symm.prod
  simp_rw [← hinner, ← hrow]
  rw [← hsum.tsum_comm]
  exact hcol.hasSum

@[dlmf 5.7.E4]
theorem digamma_one_add_zeta {z : ℂ} (hz : ‖z‖ < 1) :
    Complex.digamma (1 + z) =
      -Real.eulerMascheroniConstant +
        ∑' k : ℕ, (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) := by
  rw [(hasSum_digamma_one_add_zeta hz).tsum_eq]
  ring

@[dlmf 5.7.E5]
theorem digamma_one_add_odd_zeta {z : ℂ} (hz : ‖z‖ < 1) (hz0 : z ≠ 0) (hz1 : z ≠ 1)
    (hzm : z ≠ -1) :
    Complex.digamma (1 + z) =
      1 / (2 * z) - π / 2 * cot (π * z) + 1 / (z ^ 2 - 1) + 1 -
        Real.eulerMascheroniConstant -
        ∑' k : ℕ, (riemannZeta (2 * k + 3) - 1) * z ^ (2 * k + 2) := by
  -- the odd part, from the recurrence and reflection formulas
  have hzint : ∀ n : ℤ, z ≠ n := by
    intro n hn
    have hn' : ‖(n : ℂ)‖ < 1 := hn ▸ hz
    rw [Complex.norm_intCast] at hn'
    have : n = 0 := by
      have : |(n : ℝ)| < 1 := hn'
      exact_mod_cast (show (n : ℝ) = 0 by
        rcases abs_lt.mp this with ⟨h1, h2⟩
        have : (-1 : ℤ) < n := by exact_mod_cast h1
        have : n < 1 := by exact_mod_cast h2
        have : n = 0 := by omega
        exact_mod_cast this)
    exact hz0 (by rw [hn, this]; simp)
  have hnat : ∀ m : ℕ, z ≠ -(m : ℂ) := fun m h => hzint (-m) (by rw [h]; push_cast; ring)
  have hodd : Complex.digamma (1 + z) - Complex.digamma (1 - z) = 1 / z - π * cot (π * z) := by
    rw [Complex.digamma_one_sub hzint, add_comm, Complex.digamma_apply_add_one z hnat]
    ring
  -- the even part, from the ζ-expansion at `z` and `-z`
  have hz' : ‖-z‖ < 1 := by rwa [norm_neg]
  have hsum := (hasSum_digamma_one_add_zeta hz).add (hasSum_digamma_one_add_zeta hz')
  rw [← sub_eq_add_neg] at hsum
  set c : ℕ → ℂ := fun j => -2 * (riemannZeta (2 * j + 3) * z ^ (2 * j + 2)) with hc
  have hF : (fun k : ℕ => (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * z ^ (k + 1) +
      (-1 : ℂ) ^ (k + 2) * riemannZeta (k + 2) * (-z) ^ (k + 1)) =
      Function.extend (fun j : ℕ => 2 * j + 1) c 0 := by
    funext k
    obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
    · rw [Function.extend_apply' _ _ _ fun ⟨i, hi⟩ => by omega]
      simp [pow_succ, pow_mul, neg_pow z]
    · rw [(show Function.Injective fun j : ℕ => 2 * j + 1 from
        fun a b h => by simpa using h).extend_apply]
      simp only [hc]
      push_cast
      rw [show (2 * j + 1 + 2 : ℕ) = 2 * (j + 1) + 1 by ring, neg_pow z, pow_add (-1 : ℂ),
        pow_mul]
      ring_nf
      rw [show (-1 : ℂ) ^ (j * 2) = 1 from Even.neg_one_pow ⟨j, by ring⟩]
      ring
  rw [hF, hasSum_extend_zero (fun a b h => by simpa using h)] at hsum
  have hgeo : HasSum (fun j : ℕ => z ^ (2 * j + 2)) (z ^ 2 / (1 - z ^ 2)) := by
    have hz2 : ‖z ^ 2‖ < 1 := by
      rw [norm_pow]; nlinarith [norm_nonneg z]
    have := (hasSum_geometric_of_norm_lt_one hz2).mul_left (z ^ 2)
    simp_rw [← pow_mul, ← pow_add] at this
    convert this using 2
    · ring_nf
    · rw [div_eq_mul_inv]
  have heven := (hsum.div_const (-2)).sub hgeo
  have h1z : (1 : ℂ) - z ^ 2 ≠ 0 := by
    intro h
    have : (1 - z) * (1 + z) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h | h
    · exact hz1 (by linear_combination -h)
    · exact hzm (by linear_combination h)
  have hz2' : z ^ 2 - 1 ≠ 0 := fun h => h1z (by linear_combination -h)
  have htsum : ∑' k : ℕ, (riemannZeta (2 * k + 3) - 1) * z ^ (2 * k + 2) =
      (Complex.digamma (1 + z) + Real.eulerMascheroniConstant +
        (Complex.digamma (1 - z) + Real.eulerMascheroniConstant)) / -2 -
        z ^ 2 / (1 - z ^ 2) := by
    rw [← heven.tsum_eq]
    congr 1; funext j
    simp only [hc]
    ring
  have hB : Complex.digamma (1 - z) = Complex.digamma (1 + z) - (1 / z - π * cot (π * z)) := by
    linear_combination -hodd
  rw [htsum, hB]
  generalize cot (π * z) = C
  generalize Complex.digamma (1 + z) = D
  field_simp
  ring

/-- The half-argument digamma difference as an absolutely convergent series.
Adjacent terms of the classical alternating series are paired before taking `tsum`. -/
@[dlmf 5.7.E7]
theorem digamma_half_diff (z : ℂ) (hz : ∀ k : ℕ, z ≠ -k) :
    Complex.digamma ((z + 1) / 2) - Complex.digamma (z / 2) =
      2 * ∑' k : ℕ, (1 / (2 * k + z) - 1 / (2 * k + 1 + z)) := by
  have h1 : (z + 1) / 2 ∈ notNegNat := fun m h => hz (2 * m + 1) (by
    push_cast; linear_combination 2 * h)
  have h2 : z / 2 ∈ notNegNat := fun m h => hz (2 * m) (by
    push_cast; linear_combination 2 * h)
  rw [digamma_eq_cDigammaSeries h1, digamma_eq_cDigammaSeries h2, cDigammaSeries,
    cDigammaSeries, add_sub_add_left_eq_sub,
    ← (summable_cDigammaTerm h1).tsum_sub (summable_cDigammaTerm h2), ← tsum_mul_left]
  congr 1; funext k
  have ha : (2 * k + z : ℂ) ≠ 0 := fun h => hz (2 * k) (by
    push_cast; linear_combination h)
  have hb : (2 * k + 1 + z : ℂ) ≠ 0 := fun h => hz (2 * k + 1) (by
    push_cast; linear_combination h)
  have ha' : z / 2 + k ≠ 0 := fun h => ha (by linear_combination 2 * h)
  have hb' : (z + 1) / 2 + k ≠ 0 := fun h => hb (by linear_combination 2 * h)
  simp only [cDigammaTerm]
  field_simp
  ring

@[dlmf 5.7.E8]
theorem digamma_one_add_mul_I_im_series (y : ℝ) :
    (Complex.digamma (1 + I * y)).im = ∑' k : ℕ, y / ((k + 1 : ℝ) ^ 2 + y ^ 2) := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp [Complex.digamma_one]
  have hx : (I * (y : ℂ)) ∈ Complex.integerComplement := by
    rintro ⟨n, hn⟩
    have := congrArg Complex.im hn
    simp at this
    exact hy this.symm
  have h := cot_series_rep' hx
  have hs : Summable fun n : ℕ => 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) :=
    summable_cotTerm hx
  have hcot := AAR.Gamma.cot_pi_mul_I y hy
  have hsinh : (Real.sinh (π * y) : ℂ) ≠ 0 := by
    exact_mod_cast Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hy)
  have hy' : (y : ℂ) ≠ 0 := by exact_mod_cast hy
  have hL : ((π : ℂ) * cot (π * (I * y)) - 1 / (I * y)).im =
      1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) := by
    rw [hcot]
    have : (π : ℂ) * (-I * (Real.cosh (π * y) / Real.sinh (π * y))) - 1 / (I * y) =
        ((1 / y - π * (Real.cosh (π * y) / Real.sinh (π * y)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (-1 : ℂ) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have hterm : ∀ n : ℕ, (1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1))).im =
      -2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) := by
    intro n
    have hd : ((n + 1 : ℝ) ^ 2 + y ^ 2) ≠ 0 := by positivity
    have hd' : ((n : ℂ) + 1) ^ 2 + (y : ℂ) ^ 2 ≠ 0 := by exact_mod_cast hd
    have h1 : I * (y : ℂ) - (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have h2 : I * (y : ℂ) + (n + 1) ≠ 0 := by
      intro h; have := congrArg Complex.im h; simp at this; exact hy this
    have : 1 / (I * (y : ℂ) - (n + 1)) + 1 / (I * (y : ℂ) + (n + 1)) =
        ((-2 * (y / ((n + 1 : ℝ) ^ 2 + y ^ 2)) : ℝ) : ℂ) * I := by
      push_cast
      field_simp
      linear_combination (2 * I * (y : ℂ) ^ 3) * I_sq
    rw [this, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  have him := congrArg Complex.im h
  rw [hL, Complex.im_tsum hs] at him
  simp_rw [hterm] at him
  rw [tsum_mul_left] at him
  rw [AAR.Gamma.digamma_one_add_mul_I_im y hy]
  linear_combination (-1 / 2 : ℝ) * him

end AAR.Gamma
