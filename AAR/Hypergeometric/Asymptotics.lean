/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Solutions
public import AAR.Bessel.Modified
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.Complex.TaylorSeries

/-!
# Large-parameter asymptotics (DLMF §15.12)

The large-denominator expansions are stated along the positive real axis, with
the variable in the series disk. Remainders use Mathlib's `Asymptotics.IsBigO`.
The Bessel approximation E5–E6 uses existing `besselI` and `Real.arcosh`, with
`1 < x < 3` ensuring the hypergeometric series argument is in the disk.
E1 defines the larger complex-sector boundary; those sector domains are deferred.
E6 uses Mathlib's `Real.arcosh` (https://dlmf.nist.gov/15.12.E6); no
duplicate inverse-hyperbolic-function definition is introduced.
E7–E13 require parabolic-cylinder/Airy functions and continuous choices of
turning-point branches not yet available in this project's hypergeometric API.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

/-- `c^m k! ≤ m! (c)_k` for real `c ≥ 1` and `k ≥ m`. -/
lemma pow_mul_factorial_le_poch {c : ℝ} (hc : 1 ≤ c) {m k : ℕ} (hk : m ≤ k) :
    c ^ m * k.factorial ≤ m.factorial * (ascPochhammer ℝ k).eval c := by
  induction k, hk using Nat.le_induction with
  | base =>
    have : c ^ m ≤ (ascPochhammer ℝ m).eval c := by
      induction m with
      | zero => simp
      | succ j ih =>
        rw [ascPochhammer_succ_eval, pow_succ]
        exact mul_le_mul ih (by linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) (by positivity)
          (ascPochhammer_eval_nonneg (by linarith) j)
    have hf : (0 : ℝ) < m.factorial := by positivity
    nlinarith
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.cast_mul, ascPochhammer_succ_eval]
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ c + k := by push_cast; linarith
    have h0 : (0 : ℝ) ≤ c ^ m * k.factorial := by positivity
    calc c ^ m * (((k + 1 : ℕ) : ℝ) * k.factorial) = (c ^ m * k.factorial) * ((k + 1 : ℕ) : ℝ) := by
          ring
      _ ≤ (m.factorial * (ascPochhammer ℝ k).eval c) * (c + k) :=
          mul_le_mul ih hk1 (by positivity) (by
            have := ascPochhammer_eval_nonneg (show (0 : ℝ) ≤ c by linarith) k
            positivity)
      _ = _ := by ring

@[dlmf 15.12.E2]
theorem large_denominator_expansion (a b : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun c : ℝ => ₂F₁ a b (c : ℂ) z -
        ∑ k ∈ Finset.range m, gaussHGCoeff a b c k * z ^ k)
      (fun c : ℝ => (c : ℂ)⁻¹ ^ m) := by
  set g : ℕ → ℝ := fun k => ‖gaussHGCoeff (‖a‖ : ℂ) (‖b‖ : ℂ) 1 k * z ^ k‖ with hg
  have hgs : Summable g := summable_norm_gaussHGCoeff_mul_pow _ _ _ hz
  refine Asymptotics.IsBigO.of_bound (m.factorial * ∑' k, g k) ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with c hc
  have hc0 : (0 : ℝ) < c := by linarith
  set f : ℕ → ℂ := fun k => gaussHGCoeff a b c k * z ^ k with hf
  have hfs : Summable f := (summable_norm_gaussHGCoeff_mul_pow a b c hz).of_norm
  have hF : ₂F₁ a b (c : ℂ) z = ∑' k, f k := by
    rw [ordinaryHypergeometric_eq_tsum]
    simp only [smul_eq_mul, hf]
    congr 1
    funext n
    simp [gaussHGCoeff, poch, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
  rw [hF, ← hfs.sum_add_tsum_nat_add m, add_sub_cancel_left]
  -- termwise bound on the tail
  have hbd : ∀ k, ‖f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * g (k + m) := by
    intro k
    have hpos := pow_mul_factorial_le_poch hc (Nat.le_add_left m k)
    have hpc : ‖poch (c : ℂ) (k + m)‖ = (ascPochhammer ℝ (k + m)).eval c := by
      rw [poch, ascPochhammer_eval_ofReal, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (ascPochhammer_eval_nonneg hc0.le _)]
    have h1 : ‖poch (1 : ℂ) (k + m)‖ = (k + m).factorial := by
      rw [poch_nat_one, Complex.norm_natCast]
    have ha := norm_ascPochhammer_eval_le (le_refl ‖a‖) (k + m)
    have hb := norm_ascPochhammer_eval_le (le_refl ‖b‖) (k + m)
    have hfac : (0 : ℝ) < (k + m).factorial := by positivity
    have hP : 0 < (ascPochhammer ℝ (k + m)).eval c := by
      have : (0 : ℝ) < c ^ m * (k + m).factorial := by positivity
      have hmf : (0 : ℝ) < m.factorial := by positivity
      by_contra hneg
      have := not_lt.mp hneg
      nlinarith
    simp only [hf, hg, gaussHGCoeff, norm_mul, norm_div, norm_pow, Complex.norm_natCast, hpc, h1]
    rw [show ‖poch a (k + m)‖ = ‖(ascPochhammer ℂ (k + m)).eval a‖ from rfl,
      show ‖poch b (k + m)‖ = ‖(ascPochhammer ℂ (k + m)).eval b‖ from rfl]
    have hz0 : 0 ≤ ‖z‖ ^ (k + m) := by positivity
    have hcm : 0 < c ^ m := by positivity
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    calc ‖(ascPochhammer ℂ (k + m)).eval a‖ * ‖(ascPochhammer ℂ (k + m)).eval b‖ * ‖z‖ ^ (k + m)
        ≤ ‖poch (‖a‖ : ℂ) (k + m)‖ * ‖poch (‖b‖ : ℂ) (k + m)‖ * ‖z‖ ^ (k + m) := by gcongr
      _ = m.factorial * (c ^ m)⁻¹ * (‖poch (‖a‖ : ℂ) (k + m)‖ * ‖poch (‖b‖ : ℂ) (k + m)‖ /
            ((k + m).factorial * (k + m).factorial) * ‖z‖ ^ (k + m)) *
            ((c ^ m * (k + m).factorial) / m.factorial * (k + m).factorial) := by
          field_simp
      _ ≤ _ := by
          have hle : c ^ m * (k + m).factorial / m.factorial ≤ (ascPochhammer ℝ (k + m)).eval c := by
            rw [div_le_iff₀ (by positivity)]; linarith
          gcongr
  have hgs' : Summable fun k => g (k + m) := (summable_nat_add_iff m).mpr hgs
  have hnorm : ‖∑' k, f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := by
    calc ‖∑' k, f (k + m)‖ ≤ ∑' k, m.factorial * (c ^ m)⁻¹ * g (k + m) :=
          tsum_of_norm_bounded (hgs'.mul_left _).hasSum hbd
      _ = m.factorial * (c ^ m)⁻¹ * ∑' k, g (k + m) := tsum_mul_left
      _ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          rw [← hgs.sum_add_tsum_nat_add m]
          have : 0 ≤ ∑ i ∈ Finset.range m, g i := Finset.sum_nonneg fun i _ => norm_nonneg _
          linarith
  rw [norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc0, inv_pow]
  calc ‖∑' k, f (k + m)‖ ≤ m.factorial * (c ^ m)⁻¹ * ∑' k, g k := hnorm
    _ = _ := by ring

/-- The removable quotient in the generating function has value `1` at zero. -/
def expSubOneDiv (t : ℂ) : ℂ := if t = 0 then 1 else (exp t - 1) / t

/-- Generating function for the large-denominator coefficients. -/
@[dlmf 15.12.E4]
def largeDenominatorGenerating (a b c z t : ℂ) : ℂ :=
  expSubOneDiv t ^ (b - 1) * exp (t * (1 - c)) * (1 - z + z * exp (-t)) ^ (-a)

/-- Taylor coefficients of DLMF's generating function. -/
@[dlmf 15.12.E4]
def largeDenominatorCoeff (a b c z : ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n (largeDenominatorGenerating a b c z) 0 / (n.factorial : ℂ)

/-- `expSubOneDiv` is the difference quotient of `exp` at `0`. -/
lemma expSubOneDiv_eq_dslope : expSubOneDiv = dslope exp 0 := by
  funext t
  by_cases ht : t = 0
  · subst ht; simp [expSubOneDiv, dslope_same, Complex.deriv_exp]
  · rw [expSubOneDiv, ite_eq_right_iff.mpr (fun h => absurd h ht), dslope_of_ne _ ht, slope_def_field, exp_zero, sub_zero]

/-- `expSubOneDiv` is entire. -/
lemma analyticAt_expSubOneDiv (t : ℂ) : AnalyticAt ℂ expSubOneDiv t := by
  rw [expSubOneDiv_eq_dslope]
  have h : DifferentiableOn ℂ (dslope exp 0) Set.univ :=
    (differentiableOn_dslope Filter.univ_mem).mpr differentiable_exp.differentiableOn
  exact h.analyticAt Filter.univ_mem

/-- The generating function is analytic at `0`. -/
lemma analyticAt_largeDenominatorGenerating (a b c z : ℂ) :
    AnalyticAt ℂ (largeDenominatorGenerating a b c z) 0 := by
  have h1 : expSubOneDiv 0 ∈ slitPlane := by simp [expSubOneDiv]
  have h2 : (1 - z + z * exp (-(0 : ℂ))) ∈ slitPlane := by simp
  unfold largeDenominatorGenerating
  exact (((analyticAt_expSubOneDiv 0).cpow analyticAt_const h1).mul
    ((analyticAt_id.mul analyticAt_const).cexp)).mul
    (((analyticAt_const.sub analyticAt_const).add
      (analyticAt_const.mul (analyticAt_id.neg.cexp))).cpow analyticAt_const h2)

@[dlmf 15.12.E4]
theorem large_denominator_generating_hasSum (a b c z : ℂ) :
    ∃ r : ℝ, 0 < r ∧ ∀ t : ℂ, ‖t‖ < r →
      HasSum (fun n : ℕ => largeDenominatorCoeff a b c z n * t ^ n)
        (largeDenominatorGenerating a b c z t) := by
  obtain ⟨r, hr, h⟩ := (analyticAt_largeDenominatorGenerating a b c z).exists_ball_analyticOnNhd
  refine ⟨r, hr, fun t ht => ?_⟩
  have hs := Complex.hasSum_taylorSeries_on_ball h.differentiableOn (z := t) (by simpa using ht)
  refine hs.congr_fun fun n => ?_
  simp only [largeDenominatorCoeff, sub_zero, smul_eq_mul]
  ring


@[dlmf 15.12.E3]
theorem large_denominator_shift_expansion (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) (m : ℕ) :
    Asymptotics.IsBigO atTop
      (fun l : ℝ => Gamma (c - b + l) / Gamma (c + l) * (l : ℂ) ^ b * ₂F₁ a b (c + l) z -
        ∑ k ∈ Finset.range m, largeDenominatorCoeff a b c z k * poch b k / (l : ℂ) ^ k)
      (fun l : ℝ => (l : ℂ)⁻¹ ^ m) := by
  sorry

@[dlmf 15.12.E5]
theorem large_opposite_parameters_bessel (a b c : ℝ) {x : ℝ} (hx : 1 < x) (hx3 : x < 3) :
    let ζ : ℂ := Real.arcosh x
    ∃ r₁ r₂ : ℝ → ℂ,
      Asymptotics.IsBigO atTop r₁ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      Asymptotics.IsBigO atTop r₂ (fun l : ℝ => (l : ℂ)⁻¹ ^ 2) ∧
      ∀ᶠ l : ℝ in atTop,
        regularizedGaussHGFun (a + l) (b - l) c ((1 - (x : ℂ)) / 2) =
          (2 : ℂ) ^ (((a : ℂ) + b - 1) / 2) * (x + 1 : ℂ) ^ (((c : ℂ) - a - b - 1) / 2) /
            (x - 1 : ℂ) ^ ((c : ℂ) / 2) * (ζ * sinh ζ) ^ (1 / 2 : ℂ) *
            ((l : ℂ) + a / 2 - b / 2) ^ (1 - (c : ℂ)) *
            (besselI (c - 1) (((l : ℂ) + a / 2 - b / 2) * ζ) * (1 + r₁ l) +
              besselI (c - 2) (((l : ℂ) + a / 2 - b / 2) * ζ) / (2 * (l : ℂ) + a - b) *
                (((c : ℂ) - 1 / 2) * (c - 3 / 2) * (1 / ζ - cosh ζ / sinh ζ) +
                  (2 * (c : ℂ) - a - b - 1) * (a + b - 1) / 2 * tanh (ζ / 2) + r₂ l)) := by
  sorry

end AAR.Hypergeometric
