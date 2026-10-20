/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Confluent.Basic
public import AAR.Confluent.IntegralRepresentations
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Zeros (DLMF §§13.9, 13.22)

`p(a,b)` and `n(a,b)` count positive zeros of `M(a,b,x)` and of
`M(a,b,x)` in the left half-plane after Kummer's transformation, respectively.
`T(a,b)` and `P(a,b)` count zeros of `U(a,b,x)` on `(0,∞)`. Bessel-zero
expansions 13.9.8 and 13.22.1 are deferred pending indexed Bessel zeros.
-/

@[expose] public section

open Complex Filter Set
open scoped Real Topology
open AAR.Hypergeometric

noncomputable section

namespace AAR.Confluent

/-- Positive real zeros of `M(a,b,·)`. -/
def kummerMPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ kummerM a b x = 0}

/-- Positive real zeros of `U(a,b,·)`. -/
def kummerUPosZeros (a b : ℝ) : Set ℝ :=
  {x | 0 < x ∧ kummerU a b x = 0}

/-- The boundary case omitted by the positive-zero formulas: `M(0,b,x) = 1`. -/
theorem kummerM_posZeros_zero (b : ℝ) : (kummerMPosZeros 0 b).encard = 0 := by
  simp [kummerMPosZeros, kummerM_of_zero_param]

/- The old 13.9.3–4 statements were false at `a = 0`; 13.9.5 omitted `a,b < 0`. -/
@[dlmf 13.9.E1]
theorem kummerM_posZeros_neg_a {a b : ℝ} (ha : a < 0) (hb : 0 < b) :
    (kummerMPosZeros a b).encard = Int.toNat ⌈-a⌉ := by
  sorry

/-- Kummer's series has positive real part for nonnegative real numerator and
positive real argument, including its totalized denominator value at zero. -/
lemma kummerM_re_pos_of_nonneg {a b x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hx : 0 < x) : 0 < (kummerM a b x).re := by
  rcases eq_or_lt_of_le hb with rfl | hb
  · have h : kummerM (a : ℂ) 0 x = 1 := by
      unfold kummerM
      rw [tsum_eq_single 0]
      · simp [poch_zero]
      · intro n hn
        obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        simp only [Nat.succ_eq_add_one, poch_zero_succ, zero_mul, div_zero]
    simp [h]
  · have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := not_neg_nat_of_re_pos (by simpa using hb)
    have hs := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb').hasSum_mul_pow
      (z := (x : ℂ)) (by simp)
    have hr := Complex.hasSum_re hs
    let t : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
      ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n
    have ht : ∀ n : ℕ, (kummerMCoeff (a : ℂ) b n * (x : ℂ) ^ n).re = t n := by
      intro n
      simp [t, kummerMCoeff, poch_ofReal, ← ofReal_natCast, ← ofReal_mul,
        ← ofReal_div, ← ofReal_pow]
    simp only [ht] at hr
    have hnonneg : ∀ n, 0 ≤ t n := fun n => mul_nonneg
      (div_nonneg (poch_eval_nonneg ha n)
        (mul_nonneg (poch_eval_nonneg hb.le n) (Nat.cast_nonneg _)))
      (pow_nonneg hx.le n)
    have hle := hr.summable.sum_le_tsum ({0} : Finset ℕ) (fun n _ => hnonneg n)
    have h0 : t 0 = 1 := by simp [t]
    rw [Finset.sum_singleton, h0, hr.tsum_eq] at hle
    linarith

@[dlmf 13.9.E2]
theorem kummerM_posZeros_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (kummerMPosZeros a b).encard = 0 := by
  rw [Set.encard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro x ⟨hx, hzero⟩
  have hp := kummerM_re_pos_of_nonneg ha hb hx
  rw [hzero] at hp
  simp at hp

/-- For real parameters with `b ∉ -ℕ`, Kummer's series at a real point is real: it is the
complexification of the real power series. -/
lemma kummerM_ofReal_hasSum {a b : ℝ} (hb : ∀ k : ℕ, (b : ℂ) ≠ -k) (x : ℝ) :
    HasSum (fun n => (ascPochhammer ℝ n).eval a /
        ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n) (kummerM a b x).re ∧
      kummerM a b x = ((kummerM a b x).re : ℂ) := by
  let t : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
    ((ascPochhammer ℝ n).eval b * n.factorial) * x ^ n
  have hs := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb).hasSum_mul_pow
    (z := (x : ℂ)) (by simp)
  have ht : ∀ n : ℕ, kummerMCoeff (a : ℂ) b n * (x : ℂ) ^ n = (t n : ℂ) := by
    intro n
    simp [t, kummerMCoeff, poch_ofReal]
  simp only [ht] at hs
  have hr : HasSum t (kummerM a b x).re := by
    simpa using Complex.hasSum_re hs
  refine ⟨hr, ?_⟩
  exact hs.unique (Complex.hasSum_ofReal.mpr hr)

@[dlmf 13.9.E3]
theorem kummerM_posZeros_one {a b : ℝ} (ha : 0 < a) (hb0 : -1 < b) (hb1 : b < 0) :
    (kummerMPosZeros a b).encard = 1 := by
  have hb' : ∀ k : ℕ, (b : ℂ) ≠ -k := by
    intro k hk
    have h := congrArg re hk
    simp only [ofReal_re, neg_re, natCast_re] at h
    rcases k with _ | k
    · simp at h; linarith
    · push_cast at h; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  let c : ℕ → ℝ := fun n => (ascPochhammer ℝ n).eval a /
    ((ascPochhammer ℝ n).eval b * n.factorial)
  let f : ℝ → ℝ := fun x => (kummerM a b x).re
  have hS (x : ℝ) : HasSum (fun n => c n * x ^ n) (f x) := (kummerM_ofReal_hasSum hb' x).1
  have hR (x : ℝ) : kummerM a b x = (f x : ℂ) := (kummerM_ofReal_hasSum hb' x).2
  have hc1 : c 1 = a / b := by simp [c]
  have hcneg : ∀ n : ℕ, 1 ≤ n → c n ≤ 0 := by
    intro n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hden : (ascPochhammer ℝ (m + 1)).eval b < 0 := by
      rw [ascPochhammer_succ_left, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_comp,
        Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
      exact mul_neg_of_neg_of_pos hb1 (ascPochhammer_pos m _ (by linarith))
    have hnum := ascPochhammer_pos (m + 1) a ha
    exact div_nonpos_of_nonneg_of_nonpos hnum.le
      (mul_nonpos_of_nonpos_of_nonneg hden.le (Nat.cast_nonneg _))
  have hkey : ∀ x y : ℝ, 0 ≤ x → x ≤ y → f y - f x ≤ a / b * (y - x) := by
    intro x y hx hxy
    have hd := (hS y).sub (hS x)
    have hneg : ∀ n, 0 ≤ -(c n * y ^ n - c n * x ^ n) := by
      intro n
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have := hcneg n hn
        have hp : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx hxy n
        nlinarith
    have hle := hd.neg.summable.sum_le_tsum ({1} : Finset ℕ) (fun n _ => hneg n)
    rw [Finset.sum_singleton, hd.neg.tsum_eq, hc1] at hle
    simp only [pow_one] at hle
    linarith
  have hf0 : f 0 = 1 := by simp [f, kummerM_zero]
  have hanti : StrictAntiOn f (Set.Ici 0) := by
    intro x hx y hy hxy
    have h := hkey x y hx hxy.le
    have hab : a / b < 0 := div_neg_of_pos_of_neg ha hb1
    nlinarith
  have hcont : Continuous f := by
    have h := (hasFPowerSeriesOnBall_kummerM (a := (a : ℂ)) hb').continuousOn
    rw [Metric.eball_top] at h
    exact continuous_re.comp ((continuousOn_univ.mp h).comp continuous_ofReal)
  set x₁ : ℝ := -2 * b / a with hx₁
  have hx₁pos : 0 < x₁ := div_pos (by linarith) ha
  have hfx₁ : f x₁ < 0 := by
    have h := hkey 0 x₁ le_rfl hx₁pos.le
    rw [hf0, sub_zero, hx₁] at h
    have hbne : b ≠ 0 := hb1.ne
    have : a / b * (-2 * b / a) = -2 := by field_simp
    linarith
  obtain ⟨x₀, hx₀, hfx₀⟩ := intermediate_value_Icc' hx₁pos.le hcont.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f x₁) (f 0) by rw [hf0]; exact ⟨hfx₁.le, zero_le_one⟩)
  have hx₀pos : 0 < x₀ := by
    rcases hx₀.1.eq_or_lt with h | h
    · rw [← h, hf0] at hfx₀; norm_num at hfx₀
    · exact h
  have hset : kummerMPosZeros a b = {x₀} := by
    ext x
    simp only [kummerMPosZeros, Set.mem_ofPred_eq, Set.mem_singleton_iff, hR, ofReal_eq_zero]
    constructor
    · rintro ⟨hx, hfx⟩
      exact hanti.injOn hx.le hx₀pos.le (hfx.trans hfx₀.symm)
    · rintro rfl
      exact ⟨hx₀pos, hfx₀⟩
  rw [hset, Set.encard_singleton]

@[dlmf 13.9.E4]
theorem kummerM_posZeros_b_le_neg_one {a b : ℝ} (ha : 0 < a) (hb : b ≤ -1)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard =
      Int.toNat (⌊-(b / 2)⌋ - ⌊-((b + 1) / 2)⌋) := by
  sorry

@[dlmf 13.9.E5]
theorem kummerM_posZeros_ceil {a b : ℝ} (ha : a < 0) (hb : b < 0) (h : ⌈-a⌉ ≥ ⌈-b⌉) (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard = Int.toNat (⌈-a⌉ - ⌈-b⌉) := by
  sorry

@[dlmf 13.9.E6]
theorem kummerM_posZeros_ceil_swap {a b : ℝ} (h : ⌈-b⌉ > ⌈-a⌉) (ha : 0 < ⌈-a⌉)
    (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    (kummerMPosZeros a b).encard = Int.toNat ((⌈-b⌉ - ⌈-a⌉) % 2) := by
  sorry

@[dlmf 13.9.E7]
theorem kummerM_negZeros_eq {a b : ℝ} (hbi : ∀ k : ℕ, b ≠ -(k : ℝ)) :
    {x : ℝ | x < 0 ∧ kummerM a b x = 0}.encard =
      (kummerMPosZeros (b - a) b).encard := by
  have hb : ∀ k : ℕ, (b : ℂ) ≠ -k := fun k hk => hbi k (by exact_mod_cast hk)
  have hz (x : ℝ) : kummerM a b x = 0 ↔ kummerM (b - a) b (-x) = 0 := by
    rw [kummerM_kummer_transform hb, mul_eq_zero]
    simp [Complex.exp_ne_zero]
  have heq : {x : ℝ | x < 0 ∧ kummerM a b x = 0} =
      (fun x : ℝ => -x) ⁻¹' kummerMPosZeros (b - a) b := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, kummerMPosZeros, neg_pos, hz, ofReal_sub, ofReal_neg]
  rw [heq]
  exact Set.encard_preimage_of_bijective (Equiv.neg ℝ).bijective _

@[dlmf 13.9.E9]
theorem kummerM_large_zeros (a b : ℂ) (sign : Bool) (ha : ∀ k : ℕ, a ≠ -k)
    (hba : ∀ k : ℕ, b - a ≠ -k) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ r : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => r n -
          ((if sign then 1 else -1) * (2 * n + a) * π * I +
            log (-Gamma a / Gamma (b - a) *
              ((if sign then 1 else -1) * 2 * n * π * I) ^ (b - 2 * a))))
        (fun n : ℕ => (n : ℂ)⁻¹ * log n) ∧
      ∀ᶠ n : ℕ in atTop, kummerM a b (r n) = 0 := by
  sorry

@[dlmf 13.9.E10]
theorem kummerM_zeros_in_a (b z : ℂ) (hz : z ≠ 0) (hb : ∀ k : ℕ, b ≠ -k) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + π ^ 2 / (4 * z) * ((n : ℂ) ^ 2 + (b - 3 / 2) * n) +
          1 / (16 * z) * ((b - 3 / 2) ^ 2 * π ^ 2 + 4 / 3 * z ^ 2 -
            8 * b * (z - 1) - 4 * b ^ 2 - 3))
        (fun n : ℕ => (n : ℂ)⁻¹) ∧
      ∀ᶠ n : ℕ in atTop, kummerM (α n) b z = 0 := by
  sorry

/-- Zeros of `U(a,b,·)` in the open sector `|ph z| < π`; DLMF calls their number `T(a,b)`. -/
def kummerUSectorZeros (a b : ℝ) : Set ℂ :=
  {z | z ≠ 0 ∧ |arg z| < π ∧ kummerU a b z = 0}

/-- DLMF 13.9.11: the number of zeros in the sector `|ph z| < π` when `b ≤ 1`, `a < 0` and
`Γ(a)Γ(a-b+1) > 0`, with `a`, `b` and `a-b+1` nonintegral. Corrected 2026-10-20: the
earlier statement counted positive zeros with this formula and omitted DLMF's hypotheses;
it was false, e.g. at `(a,b) = (-1.3,-2.2)` there are no positive zeros. -/
@[dlmf 13.9.E11]
theorem kummerU_sectorZeros_gamma_pos {a b : ℝ} (hb : b ≤ 1) (ha : a < 0)
    (hai : ∀ n : ℤ, a ≠ n) (hbi : ∀ n : ℤ, b ≠ n) (habi : ∀ n : ℤ, a - b + 1 ≠ n)
    (h : 0 < Real.Gamma a * Real.Gamma (a - b + 1)) :
    (kummerUSectorZeros a b).encard = Int.toNat (⌊-a⌋ + 1) := by
  sorry

/-- DLMF 13.9.12, the companion of `kummerU_sectorZeros_gamma_pos` for
`Γ(a)Γ(a-b+1) < 0` (corrected 2026-10-20 in the same way). -/
@[dlmf 13.9.E12]
theorem kummerU_sectorZeros_gamma_neg {a b : ℝ} (hb : b ≤ 1) (ha : a < 0)
    (hai : ∀ n : ℤ, a ≠ n) (hbi : ∀ n : ℤ, b ≠ n) (habi : ∀ n : ℤ, a - b + 1 ≠ n)
    (h : Real.Gamma a * Real.Gamma (a - b + 1) < 0) :
    (kummerUSectorZeros a b).encard = Int.toNat ⌊-a⌋ := by
  sorry

@[dlmf 13.9.E13]
theorem kummerU_posZeros_none {a b : ℝ} (ha : 0 ≤ a) :
    (kummerUPosZeros a b).encard = 0 := by
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem]
  rintro x ⟨hx, hzero⟩
  rcases ha.eq_or_lt with rfl | ha
  · simp [kummerU_zero] at hzero
  · have hl := kummerU_laplace (a := (a : ℂ)) (b := b) (z := x) (by simpa using ha)
      (by simpa using hx)
    let g : ℝ → ℝ := fun t => Real.exp (-x * t) * t ^ (a - 1) * (1 + t) ^ (b - a - 1)
    have hfg : ∀ t ∈ Set.Ioi (0 : ℝ),
        exp (-(x : ℂ) * t) * (t : ℂ) ^ ((a : ℂ) - 1) * (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1) =
          (g t : ℂ) := by
      intro t ht
      have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
      have ht1 : (0 : ℝ) ≤ 1 + t := by linarith
      simp only [g, ofReal_mul, ofReal_exp, ofReal_cpow ht0, ofReal_cpow ht1]
      push_cast
      ring_nf
    have hgpos : ∀ t ∈ Set.Ioi (0 : ℝ), 0 < g t := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have : 0 < 1 + t := by linarith
      positivity
    have hgi : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
      refine MeasureTheory.IntegrableOn.congr_fun
        (kummerU_laplace_integrable (a := (a : ℂ)) (b := b) (z := x)
          (by simpa using ha) (by simpa using hx)).norm (fun t ht => ?_) measurableSet_Ioi
      rw [hfg t ht, norm_real, Real.norm_of_nonneg (hgpos t ht).le]
    have hpos : 0 < ∫ t in Set.Ioi 0, g t := by
      rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
        (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => (hgpos t ht).le) hgi]
      have hsup : Function.support g ∩ Set.Ioi 0 = Set.Ioi 0 := by
        ext t
        simp only [Set.mem_inter_iff, Function.mem_support, and_iff_right_iff_imp]
        exact fun ht => (hgpos t ht).ne'
      rw [hsup, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    have hI : (∫ t : ℝ in Set.Ioi 0,
        exp (-(x : ℂ) * t) * (t : ℂ) ^ ((a : ℂ) - 1) * (1 + (t : ℂ)) ^ ((b : ℂ) - a - 1)) =
        ((∫ t in Set.Ioi 0, g t : ℝ) : ℂ) := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hfg,
        integral_complex_ofReal]
    have hG : Gamma (a : ℂ) ≠ 0 := Gamma_ne_zero_of_re_pos (by simpa using ha)
    rw [hl, hI] at hzero
    simp [hG, hpos.ne'] at hzero

/-- DLMF 13.9.14: the number `P(a,b)` of positive zeros when `a + 1 < b ≤ 1`, with `a`, `b`
and `a-b+1` nonintegral (acquired 2026-10-20; DLMF's `P` counts positive zeros). -/
@[dlmf 13.9.E14]
theorem kummerU_posZeros_ceil {a b : ℝ} (hb : b ≤ 1) (hab : a + 1 < b)
    (hai : ∀ n : ℤ, a ≠ n) (hbi : ∀ n : ℤ, b ≠ n) (habi : ∀ n : ℤ, a - b + 1 ≠ n) :
    (kummerUPosZeros a b).encard = Int.toNat ⌈b - a - 1⌉ := by
  sorry

/-- DLMF 13.9.15: no positive zeros when `a + 1 ≥ b`. Stronger than DLMF: no restriction on
`b` and no nonintegrality hypotheses. Kummer's transformation reduces it to 13.9.13 at the
nonnegative first parameter `a - b + 1`. -/
@[dlmf 13.9.E15]
theorem kummerU_posZeros_none_of_le {a b : ℝ} (h : b ≤ a + 1) :
    (kummerUPosZeros a b).encard = 0 := by
  have h0 := kummerU_posZeros_none (a := a - b + 1) (b := 2 - b) (by linarith)
  rw [Set.encard_eq_zero, Set.eq_empty_iff_forall_notMem] at h0 ⊢
  rintro x ⟨hx, hzero⟩
  refine h0 x ⟨hx, ?_⟩
  have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  rw [kummerU_kummer_transform_all _ _ hx0] at hzero
  have hpow : (x : ℂ) ^ (1 - (b : ℂ)) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff]
    exact fun h => hx0 h.1
  push_cast
  exact (mul_eq_zero.mp hzero).resolve_left hpow

/- DLMF 13.9.14 (count of zeros of `U(a,b,·)` on the negative axis) was removed from the
formalization: with the principal-branch `kummerU` the stated count is false, since `U` is
complex-valued and bounded away from zero on the negative axis in tested cases where the
count is positive. See `STATEMENT_AUDIT_2026-09-27.md`. -/

/-- No zeros of the principal-branch `U(a,b,·)` on the negative axis when `a + 1 ≥ b`.
This is not DLMF 13.9.15, whose `P(a,b)` counts positive zeros (see
`kummerU_posZeros_none_of_le`); the `dlmf` tag was removed on 2026-10-20.
The polynomial case `a ∈ -ℕ` is excluded: there `U(-n,b,x) = (-1)ⁿ n! L_n^{(b-1)}(x)` with
`b - 1 ≤ -n`, which can vanish at negative `x` (e.g. `U(-1,-1,x) = x + 1`). For other `a`
the statement was checked numerically (mpmath, 16 October 2026); `|U|` approaches zero on the
negative axis only as `a` approaches a nonpositive integer. -/
theorem kummerU_negZeros_none {a b : ℝ} (h : a + 1 ≥ b) (ha : ∀ n : ℕ, a ≠ -(n : ℝ)) :
    {x : ℝ | x < 0 ∧ kummerU a b (x : ℂ) = 0}.encard = 0 := by
  sorry

@[dlmf 13.9.E16]
theorem kummerU_zeros_in_a (b z : ℂ) (hz : z ∈ slitPlane) :
    ∃ α : ℕ → ℂ,
      Asymptotics.IsBigO atTop
        (fun n : ℕ => α n + n + 2 / π * (z * n) ^ (1 / 2 : ℂ) + 2 * z / π ^ 2 -
          b / 2 - 1 / 4)
        (fun n : ℕ => (n : ℂ)⁻¹ ^ (1 / 2 : ℂ)) ∧
      ∀ᶠ n : ℕ in atTop, kummerU (α n) b z = 0 := by
  sorry

end AAR.Confluent
