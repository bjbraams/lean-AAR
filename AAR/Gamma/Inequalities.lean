/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Gamma.Digamma
public import AAR.Gamma.IntegralRepresentations
public import AAR.Gamma.Products
public import AAR.Gamma.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Inequalities (DLMF §5.6)

Real-variable inequalities and complex Gamma bounds from DLMF §5.6.
The Gamma-ratio bound has real shifts `0 ≤ a` and `1 ≤ b - a` and holds
on the open right half-plane. The final Gamma bound assumes `0 ≤ z.re`.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Gamma

/-- By Binet's formula the middle term is `exp Φ(x)` with `0 < Φ(x) < 1/(12x)`
(Temme §3.6.1). -/
@[dlmf 5.6.E1]
theorem Gamma_stirling_bounds {x : ℝ} (hx : 0 < x) :
    1 < (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x ∧
      (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x <
        Real.exp (1 / (12 * x)) := by
  have hQ : (2 * π) ^ (-(1 / 2 : ℝ)) * x ^ (1 / 2 - x) * Real.exp x * Real.Gamma x =
      Real.exp (binetIntegral x) := by
    rw [← Real.exp_log (Real.Gamma_pos_of_pos hx), log_Gamma_eq_add_binetIntegral hx,
      Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos hx, ← Real.exp_add,
      ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  obtain ⟨h0, h1⟩ := binetIntegral_pos_lt hx
  rw [hQ]
  exact ⟨Real.one_lt_exp_iff.mpr h0, Real.exp_lt_exp.mpr h1⟩

@[dlmf 5.6.E2]
theorem inv_Gamma_add_inv_Gamma_inv {x : ℝ} (hx : 0 < x) :
    1 / Real.Gamma x + 1 / Real.Gamma x⁻¹ ≤ 2 := by
  sorry

@[dlmf 5.6.E3]
theorem inv_Gamma_sq_add {x : ℝ} (hx : 0 < x) :
    (1 / Real.Gamma x) ^ 2 + (1 / Real.Gamma x⁻¹) ^ 2 ≤ 2 := by
  sorry

/-- `ψ` is strictly increasing on `(0, ∞)`. -/
lemma digamma_strictMonoOn : StrictMonoOn Real.digamma (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx' : (0 : ℝ) < x := hx
  have hy' : (0 : ℝ) < y := hy
  rw [Real.digamma_eq_tsum hx', Real.digamma_eq_tsum hy']
  have h := (Real.summable_digammaSeriesTerm hx').tsum_lt_tsum (i := 0)
    (fun n => by
      simp only [Real.digammaSeriesTerm]
      have : 0 < x + n := by positivity
      gcongr)
    (by simp only [Real.digammaSeriesTerm, Nat.cast_zero, add_zero]; gcongr)
    (Real.summable_digammaSeriesTerm hy')
  linarith

/-- `log Γ` is strictly convex on `(0, ∞)`. -/
lemma strictConvexOn_log_Gamma :
    StrictConvexOn ℝ (Set.Ioi 0) fun y : ℝ => Real.log (Real.Gamma y) := by
  refine StrictMonoOn.strictConvexOn_of_deriv (convex_Ioi 0)
    (fun y hy => (Real.hasDerivAt_log_Gamma hy).continuousAt.continuousWithinAt) ?_
  rw [interior_Ioi]
  intro a ha b hb hab
  rw [(Real.hasDerivAt_log_Gamma ha).deriv, (Real.hasDerivAt_log_Gamma hb).deriv]
  exact digamma_strictMonoOn ha hb hab

lemma log_Gamma_add_one' {y : ℝ} (hy : 0 < y) :
    Real.log (Real.Gamma (y + 1)) = Real.log (Real.Gamma y) + Real.log y := by
  rw [Real.Gamma_add_one hy.ne', Real.log_mul hy.ne' (Real.Gamma_pos_of_pos hy).ne', add_comm]

/-- Gautschi's inequality, from the strict log-convexity of `Γ`. -/
@[dlmf 5.6.E4]
theorem Gamma_ratio_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    x ^ (1 - s) < Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) < (x + 1) ^ (1 - s) := by
  set f : ℝ → ℝ := fun y => Real.log (Real.Gamma y) with hf
  have hsc := strictConvexOn_log_Gamma
  have hxs : 0 < x + s := by linarith
  have hfx : f (x + 1) = f x + Real.log x := log_Gamma_add_one' hx
  have hfxs : f (x + s + 1) = f (x + s) + Real.log (x + s) := log_Gamma_add_one' hxs
  have hlow : f (x + s) < (1 - s) * f x + s * f (x + 1) := by
    have := hsc.2 (show x ∈ Set.Ioi 0 from hx) (show x + 1 ∈ Set.Ioi 0 by
      simp only [Set.mem_Ioi]; linarith) (by linarith : x ≠ x + 1)
      (by linarith : (0 : ℝ) < 1 - s) hs0 (by ring : 1 - s + s = 1)
    simp only [smul_eq_mul] at this
    rwa [show (1 - s) * x + s * (x + 1) = x + s by ring] at this
  have hup : f (x + 1) < s * f (x + s) + (1 - s) * f (x + s + 1) := by
    have := hsc.2 (show x + s ∈ Set.Ioi 0 from hxs) (show x + s + 1 ∈ Set.Ioi 0 by
      simp only [Set.mem_Ioi]; linarith) (by linarith : x + s ≠ x + s + 1)
      hs0 (by linarith : (0 : ℝ) < 1 - s) (by ring : s + (1 - s) = 1)
    simp only [smul_eq_mul] at this
    rwa [show s * (x + s) + (1 - s) * (x + s + 1) = x + 1 by ring] at this
  have hGpos : 0 < Real.Gamma (x + 1) / Real.Gamma (x + s) :=
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos hxs)
  have hratio : Real.log (Real.Gamma (x + 1) / Real.Gamma (x + s)) = f (x + 1) - f (x + s) :=
    Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos hxs).ne'
  constructor
  · rw [← Real.exp_log hGpos, ← Real.exp_log (Real.rpow_pos_of_pos hx _), Real.exp_lt_exp,
      Real.log_rpow hx, hratio]
    rw [hfx] at hlow ⊢
    nlinarith
  · rw [← Real.exp_log hGpos, ← Real.exp_log (Real.rpow_pos_of_pos (by linarith : 0 < x + 1) _),
      Real.exp_lt_exp, Real.log_rpow (by linarith), hratio]
    have hl : Real.log (x + s) < Real.log (x + 1) := Real.log_lt_log hxs (by linarith)
    rw [hfxs] at hup
    nlinarith

/-- `log r ≤ (r - r⁻¹)/2` for `r ≥ 1` (logarithmic vs geometric mean). -/
lemma log_le_half_sub_inv {r : ℝ} (hr : 1 ≤ r) : Real.log r ≤ (r - r⁻¹) / 2 := by
  set k : ℝ → ℝ := fun r => (r - r⁻¹) / 2 - Real.log r with hk
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt k ((1 + (r ^ 2)⁻¹) / 2 - r⁻¹) r := by
    intro r hr
    have := (((hasDerivAt_id r).sub (hasDerivAt_inv hr.ne')).div_const 2).sub
      (Real.hasDerivAt_log hr.ne')
    exact this.congr_deriv (by first | ring | (simp only [id_eq]; ring))
  have hmono : MonotoneOn k (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun r hr => (hd r (by linarith [Set.mem_Ici.mp hr])).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (by rw [interior_Ici] at hr; linarith [Set.mem_Ioi.mp hr]))
        |>.differentiableAt.differentiableWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    have hr' : 0 < r := by linarith [Set.mem_Ioi.mp hr]
    rw [(hd r hr').deriv]
    have : (1 + (r ^ 2)⁻¹) / 2 - r⁻¹ = (1 - r⁻¹) ^ 2 / 2 := by field_simp; ring
    rw [this]; positivity
  have := hmono Set.self_mem_Ici hr hr
  simp only [hk, inv_one, sub_self, zero_div, Real.log_one] at this
  linarith

/-- `log(b/a) ≤ (b - a)/√(ab)` for `0 < a ≤ b`. -/
lemma log_div_le_sub_div_sqrt {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log (b / a) ≤ (b - a) / Real.sqrt (a * b) := by
  set r := Real.sqrt (b / a) with hr
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have hr1 : 1 ≤ r := by rw [hr]; exact Real.one_le_sqrt.mpr hba
  have hr0 : 0 < r := by linarith
  have hsq : r ^ 2 = b / a := Real.sq_sqrt (by positivity)
  have hlog : Real.log (b / a) = 2 * Real.log r := by
    rw [← hsq, Real.log_pow]; push_cast; ring
  have hab' : Real.sqrt (a * b) = a * r := by
    have ha0 : a ≠ 0 := ha.ne'
    rw [hr, show a * b = a ^ 2 * (b / a) by field_simp, Real.sqrt_mul (sq_nonneg a),
      Real.sqrt_sq ha.le]
  rw [hlog, hab']
  have h := log_le_half_sub_inv hr1
  have hb : b = a * r ^ 2 := by rw [hsq]; field_simp
  rw [hb]
  have : (a * r ^ 2 - a) / (a * r) = r - r⁻¹ := by field_simp
  rw [this]
  linarith

/-- `2(b - a)/(a + b) ≤ log(b/a)` for `0 < a ≤ b` (logarithmic vs arithmetic mean). -/
lemma two_mul_sub_div_add_le_log {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    2 * (b - a) / (a + b) ≤ Real.log (b / a) := by
  set k : ℝ → ℝ := fun r => Real.log r - 2 * (r - 1) / (r + 1) with hk
  have hd : ∀ r : ℝ, 0 < r → HasDerivAt k (r⁻¹ - 4 / (r + 1) ^ 2) r := by
    intro r hr
    have h1 : r + 1 ≠ 0 := by linarith
    have := (Real.hasDerivAt_log hr.ne').sub
      ((((hasDerivAt_id r).sub_const 1).const_mul 2).div ((hasDerivAt_id r).add_const 1) h1)
    exact this.congr_deriv (by simp only [id_eq]; ring)
  have hmono : MonotoneOn k (Set.Ici 1) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 1)
      (fun r hr => (hd r (by linarith [Set.mem_Ici.mp hr])).continuousAt.continuousWithinAt)
      (fun r hr => (hd r (by rw [interior_Ici] at hr; linarith [Set.mem_Ioi.mp hr]))
        |>.differentiableAt.differentiableWithinAt) fun r hr => ?_
    rw [interior_Ici] at hr
    have hr' : 0 < r := by linarith [Set.mem_Ioi.mp hr]
    rw [(hd r hr').deriv]
    have : r⁻¹ - 4 / (r + 1) ^ 2 = (r - 1) ^ 2 / (r * (r + 1) ^ 2) := by field_simp; ring
    rw [this]; positivity
  have hba : 1 ≤ b / a := by rw [le_div_iff₀ ha]; linarith
  have := hmono Set.self_mem_Ici hba hba
  simp only [hk, Real.log_one, sub_self, mul_zero, zero_div] at this
  have heq : 2 * (b / a - 1) / (b / a + 1) = 2 * (b - a) / (a + b) := by
    field_simp
    ring
  linarith

/-- `log Γ(z+1) - log Γ(z+s) - (1-s) ψ(z+c) → 0` as `z → ∞`, for `c > 0`. -/
lemma tendsto_log_Gamma_ratio_sub_digamma {s c : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (hc0 : 0 < c) :
    Tendsto (fun z : ℝ => Real.log (Real.Gamma (z + 1)) - Real.log (Real.Gamma (z + s)) -
      (1 - s) * Real.digamma (z + c)) atTop (𝓝 0) := by
  have hlogq : ∀ a b : ℝ, Tendsto (fun z : ℝ => Real.log (z + a) - Real.log (z + b)) atTop
      (𝓝 0) := by
    intro a b
    have h1 : Tendsto (fun z : ℝ => (z + a) / (z + b)) atTop (𝓝 1) := by
      have : Tendsto (fun z : ℝ => (1 + a * z⁻¹) / (1 + b * z⁻¹)) atTop (𝓝 ((1 + a * 0) /
          (1 + b * 0))) :=
        ((tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul a)).div
          (tendsto_const_nhds.add (tendsto_inv_atTop_zero.const_mul b)) (by simp))
      simp only [mul_zero, add_zero, div_one] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with z hz
      field_simp
    have := (Real.continuousAt_log one_ne_zero).tendsto.comp h1
    rw [Real.log_one] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (|a| + |b|)] with z hz
    have ha : 0 < z + a := by linarith [neg_abs_le a, abs_nonneg b]
    have hb : 0 < z + b := by linarith [neg_abs_le b, abs_nonneg a]
    simp only [Function.comp_apply]
    rw [Real.log_div ha.ne' hb.ne']
  have hinv : Tendsto (fun z : ℝ => (z + c)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ c tendsto_id)
  -- lower and upper bounds
  have hlo : Tendsto (fun z : ℝ => (1 - s) * (Real.log (z + 0) - Real.log (z + c))) atTop
      (𝓝 0) := by simpa using (hlogq 0 c).const_mul (1 - s)
  have hhi : Tendsto (fun z : ℝ => (1 - s) * ((Real.log (z + 1) - Real.log (z + c)) +
      (z + c)⁻¹)) atTop (𝓝 0) := by simpa using ((hlogq 1 c).add hinv).const_mul (1 - s)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [eventually_gt_atTop 0] with z hz
    obtain ⟨h1, -⟩ := Gamma_ratio_bounds hz hs0 hs1
    have hpos := div_pos (Real.Gamma_pos_of_pos (by linarith : 0 < z + 1))
      (Real.Gamma_pos_of_pos (by linarith : 0 < z + s))
    have hl := Real.log_lt_log (Real.rpow_pos_of_pos hz _) h1
    rw [Real.log_rpow hz, Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne'] at hl
    have hψ := (digamma_le_log_and (by linarith : 0 < z + c)).2
    rw [add_zero]
    nlinarith
  · filter_upwards [eventually_gt_atTop 0] with z hz
    obtain ⟨-, h2⟩ := Gamma_ratio_bounds hz hs0 hs1
    have hpos := div_pos (Real.Gamma_pos_of_pos (by linarith : 0 < z + 1))
      (Real.Gamma_pos_of_pos (by linarith : 0 < z + s))
    have hl := Real.log_lt_log hpos h2
    rw [Real.log_rpow (by linarith), Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne'
      (Real.Gamma_pos_of_pos (by linarith)).ne'] at hl
    have hψ := (digamma_le_log_and (by linarith : 0 < z + c)).1
    rw [one_div] at hψ
    nlinarith

/-- A function on `(0, ∞)` with `F(y+1) ≤ F(y)` and `F(z) → 0` as `z → ∞` is nonnegative. -/
lemma nonneg_of_antitone_step_of_tendsto {F : ℝ → ℝ} (hstep : ∀ y, 0 < y → F (y + 1) ≤ F y)
    (hlim : Tendsto F atTop (𝓝 0)) {y : ℝ} (hy : 0 < y) : 0 ≤ F y := by
  have hk : ∀ k : ℕ, F (y + k) ≤ F y := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have := hstep (y + k) (by positivity)
      push_cast
      rw [← add_assoc]
      linarith
  have hseq : Tendsto (fun k : ℕ => F (y + k)) atTop (𝓝 0) :=
    hlim.comp (tendsto_atTop_add_const_left _ y tendsto_natCast_atTop_atTop)
  exact le_of_tendsto' hseq hk

/-- The bounds of Elezović, Giordano and Pečarić. Both follow by telescoping: the step
`y ↦ y + 1` changes the gap by `log((y+1)/(y+s)) - (1-s)/(y+c)`, whose sign is fixed by the
inequalities between the logarithmic mean and the geometric (`c = √s`) or arithmetic
(`c = (1+s)/2`) means, and the gap tends to `0`. -/
@[dlmf 5.6.E5]
theorem Gamma_ratio_digamma_bounds {x s : ℝ} (hx : 0 < x) (hs0 : 0 < s) (hs1 : s < 1) :
    Real.exp ((1 - s) * Real.digamma (x + Real.sqrt s)) ≤
        Real.Gamma (x + 1) / Real.Gamma (x + s) ∧
      Real.Gamma (x + 1) / Real.Gamma (x + s) ≤
        Real.exp ((1 - s) * Real.digamma (x + (s + 1) / 2)) := by
  have hGpos : ∀ y, 0 < y → 0 < Real.Gamma (y + 1) / Real.Gamma (y + s) := fun y hy =>
    div_pos (Real.Gamma_pos_of_pos (by linarith)) (Real.Gamma_pos_of_pos (by linarith))
  have hratio : ∀ y, 0 < y → Real.log (Real.Gamma (y + 1) / Real.Gamma (y + s)) =
      Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s)) := fun y hy =>
    Real.log_div (Real.Gamma_pos_of_pos (by linarith)).ne' (Real.Gamma_pos_of_pos (by linarith)).ne'
  -- the step of `log Γ(y+1) - log Γ(y+s)` under `y ↦ y + 1`
  have hstepΓ : ∀ y, 0 < y →
      (Real.log (Real.Gamma (y + 1 + 1)) - Real.log (Real.Gamma (y + 1 + s))) =
        (Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s))) +
          (Real.log (y + 1) - Real.log (y + s)) := by
    intro y hy
    rw [log_Gamma_add_one' (by linarith : 0 < y + 1),
      show y + 1 + s = (y + s) + 1 by ring, log_Gamma_add_one' (by linarith : 0 < y + s)]
    ring
  have hsq0 : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs0
  have hsq1 : Real.sqrt s ≤ 1 := Real.sqrt_le_one.mpr hs1.le
  constructor
  · set F : ℝ → ℝ := fun y => Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s)) -
      (1 - s) * Real.digamma (y + Real.sqrt s) with hF
    have hstep : ∀ y, 0 < y → F (y + 1) ≤ F y := by
      intro y hy
      simp only [hF]
      rw [hstepΓ y hy, show y + 1 + Real.sqrt s = (y + Real.sqrt s) + 1 by ring,
        Real.digamma_add_one (by positivity)]
      -- `log((y+1)/(y+s)) ≤ (1-s)/(y+√s)`
      have hmean := log_div_le_sub_div_sqrt (a := y + s) (b := y + 1) (by linarith)
        (by linarith)
      rw [Real.log_div (by linarith) (by linarith)] at hmean
      have hgeo : y + Real.sqrt s ≤ Real.sqrt ((y + s) * (y + 1)) := by
        rw [Real.le_sqrt (by positivity) (by positivity)]
        have : (Real.sqrt s) ^ 2 = s := Real.sq_sqrt hs0.le
        nlinarith [sq_nonneg (1 - Real.sqrt s), mul_nonneg hy.le (sq_nonneg (1 - Real.sqrt s))]
      have hfrac : (y + 1 - (y + s)) / Real.sqrt ((y + s) * (y + 1)) ≤
          (1 - s) * (y + Real.sqrt s)⁻¹ := by
        rw [show y + 1 - (y + s) = 1 - s by ring, div_eq_mul_inv]
        gcongr
      nlinarith
    have h := nonneg_of_antitone_step_of_tendsto hstep
      (tendsto_log_Gamma_ratio_sub_digamma hs0 hs1 hsq0) hx
    rw [← Real.exp_log (hGpos x hx), Real.exp_le_exp, hratio x hx]
    simp only [hF] at h
    linarith
  · set G : ℝ → ℝ := fun y => (1 - s) * Real.digamma (y + (s + 1) / 2) -
      (Real.log (Real.Gamma (y + 1)) - Real.log (Real.Gamma (y + s))) with hG
    have hc0 : 0 < (s + 1) / 2 := by linarith
    have hc1 : (s + 1) / 2 ≤ 1 := by linarith
    have hstep : ∀ y, 0 < y → G (y + 1) ≤ G y := by
      intro y hy
      simp only [hG]
      rw [hstepΓ y hy, show y + 1 + (s + 1) / 2 = (y + (s + 1) / 2) + 1 by ring,
        Real.digamma_add_one (by positivity)]
      have hmean := two_mul_sub_div_add_le_log (a := y + s) (b := y + 1) (by linarith)
        (by linarith)
      rw [Real.log_div (by linarith) (by linarith)] at hmean
      have : 2 * (y + 1 - (y + s)) / (y + s + (y + 1)) = (1 - s) * (y + (s + 1) / 2)⁻¹ := by
        have : y + (s + 1) / 2 ≠ 0 := by linarith
        field_simp
        ring
      rw [this] at hmean
      nlinarith
    have hlim : Tendsto G atTop (𝓝 0) := by
      simpa [hG] using (tendsto_log_Gamma_ratio_sub_digamma hs0 hs1 hc0).neg
    have h := nonneg_of_antitone_step_of_tendsto hstep hlim hx
    rw [← Real.exp_log (hGpos x hx), Real.exp_le_exp, hratio x hx]
    simp only [hG] at h
    linarith

@[dlmf 5.6.E6]
theorem norm_Gamma_add_mul_I_le {x y : ℝ} (hx : 0 < x) :
    ‖Complex.Gamma (x + I * y)‖ ≤ |Real.Gamma x| := by
  have hre : (0 : ℝ) < (x + I * y : ℂ).re := by simpa using hx
  rw [Complex.Gamma_eq_integral hre, Complex.GammaIntegral,
    abs_of_pos (Real.Gamma_pos_of_pos hx), Real.Gamma_eq_integral hx]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  have ht' : (0 : ℝ) < t := ht
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
    Complex.norm_cpow_eq_rpow_re_of_pos ht']
  simp

@[dlmf 5.6.E7]
theorem norm_Gamma_add_mul_I_ge {x y : ℝ} (hx : 1 / 2 ≤ x) :
    ‖Complex.Gamma (x + I * y)‖ ≥ Real.sqrt (1 / Real.cosh (π * y)) * Real.Gamma x := by
  -- `|Γ(x)/Γ(x+iy)|² = ∏ (1 + y²/(x+k)²) ≤ ∏ (1 + y²/(1/2+k)²) = cosh(πy)` (DLMF 5.8.3)
  have hx0 : 0 < x := by linarith
  have hnp : ∀ s : ℝ, 0 < s → ∀ k : ℕ, (s : ℂ) ≠ -k := fun s hs k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hz : ∀ s : ℝ, 0 < s → ∀ k : ℕ, (s : ℂ) + I * y ≠ -k := fun s hs k h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP := Gamma_div_Gamma_add_mul_I_sq (y := y) (hnp x hx0)
  have hP' := Gamma_div_Gamma_add_mul_I_sq (x := 1 / 2) (y := y) (hnp _ (by norm_num))
  have hle : ∏' k : ℕ, (1 + y ^ 2 / (x + k) ^ 2) ≤ ∏' k : ℕ, (1 + y ^ 2 / (1 / 2 + k) ^ 2) := by
    refine le_of_tendsto_of_tendsto'
      (multipliable_one_add_sq_div_add_sq x y).hasProd.tendsto_prod_nat
      (multipliable_one_add_sq_div_add_sq (1 / 2) y).hasProd.tendsto_prod_nat
      fun n => Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => ?_
    have hk : (1 / 2 : ℝ) + k ≤ x + k := by linarith
    gcongr
  -- the value at `x = 1/2`
  have hhalf : ∏' k : ℕ, (1 + y ^ 2 / (1 / 2 + k) ^ 2) = Real.cosh (π * y) := by
    rw [← hP', norm_div, Real.Gamma_one_half_eq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.mpr Real.pi_pos), div_pow, Real.sq_sqrt Real.pi_pos.le]
    have h := (Gamma_half_add_mul_I y).2
    push_cast at h ⊢
    rw [h]
    have := Real.cosh_pos (π * y)
    field_simp
  have hGx := Real.Gamma_pos_of_pos hx0
  have hn : 0 < ‖Complex.Gamma (x + I * y)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero (hz x hx0))
  have hineq : Real.Gamma x ^ 2 ≤ Real.cosh (π * y) * ‖Complex.Gamma (x + I * y)‖ ^ 2 := by
    have h := hP.trans_le (hle.trans_eq hhalf)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hGx, div_pow,
      div_le_iff₀ (by positivity)] at h
    exact h
  have hc := Real.cosh_pos (π * y)
  rw [ge_iff_le, ← Real.sqrt_sq hn.le, ← Real.sqrt_sq hGx.le, ← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hc]
  linarith

/-- A Gamma-ratio bound on the right half-plane for nonnegative real shifts
separated by at least one. These restrictions are essential in DLMF 5.6.8. -/
@[dlmf 5.6.E8]
theorem Gamma_ratio_norm_le {a b : ℝ} {z : ℂ} (hz : 0 < z.re)
    (ha : 0 ≤ a) (hba : 1 ≤ b - a) :
    ‖Complex.Gamma (z + a) / Complex.Gamma (z + b)‖ ≤ ‖z‖ ^ (-(b - a)) := by
  sorry

/-- A complex Gamma bound in the closed right half-plane, away from zero. -/
@[dlmf 5.6.E9]
theorem norm_Gamma_bound {z : ℂ} (hz : z ∈ slitPlane) (habs : 1 ≤ ‖z‖)
    (hre : 0 ≤ z.re) :
    ‖Complex.Gamma z‖ ≤
      Real.sqrt (2 * π) * ‖z‖ ^ (z.re - 1 / 2) * Real.exp (-π * |z.im| / 2) *
        Real.exp (1 / (6 * ‖z‖)) := by
  sorry

end AAR.Gamma
