/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.Continuation
public import DLMF.Legendre.Toroidal
public import ToMathlib.Analysis.SpecificLimits.Pincherle

/-!
# Tools for the Ferrers Fourier series (DLMF §14.13)

The hypergeometric form behind DLMF 14.13.1–14.13.2:
`s(πi/2) 𝖯^μ_ν(cos θ) + 𝖰^μ_ν(cos θ) = √π Γ(ν+μ+1) (2 sin θ)^μ e^{s(ν+μ+1)iθ}
𝐅(ν+μ+1, μ+1/2; ν+3/2; e^{2isθ})`, `s = ±1`, `0 < θ < π` (`legFS_PQ_hyp`), for all `ν, μ`
with `ν + μ ≠ -1, -2, …`. Route:

* the inverse Joukowski map `ζ(z) = z - √(z²-1)` on `ℂ ∖ (-∞, 1]` has `|ζ| < 1`, `ζ ∉ (-∞, 0]`
  (`legFS_norm_zeta_lt_one`, `legFS_zeta_mem_slitPlane`);
* the toroidal form DLMF 14.19.3 (`toroidalQ_hypergeometric`, `z = cosh ξ`, `ζ = e^{-ξ}`) extends
  by the identity theorem to `𝑸^μ_ν(z) = √π (1-ζ²)^μ ζ^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; ζ²)` on
  `ℂ ∖ (-∞, 1]` (`legFS_olverQ_eq_G`);
* at `z = cos θ ∓ i0`, `ζ → e^{±iθ}` (`legFS_zeta_lim`); the boundary values DLMF 14.23.2
  (`olverQ_boundary_aux`) then give the identity.

Also, for the continued fractions of DLMF §14.14:

* `legFS_tannery`: `Γ(c+k) 𝐅(a, b+k; c+k; z) → (1-z)^{-a}` as `k → ∞` for `|z| < 1`
  (dominated convergence termwise);
* `legFS_hasCF_of_terminating`, `legFS_hasCF_of_exists_zero`, `legFS_hasCF_of_ratio`: the value `a₀w₁/w₀` of the project's
  `HasContinuedFraction` from a backward solution `w`, in the terminating case and under a
  ratio limit `-w_k/(a_{k+1}w_{k+2}) → ρ`, `|ρ| > 1` (`GenContFract.pinch_cfConv_tendsto`).

All helper names carry the prefix `legFS_`.
-/

@[expose] public noncomputable section

open Complex Filter Set DLMF.Hypergeometric DLMF
open scoped Real Topology

namespace DLMF.Legendre

/-- The square root `√(z²-1)` continued from `z > 1` to `ℂ ∖ (-∞, 1]`. -/
def legFS_root (z : ℂ) : ℂ := exp ((log (z-1) + log (z+1))/2)

/-- The inverse Joukowski map `ζ = z - √(z²-1)`, so that `z = (ζ + ζ⁻¹)/2` and `|ζ| < 1`. -/
def legFS_zeta (z : ℂ) : ℂ := z - legFS_root z

/-- `z+1 ∈ slitPlane` when `z-1 ∈ slitPlane`. -/
lemma legFS_add_one {z : ℂ} (hz : z-1 ∈ slitPlane) : z+1 ∈ slitPlane := by
  simpa [add_comm] using one_add_mem_slitPlane_of_sub_one hz

/-- `(√(z²-1))² = z²-1`. -/
lemma legFS_root_sq {z : ℂ} (hz : z-1 ∈ slitPlane) : legFS_root z ^ 2 = z^2 - 1 := by
  rw [legFS_root, ← exp_nat_mul, show ((2:ℕ):ℂ) * ((log (z-1) + log (z+1))/2) =
    log (z-1) + log (z+1) by push_cast; ring, exp_add, exp_log (slitPlane_ne_zero hz),
    exp_log (slitPlane_ne_zero (legFS_add_one hz))]
  ring

/-- `ζ (z + √(z²-1)) = 1`, written as `ζ (2z - ζ) = 1`. -/
lemma legFS_zeta_mul {z : ℂ} (hz : z-1 ∈ slitPlane) : legFS_zeta z * (2*z - legFS_zeta z) = 1 := by
  have := legFS_root_sq hz
  rw [legFS_zeta]; linear_combination -this

/-- `ζ ≠ 0`. -/
lemma legFS_zeta_ne_zero {z : ℂ} (hz : z-1 ∈ slitPlane) : legFS_zeta z ≠ 0 := by
  intro h; have := legFS_zeta_mul hz; rw [h, zero_mul] at this; exact zero_ne_one this

/-- `2z = ζ + ζ⁻¹`. -/
lemma legFS_two_mul_eq {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*z = legFS_zeta z + (legFS_zeta z)⁻¹ := by
  have h0 := legFS_zeta_ne_zero hz
  have := legFS_zeta_mul hz
  field_simp
  linear_combination this

/-- A point of `ℂ ∖ (-∞, 1]` is not a real number `≤ 1`. -/
lemma legFS_not_real_le_one {z : ℂ} (hz : z-1 ∈ slitPlane) {r : ℝ} (hr : r ≤ 1) : z ≠ r := by
  rintro rfl
  rw [mem_slitPlane_iff] at hz
  simp at hz; linarith

/-- `|ζ| ≠ 1` off `(-∞, 1]`: otherwise `z = Re ζ ∈ [-1, 1]`. -/
lemma legFS_norm_zeta_ne_one {z : ℂ} (hz : z-1 ∈ slitPlane) : ‖legFS_zeta z‖ ≠ 1 := by
  intro h1
  set w := legFS_zeta z
  have h0 : w ≠ 0 := legFS_zeta_ne_zero hz
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    rw [inv_def, normSq_eq_norm_sq, h1]; simp
  have h2 := legFS_two_mul_eq hz
  rw [hinv, add_conj] at h2
  have hz' : z = ((w.re:ℝ):ℂ) := by
    push_cast at h2; linear_combination h2/2
  refine legFS_not_real_le_one hz (r := w.re) ?_ hz'
  have := re_le_norm w; linarith

/-- For real `t > 1`, `ζ(t) = t - √(t²-1)`. -/
lemma legFS_zeta_real {t : ℝ} (ht : 1 < t) : legFS_zeta t = ((t - Real.sqrt (t^2-1) : ℝ) : ℂ) := by
  have hl : log ((t:ℂ)-1) + log ((t:ℂ)+1) = ((Real.log (t^2-1) : ℝ) : ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith)]
    congr 2; ring
  rw [legFS_zeta, legFS_root, hl, show ((Real.log (t^2-1) : ℝ) : ℂ)/2 = ((Real.log (t^2-1)/2 : ℝ) : ℂ)
    by push_cast; ring, ← ofReal_exp, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by nlinarith)]
  push_cast; ring_nf

/-- `ζ` is analytic on `ℂ ∖ (-∞, 1]`. -/
lemma legFS_zeta_analyticAt {z : ℂ} (hz : z-1 ∈ slitPlane) : AnalyticAt ℂ legFS_zeta z := by
  have h1 : AnalyticAt ℂ (fun w : ℂ => log (w-1)) z :=
    (analyticAt_clog hz).comp_of_eq (f := fun w : ℂ => w - 1) (by fun_prop) rfl
  have h2 : AnalyticAt ℂ (fun w : ℂ => log (w+1)) z :=
    (analyticAt_clog (legFS_add_one hz)).comp_of_eq (f := fun w : ℂ => w + 1) (by fun_prop) rfl
  exact analyticAt_id.sub ((h1.add h2).div_const.cexp)

/-- `0 < t - √(t²-1) < 1` for `t > 1`. -/
lemma legFS_real_bounds {t : ℝ} (ht : 1 < t) :
    0 < t - Real.sqrt (t^2-1) ∧ t - Real.sqrt (t^2-1) < 1 := by
  have h0 : 0 ≤ t^2 - 1 := by nlinarith
  have hs := Real.sq_sqrt h0
  have hs0 := Real.sqrt_nonneg (t^2-1)
  constructor
  · nlinarith
  · have : 0 < Real.sqrt (t^2-1) := Real.sqrt_pos.mpr (by nlinarith)
    nlinarith

/-- `|ζ| < 1` on `ℂ ∖ (-∞, 1]` (connectedness and `|ζ| ≠ 1`). -/
lemma legFS_norm_zeta_lt_one {z : ℂ} (hz : z-1 ∈ slitPlane) : ‖legFS_zeta z‖ < 1 := by
  by_contra h
  push Not at h
  set D : Set ℂ := {w : ℂ | w-1 ∈ slitPlane}
  have h2 : ((2:ℝ):ℂ) ∈ D := by show ((2:ℝ):ℂ) - 1 ∈ slitPlane; norm_num
  have hc : ContinuousOn (fun w => ‖legFS_zeta w‖) D := fun w hw =>
    (legFS_zeta_analyticAt hw).continuousAt.norm.continuousWithinAt
  have hlt : ‖legFS_zeta ((2:ℝ):ℂ)‖ < 1 := by
    obtain ⟨hp, hl⟩ := legFS_real_bounds (show (1:ℝ) < 2 by norm_num)
    rw [legFS_zeta_real (by norm_num), norm_real, Real.norm_eq_abs, abs_of_pos hp]
    exact hl
  obtain ⟨w, hw, hw1⟩ := isPreconnected_sub_one_mem_slitPlane.intermediate_value h2 hz hc
    ⟨hlt.le, h⟩
  exact legFS_norm_zeta_ne_one hw hw1

/-- `ζ ∉ (-∞, 0]` on `ℂ ∖ (-∞, 1]`. -/
lemma legFS_zeta_mem_slitPlane {z : ℂ} (hz : z-1 ∈ slitPlane) : legFS_zeta z ∈ slitPlane := by
  rw [mem_slitPlane_iff]
  by_contra h
  push Not at h
  obtain ⟨hre, him⟩ := h
  set w := legFS_zeta z
  have h0 : w ≠ 0 := legFS_zeta_ne_zero hz
  have hw : w = ((w.re:ℝ):ℂ) := by apply Complex.ext <;> simp [him]
  have hre' : w.re < 0 := lt_of_le_of_ne hre (fun h => h0 (by rw [hw, h]; simp))
  have h2 : 2*z = w + w⁻¹ := legFS_two_mul_eq hz
  have hz' : z = (((w.re + (w.re)⁻¹)/2 : ℝ) : ℂ) := by
    rw [hw] at h2
    push_cast at h2 ⊢; linear_combination h2/2
  refine legFS_not_real_le_one hz ?_ hz'
  have : (w.re)⁻¹ < 0 := inv_lt_zero.mpr hre'
  linarith


/-- The right side of the `ζ`-form of `𝑸^μ_ν`:
`√π (1-w²)^μ w^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; w²)`. -/
def legFS_G (ν μ w : ℂ) : ℂ :=
  Real.sqrt π * (1 - w^2)^μ * w^(ν+1) * regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (w^2)

/-- `legFS_G ν μ` is analytic at `w` when `w ∉ (-∞, 0]` and `1 - w² ∉ (-∞, 0]`. -/
lemma legFS_G_analyticAt (ν μ : ℂ) {w : ℂ} (hw : w ∈ slitPlane) (hw2 : 1 - w^2 ∈ slitPlane) :
    AnalyticAt ℂ (legFS_G ν μ) w := by
  have hF : AnalyticAt ℂ (fun w : ℂ => regularizedGaussHG (μ+1/2) (ν+μ+1) (ν+3/2) (w^2)) w :=
    (analyticAt_regularizedGaussHG _ _ _ (show w^2 ∈ cutPlane from hw2)).comp_of_eq
      (f := fun w : ℂ => w^2) (by fun_prop) rfl
  have h1 : AnalyticAt ℂ (fun w : ℂ => (1 - w^2)^μ) w :=
    (analyticAt_const.sub (analyticAt_id.pow 2)).cpow analyticAt_const hw2
  have h2 : AnalyticAt ℂ (fun w : ℂ => w^(ν+1)) w := analyticAt_id.cpow analyticAt_const hw
  exact ((analyticAt_const.mul h1).mul h2).mul hF

/-- `1 - w² ∈ slitPlane` for `|w| < 1`. -/
lemma legFS_one_sub_sq_mem {w : ℂ} (hw : ‖w‖ < 1) : 1 - w^2 ∈ slitPlane := by
  rw [mem_slitPlane_iff]; left
  have : (w^2).re ≤ ‖w‖^2 := by rw [← norm_pow]; exact re_le_norm _
  simp only [sub_re, one_re]
  nlinarith [norm_nonneg w]

/-- The `ζ`-form of `𝑸^μ_ν` (the complex continuation of DLMF 14.19.3):
`𝑸^μ_ν(z) = √π (1-ζ²)^μ ζ^{ν+1} 𝐅(μ+1/2, ν+μ+1; ν+3/2; ζ²)`, `ζ = z - √(z²-1)`, on `ℂ ∖ (-∞, 1]`. -/
theorem legFS_olverQ_eq_G (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν μ z = legFS_G ν μ (legFS_zeta z) := by
  set D : Set ℂ := {w : ℂ | w-1 ∈ slitPlane}
  have hg : AnalyticOnNhd ℂ (fun w => legFS_G ν μ (legFS_zeta w)) D := fun w hw =>
    (legFS_G_analyticAt ν μ (legFS_zeta_mem_slitPlane hw)
      (legFS_one_sub_sq_mem (legFS_norm_zeta_lt_one hw))).comp (legFS_zeta_analyticAt hw)
  have h2 : ((2 : ℝ) : ℂ) ∈ D := by show ((2 : ℝ) : ℂ) - 1 ∈ slitPlane; norm_num
  refine (olverQ_analytic ν μ).eqOn_of_preconnected_of_frequently_eq hg
    isPreconnected_sub_one_mem_slitPlane h2 ?_ hz
  have ht : Tendsto (fun r : ℝ => (r : ℂ)) (𝓝[≠] (2 : ℝ)) (𝓝[≠] ((2 : ℝ) : ℂ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · exact (continuous_ofReal.tendsto _).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_inj] using hr
  apply ht.frequently
  apply Eventually.frequently
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (show (1 : ℝ) < 2 by norm_num))] with t ht
  have ht1 : (1:ℝ) < t := ht
  set ξ := Real.arcosh t with hξ
  have hξ0 : 0 < ξ := Real.arcosh_pos ht1
  have hc : Real.cosh ξ = t := Real.cosh_arcosh ht1.le
  have hζ : legFS_zeta t = ((Real.exp (-ξ) : ℝ) : ℂ) := by
    rw [legFS_zeta_real ht1, Real.exp_neg, hξ, Real.exp_arcosh ht1.le,
      Real.add_sqrt_self_sq_sub_one_inv ht1.le]
  have key := toroidalQ_hypergeometric (ν+1/2) μ hξ0
  rw [hc, show ν+1/2-1/2 = ν by ring] at key
  show olverQ ν μ t = legFS_G ν μ (legFS_zeta t)
  rw [key, hζ, legFS_G]
  have he2 : ((Real.exp (-ξ) : ℝ) : ℂ)^2 = ((Real.exp (-2*ξ) : ℝ) : ℂ) := by
    rw [← ofReal_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
  have hpow : ((Real.exp (-ξ) : ℝ) : ℂ)^(ν+1) = (exp ((ν+1/2+1/2)*ξ))⁻¹ := by
    rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (Real.exp_pos _).ne'), ← ofReal_log (Real.exp_pos _).le,
      Real.log_exp, ← exp_neg]
    congr 1; push_cast; ring
  rw [he2, hpow, show ν+1/2+μ+1/2 = ν+μ+1 by ring, show ν+1/2+1 = ν+3/2 by ring]
  ring


/-- One-sided limit of `log(z-1)` at a point of `(-1, 1)` approached from the side `σ`. -/
lemma legFS_log_sub_one_lim {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {x : ℝ} (hx : x < 1) :
    Tendsto (fun ε : ℝ => log ((x:ℂ) + (σ:ℂ)*I*ε - 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1-x) : ℂ) + σ*π*I)) := by
  have hpath : Tendsto (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε - 1) (𝓝[>] (0:ℝ)) (𝓝 ((x - 1 : ℝ) : ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε - 1) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hre : ((x - 1 : ℝ) : ℂ).re < 0 := by simp; linarith
  have him : ((x - 1 : ℝ) : ℂ).im = 0 := by simp
  have hnorm : Real.log ‖((x - 1 : ℝ) : ℂ)‖ = Real.log (1-x) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]; ring_nf
  have himε : ∀ ε : ℝ, ((x:ℂ) + (σ:ℂ)*I*ε - 1).im = σ*ε := by intro ε; simp
  rcases hσ with rfl | rfl
  · have hc := continuousWithinAt_log_of_re_neg_of_im_zero hre him
    have hp' : Tendsto (fun ε : ℝ => (x:ℂ) + ((1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | 0 ≤ z.im}] ((x - 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpath, by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show 0 ≤ _; rw [himε]; simp only [one_mul]; exact le_of_lt hε⟩
    have h := hc.tendsto.comp hp'
    have e : (Real.log (1-x) : ℂ) + ((1:ℝ):ℂ)*π*I = log ((x - 1 : ℝ) : ℂ) := by
      rw [log, hnorm, arg_ofReal_of_neg (by linarith)]; push_cast; ring
    rw [e]; exact h
  · have hc := tendsto_log_nhdsWithin_im_neg_of_re_neg_of_im_zero hre him
    have hp' : Tendsto (fun ε : ℝ => (x:ℂ) + ((-1:ℝ):ℂ)*I*ε - 1) (𝓝[>] (0:ℝ))
        (𝓝[{z : ℂ | z.im < 0}] ((x - 1 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpath, by
        filter_upwards [self_mem_nhdsWithin] with ε hε
        show _ < 0; rw [himε]; have : (0:ℝ) < ε := hε; linarith⟩
    have h := hc.comp hp'
    rw [hnorm] at h
    have e : (Real.log (1-x) : ℂ) + ((-1:ℝ):ℂ)*π*I = (Real.log (1-x) : ℂ) - π*I := by push_cast; ring
    rw [e]; exact h


/-- One-sided boundary values of `ζ = z - √(z²-1)` on `(-1, 1)`: from the side `σ`,
`ζ(cos θ + σ i 0) = cos θ - σ i sin θ`. -/
lemma legFS_zeta_lim {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun ε : ℝ => legFS_zeta ((Real.cos θ:ℂ) + (σ:ℂ)*I*ε)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.cos θ:ℂ) - (σ:ℂ)*I*(Real.sin θ:ℂ))) := by
  set x := Real.cos θ with hxdef
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx1 : x < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le h0; rw [Real.cos_zero] at this
    exact this
  have hx2 : -1 < x := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ; rw [Real.cos_pi] at this
    exact this
  have hpath : Tendsto (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε) (𝓝[>] (0:ℝ)) (𝓝 (x : ℂ)) := by
    have : Continuous (fun ε : ℝ => (x:ℂ) + (σ:ℂ)*I*ε) := by fun_prop
    simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
  have hL1 := legFS_log_sub_one_lim hσ hx1
  have hL2 : Tendsto (fun ε : ℝ => log ((x:ℂ) + (σ:ℂ)*I*ε + 1)) (𝓝[>] (0:ℝ))
      (𝓝 ((Real.log (1+x) : ℂ))) := by
    have hm : ((x:ℂ) + 1) ∈ slitPlane := Or.inl (by simp; linarith)
    have hc := (continuousAt_clog hm).tendsto.comp (hpath.add_const 1)
    rw [show ((x:ℂ) + 1) = ((1 + x : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by linarith)] at hc
    exact hc
  have hR := ((hL1.add hL2).div_const 2).cexp
  have hlim : exp (((Real.log (1-x) : ℂ) + σ*π*I + (Real.log (1+x) : ℂ))/2) =
      (σ:ℂ)*I*(Real.sin θ:ℂ) := by
    have hsq : Real.sin θ = Real.sqrt (1 - x^2) := by
      rw [hxdef, Real.sin_eq_sqrt_one_sub_cos_sq h0.le hπ.le]
    have hl : (Real.log (1-x) : ℂ) + (Real.log (1+x) : ℂ) = ((Real.log (1 - x^2) : ℝ) : ℂ) := by
      rw [← ofReal_add, ← Real.log_mul (by linarith) (by linarith)]; congr 2; ring
    rw [show ((Real.log (1-x) : ℂ) + σ*π*I + (Real.log (1+x) : ℂ))/2 =
      ((Real.log (1-x) : ℂ) + (Real.log (1+x) : ℂ))/2 + σ*π/2*I by ring, hl, exp_add,
      show ((Real.log (1 - x^2) : ℝ) : ℂ)/2 = ((Real.log (1 - x^2)/2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_exp, hsq, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by nlinarith)]
    rw [show Real.log (1 - x^2) * (1/2) = Real.log (1 - x^2)/2 by ring]
    rcases hσ with rfl | rfl
    · push_cast; rw [show (1:ℂ)*π/2*I = (π/2:ℂ)*I by ring, exp_mul_I, cos_pi_div_two, sin_pi_div_two]
      ring
    · push_cast; rw [show (-1:ℂ)*π/2*I = (-(π/2):ℂ)*I by ring, exp_mul_I, cos_neg, sin_neg,
        cos_pi_div_two, sin_pi_div_two]
      ring
  rw [hlim] at hR
  have := hpath.sub hR
  refine this.congr' (Eventually.of_forall fun ε => ?_)
  simp only [legFS_zeta, legFS_root]



/-- `cos θ + s i sin θ = e^{isθ}` for `s = ±1`. -/
lemma legFS_side_exp {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    (Real.cos θ:ℂ) - ((-s:ℝ):ℂ)*I*(Real.sin θ:ℂ) = exp ((s:ℂ)*θ*I) := by
  rcases hs with rfl | rfl
  · rw [show ((1:ℝ):ℂ)*θ*I = (θ:ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    push_cast; ring
  · rw [show ((-1:ℝ):ℂ)*θ*I = (-(θ:ℂ))*I by push_cast; ring, exp_mul_I, cos_neg, sin_neg,
      ← ofReal_cos, ← ofReal_sin]
    push_cast; ring

/-- `1 - e^{2isθ} = 2 sin θ · e^{is(θ - π/2)}` for `s = ±1`. -/
lemma legFS_one_sub_exp_sq {s : ℝ} (hs : s = 1 ∨ s = -1) (θ : ℝ) :
    1 - exp ((s:ℂ)*θ*I)^2 = ((2*Real.sin θ : ℝ) : ℂ) * exp (((s*(θ - π/2) : ℝ) : ℂ)*I) := by
  have hu : exp ((θ:ℂ)*I) ≠ 0 := exp_ne_zero _
  have hsin : Complex.sin (θ:ℂ) = (exp (-(θ:ℂ)*I) - exp ((θ:ℂ)*I))*I/2 := by
    rw [Complex.sin]
  have hneg : exp (-(θ:ℂ)*I) = (exp ((θ:ℂ)*I))⁻¹ := by rw [neg_mul, exp_neg]
  have hpi : exp ((π/2:ℂ)*I) = I := by rw [exp_mul_I, cos_pi_div_two, sin_pi_div_two]; ring
  have hpi' : exp (-(π/2:ℂ)*I) = -I := by
    rw [neg_mul, exp_neg, hpi, inv_I]
  rcases hs with rfl | rfl
  · rw [show (((1:ℝ)*(θ - π/2) : ℝ) : ℂ)*I = (θ:ℂ)*I + (-(π/2:ℂ)*I) by push_cast; ring, exp_add,
      hpi', show ((1:ℝ):ℂ)*θ*I = (θ:ℂ)*I by push_cast; ring]
    push_cast; rw [hsin, hneg]; field_simp; ring_nf; rw [I_sq]; ring
  · rw [show (((-1:ℝ)*(θ - π/2) : ℝ) : ℂ)*I = -(θ:ℂ)*I + ((π/2:ℂ)*I) by push_cast; ring, exp_add,
      hpi, show ((-1:ℝ):ℂ)*θ*I = -(θ:ℂ)*I by push_cast; ring]
    push_cast; rw [hsin, hneg]; field_simp; ring_nf; rw [I_sq]; ring



/-- DLMF 14.13 (unnumbered) for real side `s = ±1`:
`s(πi/2) 𝖯^μ_ν(cos θ) + 𝖰^μ_ν(cos θ) = √π Γ(ν+μ+1) (2 sin θ)^μ e^{s(ν+μ+1)iθ} 𝐅(ν+μ+1, μ+1/2; ν+3/2; e^{2isθ})`. -/
theorem legFS_PQ_hyp (ν μ : ℂ) (hr : LegendreQRegular ν μ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π)
    {s : ℝ} (hs : s = 1 ∨ s = -1) :
    (s:ℂ)*π*I/2*ferrersP ν μ (Real.cos θ) + ferrersQ ν μ (Real.cos θ) =
      Real.sqrt π*Gamma (ν+μ+1)*(2*Real.sin θ:ℂ)^μ*exp ((s:ℂ)*(ν+μ+1)*I*θ)*
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp ((s:ℂ)*2*I*θ)) := by
  have hσ : -s = 1 ∨ -s = -1 := by rcases hs with rfl | rfl <;> norm_num
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    refine ⟨?_, ?_⟩
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ; rwa [Real.cos_pi] at this
    · have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hπ.le h0; rwa [Real.cos_zero] at this
  set w₀ := exp ((s:ℂ)*θ*I) with hw₀
  have hθs : -π < s*θ ∧ s*θ < π := by
    rcases hs with rfl | rfl <;> constructor <;> linarith
  have hw0 : w₀ ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    rw [hw₀, show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_cos,
      ← ofReal_sin]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one, zero_add]
    rcases hs with rfl | rfl
    · simpa using hsin.ne'
    · simpa using hsin.ne'
  have hφ : -(π/2) < s*(θ - π/2) ∧ s*(θ - π/2) < π/2 := by
    rcases hs with rfl | rfl <;> constructor <;> linarith
  have hsq : 1 - w₀^2 = ((2*Real.sin θ : ℝ) : ℂ) * exp (((s*(θ - π/2) : ℝ) : ℂ)*I) :=
    legFS_one_sub_exp_sq hs θ
  have hw2 : 1 - w₀^2 ∈ slitPlane := by
    rw [hsq, mem_slitPlane_iff]; left
    rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]
    simp only [mul_re, ofReal_re, ofReal_im, add_re, I_re, I_im, zero_mul, mul_zero,
      sub_zero, add_zero, mul_one]
    have := Real.cos_pos_of_mem_Ioo ⟨hφ.1, hφ.2⟩
    simp; positivity
  -- the boundary value of `𝑸^μ_ν` from the side `-s`
  have hlimQ := olverQ_boundary_aux ν μ hr (-s) hσ hx
  have hζ := legFS_zeta_lim hσ h0 hπ
  rw [legFS_side_exp hs] at hζ
  have hG := (legFS_G_analyticAt ν μ hw0 hw2).continuousAt.tendsto.comp hζ
  have heq : (fun ε : ℝ => olverQ ν μ ((Real.cos θ:ℂ) + ((-s:ℝ):ℂ)*I*ε)) =ᶠ[𝓝[>] (0:ℝ)]
      (legFS_G ν μ ∘ fun ε : ℝ => legFS_zeta ((Real.cos θ:ℂ) + ((-s:ℝ):ℂ)*I*ε)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : (0:ℝ) < ε := hε
    refine legFS_olverQ_eq_G ν μ ?_
    rw [mem_slitPlane_iff]; right
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, mul_zero, I_im, mul_one,
      zero_add, one_im, sub_zero, ofReal_neg, neg_re, neg_im, add_zero, neg_zero]
    rcases hs with rfl | rfl <;> simp <;> exact hε'.ne'
  have huniq := tendsto_nhds_unique hlimQ (hG.congr' heq.symm)
  have hΓ : Gamma (ν+μ+1) ≠ 0 := Gamma_ne_zero (fun n he => hr n (by linear_combination he))
  have hE : exp (((-s:ℝ):ℂ)*μ*π*I/2) * exp ((s:ℂ)*μ*π*I/2) = 1 := by
    rw [← exp_add, show ((-s:ℝ):ℂ)*μ*π*I/2 + (s:ℂ)*μ*π*I/2 = 0 by push_cast; ring, exp_zero]
  have key : (s:ℂ)*π*I/2*ferrersP ν μ (Real.cos θ) + ferrersQ ν μ (Real.cos θ) =
      Gamma (ν+μ+1) * exp ((s:ℂ)*μ*π*I/2) * legFS_G ν μ w₀ := by
    rw [← huniq]
    have e : ∀ A B C D X : ℂ, C * B * (A / D * X) = (A*B) * (C/D) * X := by intros; ring
    rw [e, hE, div_self hΓ]; push_cast; ring
  have hr0 : (0:ℝ) < 2*Real.sin θ := by positivity
  have hpow1 : (1 - w₀^2)^μ = (2*Real.sin θ:ℂ)^μ * exp ((((s*(θ - π/2) : ℝ) : ℂ)*I)*μ) := by
    rw [hsq, cpow_def_of_ne_zero (mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') (exp_ne_zero _)),
      log_ofReal_mul hr0 (exp_ne_zero _), log_exp (by simp; linarith [hφ.1, Real.pi_pos])
        (by simp; linarith [hφ.2, Real.pi_pos]),
      show (2*Real.sin θ:ℂ) = ((2*Real.sin θ : ℝ) : ℂ) by push_cast; ring,
      cpow_def_of_ne_zero (ofReal_ne_zero.mpr hr0.ne'), ← ofReal_log hr0.le, ← exp_add]
    congr 1; ring
  have hpow2 : w₀^(ν+1) = exp ((s:ℂ)*θ*I*(ν+1)) := by
    rw [hw₀, cpow_def_of_ne_zero (exp_ne_zero _), log_exp]
    · rw [show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring]; simp; linarith [hθs.1]
    · rw [show (s:ℂ)*θ*I = ((s*θ:ℝ):ℂ)*I by push_cast; ring]; simp; linarith [hθs.2]
  have hsq2 : w₀^2 = exp ((s:ℂ)*2*I*θ) := by
    rw [hw₀, ← exp_nat_mul]; congr 1; push_cast; ring
  rw [key, legFS_G, hpow1, hpow2, regularizedGaussHG_symm _ _ _ (show w₀^2 ∈ cutPlane from hw2),
    hsq2]
  have hx : exp ((s:ℂ)*μ*π*I/2) * exp ((((s*(θ - π/2) : ℝ) : ℂ)*I)*μ) * exp ((s:ℂ)*θ*I*(ν+1)) =
      exp ((s:ℂ)*(ν+μ+1)*I*θ) := by
    rw [← exp_add, ← exp_add]; congr 1; push_cast; ring
  linear_combination (Gamma (ν+μ+1) * Real.sqrt π * (2*Real.sin θ:ℂ)^μ *
    regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp ((s:ℂ)*2*I*θ))) * hx


/-! ### A Tannery limit for `𝐅(a, b+k; c+k; z)` -/

/-- `‖(a)_n‖ ≤ (‖a‖)_n`. -/
lemma legFS_norm_poch_le (a : ℂ) (n : ℕ) : ‖poch a n‖ ≤ ‖poch (‖a‖:ℂ) n‖ := by
  induction n with
  | zero => simp [poch]
  | succ n ih =>
    simp only [poch, ascPochhammer_succ_eval, norm_mul] at ih ⊢
    refine mul_le_mul ih ?_ (norm_nonneg _) (norm_nonneg _)
    rw [show ((‖a‖:ℂ) + n) = ((‖a‖ + n : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    exact (norm_add_le _ _).trans (by simp)

/-- The ratio `(b+k)_n Γ(c+k)/Γ(c+k+n)` appearing in `Γ(c+k) 𝐅(a, b+k; c+k; z)`. -/
def legFS_q (b c : ℂ) (k n : ℕ) : ℂ := poch (b+k) n * Gamma (c+k) / Gamma (c+k+n)

/-- For `Re (c+k) > 0`, the recursion `q_{n+1} = q_n (b+k+n)/(c+k+n)`. -/
lemma legFS_q_succ (b c : ℂ) {k : ℕ} (hk : 0 < (c+k).re) (n : ℕ) :
    legFS_q b c k (n+1) = legFS_q b c k n * ((b+k+n)/(c+k+n)) := by
  have hre : 0 < (c+k+n).re := by simp at hk ⊢; positivity
  have h1 : c+k+n ≠ 0 := fun h => by rw [h] at hre; simp at hre
  have hG : Gamma (c+k+n) ≠ 0 := Gamma_ne_zero_of_re_pos hre
  have e : Gamma (c+k+((n+1:ℕ):ℂ)) = (c+k+n) * Gamma (c+k+n) := by
    rw [show c+k+((n+1:ℕ):ℂ) = (c+k+n)+1 by push_cast; ring, Gamma_add_one _ h1]
  simp only [legFS_q, poch, ascPochhammer_succ_eval, e]
  field_simp

/-- For `Re (c+k) > 0`, `q_0 = 1`. -/
lemma legFS_q_zero (b c : ℂ) {k : ℕ} (hk : 0 < (c+k).re) : legFS_q b c k 0 = 1 := by
  simp [legFS_q, poch, Gamma_ne_zero_of_re_pos hk]

/-- `(k+β)/(k+γ) → 1`. -/
lemma legFS_ratio_tendsto (β γ : ℂ) :
    Tendsto (fun k : ℕ => ((k:ℂ)+β)/((k:ℂ)+γ)) atTop (𝓝 1) := by
  have h0 : Tendsto (fun k : ℕ => ((k:ℂ))⁻¹) atTop (𝓝 0) := 
    tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℂ)
  have h : Tendsto (fun k : ℕ => (1 + β*(k:ℂ)⁻¹)/(1 + γ*(k:ℂ)⁻¹)) atTop (𝓝 ((1 + β*0)/(1+γ*0))) :=
    ((tendsto_const_nhds.add (h0.const_mul β)).div (tendsto_const_nhds.add (h0.const_mul γ))
      (by simp))
  simp only [mul_zero, add_zero, div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with k hk
  have : (k:ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

/-- Per-term limit: `q_k(n) → 1` as `k → ∞`. -/
lemma legFS_q_tendsto (b c : ℂ) (n : ℕ) : Tendsto (fun k => legFS_q b c k n) atTop (𝓝 1) := by
  have hev : ∀ᶠ k : ℕ in atTop, 0 < (c+k).re := by
    obtain ⟨K, hK⟩ := exists_nat_gt (-c.re)
    filter_upwards [eventually_ge_atTop K] with k hk
    have : (K:ℝ) ≤ k := by exact_mod_cast hk
    simp; linarith
  induction n with
  | zero =>
    exact tendsto_const_nhds.congr' (by filter_upwards [hev] with k hk; rw [legFS_q_zero b c hk])
  | succ n ih =>
    have hr : Tendsto (fun k : ℕ => (b+k+n)/(c+k+n)) atTop (𝓝 1) :=
      (legFS_ratio_tendsto (b+n) (c+n)).congr fun k => by ring_nf
    have := ih.mul hr
    rw [one_mul] at this
    exact this.congr' (by filter_upwards [hev] with k hk; rw [legFS_q_succ b c hk])

/-- Uniform bound: `‖q_k(n)‖ ≤ (1+ε)^n` for `k` large. -/
lemma legFS_q_bound (b c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ k : ℕ in atTop, ∀ n, ‖legFS_q b c k n‖ ≤ (1+ε)^n := by
  obtain ⟨K, hK⟩ := exists_nat_gt (‖b-c‖/ε - c.re + 1)
  filter_upwards [eventually_ge_atTop K] with k hk n
  have hkK : (K:ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (c+k).re := by
    simp; have := div_nonneg (norm_nonneg (b-c)) hε.le; linarith
  induction n with
  | zero => rw [legFS_q_zero b c hpos]; simp
  | succ n ih =>
    rw [legFS_q_succ b c hpos, norm_mul, pow_succ]
    refine mul_le_mul ih ?_ (norm_nonneg _) (by positivity)
    have hre : ‖b-c‖/ε < (c+k+n).re := by
      simp; have : (0:ℝ) ≤ n := n.cast_nonneg; linarith
    have hn0 : 0 < ‖c+k+n‖ := lt_of_lt_of_le (lt_of_le_of_lt (by positivity) hre) (re_le_norm _)
    rw [show b+k+n = (c+k+n) + (b-c) by ring, add_div, div_self (norm_pos_iff.mp hn0),
      ]
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_div]
    gcongr
    rw [div_le_iff₀ hn0]
    have := (div_lt_iff₀ hε).mp hre
    nlinarith [re_le_norm (c+k+n)]

/-- **Tannery limit.** For `‖z‖ < 1`, `Γ(c+k) 𝐅(a, b+k; c+k; z) → (1-z)^{-a}` as `k → ∞`. -/
theorem legFS_tannery (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun k : ℕ => Gamma (c+k) * regularizedGaussHGFun a (b+k) (c+k) z) atTop
      (𝓝 ((1-z)^(-a))) := by
  set ε : ℝ := (1 - ‖z‖)/2
  have hε : 0 < ε := by simp only [ε]; linarith
  set r : ℝ := (1+ε)*‖z‖
  have hr0 : 0 ≤ r := by positivity
  have hr1 : ‖(r:ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0]
    simp only [r, ε]; nlinarith [norm_nonneg z]
  have hS := (hasSum_one_sub_cpow_neg (‖a‖:ℂ) hr1).summable.norm
  have hlim := hasSum_one_sub_cpow_neg a hz
  rw [← hlim.tsum_eq]
  have key : ∀ k : ℕ, Gamma (c+k) * regularizedGaussHGFun a (b+k) (c+k) z =
      ∑' n : ℕ, poch a n / n.factorial * z^n * legFS_q b c k n := by
    intro k
    rw [regularizedGaussHGFun_eq_tsum, ← tsum_mul_left]
    congr 1; funext n
    simp only [legFS_q, poch]; ring
  simp only [key]
  refine tendsto_tsum_of_dominated_convergence hS (fun n => ?_) ?_
  · have := (legFS_q_tendsto b c n).const_mul (poch a n / n.factorial * z^n)
    rwa [mul_one] at this
  · filter_upwards [legFS_q_bound b c hε] with k hk n
    rw [norm_mul, norm_mul, norm_mul, norm_div, norm_div, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hr0, show r^n = (1+ε)^n * ‖z‖^n from mul_pow _ _ _]
    have h1 := legFS_norm_poch_le a n
    have h2 := hk n
    have : 0 ≤ ‖z‖^n := by positivity
    have : 0 ≤ ‖((n.factorial : ℕ) : ℂ)‖ := norm_nonneg _
    calc ‖poch a n‖ / ‖((n.factorial : ℕ) : ℂ)‖ * ‖z‖^n * ‖legFS_q b c k n‖
        ≤ ‖poch (‖a‖:ℂ) n‖ / ‖((n.factorial : ℕ) : ℂ)‖ * ‖z‖^n * (1+ε)^n := by gcongr
      _ = _ := by ring

/-! ### Terminating and Pincherle-type continued fractions -/

/-- Up to the first vanishing partial numerator `a_K`, the project's continuants are Mathlib's. -/
lemma legFS_cfContinuants_eq {a b : ℕ → ℂ} {K : ℕ} (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0)
    (n : ℕ) (hn : n ≤ K) :
    DLMF.cfContinuants a b 0 n =
      ((GenContFract.cfConv_ofFun 0 a b).nums n, (GenContFract.cfConv_ofFun 0 a b).dens n, false) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.cfContinuants]; rfl
    · simp [DLMF.cfContinuants, GenContFract.cfConv_nums_one, GenContFract.cfConv_dens_one]
    · have h1 := ih (n + 1) (by omega) (by omega)
      have h0 := ih n (by omega) (by omega)
      have han : a (n + 1) ≠ 0 := ha (n + 1) (by omega) (by omega)
      rw [DLMF.cfContinuants, h1, h0, GenContFract.cfConv_nums_step, GenContFract.cfConv_dens_step]
      simp [han, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen]

/-- After the first vanishing partial numerator `a_K` (`K ≥ 1`) the project's finite continued
fraction freezes at the `K`-th Mathlib convergent. -/
lemma legFS_cfTail_freeze {a b : ℕ → ℂ} {K : ℕ} (hK : 1 ≤ K)
    (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0) (haK : a K = 0) {N : ℕ} (hN : K ≤ N) :
    DLMF.cfTail a b 0 N = (GenContFract.cfConv_ofFun 0 a b).convs K := by
  have hfr : ∀ j, DLMF.cfContinuants a b 0 (K + 1 + j) =
      ((GenContFract.cfConv_ofFun 0 a b).nums K, (GenContFract.cfConv_ofFun 0 a b).dens K, true) := by
    intro j
    induction j with
    | zero =>
      obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
      rw [show m + 1 + 1 + 0 = m + 2 by ring, DLMF.cfContinuants,
        legFS_cfContinuants_eq ha (m + 1) le_rfl]
      simp [haK]
    | succ j ih =>
      rw [show K + 1 + (j + 1) = (K + j) + 2 by ring, DLMF.cfContinuants,
        show K + j + 1 = K + 1 + j by ring, ih]
      simp
  rcases hN.eq_or_lt with rfl | hlt
  · simp only [DLMF.cfTail, legFS_cfContinuants_eq ha K le_rfl]; rfl
  · obtain ⟨j, rfl⟩ : ∃ j, N = K + 1 + j := ⟨N - K - 1, by omega⟩
    simp only [DLMF.cfTail, hfr]; rfl

/-- A terminating continued fraction (first vanishing numerator `a_K`, `K ≥ 1`) with a backward
solution `w`, `w₀ ≠ 0`, has the value `a₀ w₁/w₀`. -/
lemma legFS_hasCF_of_terminating {a b w : ℕ → ℂ} {K : ℕ} (hK : 1 ≤ K)
    (ha : ∀ k, 1 ≤ k → k < K → a k ≠ 0) (haK : a K = 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 1 := ⟨K - 1, by omega⟩
  obtain ⟨e1, e2⟩ := GenContFract.cfConv_invariant (h := (0:ℂ)) hw m
  rw [haK, zero_mul, zero_mul, add_zero] at e1 e2
  have hwK : w (m + 1) ≠ 0 := fun h => hw0 (by rw [← e2, h, mul_zero])
  have hB : (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) ≠ 0 :=
    fun h => hw0 (by rw [← e2, h, zero_mul])
  have hval : (GenContFract.cfConv_ofFun 0 a b).convs (m + 1) = a 0 * w 1 / w 0 := by
    change (GenContFract.cfConv_ofFun 0 a b).nums (m + 1) /
      (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) = _
    rw [div_eq_div_iff hB hw0, ← e2]
    linear_combination (GenContFract.cfConv_ofFun 0 a b).dens (m + 1) * e1
  unfold DLMF.HasContinuedFraction
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (m + 1)] with N hN
  rw [legFS_cfTail_freeze hK ha haK hN, hval]

/-- With no vanishing partial numerator, Pincherle's criterion with a ratio limit gives the value
`a₀ w₁/w₀` of the project's continued fraction. -/
lemma legFS_hasCF_of_ratio {a b w : ℕ → ℂ} (ha : ∀ k, a k ≠ 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0)
    (hwev : ∀ᶠ k in atTop, w k ≠ 0) {ρ : ℂ} (hρ : 1 < ‖ρ‖)
    (hlim : Tendsto (fun k => -(w k / (a (k + 1) * w (k + 2)))) atTop (𝓝 ρ)) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  have h := GenContFract.pinch_cfConv_tendsto (h := (0:ℂ)) hw hw0 ha hwev hρ hlim
  rw [zero_add] at h
  unfold DLMF.HasContinuedFraction
  refine h.congr fun N => ?_
  have := legFS_cfContinuants_eq (b := b) (K := N) (fun k _ _ => ha k) N le_rfl
  simp only [DLMF.cfTail, this]; rfl

/-- If `a₀ = 0` every finite continued fraction has numerator `0`. -/
lemma legFS_cfContinuants_fst_zero {a b : ℕ → ℂ} (h0 : a 0 = 0) (n : ℕ) :
    (DLMF.cfContinuants a b 0 n).1 = 0 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [DLMF.cfContinuants]
    · simp [DLMF.cfContinuants, h0]
    · have h1 := ih (n + 1) (by omega)
      have h2 := ih n (by omega)
      rw [DLMF.cfContinuants]
      split_ifs
      · exact h1
      · simp [GenContFract.nextConts, GenContFract.nextNum, h1, h2]

/-- A continued fraction with a vanishing partial numerator and a backward solution `w`,
`w₀ ≠ 0`, has the value `a₀ w₁/w₀`. -/
lemma legFS_hasCF_of_exists_zero {a b w : ℕ → ℂ} (hex : ∃ K, a K = 0)
    (hw : ∀ k, w k = b k * w (k + 1) + a (k + 1) * w (k + 2)) (hw0 : w 0 ≠ 0) :
    DLMF.HasContinuedFraction a b (a 0 * w 1 / w 0) := by
  classical
  have hK := Nat.find_spec hex
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
  · rw [h] at hK
    rw [hK, zero_mul, zero_div]
    unfold DLMF.HasContinuedFraction
    refine tendsto_const_nhds.congr fun N => ?_
    simp only [DLMF.cfTail, legFS_cfContinuants_fst_zero hK, zero_div]
  · exact legFS_hasCF_of_terminating h (fun k _ hk => Nat.find_min hex hk) hK hw hw0

end DLMF.Legendre
