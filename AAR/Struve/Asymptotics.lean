/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.AngerWeber
public import AAR.Airy.Scorer
public import AAR.Confluent.TricomiRotated

/-!
# Struve and Anger–Weber asymptotics

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The large-argument expansions 11.6.1 and 11.6.2 are proved by Watson's lemma
(`hasAsymptoticExpansion_integral_cexp_smul_sector`). For `𝐊_ν` the Laplace integral
11.5.2 (`AAR.Bessel.struveK_eq_integral`) is rotated to the ray `arg t = α`, `|α| < π/2`
(`struveK_eq_struveKRotated`, by `Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate`
and analytic continuation, following `AAR.Confluent.kummerU_eq_tricomiRotated`); two
rotated sectors cover `|arg z| ≤ π - δ`. For `𝐌_ν` the integral 11.5.4 gives the case
`re ν > 1/2`, and the recurrence 11.4.25 with 10.29.1 extends it to all orders.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel AAR.Airy

/-- struveAsymptoticTerm. -/
def struveAsymptoticTerm (ν z : ℂ) (k : ℕ) : ℂ :=
  Gamma (k+1/2)/Gamma (ν+1/2-k)*(z/2)^(ν-2*k-1)/π

section WatsonExpansions

open AAR.Confluent
open scoped Interval

/-- `cos y · (1 + r²) ≤ ‖1 + (r e^{iy})²‖`. -/
lemma cos_mul_le_norm_one_add_sq (r y : ℝ) :
    Real.cos y * (1 + r ^ 2) ≤ ‖1 + ((r : ℂ) * exp (y * I)) ^ 2‖ := by
  set w := 1 + ((r : ℂ) * exp (y * I)) ^ 2 with hw
  have hexp : ((r : ℂ) * exp (y * I)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  have hre : w.re = 1 + r ^ 2 * Real.cos (2 * y) := by
    rw [hw, add_re, hexp, re_ofReal_mul, exp_ofReal_mul_I_re]; simp
  have him : w.im = r ^ 2 * Real.sin (2 * y) := by
    rw [hw, add_im, hexp, im_ofReal_mul, exp_ofReal_mul_I_im]; simp
  have hsq : ‖w‖ ^ 2 = (Real.cos y * (1 + r ^ 2)) ^ 2 + (Real.sin y * (1 - r ^ 2)) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, hre, him, Real.cos_two_mul, Real.sin_two_mul]
    linear_combination (4 * (r ^ 2) ^ 2 * Real.cos y ^ 2 - (1 - r ^ 2) ^ 2) *
      Real.sin_sq_add_cos_sq y
  calc Real.cos y * (1 + r ^ 2) ≤ |Real.cos y * (1 + r ^ 2)| := le_abs_self _
    _ = Real.sqrt ((Real.cos y * (1 + r ^ 2)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖w‖ ^ 2) := Real.sqrt_le_sqrt (by rw [hsq]; nlinarith [sq_nonneg (Real.sin y * (1 - r ^ 2))])
    _ = ‖w‖ := Real.sqrt_sq (norm_nonneg _)

/-- `1 + (r e^{iy})²` lies in the slit plane for `|y| < π/2`. -/
lemma one_add_sq_mem_slitPlane {r y : ℝ} (hy : |y| < π / 2) :
    1 + ((r : ℂ) * exp (y * I)) ^ 2 ∈ slitPlane := by
  have hexp : ((r : ℂ) * exp (y * I)) ^ 2 = ((r ^ 2 : ℝ) : ℂ) * exp (((2 * y : ℝ) : ℂ) * I) := by
    rw [mul_pow, ← exp_nat_mul]; push_cast; ring_nf
  rw [mem_slitPlane_iff, add_re, add_im, hexp, re_ofReal_mul, im_ofReal_mul,
    exp_ofReal_mul_I_re, exp_ofReal_mul_I_im]
  simp only [one_re, one_im, zero_add]
  by_cases hs : Real.sin (2 * y) = 0
  · left
    have h0 : 2 * y = 0 := by
      rw [Real.sin_eq_zero_iff_of_lt_of_lt] at hs
      · exact hs
      · linarith [neg_abs_le y]
      · linarith [le_abs_self y]
    rw [h0, Real.cos_zero]; positivity
  · rcases eq_or_ne r 0 with h | h
    · left; simp [h]
    · right; exact mul_ne_zero (by positivity) hs

/-- A point between `0` and `α` has modulus at most `|α|`. -/
lemma abs_le_abs_of_mem_uIcc_zero_left {α y : ℝ} (hy : y ∈ [[0, α]]) : |y| ≤ |α| := by
  rcases le_total 0 α with h | h
  · rw [uIcc_of_le h] at hy; rw [abs_of_nonneg hy.1, abs_of_nonneg h]; exact hy.2
  · rw [uIcc_of_ge h] at hy; rw [abs_of_nonpos hy.2, abs_of_nonpos h]; linarith [hy.1]

/-- A polynomial bound for `(1 + (r e^{iy})²)^a`, uniform in `|y| ≤ |α| < π/2`. -/
lemma norm_one_add_sq_mul_exp_cpow_le {a : ℂ} {α : ℝ} (hα : |α| < π / 2) {N : ℕ} (hN : |a.re| ≤ N)
    {r y : ℝ} (hr : 0 ≤ r) (hy : |y| ≤ |α|) :
    ‖(1 + ((r : ℂ) * exp (y * I)) ^ 2) ^ a‖ ≤
      Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|) := by
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hcα1 : Real.cos α ≤ 1 := Real.cos_le_one α
  have hcy : Real.cos α ≤ Real.cos y := by
    rw [← Real.cos_abs α, ← Real.cos_abs y]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith [Real.pi_pos]) hy
  set m := ‖1 + ((r : ℂ) * exp (y * I)) ^ 2‖ with hm
  have hm1 : m ≤ (1 + r) ^ 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_one, norm_pow, norm_mul_exp_I_eq r hr]; nlinarith
  have hm0 : Real.cos α ≤ m := by
    refine le_trans ?_ (cos_mul_le_norm_one_add_sq r y)
    nlinarith [sq_nonneg r]
  refine (norm_cpow_le_exp _ _).trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
  have hK : 1 ≤ Real.cos α ^ (-(N : ℝ)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hcα hcα1 (by simp)
  have hP : 1 ≤ (1 + r) ^ (2 * N) := one_le_pow₀ (by linarith)
  rcases le_total 0 a.re with h | h
  · calc m ^ a.re ≤ ((1 + r) ^ 2) ^ a.re := Real.rpow_le_rpow (norm_nonneg _) hm1 h
      _ ≤ ((1 + r) ^ 2) ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le (by nlinarith)
          (by linarith [le_abs_self a.re])
      _ = (1 + r) ^ (2 * N) := by rw [Real.rpow_natCast, ← pow_mul]
      _ ≤ _ := le_mul_of_one_le_left (by positivity) hK
  · calc m ^ a.re ≤ Real.cos α ^ a.re := Real.rpow_le_rpow_of_nonpos hcα hm0 h
      _ ≤ Real.cos α ^ (-(N : ℝ)) := Real.rpow_le_rpow_of_exponent_ge hcα hcα1
          (by linarith [neg_abs_le a.re])
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hP

/-- The integrand `e^{-zt} (1+t²)^a` of the Laplace representation of `𝐊_ν`. -/
def struveKKernel (a z t : ℂ) : ℂ := exp (-z * t) * (1 + t ^ 2) ^ a

/-- Pointwise bound for the kernel on the ray `r e^{iy}`. -/
lemma norm_struveKKernel_le {a : ℂ} {α : ℝ} (hα : |α| < π / 2) {N : ℕ} (hN : |a.re| ≤ N)
    (z : ℂ) {r y : ℝ} (hr : 0 ≤ r) (hy : |y| ≤ |α|) :
    ‖struveKKernel a z (r * exp (y * I))‖ ≤ Real.exp (-(z * (r * exp (y * I))).re) *
      (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by
  rw [struveKKernel, norm_mul, Complex.norm_exp, neg_mul, neg_re]
  exact mul_le_mul_of_nonneg_left (norm_one_add_sq_mul_exp_cpow_le hα hN hr hy) (Real.exp_pos _).le

/-- The kernel is holomorphic on the rays `r e^{iy}`, `|y| < π/2`. -/
lemma differentiableAt_struveKKernel (a z : ℂ) {r y : ℝ} (hy : |y| < π / 2) :
    DifferentiableAt ℂ (struveKKernel a z) (r * exp (y * I)) := by
  unfold struveKKernel
  exact (by fun_prop : DifferentiableAt ℂ (fun t : ℂ => exp (-z * t)) _).mul
    ((by fun_prop : DifferentiableAt ℂ (fun t : ℂ => 1 + t ^ 2) _).cpow (differentiableAt_const _)
      (one_add_sq_mem_slitPlane hy))

/-- Rotation of the ray in the Laplace integral of `𝐊_ν`, on the common half-plane. -/
lemma integral_struveKKernel_rotate {a z : ℂ} {α : ℝ} (hα : |α| < π / 2) (hz0 : 0 < z.re)
    (hzα : 0 < (z * exp (α * I)).re) :
    ∫ r in Ioi (0 : ℝ), struveKKernel a z r =
      exp (α * I) * ∫ r in Ioi (0 : ℝ), struveKKernel a z (r * exp (α * I)) := by
  set κ0 := min z.re (z * exp (α * I)).re with hκ0
  have hκ0pos : 0 < κ0 := lt_min hz0 hzα
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N : ℝ)) * Real.exp (π * |a.im|) with hB
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hB0 : 0 ≤ B := by positivity
  obtain ⟨M, hM⟩ := exists_rpow_mul_exp_neg_le ((2 * N : ℕ) : ℝ) (b := κ0 / 2) (by positivity)
  have hM0 : 0 ≤ M := (by positivity : (0 : ℝ) ≤ 1 ^ ((2 * N : ℕ) : ℝ) *
    Real.exp (-(κ0 / 2) * 1)).trans (hM 1 le_rfl)
  set C := max (2 ^ (2 * N) * B) (2 ^ (2 * N) * B * M) with hC
  have hbound : ∀ r : ℝ, 0 < r → ∀ y ∈ [[0, α]], ‖struveKKernel a z (r * exp (y * I))‖ ≤
      Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B := by
    intro r hr y hy
    have hb := norm_struveKKernel_le hα hN z hr.le (abs_le_abs_of_mem_uIcc_zero_left hy)
    refine hb.trans ?_
    have hre : κ0 * r ≤ (z * ((r : ℂ) * exp (y * I))).re := by
      rw [mul_left_comm, re_ofReal_mul]
      have := re_mul_exp_mul_I_ge hα hz0 hzα hy
      nlinarith
    have he : Real.exp (-(z * ((r : ℂ) * exp (y * I))).re) ≤ Real.exp (-κ0 * r) :=
      Real.exp_le_exp.mpr (by linarith)
    calc Real.exp (-(z * ((r : ℂ) * exp (y * I))).re) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|))
        ≤ Real.exp (-κ0 * r) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by gcongr
      _ = _ := by rw [hB]; ring
  refine Complex.integral_Ioi_eq_exp_mul_integral_Ioi_rotate (σ := 1) (κ := κ0 / 2) (C := C)
    one_pos (by positivity) ?_ ?_ ?_
  · intro r hr y hy
    exact differentiableAt_struveKKernel a z (abs_lt_of_mem_uIcc hα hy)
  · intro r hr hr1 y hy
    refine (hbound r hr y hy).trans ?_
    have h1 : Real.exp (-κ0 * r) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h2 : (1 + r) ^ (2 * N) ≤ 2 ^ (2 * N) := pow_le_pow_left₀ (by linarith) (by linarith) _
    rw [sub_self, Real.rpow_zero, mul_one]
    calc Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B ≤ 1 * 2 ^ (2 * N) * B := by gcongr
      _ = 2 ^ (2 * N) * B := by ring
      _ ≤ C := le_max_left _ _
  · intro r hr y hy
    have hr0 : 0 < r := by linarith
    refine (hbound r hr0 y hy).trans ?_
    have h2 : (1 + r) ^ (2 * N) ≤ 2 ^ (2 * N) * r ^ (2 * N) := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (by linarith) (by linarith) _
    have hsplit : Real.exp (-κ0 * r) = Real.exp (-(κ0 / 2) * r) * Real.exp (-(κ0 / 2) * r) := by
      rw [← Real.exp_add]; ring_nf
    have hMr := hM r hr
    rw [Real.rpow_natCast] at hMr
    calc Real.exp (-κ0 * r) * (1 + r) ^ (2 * N) * B
        ≤ Real.exp (-κ0 * r) * (2 ^ (2 * N) * r ^ (2 * N)) * B := by gcongr
      _ = 2 ^ (2 * N) * B * (r ^ (2 * N) * Real.exp (-(κ0 / 2) * r)) *
            Real.exp (-(κ0 / 2) * r) := by rw [hsplit]; ring
      _ ≤ 2 ^ (2 * N) * B * M * Real.exp (-(κ0 / 2) * r) := by gcongr
      _ ≤ C * Real.exp (-(κ0 / 2) * r) := by gcongr; exact le_max_right _ _

/-- The rotated Laplace integral `∫₀^∞ e^{-z r e^{iα}} (1 + (r e^{iα})²)^a dr`. -/
def struveKRotIntegral (a : ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  ∫ r in Ioi (0 : ℝ), struveKKernel a z (r * exp (α * I))

/-- The rotated integral is holomorphic on the half-plane `re (z e^{iα}) > 0`. -/
lemma differentiableOn_struveKRotIntegral (a : ℂ) {α : ℝ} (hα : |α| < π / 2) :
    DifferentiableOn ℂ (struveKRotIntegral a α) {z : ℂ | 0 < (z * exp (α * I)).re} := by
  intro z₀ hz₀
  change 0 < (z₀ * exp (α * I)).re at hz₀
  set ω := exp (α * I) with hω
  set δ : ℝ := (z₀ * ω).re / 2 with hδ
  have hδ0 : 0 < δ := by positivity
  have hre : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 ≤ r → δ * r ≤ (z * ((r : ℂ) * ω)).re := by
    intro z hz r hr
    rw [Metric.mem_ball, dist_eq_norm] at hz
    have h1 : |((z - z₀) * ω).re| ≤ ‖z - z₀‖ := by
      refine (abs_re_le_norm _).trans ?_
      rw [norm_mul, hω, norm_exp_ofReal_mul_I, mul_one]
    have h2 : (z * ((r : ℂ) * ω)).re = r * (z * ω).re := by
      rw [mul_left_comm, re_ofReal_mul]
    have h3 : (z * ω).re = (z₀ * ω).re + ((z - z₀) * ω).re := by
      rw [← add_re]; ring_nf
    rw [h2, h3]
    have := (abs_le.mp h1).1
    nlinarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N : ℝ)) * Real.exp (π * |a.im|) with hB
  have hcα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  set F : ℂ → ℝ → ℂ := fun z r => struveKKernel a z (r * ω) with hF
  have hcontF : ∀ z : ℂ, ContinuousOn (F z) (Ioi 0) := fun z r _ =>
    (ContinuousAt.comp (g := struveKKernel a z) (f := fun r : ℝ => (r : ℂ) * ω) (x := r)
      (differentiableAt_struveKKernel a z hα).continuousAt
      (by fun_prop : Continuous fun r : ℝ => (r : ℂ) * ω).continuousAt).continuousWithinAt
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (F z) (volume.restrict (Ioi 0)) := fun z =>
    (hcontF z).aestronglyMeasurable measurableSet_Ioi
  have hbnd : ∀ z ∈ Metric.ball z₀ δ, ∀ r : ℝ, 0 < r →
      ‖F z r‖ ≤ Real.exp (-δ * r) * r ^ (0 : ℝ) * (1 + r) ^ (2 * N) * B := by
    intro z hz r hr
    have hb := norm_struveKKernel_le hα hN z hr.le le_rfl
    refine hb.trans ?_
    have := hre z hz r hr.le
    have he : Real.exp (-(z * ((r : ℂ) * ω)).re) ≤ Real.exp (-δ * r) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [Real.rpow_zero, mul_one, hB]
    calc Real.exp (-(z * ((r : ℂ) * ω)).re) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|))
        ≤ Real.exp (-δ * r) *
          (Real.cos α ^ (-(N : ℝ)) * (1 + r) ^ (2 * N) * Real.exp (π * |a.im|)) := by gcongr
      _ = _ := by ring
  set G : ℝ → ℝ := fun r => Real.exp (-δ * r) * r ^ (1 : ℝ) * (1 + r) ^ (2 * N) * B with hGdef
  have hG : IntegrableOn G (Ioi 0) :=
    (integrableOn_exp_mul_rpow_mul_one_add_pow (by norm_num) hδ0 (2 * N)).mul_const B
  have hint0 : Integrable (F z₀) (volume.restrict (Ioi 0)) := by
    refine Integrable.mono' ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0)
      (by norm_num) hδ0 (2 * N)).mul_const B) (hmeas z₀) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    exact hbnd z₀ (Metric.mem_ball_self hδ0) r hr
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi 0)) (F := F) (F' := fun z r => -((r : ℂ) * ω) * F z r)
    (bound := G) (Metric.ball_mem_nhds _ hδ0) (Eventually.of_forall hmeas) hint0
    ((((by fun_prop : Continuous fun r : ℝ => -((r : ℂ) * ω)).continuousOn).mul
      (hcontF z₀)).aestronglyMeasurable measurableSet_Ioi) ?_ hG ?_
  · exact hd.2.differentiableAt.differentiableWithinAt
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr z hz => ?_)
    have hr : (0 : ℝ) < r := hr
    rw [norm_mul, norm_neg, norm_mul_exp_I_eq r hr.le]
    calc r * ‖F z r‖ ≤ r * (Real.exp (-δ * r) * r ^ (0 : ℝ) * (1 + r) ^ (2 * N) * B) :=
          mul_le_mul_of_nonneg_left (hbnd z hz r hr) hr.le
      _ = G r := by rw [hGdef]; simp only [Real.rpow_zero, Real.rpow_one]; ring
  · refine Eventually.of_forall fun r z _ => ?_
    have h := ((hasDerivAt_id z).neg.mul_const ((r : ℂ) * ω)).cexp.mul_const
      ((1 + ((r : ℂ) * ω) ^ 2) ^ a)
    simp only [hF, struveKKernel]
    convert h using 1
    · funext w; simp
    · simp; ring

/-- The rotated representation `𝐊_ν(z) = 2(z/2)^ν/(√π Γ(ν+1/2)) · e^{iα} ∫₀^∞ …`. -/
def struveKRotated (ν : ℂ) (α : ℝ) (z : ℂ) : ℂ :=
  2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
    (exp (α * I) * struveKRotIntegral (ν - 1 / 2) α z)

/-- **Rotated Laplace representation of `𝐊_ν`**: for `|α| < π/2` and `re (z e^{iα}) > 0`. -/
theorem struveK_eq_struveKRotated (ν : ℂ) {α : ℝ} (hα : |α| < π / 2) {z : ℂ}
    (hz : 0 < (z * exp (α * I)).re) : struveK ν z = struveKRotated ν α z := by
  set ω := exp (α * I) with hω
  set H : Set ℂ := {z : ℂ | 0 < (z * ω).re} with hH
  have hHo : IsOpen H := isOpen_lt continuous_const (by fun_prop)
  have hHc : Convex ℝ H := by
    intro z₁ hz₁ z₂ hz₂ s t hs ht hst
    change 0 < ((s • z₁ + t • z₂) * ω).re
    change 0 < (z₁ * ω).re at hz₁
    change 0 < (z₂ * ω).re at hz₂
    rw [add_mul, add_re, smul_mul_assoc, smul_mul_assoc, Complex.smul_re, Complex.smul_re,
      smul_eq_mul, smul_eq_mul]
    rcases eq_or_lt_of_le hs with h | h
    · subst h; simp at hst; subst hst; simpa using hz₂
    · nlinarith [mul_pos h hz₁, mul_nonneg ht hz₂.le]
  have hcosα : 0 < Real.cos α := Real.cos_pos_of_mem_Ioo
    ⟨by linarith [neg_abs_le α], by linarith [le_abs_self α]⟩
  have hHslit : H ⊆ slitPlane := by
    intro w hw
    change 0 < (w * ω).re at hw
    by_contra h
    rw [mem_slitPlane_iff, not_or] at h
    push Not at h
    have hw' : w = (w.re : ℂ) := Complex.ext (by simp) (by simp [h.2])
    rw [hw', re_ofReal_mul, hω, exp_ofReal_mul_I_re] at hw
    nlinarith [h.1]
  have hU : AnalyticOnNhd ℂ (struveK ν) H :=
    (AAR.Bessel.analyticOnNhd_struveK ν).mono hHslit
  have hpre : DifferentiableOn ℂ
      (fun z : ℂ => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))) H := by
    intro w hw
    have h2 := div_two_mem_slitPlane (hHslit hw)
    exact ((((differentiableAt_id.div_const 2).cpow (differentiableAt_const ν) h2).const_mul
      2).div_const _).differentiableWithinAt
  have hV : AnalyticOnNhd ℂ (struveKRotated ν α) H :=
    (hpre.mul ((differentiableOn_struveKRotIntegral (ν - 1 / 2) hα).const_mul ω)).analyticOnNhd
      hHo
  set zs : ℂ := exp ((-(α / 2) : ℝ) * I) with hzs
  have hzs0 : 0 < zs.re := by
    rw [hzs, exp_ofReal_mul_I_re, Real.cos_neg]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hzsH : 0 < (zs * ω).re := by
    rw [hzs, hω, ← exp_add, show ((-(α / 2) : ℝ) : ℂ) * I + α * I = ((α / 2 : ℝ) : ℂ) * I by
      push_cast; ring, exp_ofReal_mul_I_re]
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le α, Real.pi_pos],
      by linarith [le_abs_self α, Real.pi_pos]⟩
  have hev : struveK ν =ᶠ[𝓝 zs] struveKRotated ν α := by
    have hopen : IsOpen {w : ℂ | 0 < w.re ∧ 0 < (w * ω).re} :=
      (isOpen_lt continuous_const continuous_re).inter (isOpen_lt continuous_const
        (by fun_prop : Continuous fun w : ℂ => (w * ω).re))
    filter_upwards [hopen.mem_nhds ⟨hzs0, hzsH⟩] with w hw
    rw [AAR.Bessel.struveK_eq_integral ν hw.1, struveKRotated, struveKRotIntegral,
      ← integral_struveKKernel_rotate hα hw.1 hw.2]
    rfl
  exact hU.eqOn_of_preconnected_of_eventuallyEq hV hHc.isPreconnected hzsH hev hz


/-- `(a)(a-1)⋯(a-k+1)/Γ(a+1) = 1/Γ(a+1-k)`. -/
lemma neg_one_pow_mul_poch_mul_inv_Gamma (a : ℂ) (k : ℕ) :
    (Gamma (a + 1))⁻¹ * ((-1) ^ k * poch (-a) k) = (Gamma (a + 1 - k))⁻¹ := by
  induction k with
  | zero => simp [poch]
  | succ k ih =>
    rw [poch_succ, pow_succ, show (Gamma (a + 1))⁻¹ * ((-1) ^ k * (-1) * (poch (-a) k * (-a + k)))
      = (Gamma (a + 1))⁻¹ * ((-1) ^ k * poch (-a) k) * (a - k) by ring, ih,
      AAR.Hypergeometric.inv_Gamma_eq_mul_inv_Gamma_add_one (a + 1 - ((k + 1 : ℕ) : ℂ))]
    push_cast
    rw [show a + 1 - (k + 1) + 1 = a + 1 - k by ring]
    ring

/-- `Γ(k+1/2) k! 4^k = (2k)! √π`. -/
lemma Gamma_nat_add_half_mul (k : ℕ) :
    Gamma (k + 1 / 2) * (k ! : ℂ) * 4 ^ k = ((2 * k) ! : ℂ) * Real.sqrt π := by
  have h := Complex.Gamma_mul_Gamma_add_half ((k : ℂ) + 1 / 2)
  rw [show (k : ℂ) + 1 / 2 + 1 / 2 = (k : ℂ) + 1 by ring, Complex.Gamma_nat_eq_factorial,
    show 2 * ((k : ℂ) + 1 / 2) = ((2 * k : ℕ) : ℂ) + 1 by push_cast; ring,
    Complex.Gamma_nat_eq_factorial,
    show (1 : ℂ) - (((2 * k : ℕ) : ℂ) + 1) = -((2 * k : ℕ) : ℂ) by ring, cpow_neg,
    cpow_natCast] at h
  have h4 : (2 : ℂ) ^ (2 * k) = 4 ^ k := by rw [pow_mul]; norm_num
  rw [h4] at h
  have h40 : (4 : ℂ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [h]; field_simp

/-- The coefficient identity behind DLMF 11.6.1. -/
lemma struveK_coeff_eq (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (k : ℕ) :
    2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) *
      ((z ^ (2 * k + 1))⁻¹ * (Gamma (((2 * k : ℕ) : ℂ) + 1) * Ring.choose (ν - 1 / 2) k)) =
      struveAsymptoticTerm ν z k := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hch : Ring.choose (ν - 1 / 2) k = (-1) ^ k * poch (-(ν - 1 / 2)) k / k ! := by
    rw [← ring_choose_neg_eq_poch, neg_neg]
  have hG := neg_one_pow_mul_poch_mul_inv_Gamma (ν - 1 / 2) k
  rw [show ν - 1 / 2 + 1 = ν + 1 / 2 by ring] at hG
  have hH := Gamma_nat_add_half_mul k
  have hpow : (z / 2) ^ (ν - 2 * k - 1) = (z / 2) ^ ν * 2 ^ (2 * k + 1) * (z ^ (2 * k + 1))⁻¹ := by
    rw [show ν - 2 * k - 1 = ν - ((2 * k + 1 : ℕ) : ℂ) by push_cast; ring, cpow_sub _ _ hz2,
      cpow_natCast, div_pow]
    field_simp
  rw [struveAsymptoticTerm, hpow, Complex.Gamma_nat_eq_factorial, hch, div_eq_mul_inv _ (Gamma (ν + 1 / 2 - k)), ← hG]
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π : ℂ) = Real.sqrt π * Real.sqrt π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h' : (((2 * k) ! : ℕ) : ℂ) = Gamma (k + 1 / 2) * k ! * 4 ^ k / Real.sqrt π := by
    rw [hH]; field_simp
  rw [hpi, h']
  rw [show (2 : ℂ) ^ (2 * k + 1) = 4 ^ k * 2 by rw [pow_succ, pow_mul]; norm_num]
  field_simp

/-- A sum over even indices below `N`, reindexed. -/
lemma sum_range_ite_even (g : ℕ → ℂ) (N : ℕ) :
    ∑ n ∈ Finset.range N, (if Even n then g (n / 2) else 0) =
      ∑ k ∈ Finset.range ((N + 1) / 2), g k := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    rcases Nat.even_or_odd N with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · simp only [show Even (m + m) from ⟨m, rfl⟩, ↓reduceIte]
      rw [show (m + m + 1 + 1) / 2 = m + 1 by omega,
        show (m + m + 1) / 2 = m by omega, show (m + m) / 2 = m by omega, Finset.sum_range_succ]
    · simp only [show ¬Even (2 * m + 1) from Nat.not_even_iff_odd.mpr ⟨m, rfl⟩, ↓reduceIte]
      rw [add_zero,
        show (2 * m + 1 + 1 + 1) / 2 = m + 1 by omega, show (2 * m + 1 + 1) / 2 = m + 1 by omega]

/-- Coefficients of `(1 + (t e^{iα})²)^a = ∑ Aₙ tⁿ`. -/
def struveKCoeffA (a : ℂ) (α : ℝ) (n : ℕ) : ℂ :=
  if Even n then exp (α * I) ^ n * Ring.choose a (n / 2) else 0

/-- Watson's lemma for the rotated Laplace integral of `𝐊_ν`. -/
lemma hasAsymptoticExpansion_struveKRotIntegral (a : ℂ) {δ α : ℝ} (hδ : 0 < δ)
    (hα : |α| < π / 2) :
    HasAsymptoticExpansion (rotSectorAtTop δ α)
      (fun (n : ℕ) (z : ℂ) => (z * exp (α * I)) ^ (-((n : ℂ) + 1)))
      (fun n => Gamma ((n : ℂ) + 1) • struveKCoeffA a α n) (struveKRotIntegral a α) := by
  set ω := exp (α * I) with hω
  set F : ℝ → ℂ := fun r => (1 + ((r : ℂ) * ω) ^ 2) ^ a with hF
  obtain ⟨N0, hN0⟩ : ∃ N : ℕ, |a.re| ≤ N := ⟨⌈|a.re|⌉₊, Nat.le_ceil _⟩
  set B := Real.cos α ^ (-(N0 : ℝ)) * Real.exp (π * |a.im|) with hB
  have hFcont : Continuous F := continuous_iff_continuousAt.2 fun r =>
    (by fun_prop : Continuous fun r : ℝ => 1 + ((r : ℂ) * ω) ^ 2).continuousAt.cpow
      continuousAt_const (one_add_sq_mem_slitPlane hα)
  have hint : IntegrableOn (fun r => Real.exp (-1 * r) • F r) (Ioi 0) := by
    refine ((integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (by norm_num) one_pos
      (2 * N0)).mul_const B).mono'
      (((by fun_prop : Continuous fun r : ℝ => Real.exp (-1 * r)).smul hFcont
        ).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun r hr => ?_)
    have hr : (0 : ℝ) < r := hr
    have h := norm_one_add_sq_mul_exp_cpow_le hα hN0 hr.le le_rfl (a := a)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Real.rpow_zero, mul_one]
    calc Real.exp (-1 * r) * ‖F r‖ ≤ Real.exp (-1 * r) *
          (Real.cos α ^ (-(N0 : ℝ)) * (1 + r) ^ (2 * N0) * Real.exp (π * |a.im|)) :=
          mul_le_mul_of_nonneg_left h (Real.exp_pos _).le
      _ = _ := by rw [hB]; ring
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_pos (show (0 : ℝ) < t from ht) 2
  have hFexp : ∀ N : ℕ, (fun t => F t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + 1 - 1)) • struveKCoeffA a α n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    intro N
    set M := (N + 1) / 2 with hM
    have hb := (one_add_mul_cpow_sub_sum_isBigO (ω ^ 2) a M).comp_tendsto ht2
    have hpow : (fun t : ℝ => (t ^ 2) ^ M) =O[𝓝[>] 0]
        fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [one_re, add_sub_cancel_right, Real.rpow_natCast, one_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg ht.1.le _),
        ← pow_mul]
      exact pow_le_pow_of_le_one ht.1.le ht.2.le (by omega)
    refine (hb.trans hpow).congr' (Eventually.of_forall fun t => ?_) EventuallyEq.rfl
    simp only [Function.comp_apply, hF]
    congr 1
    · congr 1; push_cast; ring
    · rw [← sum_range_ite_even]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [add_sub_cancel_right, cpow_natCast, smul_eq_mul, struveKCoeffA]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega]
        push_cast
        ring
      · simp
  have hW := (hasAsymptoticExpansion_integral_cexp_smul_sector (μ := 1) (by simp) hδ hint
    hFexp).comp_tendsto (tendsto_rotSectorAtTop δ α)
  refine hW.congr' (Eventually.of_forall fun z => ?_)
  simp only [Function.comp_apply, struveKRotIntegral, struveKKernel, hF, smul_eq_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun r _ => ?_
  rw [hω]; ring_nf

/-- `‖(z/2)^w‖ = 2^{-re w} ‖z^w‖`. -/
lemma norm_div_two_cpow (z w : ℂ) : ‖(z / 2) ^ w‖ = 2 ^ (-w.re) * ‖z ^ w‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · rw [zero_div]
    rcases eq_or_ne w 0 with rfl | hw
    · simp
    · rw [zero_cpow hw, norm_zero, mul_zero]
  · have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
    have harg : arg (z / 2) = arg z := by
      rw [div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
        arg_mul_real (by norm_num)]
    rw [norm_cpow_of_ne_zero hz2, norm_cpow_of_ne_zero hz, harg, norm_div, Complex.norm_ofNat,
      Real.div_rpow (norm_nonneg _) (by norm_num), Real.rpow_neg (by norm_num)]
    ring

/-- `(z/2)^w = O(z^w)` along any filter. -/
lemma isBigO_div_two_cpow (l : Filter ℂ) (w : ℂ) :
    (fun z : ℂ => (z / 2) ^ w) =O[l] fun z => z ^ w :=
  IsBigO.of_bound (2 ^ (-w.re)) (Eventually.of_forall fun z => (norm_div_two_cpow z w).le)

/-- DLMF 11.6.1 in a rotated sector `δ |z| ≤ re (z e^{iα})`. -/
theorem struveK_asymptotic_rotSector (ν : ℂ) {δ α : ℝ} (hδ : 0 < δ) (hα : |α| < π / 2)
    (N : ℕ) :
    (fun z : ℂ => struveK ν z - ∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k)
      =O[rotSectorAtTop δ α] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  set ω := exp (α * I) with hω
  have hω0 : ω ≠ 0 := exp_ne_zero _
  set P : ℂ → ℂ := fun z => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) with hP
  have hE := hasAsymptoticExpansion_struveKRotIntegral (ν - 1 / 2) hδ hα (2 * N)
  have hev := eventually_rotSectorAtTop hδ hα
  have h1 := (isBigO_refl (fun z => P z * ω) (rotSectorAtTop δ α)).mul hE
  -- the scale
  have hscale : ∀ z : ℂ, z ≠ 0 → ∀ m : ℕ,
      (z * ω) ^ (-(((m : ℕ) : ℂ) + 1)) = (z ^ (m + 1))⁻¹ * (ω ^ (m + 1))⁻¹ := by
    intro z hz m
    rw [cpow_neg, show ((m : ℕ) : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast,
      mul_pow, mul_inv]
  have h2 : (fun z => P z * ω * (z * ω) ^ (-(((2 * N : ℕ) : ℂ) + 1))) =O[rotSectorAtTop δ α]
      fun z : ℂ => z ^ (ν - 2 * N - 1) := by
    have hc : (fun z => P z * ω * (z * ω) ^ (-(((2 * N : ℕ) : ℂ) + 1))) =ᶠ[rotSectorAtTop δ α]
        fun z => (2 / (Real.sqrt π * Gamma (ν + 1 / 2)) / ω ^ (2 * N) / 2 ^ (2 * N + 1)) *
          (z / 2) ^ (ν - 2 * N - 1) := by
      filter_upwards [hev] with z hz
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
      have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
      rw [hscale z hz0, show ν - 2 * N - 1 = ν - ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
        cpow_sub _ _ hz2, cpow_natCast, div_pow, hP]
      simp only
      field_simp
      ring
    exact (hc.trans_isBigO ((isBigO_div_two_cpow _ _).const_mul_left _))
  refine (h1.congr' ?_ EventuallyEq.rfl).trans h2
  filter_upwards [hev] with z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  rw [struveK_eq_struveKRotated ν hα hz.2.1, struveKRotated, mul_sub]
  congr 1
  · simp only [hP]; ring
  · rw [Finset.mul_sum]
    have hsum : ∀ n ∈ Finset.range (2 * N), P z * ω * ((z * ω) ^ (-((n : ℂ) + 1)) •
        Gamma ((n : ℂ) + 1) • struveKCoeffA (ν - 1 / 2) α n) =
        if Even n then struveAsymptoticTerm ν z (n / 2) else 0 := by
      intro n _
      rw [struveKCoeffA]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega, ← struveK_coeff_eq ν hz0 m, smul_eq_mul, smul_eq_mul,
          show ((m + m : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) by push_cast; ring,
          hscale z hz0, show m + m = 2 * m by ring]
        simp only [hP]
        field_simp
        ring
      · simp
    rw [Finset.sum_congr rfl hsum, sum_range_ite_even, show (2 * N + 1) / 2 = N by omega]

/-- Unfolding an eventual statement in a rotated Watson sector. -/
lemma exists_of_eventually_rotSectorAtTop {δ α : ℝ} {p : ℂ → Prop}
    (h : ∀ᶠ z in rotSectorAtTop δ α, p z) :
    ∃ R, ∀ z : ℂ, R ≤ ‖z‖ → δ * ‖z‖ ≤ (z * exp (α * I)).re → p z := by
  rw [rotSectorAtTop, eventually_comap, sectorAtTop, eventually_inf_principal, eventually_comap,
    eventually_atTop] at h
  obtain ⟨R, hR⟩ := h
  refine ⟨R, fun z hz hzs => ?_⟩
  have hn : ‖z * exp (α * I)‖ = ‖z‖ := by rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
  exact hR ‖z‖ hz (z * exp (α * I)) hn (by show δ * ‖z * exp (α * I)‖ ≤ (z * exp (α * I)).re; rw [hn]; exact hzs) z rfl

/-- The closed sector `|arg z| ≤ π - δ` is covered by two rotated Watson sectors. -/
lemma sector_le_sup_rotSectorAtTop {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    AAR.DLMF.sector (π - δ) ≤ rotSectorAtTop (Real.sin (δ / 2)) (-((π - δ) / 2)) ⊔
      rotSectorAtTop (Real.sin (δ / 2)) ((π - δ) / 2) := by
  intro U hU
  rw [mem_sup] at hU
  obtain ⟨R1, h1⟩ := exists_of_eventually_rotSectorAtTop (p := (· ∈ U)) hU.1
  obtain ⟨R2, h2⟩ := exists_of_eventually_rotSectorAtTop (p := (· ∈ U)) hU.2
  have key : ∀ (z : ℂ) (β : ℝ), |arg z + β| ≤ (π - δ) / 2 →
      Real.sin (δ / 2) * ‖z‖ ≤ (z * exp (β * I)).re := by
    intro z β hb
    rw [re_mul_exp_mul_I, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [← Real.cos_abs, show δ / 2 = π / 2 - (π - δ) / 2 by ring, Real.sin_pi_div_two_sub]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) hb
  change ∀ᶠ z in AAR.DLMF.sector (π - δ), z ∈ U
  rw [AAR.DLMF.sector, eventually_inf_principal]
  refine (tendsto_comap.eventually (eventually_ge_atTop (max R1 R2))).mono fun z hzR hzS => ?_
  obtain ⟨-, hzarg⟩ := hzS
  rcases le_total 0 (arg z) with h | h
  · refine h1 z ((le_max_left _ _).trans hzR) (key z _ ?_)
    rw [abs_le]; constructor <;> linarith [abs_le.mp hzarg]
  · refine h2 z ((le_max_right _ _).trans hzR) (key z _ ?_)
    rw [abs_le]; constructor <;> linarith [abs_le.mp hzarg]

/-! ### The modified function `𝐌_ν` -/

/-- Coefficients of `(1 - t²)^a = ∑ Bₙ tⁿ`. -/
def struveMCoeffB (a : ℂ) (n : ℕ) : ℂ :=
  if Even n then (-1) ^ (n / 2) * Ring.choose a (n / 2) else 0

/-- The weight `(1 - t²)^a` on `t ≤ 1`, extended by zero. -/
def struveMWeight (a : ℂ) (t : ℝ) : ℂ :=
  (Iic (1 : ℝ)).indicator (fun t : ℝ => (1 - (t : ℂ) ^ 2) ^ a) t

lemma hasAsymptoticExpansion_struveMIntegral {a : ℂ} (ha : 0 < a.re) {δ : ℝ} (hδ : 0 < δ) :
    HasAsymptoticExpansion (sectorAtTop δ) (fun (n : ℕ) (z : ℂ) => z ^ (-((n : ℂ) + 1)))
      (fun n => Gamma ((n : ℂ) + 1) • struveMCoeffB a n)
      (fun z => ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight a t) := by
  have hmeas : Measurable (struveMWeight a) :=
    ((measurable_const.sub (Complex.measurable_ofReal.pow_const 2)).pow_const a).indicator
      measurableSet_Iic
  have hbd : ∀ t : ℝ, 0 < t → ‖struveMWeight a t‖ ≤ 1 := by
    intro t _
    unfold struveMWeight
    by_cases h : t ∈ Iic (1 : ℝ)
    · rw [indicator_of_mem h]
      have h1 : (1 - (t : ℂ) ^ 2) = ((1 - t ^ 2 : ℝ) : ℂ) := by push_cast; ring
      have ht1 : t ≤ 1 := h
      have h0 : 0 ≤ 1 - t ^ 2 := by nlinarith
      rw [h1, norm_cpow_eq_rpow_re_of_nonneg h0 ha.ne']
      exact Real.rpow_le_one h0 (by nlinarith) ha.le
    · rw [indicator_of_notMem h, norm_zero]; exact zero_le_one
  have hint : IntegrableOn (fun t => Real.exp (-1 * t) • struveMWeight a t) (Ioi 0) := by
    refine (integrableOn_exp_mul_rpow_mul_one_add_pow (s := 0) (by norm_num) one_pos 0).mono'
      (((by fun_prop : Continuous fun t : ℝ => Real.exp (-1 * t)).measurable.smul
        hmeas).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun t ht => ?_)
    rw [norm_smul, Real.norm_eq_abs, Real.abs_exp, Real.rpow_zero, pow_zero, mul_one, mul_one]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (hbd t ht)
  have ht2 : Tendsto (fun t : ℝ => t ^ 2) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact pow_pos (show (0 : ℝ) < t from ht) 2
  have hFexp : ∀ N : ℕ, (fun t => struveMWeight a t - ∑ n ∈ Finset.range N,
      ((t : ℂ) ^ ((n : ℂ) + 1 - 1)) • struveMCoeffB a n) =O[𝓝[>] 0]
      fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
    intro N
    set M := (N + 1) / 2 with hM
    have hb := (one_add_mul_cpow_sub_sum_isBigO (-1) a M).comp_tendsto ht2
    have hpow : (fun t : ℝ => (t ^ 2) ^ M) =O[𝓝[>] 0]
        fun t => t ^ ((N : ℝ) + (1 : ℂ).re - 1) := by
      refine IsBigO.of_bound 1 ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
      rw [one_re, add_sub_cancel_right, Real.rpow_natCast, one_mul, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (pow_nonneg ht.1.le _),
        ← pow_mul]
      exact pow_le_pow_of_le_one ht.1.le ht.2.le (by omega)
    refine (hb.trans hpow).congr' ?_ EventuallyEq.rfl
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [Function.comp_apply, struveMWeight,
      indicator_of_mem (show t ∈ Iic (1 : ℝ) from ht.2.le)]
    congr 1
    · congr 1; push_cast; ring
    · rw [← sum_range_ite_even]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [add_sub_cancel_right, cpow_natCast, smul_eq_mul, struveMCoeffB]
      split_ifs with h
      · obtain ⟨m, rfl⟩ := h
        rw [show (m + m) / 2 = m by omega]
        push_cast
        ring
      · simp
  exact hasAsymptoticExpansion_integral_cexp_smul_sector (μ := 1) (by simp) hδ hint hFexp

/-- DLMF 11.5.4 written as a Laplace integral over `(0, ∞)`. -/
lemma struveM_eq_integral_weight {ν : ℂ} (hν : -1 / 2 < ν.re) {z : ℂ} (hz : 0 < z.re) :
    struveM ν z = -(2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2))) *
      ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight (ν - 1 / 2) t := by
  rw [struveM_eq_poisson hν (Or.inl hz), intervalIntegral.integral_of_le zero_le_one,
    ← Ioi_inter_Iic, ← setIntegral_indicator (measurableSet_Iic (a := (1 : ℝ)))]
  have h : ∫ t in Ioi (0 : ℝ), (Iic (1 : ℝ)).indicator
      (fun t : ℝ => exp (-z * t) * (1 - (t : ℂ) ^ 2) ^ (ν - 1 / 2)) t =
      ∫ t in Ioi (0 : ℝ), exp (-(z * t)) • struveMWeight (ν - 1 / 2) t := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [struveMWeight]
    by_cases h : t ∈ Iic (1 : ℝ)
    · rw [indicator_of_mem h, indicator_of_mem h, smul_eq_mul, neg_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, smul_zero]
  rw [h]; ring

/-- Points of a Watson sector eventually have `‖z‖ ≥ 1` and `re z > 0`. -/
lemma eventually_re_pos_sectorAtTop {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ z in sectorAtTop δ, 1 ≤ ‖z‖ ∧ 0 < z.re :=
  eventually_sectorAtTop (R := 1) fun z hz hzs => ⟨hz, by nlinarith⟩

/-- DLMF 11.6.2 for `re ν > 1/2`, in the Watson sector `δ |z| ≤ re z`. -/
lemma struveM_asymptotic_sectorAtTop_of_re {ν : ℂ} (hν : 1 / 2 < ν.re) {δ : ℝ} (hδ : 0 < δ)
    (N : ℕ) :
    (fun z : ℂ => struveM ν z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
      =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  set P : ℂ → ℂ := fun z => 2 * (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 1 / 2)) with hP
  have hE := hasAsymptoticExpansion_struveMIntegral (a := ν - 1 / 2) (by simp; linarith) hδ
    (2 * N)
  have hev := eventually_re_pos_sectorAtTop hδ
  have h1 := (isBigO_refl (fun z => -P z) (sectorAtTop δ)).mul hE
  have hscale : ∀ z : ℂ, ∀ m : ℕ, z ^ (-(((m : ℕ) : ℂ) + 1)) = (z ^ (m + 1))⁻¹ := by
    intro z m
    rw [cpow_neg, show ((m : ℕ) : ℂ) + 1 = ((m + 1 : ℕ) : ℂ) by push_cast; ring, cpow_natCast]
  have h2 : (fun z => -P z * z ^ (-(((2 * N : ℕ) : ℂ) + 1))) =O[sectorAtTop δ]
      fun z : ℂ => z ^ (ν - 2 * N - 1) := by
    have hc : (fun z => -P z * z ^ (-(((2 * N : ℕ) : ℂ) + 1))) =ᶠ[sectorAtTop δ]
        fun z => (-(2 / (Real.sqrt π * Gamma (ν + 1 / 2))) / 2 ^ (2 * N + 1)) *
          (z / 2) ^ (ν - 2 * N - 1) := by
      filter_upwards [hev] with z hz
      have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
      have hz2 : z / 2 ≠ 0 := div_ne_zero hz0 two_ne_zero
      rw [hscale z, show ν - 2 * N - 1 = ν - ((2 * N + 1 : ℕ) : ℂ) by push_cast; ring,
        cpow_sub _ _ hz2, cpow_natCast, div_pow, hP]
      simp only
      field_simp
    exact (hc.trans_isBigO ((isBigO_div_two_cpow _ _).const_mul_left _))
  refine (h1.congr' ?_ EventuallyEq.rfl).trans h2
  filter_upwards [hev] with z hz
  have hz0 : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; linarith [hz.1]
  rw [struveM_eq_integral_weight (by linarith) hz.2, mul_sub]
  congr 1
  rw [Finset.mul_sum]
  have hsum : ∀ n ∈ Finset.range (2 * N), -P z * (z ^ (-((n : ℂ) + 1)) •
      Gamma ((n : ℂ) + 1) • struveMCoeffB (ν - 1 / 2) n) =
      if Even n then (-1) ^ (n / 2 + 1) * struveAsymptoticTerm ν z (n / 2) else 0 := by
    intro n _
    rw [struveMCoeffB]
    split_ifs with h
    · obtain ⟨m, rfl⟩ := h
      rw [show (m + m) / 2 = m by omega, ← struveK_coeff_eq ν hz0 m, smul_eq_mul, smul_eq_mul,
        show ((m + m : ℕ) : ℂ) = ((2 * m : ℕ) : ℂ) by push_cast; ring, hscale z]
      simp only [hP]
      ring
    · simp
  rw [Finset.sum_congr rfl hsum, sum_range_ite_even (fun k => (-1) ^ (k + 1) *
    struveAsymptoticTerm ν z k), show (2 * N + 1) / 2 = N by omega]

/-- The recurrence `𝐌_{ν-1} = 𝐌_{ν+1} + (2ν/z) 𝐌_ν + (z/2)^ν/(√π Γ(ν+3/2))`. -/
lemma struveM_sub_one (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveM (ν - 1) z = struveM (ν + 1) z + 2 * ν / z * struveM ν z +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) := by
  have hL := struveL_recurrence ν hz
  have hI := AAR.Bessel.besselI_sub_add (ν := ν) (slitPlane_ne_zero hz)
  simp only [struveM]
  linear_combination hL + hI

/-- The asymptotic coefficients satisfy the same recurrence. -/
lemma struveAsymptoticTerm_sum_sub_one (ν : ℂ) {z : ℂ} (hz : z ≠ 0) (N : ℕ) :
    ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm (ν - 1) z k =
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm (ν + 1) z k +
      2 * ν / z * ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hs : (Real.sqrt π : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hpi : (π : ℂ) = Real.sqrt π * Real.sqrt π := by
    rw [← ofReal_mul, Real.mul_self_sqrt Real.pi_pos.le]
  have hG12 : Gamma (1 / 2) = Real.sqrt π := by
    rw [Complex.Gamma_one_half_eq, Real.sqrt_eq_rpow, ofReal_cpow Real.pi_pos.le]; push_cast; rfl
  rw [Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (-1) ^ (0 + 1) * struveAsymptoticTerm (ν + 1) z 0 +
      (z / 2) ^ ν / (Real.sqrt π * Gamma (ν + 3 / 2)) = 0 := by
    simp only [struveAsymptoticTerm, Nat.cast_zero, zero_add, mul_zero, sub_zero]
    rw [show ν + 1 + 1 / 2 = ν + 3 / 2 by ring, show ν + 1 - 1 = ν by ring, hG12, hpi]
    field_simp
    ring
  rw [show ∀ A B C D : ℂ, A + B + C + D = (A + C) + (B + D) by intros; ring, h0, add_zero,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [struveAsymptoticTerm]
  push_cast
  have hk : (k : ℂ) + 1 / 2 ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hΓ : Gamma ((k : ℂ) + 1 + 1 / 2) = ((k : ℂ) + 1 / 2) * Gamma ((k : ℂ) + 1 / 2) := by
    rw [show (k : ℂ) + 1 + 1 / 2 = (k : ℂ) + 1 / 2 + 1 by ring, Complex.Gamma_add_one _ hk]
  have hinv := AAR.Hypergeometric.inv_Gamma_eq_mul_inv_Gamma_add_one (ν - 1 / 2 - k)
  rw [show ν - 1 / 2 - (k : ℂ) + 1 = ν + 1 / 2 - k by ring] at hinv
  have e1 : (z / 2) ^ (ν - 1 - 2 * (k : ℂ) - 1) = (z / 2) ^ (ν - 2 * k - 2) := by ring_nf
  have e2 : (z / 2) ^ (ν + 1 - 2 * ((k : ℂ) + 1) - 1) = (z / 2) ^ (ν - 2 * k - 2) := by ring_nf
  have e3 : (z / 2) ^ (ν - 2 * (k : ℂ) - 1) = (z / 2) ^ (ν - 2 * k - 2) * (z / 2) := by
    rw [show ν - 2 * (k : ℂ) - 1 = (ν - 2 * k - 2) + 1 by ring, cpow_add _ _ hz2, cpow_one]
  rw [e1, e2, e3, hΓ, show ν - 1 + 1 / 2 - (k : ℂ) = ν - 1 / 2 - k by ring,
    show ν + 1 + 1 / 2 - ((k : ℂ) + 1) = ν + 1 / 2 - k by ring,
    div_eq_mul_inv (Gamma ((k : ℂ) + 1 / 2)) (Gamma (ν - 1 / 2 - k)), hinv]
  field_simp
  ring

/-- One downward step of the recurrence for the expansion of `𝐌_ν`. -/
lemma struveM_asymptotic_step {l : Filter ℂ} (hl : ∀ᶠ z in l, z ∈ slitPlane) {μ : ℂ} (N : ℕ)
    (h1 : (fun z : ℂ => struveM (μ + 1) z -
      ∑ k ∈ Finset.range (N + 1), (-1) ^ (k + 1) * struveAsymptoticTerm (μ + 1) z k)
      =O[l] fun z : ℂ => z ^ (μ + 1 - 2 * ((N + 1 : ℕ) : ℂ) - 1))
    (h0 : (fun z : ℂ => struveM μ z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm μ z k)
      =O[l] fun z : ℂ => z ^ (μ - 2 * N - 1)) :
    (fun z : ℂ => struveM (μ - 1) z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm (μ - 1) z k)
      =O[l] fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
  have hinv : (fun z : ℂ => 2 * μ / z) =O[l] fun z : ℂ => z⁻¹ :=
    ((isBigO_refl (fun z : ℂ => z⁻¹) l).const_mul_left (2 * μ)).congr_left
      fun z => by rw [div_eq_mul_inv]
  have h0' := hinv.mul h0
  have hpow : (fun z : ℂ => z⁻¹ * z ^ (μ - 2 * N - 1)) =ᶠ[l]
      fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
    filter_upwards [hl] with z hz
    rw [show μ - 1 - 2 * (N : ℂ) - 1 = (μ - 2 * N - 1) - 1 by ring,
      cpow_sub (μ - 2 * N - 1) 1 (slitPlane_ne_zero hz), cpow_one, div_eq_mul_inv, mul_comm]
  have h1' : (fun z : ℂ => z ^ (μ + 1 - 2 * ((N + 1 : ℕ) : ℂ) - 1)) =
      fun z : ℂ => z ^ (μ - 1 - 2 * N - 1) := by
    funext z; congr 1; push_cast; ring
  rw [h1'] at h1
  refine (h1.add (h0'.trans_eventuallyEq hpow)).congr' ?_ EventuallyEq.rfl
  filter_upwards [hl] with z hz
  rw [struveM_sub_one μ hz, struveAsymptoticTerm_sum_sub_one μ (slitPlane_ne_zero hz) N]
  ring

/-- DLMF 11.6.2 for all orders, in the Watson sector `δ |z| ≤ re z`. -/
theorem struveM_asymptotic_sectorAtTop (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    (fun z : ℂ => struveM ν z -
      ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
      =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) := by
  have hl : ∀ᶠ z in sectorAtTop δ, z ∈ slitPlane :=
    (eventually_re_pos_sectorAtTop hδ).mono fun z hz => Or.inl hz.2
  suffices h : ∀ m : ℕ, ∀ ν : ℂ, 1 / 2 - m < ν.re → ∀ N : ℕ,
      (fun z : ℂ => struveM ν z -
        ∑ k ∈ Finset.range N, (-1) ^ (k + 1) * struveAsymptoticTerm ν z k)
        =O[sectorAtTop δ] fun z : ℂ => z ^ (ν - 2 * N - 1) by
    obtain ⟨m, hm⟩ := exists_nat_gt (1 / 2 - ν.re)
    exact h m ν (by linarith) N
  intro m
  induction m with
  | zero =>
    intro ν hν N
    exact struveM_asymptotic_sectorAtTop_of_re (by simpa using hν) hδ N
  | succ m ih =>
    intro ν hν N
    have h1 := ih (ν + 1 + 1) (by simp at hν ⊢; linarith) (N + 1)
    have h0 := ih (ν + 1) (by simp at hν ⊢; linarith) N
    have h := struveM_asymptotic_step hl N h1 h0
    rw [show ν + 1 - 1 = ν by ring] at h
    exact h

/-- The sector `|arg z| ≤ π/2 - δ` lies in the Watson sector `sin δ · |z| ≤ re z`. -/
lemma sector_le_sectorAtTop {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π / 2) :
    AAR.DLMF.sector (π / 2 - δ) ≤ sectorAtTop (Real.sin δ) := by
  refine inf_le_inf_left _ (principal_mono.mpr fun z hz => ?_)
  obtain ⟨hz0, harg⟩ := hz
  change Real.sin δ * ‖z‖ ≤ z.re
  have hre : z.re = ‖z‖ * Real.cos (arg z) := by
    rw [Complex.cos_arg hz0]; field_simp [norm_ne_zero_iff.mpr hz0]
  rw [hre, mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  rw [← Real.cos_abs, show δ = π / 2 - (π / 2 - δ) by ring, Real.sin_pi_div_two_sub]
  exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg

end WatsonExpansions

/-- struveK asymptotic. -/
@[dlmf 11.6.E1]
theorem struveK_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => struveK ν z-∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  have hs : 0 < Real.sin (δ / 2) := Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  have hα : |(π - δ) / 2| < π / 2 := by rw [abs_lt]; constructor <;> linarith
  have hα' : |-((π - δ) / 2)| < π / 2 := by rwa [abs_neg]
  exact ((struveK_asymptotic_rotSector ν hs hα' N).sup
    (struveK_asymptotic_rotSector ν hs hα N)).mono (sector_le_sup_rotSectorAtTop hδ hδπ)

/-- struveM asymptotic. -/
@[dlmf 11.6.E2]
theorem struveM_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => struveM ν z-∑ k ∈ Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ => z^(ν-2*N-1)) :=
  (struveM_asymptotic_sectorAtTop ν (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith)) N).mono
    (sector_le_sectorAtTop hδ hδπ)

/-- struveK primitive asymptotic. -/
@[dlmf 11.6.E3]
theorem struveK_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

/-- struveM primitive asymptotic. -/
@[dlmf 11.6.E4]
theorem struveM_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

section LargeOrder

open scoped Interval

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ s sin δ` for `s > 0`. -/
lemma mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ) {s : ℝ}
    (hs : 0 < s) : s * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (s * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs.le) hc, sq_nonneg (r * Real.cos θ),
        sq_nonneg (r * Real.sin θ), mul_le_mul_of_nonneg_left hsd (sq_nonneg s)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]
        have : 0 ≤ Real.sin (π - |θ|) := Real.sin_nonneg_of_nonneg_of_le_pi
          (by linarith [Complex.abs_arg_le_pi ν]) (by linarith [abs_nonneg θ])
        exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (r + s * Real.cos θ) ^ 2 + s ^ 2 * Real.sin θ ^ 2 := by
        linear_combination (r ^ 2 - s ^ 2) * hcs
      rw [e]
      nlinarith [sq_nonneg (r + s * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg s)]
  calc s * Real.sin δ ≤ |s * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((s * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- `‖1/Γ(s₀ + k)‖ ≤ ‖1/Γ(s₀)‖ / ((3/2) sin δ)^k` for `s₀ = ν + N + 3/2` in the sector. -/
lemma norm_inv_Gamma_add_nat_le_of_arg {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π)
    (harg : |arg ν| ≤ π - δ) (N k : ℕ) :
    ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ / (3 / 2 * Real.sin δ) ^ k := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hρ : 0 < 3 / 2 * Real.sin δ := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    set s := ν + N + 3 / 2 + k with hs
    have hsn : (N + 3 / 2 + k : ℝ) * Real.sin δ ≤ ‖s‖ := by
      have := mul_sin_le_norm_add_ofReal hδ harg (s := N + 3 / 2 + k) (by positivity)
      rw [hs]; convert this using 2; push_cast; ring
    have hs1 : 3 / 2 * Real.sin δ ≤ ‖s‖ := le_trans (by
      have : (3 / 2 : ℝ) ≤ N + 3 / 2 + k := by
        have := (N.cast_nonneg : (0 : ℝ) ≤ N); have := (k.cast_nonneg : (0 : ℝ) ≤ k); linarith
      nlinarith) hsn
    have hs0 : s ≠ 0 := by
      intro h; rw [h, norm_zero] at hs1; linarith
    have hrec := AAR.Hypergeometric.inv_Gamma_eq_mul_inv_Gamma_add_one s
    have h1 : (Gamma (s + 1))⁻¹ = (Gamma s)⁻¹ / s := by
      rw [hrec]; field_simp
    rw [show ν + N + 3 / 2 + ((k + 1 : ℕ) : ℂ) = s + 1 by rw [hs]; push_cast; ring, h1,
      norm_div, pow_succ, ← div_div]
    exact div_le_div₀ (by positivity) ih hρ hs1

/-- Tail bound for the Struve series in the order variable. -/
lemma struve_series_tail_isBigO {z : ℂ} (hz : z ≠ 0) {ε : ℂ} (hε : ‖ε‖ = 1) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) (S : ℂ → ℂ)
    (hS : ∀ ν, HasSum (fun n : ℕ => ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) (S ν)) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * S ν - (z / 2) ^ (ν + 1) *
      ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n) =O[sector (π - δ)]
      (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + N + 3 / 2)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set ρ := 3 / 2 * Real.sin δ with hρdef
  have hρ : 0 < ρ := by positivity
  set q := ‖z / 2‖ with hq
  have hq0 : 0 < q := norm_pos_iff.mpr (div_ne_zero hz two_ne_zero)
  set a : ℕ → ℝ := fun k => q ^ (2 * (k + N)) / (Real.Gamma ((k + N : ℕ) + 3 / 2) * ρ ^ k)
    with hadef
  have hΓpos : ∀ n : ℕ, 0 < Real.Gamma ((n : ℝ) + 3 / 2) := fun n =>
    Real.Gamma_pos_of_pos (by positivity)
  have hapos : ∀ k, 0 < a k := fun k => by rw [hadef]; have := hΓpos (k + N); positivity
  have hsum : Summable a := by
    refine summable_of_ratio_test_tendsto_lt_one (l := 0) zero_lt_one
      (Eventually.of_forall fun k => (hapos k).ne') ?_
    have hratio : ∀ k : ℕ, ‖a (k + 1)‖ / ‖a k‖ = q ^ 2 / ρ * ((k + N : ℝ) + 3 / 2)⁻¹ := by
      intro k
      rw [Real.norm_of_nonneg (hapos _).le, Real.norm_of_nonneg (hapos _).le, hadef]
      simp only
      have hG : Real.Gamma (((k + 1 + N : ℕ) : ℝ) + 3 / 2) =
          ((k + N : ℝ) + 3 / 2) * Real.Gamma (((k + N : ℕ) : ℝ) + 3 / 2) := by
        rw [show (((k + 1 + N : ℕ) : ℝ) + 3 / 2) = ((k + N : ℕ) : ℝ) + 3 / 2 + 1 by
          push_cast; ring, Real.Gamma_add_one (by positivity)]
        push_cast; ring
      rw [hG, show 2 * (k + 1 + N) = 2 * (k + N) + 2 by ring, pow_add, pow_succ]
      have := hΓpos (k + N)
      have : (0 : ℝ) < (k + N : ℝ) + 3 / 2 := by positivity
      field_simp
      ring
    simp_rw [hratio]
    rw [show (0 : ℝ) = q ^ 2 / ρ * 0 by ring]
    refine tendsto_const_nhds.mul (tendsto_inv_atTop_zero.comp ?_)
    exact tendsto_atTop_add_const_right _ _ (tendsto_natCast_atTop_atTop.atTop_add
      tendsto_const_nhds)
  set A := ∑' k, a k
  refine IsBigO.of_bound A ?_
  rw [AAR.DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨-, harg⟩ := hν
  have htail : S ν - ∑ n ∈ Finset.range N, ε ^ n * (z / 2) ^ (2 * n) * struveCoeff ν n =
      ∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N) := by
    rw [← (hS ν).tsum_eq, ← (hS ν).summable.sum_add_tsum_nat_add N]; ring
  have hbd : ∀ k, ‖ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) * struveCoeff ν (k + N)‖ ≤
      ‖(Gamma (ν + N + 3 / 2))⁻¹‖ * a k := by
    intro k
    have hG := norm_inv_Gamma_add_nat_le_of_arg hδ hδπ harg N k
    rw [norm_mul, norm_mul, norm_pow, norm_pow, hε, one_pow, one_mul, struveCoeff, one_div,
      mul_inv, norm_mul, show ((k + N : ℕ) : ℂ) + 3 / 2 = (((k + N : ℕ) + 3 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, ← ofReal_inv, Complex.norm_real,
      Real.norm_of_nonneg (inv_nonneg.mpr (hΓpos _).le),
      show ((k + N : ℕ) : ℂ) + ν + 3 / 2 = ν + N + 3 / 2 + k by push_cast; ring, hadef]
    simp only
    rw [← hq]
    calc q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          ‖(Gamma (ν + N + 3 / 2 + k))⁻¹‖)
        ≤ q ^ (2 * (k + N)) * ((Real.Gamma ((k + N : ℕ) + 3 / 2))⁻¹ *
          (‖(Gamma (ν + N + 3 / 2))⁻¹‖ / ρ ^ k)) := by gcongr
      _ = _ := by field_simp
  have hT := tsum_of_norm_bounded ((hsum.hasSum).mul_left ‖(Gamma (ν + N + 3 / 2))⁻¹‖) hbd
  rw [← mul_sub, htail, norm_mul, norm_div]
  calc ‖(z / 2) ^ (ν + 1)‖ * ‖∑' k, ε ^ (k + N) * (z / 2) ^ (2 * (k + N)) *
        struveCoeff ν (k + N)‖
      ≤ ‖(z / 2) ^ (ν + 1)‖ * (‖(Gamma (ν + N + 3 / 2))⁻¹‖ * A) := by gcongr
    _ = _ := by rw [norm_inv]; ring

/-- In the sector `|arg ν| ≤ π - δ`, `‖ν + s‖ ≥ ‖ν‖ sin δ` for `s ≥ 0`. -/
lemma norm_mul_sin_le_norm_add_ofReal {ν : ℂ} {δ : ℝ} (hδ : 0 < δ) (harg : |arg ν| ≤ π - δ)
    {s : ℝ} (hs : 0 ≤ s) : ‖ν‖ * Real.sin δ ≤ ‖ν + s‖ := by
  set θ := arg ν
  set r := ‖ν‖
  have hre : ν.re = r * Real.cos θ := (norm_mul_cos_arg ν).symm
  have him : ν.im = r * Real.sin θ := (norm_mul_sin_arg ν).symm
  have hr0 : 0 ≤ r := norm_nonneg _
  have hsq : ‖ν + s‖ ^ 2 = (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, normSq_apply, add_re, add_im, ofReal_re, ofReal_im, add_zero, hre, him]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  have hkey : (r * Real.sin δ) ^ 2 ≤ ‖ν + s‖ ^ 2 := by
    rw [hsq]
    have hsd := Real.sin_sq_le_one δ
    rcases le_or_gt 0 (Real.cos θ) with hc | hc
    · nlinarith [mul_nonneg (mul_nonneg hr0 hs) hc, sq_nonneg s,
        mul_le_mul_of_nonneg_left hsd (sq_nonneg r)]
    · have hθ : π / 2 < |θ| := by
        by_contra h; push Not at h
        have := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (x := θ)
          (by linarith [neg_abs_le θ]) (by linarith [le_abs_self θ])
        linarith
      have h1 : Real.sin δ ≤ Real.sin (π - |θ|) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
          (by linarith)
      have hδ0 : 0 ≤ Real.sin δ :=
        Real.sin_nonneg_of_nonneg_of_le_pi hδ.le (by linarith [abs_nonneg θ])
      have h2 : Real.sin (π - |θ|) ^ 2 = Real.sin θ ^ 2 := by
        rw [Real.sin_pi_sub]
        rcases le_total 0 θ with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, Real.sin_neg, neg_sq]
      have h3 : Real.sin δ ^ 2 ≤ Real.sin θ ^ 2 := by
        rw [← h2]; exact pow_le_pow_left₀ hδ0 h1 2
      have e : (r * Real.cos θ + s) ^ 2 + (r * Real.sin θ) ^ 2 =
          (s + r * Real.cos θ) ^ 2 + r ^ 2 * Real.sin θ ^ 2 := by ring
      rw [e]
      nlinarith [sq_nonneg (s + r * Real.cos θ), mul_le_mul_of_nonneg_left h3 (sq_nonneg r)]
  calc r * Real.sin δ ≤ |r * Real.sin δ| := le_abs_self _
    _ = Real.sqrt ((r * Real.sin δ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (‖ν + s‖ ^ 2) := Real.sqrt_le_sqrt hkey
    _ = ‖ν + s‖ := Real.sqrt_sq (norm_nonneg _)

/-- Shifting a point of the sector to the right keeps it in the slit plane. -/
lemma add_ofReal_mem_slitPlane_of_arg {ν : ℂ} (hν : ν ≠ 0) {δ : ℝ} (hδ : 0 < δ)
    (harg : |arg ν| ≤ π - δ) {s : ℝ} (hs : 0 ≤ s) : ν + s ∈ slitPlane := by
  have hslit : ν ∈ slitPlane := mem_slitPlane_iff_arg.mpr
    ⟨fun h => by rw [h, abs_of_pos Real.pi_pos] at harg; linarith, hν⟩
  rcases mem_slitPlane_iff.mp hslit with h | h
  · exact Or.inl (by simp; linarith)
  · exact Or.inr (by simpa using h)

/-- `log (ν + c) - log ν = ∫₀^c ds / (ν + s)` along a horizontal segment in the slit plane. -/
lemma log_add_ofReal_sub_log {ν : ℂ} (hν : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane) {c : ℝ}
    (hc : 0 ≤ c) : log (ν + c) - log ν = ∫ s in (0 : ℝ)..c, (ν + s)⁻¹ := by
  have hd : ∀ s ∈ [[0, c]], HasDerivAt (fun s : ℝ => log (ν + s)) (ν + s)⁻¹ s := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    have h1 : HasDerivAt (fun s : ℝ => ν + (s : ℂ)) 1 s := by
      simpa using ((hasDerivAt_id (s : ℂ)).const_add ν).comp_ofReal
    have h := h1.clog_real (hν s hs.1)
    simpa using h
  have hcont : ContinuousOn (fun s : ℝ => (ν + s)⁻¹) [[0, c]] := by
    intro s hs
    rw [uIcc_of_le hc] at hs
    exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
      (slitPlane_ne_zero (hν s hs.1))).continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hcont.intervalIntegrable]
  simp

/-- `log (z/2) = log z - log 2`. -/
lemma log_div_two_eq {z : ℂ} (hz : z ≠ 0) : log (z / 2) = log z - log 2 := by
  have h2 : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  apply Complex.ext
  · rw [log_re, sub_re, log_re, h2, ← ofReal_log (by norm_num), ofReal_re, ← h2, norm_div,
      Complex.norm_ofNat, Real.log_div (norm_ne_zero_iff.mpr hz) (by norm_num)]
  · rw [log_im, sub_im, log_im, h2, ← ofReal_log (by norm_num), ofReal_im, sub_zero, ← h2,
      div_eq_mul_inv, show (2 : ℂ)⁻¹ = ((2⁻¹ : ℝ) : ℂ) by push_cast; rfl,
      arg_mul_real (by norm_num)]

lemma tendsto_norm_sector (α : ℝ) : Tendsto (fun ν : ℂ => ‖ν‖) (sector α) atTop :=
  tendsto_comap.mono_left inf_le_left

/-- The Stirling correction in the leading large-order term tends to `0`. -/
lemma tendsto_struve_stirling_exponent {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    Tendsto (fun ν : ℂ => (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 -
      AAR.Gamma.binetMu (ν + 3 / 2)) (sector (π - δ)) (𝓝 0) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  have hcos : 0 < 1 - Real.cos δ := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hδπ.le hδ
    rw [Real.cos_zero] at this; linarith
  set C := 3 / 2 / Real.sin δ + 1 / (6 * (1 - Real.cos δ)) with hC
  have hb : Tendsto (fun ν : ℂ => C * ‖ν‖⁻¹) (sector (π - δ)) (𝓝 0) := by
    simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul C
  refine squeeze_zero_norm' ?_ hb
  rw [AAR.DLMF.sector, eventually_inf_principal]
  filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))]
    with ν hν0 hν
  obtain ⟨hν, harg⟩ := hν
  set r := ‖ν‖ with hr
  have hshift : ∀ s : ℝ, 0 ≤ s → ν + s ∈ slitPlane := fun s hs =>
    add_ofReal_mem_slitPlane_of_arg hν hδ harg hs
  -- the logarithmic part
  have hlog := log_add_ofReal_sub_log hshift (c := 3 / 2) (by norm_num)
  push_cast at hlog
  have hA : (ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 =
      ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) := by
    have hint : IntervalIntegrable (fun s : ℝ => (ν + s)⁻¹) volume 0 (3 / 2) := by
      refine ContinuousOn.intervalIntegrable fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      exact ((continuous_const.add continuous_ofReal).continuousAt.inv₀
        (slitPlane_ne_zero (hshift s hs.1))).continuousWithinAt
    have h1 : ∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s) =
        ∫ s in (0 : ℝ)..(3 / 2), (1 - (ν + 1) * (ν + s)⁻¹) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le (by norm_num)] at hs
      have := slitPlane_ne_zero (hshift s hs.1)
      field_simp
      ring
    rw [h1, intervalIntegral.integral_sub intervalIntegrable_const (hint.const_mul _),
      intervalIntegral.integral_const_mul, ← hlog]
    simp
    ring
  have hAb : ‖∫ s in (0 : ℝ)..(3 / 2), ((s : ℂ) - 1) / (ν + s)‖ ≤
      1 / (r * Real.sin δ) * |3 / 2 - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun s hs => ?_
    rw [uIoc_of_le (by norm_num)] at hs
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := s) hs.1.le
    have h2 : ‖(s : ℂ) - 1‖ ≤ 1 := by
      rw [show (s : ℂ) - 1 = ((s - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_eq_abs, abs_le]
      constructor <;> linarith [hs.1, hs.2]
    rw [norm_div]
    have hp : 0 < r * Real.sin δ := by positivity
    calc ‖(s : ℂ) - 1‖ / ‖ν + s‖ ≤ 1 / ‖ν + s‖ := by gcongr
      _ ≤ 1 / (r * Real.sin δ) := by gcongr
  -- the Binet part
  have hw : ν + 3 / 2 ∈ slitPlane := by simpa using hshift (3 / 2) (by norm_num)
  have hμ := AAR.Gamma.norm_binetMu_le hw
  have hcosθ : -Real.cos δ ≤ Real.cos (arg ν) := by
    rw [← Real.cos_pi_sub, ← Real.cos_abs (arg ν)]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) harg
  have hre : ν.re = r * Real.cos (arg ν) := (norm_mul_cos_arg ν).symm
  have hwre : r * (1 - Real.cos δ) ≤ ‖ν + 3 / 2‖ + (ν + 3 / 2).re := by
    have h1 : r ≤ ‖ν + 3 / 2‖ + 3 / 2 := by
      have := norm_add_le (ν + 3 / 2) (-(3 / 2 : ℂ))
      simp only [add_neg_cancel_right, norm_neg] at this
      norm_num at this ⊢; linarith
    have h2 : (ν + 3 / 2).re = ν.re + 3 / 2 := by simp
    rw [h2, hre]
    nlinarith
  have hμb : ‖AAR.Gamma.binetMu (ν + 3 / 2)‖ ≤ 1 / (6 * (r * (1 - Real.cos δ))) :=
    hμ.trans (one_div_le_one_div_of_le (by positivity) (by linarith))
  rw [hA]
  refine (norm_sub_le _ _).trans ?_
  have e : C * r⁻¹ = 1 / (r * Real.sin δ) * |3 / 2 - 0| + 1 / (6 * (r * (1 - Real.cos δ))) := by
    rw [hC, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2 - 0)]
    field_simp
    ring
  rw [e]
  exact add_le_add hAb hμb

/-- The leading term of the Struve series written through Binet's formula. -/
lemma struve_lead_eq {z : ℂ} (hz : z ≠ 0) {ν : ℂ} (hν : ν ≠ 0) (hw : ν + 3 / 2 ∈ slitPlane) :
    (z / 2) ^ (ν + 1) * struveCoeff ν 0 =
      z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) *
        exp ((ν + 1) * (log ν - log (ν + 3 / 2)) + 3 / 2 - AAR.Gamma.binetMu (ν + 3 / 2)) := by
  have hz2 : z / 2 ≠ 0 := div_ne_zero hz two_ne_zero
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hG32 : Gamma (3 / 2) = exp (log π * (1 / 2)) / exp (log 2) := by
    rw [show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num, Complex.Gamma_add_one _ (by norm_num),
      Complex.Gamma_one_half_eq, cpow_def_of_ne_zero hπ, exp_log two_ne_zero]
    ring
  have hGw := AAR.Gamma.Gamma_eq_exp_binetExponent hw
  have hl2π : log (2 * π : ℂ) = log 2 + log π := by
    rw [show (2 * π : ℂ) = ((2 * π : ℝ) : ℂ) by push_cast; ring, ← ofReal_log (by positivity),
      Real.log_mul (by norm_num) Real.pi_ne_zero, ofReal_add, ofReal_log (by norm_num),
      ofReal_log Real.pi_pos.le]
    norm_num
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) = exp (log 2 * (1 / 2)) := by
    rw [Real.sqrt_eq_rpow, ofReal_cpow (by norm_num), cpow_def_of_ne_zero (by norm_num)]
    push_cast; ring_nf
  have hpre : z / (π * ν * Real.sqrt 2) = exp (log z - log π - log ν - log 2 * (1 / 2)) := by
    rw [Complex.exp_sub, Complex.exp_sub, Complex.exp_sub, exp_log hz, exp_log hπ, exp_log hν,
      ← hs2]
    field_simp
  rw [hpre, struveCoeff, Nat.cast_zero, zero_add, zero_add, hG32, hGw, AAR.Gamma.binetExponent,
    hl2π, cpow_def_of_ne_zero hz2, log_div_two_eq hz]
  simp only [div_eq_mul_inv, one_mul, ← Complex.exp_neg, ← Complex.exp_add]
  congr 1
  ring

/-- `(z/2)^{ν+1} / (Γ(3/2) Γ(ν+3/2))` has the leading behaviour of DLMF 11.6.5. -/
lemma struve_lead_isEquivalent {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => (z / 2) ^ (ν + 1) * struveCoeff ν 0) ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  refine isEquivalent_of_tendsto_one ?_
  have h := (Complex.continuous_exp.tendsto 0).comp (tendsto_struve_stirling_exponent hδ hδπ)
  rw [Complex.exp_zero] at h
  refine h.congr' ?_
  rw [EventuallyEq, AAR.DLMF.sector, eventually_inf_principal]
  refine Eventually.of_forall fun ν hν => ?_
  obtain ⟨hν0, harg⟩ := hν
  have hw : ν + 3 / 2 ∈ slitPlane := by
    simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num)
  have hg : z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) ≠ 0 := by
    refine mul_ne_zero (div_ne_zero hz (mul_ne_zero (mul_ne_zero ?_ hν0) ?_)) (exp_ne_zero _)
    · exact ofReal_ne_zero.mpr Real.pi_ne_zero
    · exact ofReal_ne_zero.mpr (by positivity)
  simp only [Function.comp_apply, Pi.div_apply]
  rw [struve_lead_eq hz hν0 hw, mul_div_cancel_left₀ _ hg]

/-- From the first term of the order expansion to the leading behaviour of DLMF 11.6.5. -/
lemma isEquivalent_of_struve_order_expansion {f : ℂ → ℂ} {z : ℂ} (hz : z ≠ 0) {δ : ℝ}
    (hδ : 0 < δ) (hδπ : δ < π)
    (h : (fun ν : ℂ => f ν - (z / 2) ^ (ν + 1) * struveCoeff ν 0) =O[sector (π - δ)]
      fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) :
    f ~[sector (π - δ)]
      fun ν => z / (π * ν * Real.sqrt 2) * exp (ν * (1 + log z - log 2 - log ν)) := by
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ hδπ
  set lead : ℂ → ℂ := fun ν => (z / 2) ^ (ν + 1) * struveCoeff ν 0 with hlead
  set k : ℂ → ℂ := fun ν => Gamma (3 / 2) / (ν + 3 / 2) with hk
  have hk0 : Tendsto k (sector (π - δ)) (𝓝 0) := by
    have hb : Tendsto (fun ν : ℂ => ‖Gamma (3 / 2)‖ / Real.sin δ * ‖ν‖⁻¹) (sector (π - δ))
        (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (tendsto_norm_sector (π - δ))).const_mul
        (‖Gamma (3 / 2)‖ / Real.sin δ)
    refine squeeze_zero_norm' ?_ hb
    rw [AAR.DLMF.sector, eventually_inf_principal]
    filter_upwards [tendsto_comap.eventually (eventually_gt_atTop (0 : ℝ))] with ν hν0 hν
    obtain ⟨-, harg⟩ := hν
    have h1 := norm_mul_sin_le_norm_add_ofReal hδ harg (s := 3 / 2) (by norm_num)
    push_cast at h1
    rw [hk, norm_div]
    have hp : 0 < ‖ν‖ * Real.sin δ := by positivity
    calc ‖Gamma (3 / 2)‖ / ‖ν + 3 / 2‖ ≤ ‖Gamma (3 / 2)‖ / (‖ν‖ * Real.sin δ) := by gcongr
      _ = _ := by field_simp
  have hko : k =o[sector (π - δ)] fun _ => (1 : ℂ) := (isLittleO_one_iff ℂ).mpr hk0
  have hrem : (fun ν : ℂ => (z / 2) ^ (ν + 1) / Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2)) =ᶠ[sector (π - δ)]
      fun ν => lead ν * k ν := by
    rw [EventuallyEq, AAR.DLMF.sector, eventually_inf_principal]
    refine Eventually.of_forall fun ν hν => ?_
    obtain ⟨hν0, harg⟩ := hν
    have hw0 : ν + 3 / 2 ≠ 0 := slitPlane_ne_zero (by
      simpa using add_ofReal_mem_slitPlane_of_arg hν0 hδ harg (s := 3 / 2) (by norm_num))
    have hG32 : Gamma (3 / 2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by norm_num)
    have hrec := AAR.Hypergeometric.inv_Gamma_eq_mul_inv_Gamma_add_one (ν + 3 / 2)
    have h5 : (Gamma (ν + ((1 : ℕ) : ℂ) + 3 / 2))⁻¹ = (Gamma (ν + 3 / 2))⁻¹ / (ν + 3 / 2) := by
      rw [show ν + ((1 : ℕ) : ℂ) + 3 / 2 = ν + 3 / 2 + 1 by push_cast; ring, eq_div_iff hw0,
        mul_comm, ← hrec]
    simp only [hlead, hk, struveCoeff, Nat.cast_zero, zero_add]
    rw [div_eq_mul_inv, h5]
    field_simp
  have hE : (fun ν => f ν - lead ν) =o[sector (π - δ)] lead := by
    have h1 := h.trans_eventuallyEq hrem
    have h2 : (fun ν => lead ν * k ν) =o[sector (π - δ)] fun ν => lead ν * 1 :=
      (isBigO_refl lead _).mul_isLittleO hko
    simpa using h1.trans_isLittleO h2
  have hE' : f ~[sector (π - δ)] lead := hE
  exact hE'.trans (struve_lead_isEquivalent hz hδ hδπ)

end LargeOrder

/-- struveH large order. -/
@[dlmf 11.6.E5]
theorem struveH_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveH ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  simpa [struveH] using struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ 1
    (fun ν => struveHCore ν z) (fun ν => hasSum_struveHCore ν z)

/-- struveL large order. -/
@[dlmf 11.6.E5]
theorem struveL_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveL ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  refine isEquivalent_of_struve_order_expansion (slitPlane_ne_zero hz) hδ hδπ ?_
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ 1
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

/-- Finite polynomial formula for the saddle-endpoint coefficients. -/
def struveScaledCoeff (lam : ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (k+1), if k ≤ 2*j then
    ((2*j).factorial:ℂ)/(j.factorial:ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X-Polynomial.C (1/2+r:ℂ))).coeff (2*j-k) /
      lam^(2*j) else 0) / (k.factorial:ℂ)

/-- struveK scaled asymptotic. -/
@[dlmf 11.6.E6]
theorem struveK_scaled_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveM scaled asymptotic. -/
@[dlmf 11.6.E7]
theorem struveM_scaled_asymptotic {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => -Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveScaledCoeff initial. -/
@[dlmf 11.6.E8]
theorem struveScaledCoeff_initial (lam : ℂ) (hlam : lam ≠ 0) :
    struveScaledCoeff lam 0=1 ∧ struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧ struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam 4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4) := by
  simp only [struveScaledCoeff, Finset.sum_range_succ, Finset.prod_range_succ,
    Finset.sum_range_zero, Finset.prod_range_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Nat.factorial, Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_one,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X] <;>
    field_simp <;> ring

/-- struveL scaled equiv. -/
@[dlmf 11.6.E9]
theorem struveL_scaled_equiv {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => struveL ν (lam*ν)) ~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν)) := by
  sorry

section BinomialRemainder

open scoped Interval

/-- The binomial remainder `(1+u)^a - ∑_{k<m} (a choose k) u^k`. -/
def struveBinomRem (a : ℝ) (m : ℕ) (u : ℝ) : ℝ :=
  (1 + u) ^ a - ∑ k ∈ Finset.range m, Ring.choose a k * u ^ k

/-- `(k+1) (a choose k+1) = a (a-1 choose k)`. -/
lemma succ_mul_ring_choose_succ (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * Ring.choose a (k + 1) = a * Ring.choose (a - 1) k := by
  have h1 := AAR.Confluent.ring_choose_neg_eq_poch (-(a : ℂ)) (k + 1)
  have h2 := AAR.Confluent.ring_choose_neg_eq_poch (-(a : ℂ) + 1) k
  rw [neg_neg] at h1
  rw [show -(-(a : ℂ) + 1) = (a : ℂ) - 1 by ring] at h2
  apply Complex.ofReal_injective
  push_cast
  rw [h1, h2, poch_succ_left, Nat.factorial_succ]
  push_cast
  have hk : (k ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  field_simp
  ring

/-- `d/du` of the binomial remainder lowers `a` and `m` by one. -/
lemma hasDerivAt_struveBinomRem (a : ℝ) (m : ℕ) {u : ℝ} (hu : -1 < u) :
    HasDerivAt (struveBinomRem a (m + 1)) (a * struveBinomRem (a - 1) m u) u := by
  have h1 : HasDerivAt (fun u : ℝ => (1 + u) ^ a) (1 * a * (1 + u) ^ (a - 1)) u :=
    ((hasDerivAt_id u).const_add 1).rpow_const (Or.inl (by simp; linarith))
  have h2 : HasDerivAt (fun u : ℝ => ∑ k ∈ Finset.range (m + 1), Ring.choose a k * u ^ k)
      (∑ k ∈ Finset.range (m + 1), Ring.choose a k * (k * u ^ (k - 1))) u :=
    HasDerivAt.fun_sum fun k _ => (hasDerivAt_pow k u).const_mul _
  convert h1.sub h2 using 1
  · funext v; rfl
  unfold struveBinomRem
  rw [Finset.sum_range_succ', mul_sub, Finset.mul_sum]
  simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel, Nat.cast_succ]
  rw [one_mul]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← mul_assoc, ← succ_mul_ring_choose_succ]
  ring

/-- The binomial remainder is continuous on `[0, ∞)`. -/
lemma continuousOn_struveBinomRem (a : ℝ) (m : ℕ) : ContinuousOn (struveBinomRem a m) (Ici 0) := by
  refine ((continuousOn_const.add continuousOn_id).rpow_const fun x hx => Or.inl ?_).sub
    (by fun_prop)
  have : (0 : ℝ) ≤ x := hx
  simp; linarith

/-- The remainder after at least one term vanishes at `0`. -/
lemma struveBinomRem_succ_zero (a : ℝ) (m : ℕ) : struveBinomRem a (m + 1) 0 = 0 := by
  simp [struveBinomRem, Finset.sum_range_succ']

/-- Integral form of the binomial remainder. -/
lemma struveBinomRem_succ_eq_integral (a : ℝ) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    struveBinomRem a (m + 1) u = a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s := by
  rw [← intervalIntegral.integral_const_mul]
  have hint : IntervalIntegrable (fun s => a * struveBinomRem (a - 1) m s) volume 0 u :=
    ((continuousOn_struveBinomRem (a - 1) m).mono (by
      rw [uIcc_of_le hu]; exact Icc_subset_Ici_self)).intervalIntegrable.const_mul a
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := struveBinomRem a (m + 1)) (fun s hs => ?_)
    hint, struveBinomRem_succ_zero, sub_zero]
  rw [uIcc_of_le hu] at hs
  exact hasDerivAt_struveBinomRem a m (by linarith [hs.1])

/-- Sign and size of the binomial remainder for `a ≤ m` and `u ≥ 0`. -/
lemma struveBinomRem_bound (m : ℕ) : ∀ a : ℝ, a ≤ m → ∀ u : ℝ, 0 ≤ u →
    0 ≤ Ring.choose a m * struveBinomRem a m u ∧ |struveBinomRem a m u| ≤ |Ring.choose a m| * u ^ m := by
  induction m with
  | zero =>
    intro a ha u hu
    simp only [struveBinomRem, Finset.range_zero, Finset.sum_empty, sub_zero, Ring.choose_zero_right,
      one_mul, pow_zero, abs_one, mul_one]
    have h0 : 0 ≤ (1 + u) ^ a := Real.rpow_nonneg (by linarith) _
    refine ⟨h0, ?_⟩
    rw [abs_of_nonneg h0]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by simpa using ha)
  | succ m ih =>
    intro a ha u hu
    have ih' := ih (a - 1) (by push_cast at ha; linarith)
    have hc := succ_mul_ring_choose_succ a m
    have hm1 : (0 : ℝ) < m + 1 := by positivity
    have hc' : Ring.choose a (m + 1) = a * Ring.choose (a - 1) m / (m + 1) := by
      field_simp; linarith
    have hcont := (continuousOn_struveBinomRem (a - 1) m).mono (show Icc 0 u ⊆ Ici 0 from
      Icc_subset_Ici_self)
    have hint : IntervalIntegrable (struveBinomRem (a - 1) m) volume 0 u :=
      (hcont.mono (by rw [uIcc_of_le hu])).intervalIntegrable
    rw [struveBinomRem_succ_eq_integral a m hu, hc']
    constructor
    · have : a * Ring.choose (a - 1) m / (m + 1) * (a * ∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s)
          = a ^ 2 / (m + 1) * ∫ s in (0 : ℝ)..u, Ring.choose (a - 1) m * struveBinomRem (a - 1) m s := by
        rw [intervalIntegral.integral_const_mul]; ring
      rw [this]
      refine mul_nonneg (by positivity) (intervalIntegral.integral_nonneg hu fun s hs => ?_)
      exact (ih' s hs.1).1
    · rw [abs_mul, abs_div, abs_mul, abs_of_pos hm1]
      have hb : |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s| ≤
          |Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1)) := by
        refine (intervalIntegral.abs_integral_le_integral_abs hu).trans ?_
        have hmono : ∫ s in (0 : ℝ)..u, |struveBinomRem (a - 1) m s| ≤
            ∫ s in (0 : ℝ)..u, |Ring.choose (a - 1) m| * s ^ m :=
          intervalIntegral.integral_mono_on hu hint.abs ((by fun_prop : Continuous fun s : ℝ =>
            |Ring.choose (a - 1) m| * s ^ m).intervalIntegrable _ _) fun s hs => (ih' s hs.1).2
        refine hmono.trans (le_of_eq ?_)
        rw [intervalIntegral.integral_const_mul, integral_pow]
        simp
      calc |a| * |∫ s in (0 : ℝ)..u, struveBinomRem (a - 1) m s|
          ≤ |a| * (|Ring.choose (a - 1) m| * (u ^ (m + 1) / (m + 1))) := by gcongr
        _ = _ := by ring

end BinomialRemainder

/-- First omitted term bounds the real positive-argument remainder. -/
theorem struveK_remainder_sign {ν x : ℝ} (hx : 0 < x) (m : ℕ) (hm : ν ≤ m+1/2) :
    let R := struveK ν x-∑ k ∈ Finset.range m, struveAsymptoticTerm ν x k; R.im=0 ∧ R.re*(struveAsymptoticTerm ν x m).re ≥ 0 ∧ ‖R‖ ≤ ‖struveAsymptoticTerm ν x m‖ := by
  intro R
  set a : ℝ := ν - 1 / 2 with ha
  have hxC : 0 < ((x : ℂ)).re := by simpa using hx
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  set p : ℝ := 2 * (x / 2) ^ ν / (Real.sqrt π * Real.Gamma (ν + 1 / 2)) with hpdef
  have hp : 2 * ((x : ℂ) / 2) ^ (ν : ℂ) / (Real.sqrt π * Gamma ((ν : ℂ) + 1 / 2)) = (p : ℂ) := by
    rw [show (x : ℂ) / 2 = ((x / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity), show (ν : ℂ) + 1 / 2 = ((ν + 1 / 2 : ℝ) : ℂ) by
        push_cast; ring, Complex.Gamma_ofReal, hpdef]
    push_cast; ring
  set e : ℝ → ℝ := fun t => Real.exp (-x * t) with he
  set L : ℕ → ℝ := fun k => ((2 * k) ! : ℝ) / x ^ (2 * k + 1) with hLdef
  have hpow : ∀ (k : ℕ) (t : ℝ), 0 < t → t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) = (t ^ 2) ^ k := by
    intro k t ht
    rw [show ((2 * k + 1 : ℕ) : ℝ) - 1 = ((2 * k : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
  have hLint : ∀ k : ℕ, IntegrableOn (fun t => e t * (t ^ 2) ^ k) (Ioi 0) := fun k =>
    (integrableOn_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ)) (by positivity)
      hx).congr_fun (fun t ht => by simp only [he, hpow k t ht]) measurableSet_Ioi
  have hL : ∀ k : ℕ, ∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k = L k := by
    intro k
    have h := integral_exp_neg_mul_mul_rpow_sub_one (s := ((2 * k + 1 : ℕ) : ℝ))
      (by positivity) hx
    rw [show (∫ t in Ioi (0 : ℝ), e t * (t ^ 2) ^ k) = ∫ t in Ioi (0 : ℝ),
      Real.exp (-x * t) * t ^ (((2 * k + 1 : ℕ) : ℝ) - 1) from
      setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [he, hpow k t ht]), h, show ((2 * k + 1 : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) + 1 by push_cast; ring,
      Real.Gamma_nat_eq_factorial, Real.rpow_neg hx.le, show ((2 * k : ℕ) : ℝ) + 1 =
      ((2 * k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, hLdef]
    rfl
  have hpt : ∀ t : ℝ, ((e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) =
      exp (-(x : ℂ) * t) * (1 + (t : ℂ) ^ 2) ^ ((ν : ℂ) - 1 / 2) := by
    intro t
    rw [show (1 + (t : ℂ) ^ 2) = ((1 + t ^ 2 : ℝ) : ℂ) by push_cast; ring,
      show (ν : ℂ) - 1 / 2 = ((ν - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← ofReal_cpow (by positivity)]
    simp only [he, ha]
    push_cast
    ring_nf
  have hI0int : IntegrableOn (fun t => e t * (1 + t ^ 2) ^ a) (Ioi 0) := by
    refine (AAR.Bessel.integrableOn_yLaplaceKernel (ν : ℂ) hxC).norm.mono'
      ((by fun_prop : Continuous fun t : ℝ => Real.exp (-x * t)).aestronglyMeasurable.mul
        (Continuous.aestronglyMeasurable (by
          exact (continuous_const.add (continuous_pow 2)).rpow_const fun t =>
            Or.inl (by simp only [Pi.add_apply]; positivity)))) ?_
    refine Eventually.of_forall fun t => le_of_eq ?_
    rw [AAR.Bessel.yLaplaceKernel, ← hpt, Complex.norm_real]
  have hK : struveK ν x = (p : ℂ) * ((∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a : ℝ) : ℂ) := by
    rw [AAR.Bessel.struveK_eq_integral _ hxC, hp]
    have h := integral_complex_ofReal (f := fun t => e t * (1 + t ^ 2) ^ a)
      (μ := volume.restrict (Ioi 0))
    rw [← h]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [hpt]
  have hT : ∀ k : ℕ, struveAsymptoticTerm ν x k = ((p * (Ring.choose a k * L k) : ℝ) : ℂ) := by
    intro k
    rw [← struveK_coeff_eq (ν : ℂ) hx0 k, hp, Complex.Gamma_nat_eq_factorial,
      show (ν : ℂ) - 1 / 2 = (a : ℂ) by rw [ha]; push_cast; ring,
      ← Complex.ofReal_choose, hLdef]
    push_cast
    field_simp
  have hsumint : IntegrableOn (fun t => ∑ k ∈ Finset.range m,
      Ring.choose a k * (e t * (t ^ 2) ^ k)) (Ioi 0) :=
    integrable_finsetSum _ fun k _ => (hLint k).const_mul _
  have hJ : (∫ t in Ioi (0 : ℝ), e t * (1 + t ^ 2) ^ a) -
      ∑ k ∈ Finset.range m, Ring.choose a k * L k =
      ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) := by
    have h1 : ∑ k ∈ Finset.range m, Ring.choose a k * L k =
        ∫ t in Ioi (0 : ℝ), ∑ k ∈ Finset.range m, Ring.choose a k * (e t * (t ^ 2) ^ k) := by
      rw [integral_finsetSum _ fun k _ => (hLint k).const_mul _]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_const_mul, hL]
    rw [h1, ← integral_sub hI0int hsumint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  set J := ∫ t in Ioi (0 : ℝ), e t * struveBinomRem a m (t ^ 2) with hJdef
  have hJint : IntegrableOn (fun t => e t * struveBinomRem a m (t ^ 2)) (Ioi 0) := by
    refine (hI0int.sub hsumint).congr_fun (fun t _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, struveBinomRem, mul_sub, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : R = ((p * J : ℝ) : ℂ) := by
    simp only [R]
    rw [hK, Finset.sum_congr rfl fun k _ => hT k, ← hJ]
    push_cast
    rw [mul_sub, Finset.mul_sum]
  have ham : a ≤ m := by rw [ha]; linarith
  have hbd := struveBinomRem_bound m a ham
  have hL0 : 0 ≤ L m := by rw [hLdef]; positivity
  refine ⟨by rw [hR, ofReal_im], ?_, ?_⟩
  · rw [hR, hT m, ofReal_re, ofReal_re]
    have hcJ : 0 ≤ Ring.choose a m * J := by
      rw [hJdef, ← integral_const_mul]
      refine setIntegral_nonneg measurableSet_Ioi fun t _ => ?_
      have := (hbd (t ^ 2) (sq_nonneg t)).1
      have he0 : 0 ≤ e t := (Real.exp_pos _).le
      nlinarith
    have : p * J * (p * (Ring.choose a m * L m)) = p ^ 2 * L m * (Ring.choose a m * J) := by ring
    rw [this]; exact mul_nonneg (mul_nonneg (sq_nonneg _) hL0) hcJ
  · rw [hR, hT m, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_mul, abs_mul, abs_mul, abs_of_nonneg hL0]
    gcongr
    rw [hJdef, ← hL m, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (setIntegral_mono_on hJint.abs
      ((hLint m).const_mul _) measurableSet_Ioi fun t _ => ?_)
    rw [abs_mul, abs_of_nonneg (Real.exp_pos _).le]
    have := (hbd (t ^ 2) (sq_nonneg t)).2
    have he0 : 0 ≤ e t := (Real.exp_pos _).le
    calc e t * |struveBinomRem a m (t ^ 2)| ≤ e t * (|Ring.choose a m| * (t ^ 2) ^ m) :=
          mul_le_mul_of_nonneg_left this he0
      _ = _ := by ring

/-- angerF. -/
@[dlmf 11.11.E1]
def angerF (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+1)^2)

/-- angerG. -/
@[dlmf 11.11.E1]
def angerG (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+2)^2)

/-- angerFG poch. -/
@[dlmf 11.11.E1]
theorem angerFG_poch (ν : ℂ) (k : ℕ) :
    angerF ν k = (-4)^k*poch (1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k := by
  induction k with
  | zero => simp [angerF, angerG, poch_zero]
  | succ k ih =>
    rcases ih with ⟨ihF, ihG⟩
    have hF : angerF ν (k+1)=angerF ν k*(ν^2-(2*k+1)^2) := by
      simp [angerF, Finset.prod_range_succ]
    have hG : angerG ν (k+1)=angerG ν k*(ν^2-(2*k+2)^2) := by
      simp [angerG, Finset.prod_range_succ]
    rw [hF,hG,ihF,ihG,poch_succ,poch_succ,poch_succ,poch_succ,pow_succ]
    push_cast
    constructor <;> ring

/-- angerJ large argument. -/
@[dlmf 11.11.E2]
theorem angerJ_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerJ ν z-besselJ ν z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- weberE large argument. -/
@[dlmf 11.11.E3]
theorem weberE_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => weberE ν z+besselY ν z-(∑ k ∈ Finset.range N, -(1+cos (π*ν))/π*angerF ν k/z^(2*k+1)-ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA large argument. -/
@[dlmf 11.11.E4]
theorem angerA_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- Large orders separated from all integers. -/
def nonintegerOrderSector (ε : ℝ) : Filter ℂ :=
  sector π ⊓ 𝓟 {ν : ℂ | ∀ n : ℤ, ε ≤ ‖ν-n‖}

/-- angerJ large order. -/
@[dlmf 11.11.E5]
theorem angerJ_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- weberE large order. -/
@[dlmf 11.11.E6]
theorem weberE_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- One integration by parts against `e^{ωθ}` on `[0, π]`. -/
theorem integral_exp_mul_ibp {ω : ℂ} (hω : ω ≠ 0) {H H' : ℝ → ℂ}
    (hd : ∀ θ, HasDerivAt H (H' θ) θ) (hc : Continuous H') :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) =
      (exp (ω*π) * H π - H 0)/ω - (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
  have hv : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => exp (ω*θ)/ω) (exp (ω*θ)) θ := by
    intro θ _
    have := (((hasDerivAt_id (θ:ℝ)).ofReal_comp.const_mul ω).cexp).div_const ω
    refine this.congr_deriv ?_
    simp only [id, ofReal_one, mul_one]; field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hd θ) hv
    (hc.intervalIntegrable _ _) ((by fun_prop : Continuous fun θ : ℝ => exp (ω*θ)).intervalIntegrable _ _)
  have e1 : (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) = ∫ θ : ℝ in 0..π, H θ * exp (ω*θ) :=
    intervalIntegral.integral_congr fun θ _ => by ring
  have e2 : (∫ θ : ℝ in 0..π, H' θ * (exp (ω*θ)/ω)) =
      (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [e1, hibp, e2]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- `|∫₀^π e^{itθ} k| ≤ ∫₀^π |k|`. -/
theorem norm_integral_exp_I_mul_le (t : ℝ) (k : ℝ → ℂ) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ ∫ θ : ℝ in 0..π, ‖k θ‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_)
  simp only [norm_mul]
  rw [show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Derivatives of `θ ↦ exp (a sin θ)`. -/
theorem hasDerivAt_exp_mul_sin (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => exp (a*Real.sin θ)) (a*Real.cos θ*exp (a*Real.sin θ)) θ := by
  have := ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul a).cexp
  convert this using 1; ring

theorem hasDerivAt_exp_mul_sin_one (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => a*Real.cos θ*exp (a*Real.sin θ))
      ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) θ := by
  have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul a).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1; push_cast; ring

theorem hasDerivAt_exp_mul_sin_two (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))
      ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have h1 := (((hc.pow 2).const_mul (a^2)).sub (hs.const_mul a)).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; push_cast; ring

theorem integral_exp_mul_exp_sin_odd {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = -1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = -2/ω + (1/ω^2) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

theorem integral_exp_mul_exp_sin_even {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = 1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = 2*a/ω^2 - (1/ω^3) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ -
        a*Real.cos θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_two a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

/-- The Weber function as a combination of two exponential integrals. -/
theorem weberE_eq_exp_integrals (ν z : ℂ) :
    weberE ν z = 1/π * (I/2 * ((∫ θ : ℝ in 0..π, exp ((-I*ν)*θ) * exp ((I*z)*Real.sin θ)) -
      ∫ θ : ℝ in 0..π, exp ((I*ν)*θ) * exp ((-I*z)*Real.sin θ))) := by
  unfold weberE
  congr 1
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- A uniform bound for an integral against `e^{itθ}`. -/
theorem norm_integral_exp_I_mul_le_const (t : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : ∀ θ, ‖k θ‖ ≤ C) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ C * π := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun θ : ℝ => exp ((I*t)*θ) * k θ) (C := C) (fun θ _ => by
      rw [norm_mul, show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]; exact hk θ)
  rwa [sub_zero, abs_of_pos Real.pi_pos] at this

theorem exp_I_mul_odd_mul_pi (n : ℤ) : exp ((I*(2*n+1:ℂ))*π) = -1 := by
  rw [show (I*(2*n+1:ℂ))*π = n*(2*π*I) + π*I by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

theorem exp_I_mul_even_mul_pi (n : ℤ) : exp ((I*(2*n:ℂ))*π) = 1 := by
  rw [show (I*(2*n:ℂ))*π = n*(2*π*I) by ring, Complex.exp_int_mul_two_pi_mul_I]

theorem exp_neg_I_mul_odd_mul_pi (n : ℤ) : exp ((-I*(2*n+1:ℂ))*π) = -1 := by
  have := exp_I_mul_odd_mul_pi (-n-1)
  rw [← this]; congr 1; push_cast; ring

theorem exp_neg_I_mul_even_mul_pi (n : ℤ) : exp ((-I*(2*n:ℂ))*π) = 1 := by
  have := exp_I_mul_even_mul_pi (-n)
  rw [← this]; congr 1; push_cast; ring

/-- `E_{2n+1}(z) = 2/((2n+1)π) + O((2n+1)^{-2})`, uniformly in `n`. -/
theorem weberE_odd_bound (z : ℂ) : ∃ M : ℝ, ∀ n : ℤ,
    ‖weberE (2*n+1) z - 2/((2*n+1:ℂ)*π)‖ ≤ M / ((2*n+1:ℝ))^2 := by
  set K : ℝ := (‖z‖^2 + ‖z‖) * Real.exp ‖z‖
  have hH2 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)‖ ≤ K := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have h1 : ‖a^2*(Real.cos θ:ℂ)^2 - a*Real.sin θ‖ ≤ ‖z‖^2 + ‖z‖ := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha]
      have : |Real.cos θ|^2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ)]
      have hz := norm_nonneg z
      nlinarith [abs_nonneg (Real.sin θ)]
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  refine ⟨K * π / π, fun n => ?_⟩
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_odd hω1 (exp_neg_I_mul_odd_mul_pi n),
    integral_exp_mul_exp_sin_odd hω2 (exp_I_mul_odd_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n+1:ℂ))*θ) *
    (((I*z)^2*(Real.cos θ)^2 - (I*z)*Real.sin θ)*exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n+1:ℂ))*θ) *
    (((-I*z)^2*(Real.cos θ)^2 - (-I*z)*Real.sin θ)*exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH2 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH2 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((-2/(-I*(2*n+1:ℂ)) + 1/(-I*(2*n+1:ℂ))^2 * R1) -
      (-2/(I*(2*n+1:ℂ)) + 1/(I*(2*n+1:ℂ))^2 * R2))) - 2/((2*n+1:ℂ)*π) =
      (I/(2*π)) * (R2 - R1) / (t:ℂ)^2 := by
    rw [ht]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  rw [key, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖I/(2*(π:ℂ))‖ = 1/(2*π) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hI]
  have hsum : ‖R2 - R1‖ ≤ 2*(K*π) := (norm_sub_le _ _).trans (by linarith)
  have ht2 : 0 < t^2 := by positivity
  rw [div_le_div_iff_of_pos_right ht2]
  calc 1/(2*π) * ‖R2 - R1‖ ≤ 1/(2*π) * (2*(K*π)) := by gcongr
    _ = K * π / π := by field_simp

/-- `|2n+1| ≥ |n|` and `|2n| ≥ |n|` in real form. -/
theorem abs_two_mul_add_ge (n : ℤ) (e : ℝ) (he : e = 0 ∨ e = 1) :
    (|n| : ℝ) ≤ |2*(n:ℝ)+e| ∨ n = 0 := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inr h
  left
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : (1:ℤ) ≤ |n| := Int.one_le_abs h
    exact_mod_cast this
  rcases he with rfl | rfl
  · rw [add_zero, abs_mul]; norm_num; linarith [abs_nonneg (n:ℝ)]
  · have := abs_sub_abs_le_abs_sub (2*(n:ℝ)) (-1)
    rw [abs_mul, abs_two, abs_neg, abs_one, sub_neg_eq_add] at this
    linarith

theorem norm_sub_sub_le_add_add (A B C : ℂ) : ‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_sub_le A B])

/-- `E_{2n}(z) = 2z/(π(2n)²) + O(|z| (2n)^{-3})`, uniformly in `n ≠ 0`. -/
theorem weberE_even_bound (z : ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℤ, n ≠ 0 →
    ‖weberE (2*n) z - 2*z/(π*(2*n:ℂ)^2)‖ ≤ ‖z‖ * K / |(2*n:ℝ)|^3 := by
  set K0 : ℝ := (‖z‖^2 + 3*‖z‖ + 1) * Real.exp ‖z‖
  have hK0 : 0 ≤ K0 := by positivity
  have hH3 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)‖ ≤
        ‖z‖ * K0 := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have hz := norm_nonneg z
    have h1 : ‖a^3*(Real.cos θ:ℂ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ‖ ≤
        ‖z‖^3 + 3*‖z‖^2 + ‖z‖ := by
      refine (norm_sub_sub_le_add_add _ _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha, Complex.norm_ofNat]
      have hc3 : |Real.cos θ|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have hsc : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      have e1 : ‖z‖^3 * |Real.cos θ|^3 ≤ ‖z‖^3 := by
        calc _ ≤ ‖z‖^3 * 1 := by gcongr
          _ = _ := mul_one _
      have e2 : 3 * ‖z‖^2 * |Real.sin θ| * |Real.cos θ| ≤ 3*‖z‖^2 := by
        calc _ = 3 * ‖z‖^2 * (|Real.sin θ| * |Real.cos θ|) := by ring
          _ ≤ 3 * ‖z‖^2 * 1 := by gcongr
          _ = _ := mul_one _
      have e3 : ‖z‖ * |Real.cos θ| ≤ ‖z‖ := by
        calc _ ≤ ‖z‖ * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    calc _ ≤ (‖z‖^3 + 3*‖z‖^2 + ‖z‖) * Real.exp ‖z‖ :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = ‖z‖ * K0 := by simp only [K0]; ring
  refine ⟨K0, hK0, fun n hn => ?_⟩
  set t : ℝ := 2*n
  have ht : (2*n:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_even hω1 (exp_neg_I_mul_even_mul_pi n),
    integral_exp_mul_exp_sin_even hω2 (exp_I_mul_even_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n:ℂ))*θ) *
    (((I*z)^3*(Real.cos θ)^3 - 3*(I*z)^2*Real.sin θ*Real.cos θ - (I*z)*Real.cos θ)*
      exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n:ℂ))*θ) *
    (((-I*z)^3*(Real.cos θ)^3 - 3*(-I*z)^2*Real.sin θ*Real.cos θ - (-I*z)*Real.cos θ)*
      exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH3 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH3 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((2*(I*z)/(-I*(2*n:ℂ))^2 - 1/(-I*(2*n:ℂ))^3 * R1) -
      (2*(-I*z)/(I*(2*n:ℂ))^2 - 1/(I*(2*n:ℂ))^3 * R2))) - 2*z/(π*(2*n:ℂ)^2) =
      -(R1 + R2) / (2*π*(t:ℂ)^3) := by
    rw [ht]
    have e1 : (-I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e2 : (I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e3 : (-I*(t:ℂ))^3 = I*(t:ℂ)^3 := by linear_combination (-I*(t:ℂ)^3) * I_sq
    have e4 : (I*(t:ℂ))^3 = -(I*(t:ℂ)^3) := by linear_combination (I*(t:ℂ)^3) * I_sq
    rw [e1, e2, e3, e4]
    field_simp
    ring_nf
    simp only [I_sq]
    ring_nf
  rw [key]
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsum : ‖R1 + R2‖ ≤ 2*(‖z‖ * K0 * π) := (norm_add_le _ _).trans (by linarith)
  have ht3 : 0 < |t|^3 := by positivity
  rw [div_le_div_iff₀ (by positivity) ht3]
  nlinarith [Real.pi_pos]

/-- weberE large integer 0. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_0 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+0) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π)) := by
  obtain ⟨K, hK, hb⟩ := weberE_even_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (2/c + K*π/c + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  have h2c : 0 ≤ 2/c := by positivity
  have hKc : 0 ≤ K*π/c := by positivity
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn1; linarith
  set t : ℝ := 2*n
  set x : ℝ := |t|
  have hx : x = 2*|(n:ℝ)| := by simp only [x, t, abs_mul, abs_two]
  have hx2 : 2 ≤ x := by linarith
  have hxN : (N:ℝ) ≤ x := by linarith
  have hxc : 2/c ≤ x := by linarith
  have hxK : K*π/c ≤ x := by linarith
  have ht : (2*n:ℂ) = t := by simp [t]
  have htx : t^2 = x^2 := (sq_abs t).symm
  have hx0 : 0 < x := by linarith
  have hx21 : 0 < x^2 - 1 := by nlinarith
  rw [Pi.sub_apply, add_zero]
  set u := weberE (2*n) z
  set w : ℂ := 2*z/(π*(2*n:ℂ)^2)
  set v : ℂ := 2*z/((4*(n:ℂ)^2-1)*π)
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 fun h => by
    have : x = 0 := by simp only [x, h, abs_zero]
    linarith
  have hn4 : (4*(n:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) := by
    rw [← htx]; push_cast [t]; ring
  have hn4ne : (4*(n:ℂ)^2-1) ≠ 0 := by rw [hn4]; exact ofReal_ne_zero.2 hx21.ne'
  have hwv : w - v = -(2*z) / (π*(t:ℂ)^2*((x^2-1:ℝ):ℂ)) := by
    simp only [w, v]
    rw [ht, hn4]
    have : ((x^2-1:ℝ):ℂ) = (t:ℂ)^2 - 1 := by push_cast [← htx]; ring
    have h1 : ((x^2-1:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.2 hx21.ne'
    rw [this] at h1 ⊢
    field_simp
    ring
  have hnv : ‖v‖ = 2*‖z‖/((x^2-1)*π) := by
    simp only [v]
    rw [hn4, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le]
  have hnwv : ‖w - v‖ = 2*‖z‖/(π*x^2*(x^2-1)) := by
    rw [hwv, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  have huw : ‖u - w‖ ≤ ‖z‖ * K / x^3 := hb n hn0
  have htri : ‖u - v‖ ≤ ‖u - w‖ + ‖w - v‖ := by
    have := norm_add_le (u - w) (w - v); rwa [sub_add_sub_cancel] at this
  rw [hnv]
  refine htri.trans ?_
  rw [hnwv]
  have hzn := norm_nonneg z
  have e1 : K / x^3 ≤ c/((x^2-1)*π) := by
    have ha : K / x^3 ≤ c/(x^2*π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : K*π ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxK
      nlinarith [sq_nonneg x]
    refine ha.trans (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
    nlinarith [Real.pi_pos]
  have e2 : 2/(π*x^2*(x^2-1)) ≤ c/((x^2-1)*π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxc
    have : 2 ≤ c*x^2 := by nlinarith
    have hp : 0 < (x^2-1)*π := by positivity
    nlinarith
  refine (add_le_add huw le_rfl).trans ?_
  calc ‖z‖ * K / x^3 + 2*‖z‖/(π*x^2*(x^2-1)) = ‖z‖ * (K/x^3 + 2/(π*x^2*(x^2-1))) := by ring
    _ ≤ ‖z‖ * (c/((x^2-1)*π) + c/((x^2-1)*π)) := by gcongr
    _ = c * (2*‖z‖/((x^2-1)*π)) := by ring

/-- weberE large integer 1. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_1 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+1) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π)) := by
  obtain ⟨M, hM⟩ := weberE_odd_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (M * π / (2*c) + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htabs : M * π / (2*c) ≤ |t| := by
    rcases abs_two_mul_add_ge n 1 (Or.inr rfl) with h | h
    · linarith
    · subst h
      simp only [Int.cast_zero, abs_zero, mul_zero, zero_add, abs_one, t] at hnR ⊢
      have : (N:ℝ) ≤ 0 := hnR
      linarith
  have htpos : 0 < |t| := abs_pos.2 ht0
  have hv : ‖(2:ℂ)/((2*n+1:ℂ)*π)‖ = 2/(|t| * π) := by
    rw [ht, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hv, Pi.sub_apply]
  refine (hM n).trans ?_
  have hMle : M * π ≤ 2*c*|t| := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2*c)).1 htabs
    linarith
  rw [← sq_abs t, div_le_iff₀ (by positivity)]
  have : c * (2 / (|t| * π)) * |t|^2 = 2*c*|t|/π := by field_simp
  rw [this, le_div_iff₀ Real.pi_pos]
  linarith

/-- Coefficients in the scaled Anger–Weber expansion. -/
def angerScaledA : ℕ → ℂ → ℂ
  | 0 => fun lam => 1/(1+lam)
  | k+1 => fun lam => limUnder (𝓝[≠] lam) (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))

/-- Derivative of a quadratic divided by a power of `1 + l`. -/
theorem hasDerivAt_quadratic_div_pow (a b c : ℂ) (n : ℕ) {l : ℂ} (hl : 1+l ≠ 0) :
    HasDerivAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1))
      (((2*a*l+b)*(1+l)-(n+1)*(a*l^2+b*l+c))/(1+l)^(n+2)) l := by
  have hp : HasDerivAt (fun l : ℂ => a*l^2+b*l+c) (2*a*l+b) l := by
    convert (((hasDerivAt_pow 2 l).const_mul a).add ((hasDerivAt_id' l).const_mul b)).add_const c
      using 1
    simp; ring
  have hq : HasDerivAt (fun l : ℂ => (1+l)^(n+1)) ((n+1)*(1+l)^n) l := by
    convert ((hasDerivAt_id' l).const_add 1).pow (n+1) using 1
    simp
  convert hp.div hq (pow_ne_zero _ hl) using 1
  field_simp
  ring

/-- One step of the recursion for `angerScaledA`: if the `k`-th coefficient agrees with `g`
off `l = -1`, with derivatives `d`, `e`, then the removable limit defining the next
coefficient is the continuous closed form `G`. -/
theorem angerScaledA_succ_eq (k : ℕ) {g d e G : ℂ → ℂ}
    (hA : ∀ l, 1+l ≠ 0 → angerScaledA k l = g l)
    (hd : ∀ l, 1+l ≠ 0 → HasDerivAt g (d l) l)
    (he : ∀ l, 1+l ≠ 0 → HasDerivAt d (e l) l)
    (halg : ∀ l, 1+l ≠ 0 → l ≠ 1 → l/(1-l^2)*(l*e l+d l)/((2*k+1:ℂ)*(2*k+2)) = G l)
    (hG : ∀ l, 1+l ≠ 0 → ContinuousAt G l) {lam : ℂ} (hlam : 1+lam ≠ 0) :
    angerScaledA (k+1) lam = G lam := by
  have hU : IsOpen {l : ℂ | 1+l ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hAd : ∀ l, 1+l ≠ 0 → HasDerivAt (angerScaledA k) (d l) l := fun l hl =>
    (hd l hl).congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hl] with x hx using hA x hx)
  have hAe : ∀ l, 1+l ≠ 0 → iteratedDeriv 2 (angerScaledA k) l = e l := by
    intro l hl
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine ((he l hl).congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hl] with x hx using (hAd x hx).deriv
  have hev : ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0 ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (hU.mem_nhds hlam) :
      ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  show limUnder _ _ = _
  refine (((hG lam hlam).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_).limUnder_eq
  filter_upwards [hev] with l hl
  rw [hAe l hl.1, (hAd l hl.1).deriv, halg l hl.1 hl.2]

/-- angerScaledA initial. -/
@[dlmf 11.11.E9]
theorem angerScaledA_initial (lam : ℂ) (h : lam ≠ -1) :
    angerScaledA 1 lam = -lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
  have hlam : 1+lam ≠ 0 := fun h0 => h (by linear_combination h0)
  have hc : ∀ (a b c : ℂ) (n : ℕ) l, 1+l ≠ 0 → ContinuousAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1)) l :=
    fun a b c n l hl => (hasDerivAt_quadratic_div_pow a b c n hl).continuousAt
  have h1m : ∀ l : ℂ, 1+l ≠ 0 → l ≠ 1 → 1-l^2 ≠ 0 := fun l hl h1 => by
    have : 1-l ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    rw [show 1-l^2 = (1-l)*(1+l) by ring]; exact mul_ne_zero this hl
  have s1 : ∀ l, 1+l ≠ 0 → angerScaledA 1 l = (0*l^2+(-1/2)*l+0)/(1+l)^(3+1) := by
    intro l hl
    refine angerScaledA_succ_eq 0 (g := fun l => (0*l^2+0*l+1)/(1+l)^(0+1))
      (d := fun l => (0*l^2+0*l+(-1))/(1+l)^(1+1)) (e := fun l => (0*l^2+0*l+2)/(1+l)^(2+1))
      (fun l hl => by simp [angerScaledA]) (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 0 1 0 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 0 (-1) 1 hl using 1; field_simp; ring
    · have := h1m l hl h1; field_simp; ring
  have s2 : ∀ l, 1+l ≠ 0 → angerScaledA 2 l = ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1) := by
    intro l hl
    refine angerScaledA_succ_eq 1 (g := fun l => (0*l^2+(-1/2)*l+0)/(1+l)^(3+1))
      (d := fun l => (0*l^2+(3/2)*l+(-1/2))/(1+l)^(4+1))
      (e := fun l => (0*l^2+(-6)*l+4)/(1+l)^(5+1))
      s1 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 (-1/2) 0 3 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 (3/2) (-1/2) 4 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
  have s3 : angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
    refine angerScaledA_succ_eq 2 (g := fun l => ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1))
      (d := fun l => ((-45/24)*l^2+1*l+(-1/24))/(1+l)^(7+1))
      (e := fun l => ((270/24)*l^2+(-258/24)*l+(32/24))/(1+l)^(8+1))
      (G := fun l => -(225*l^3-54*l^2+l)/(720*(1+l)^10))
      s2 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => ?_) hlam
    · convert hasDerivAt_quadratic_div_pow (9/24) (-1/24) 0 6 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow (-45/24) 1 (-1/24) 7 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
    · exact ((by fun_prop : Continuous fun l : ℂ => -(225*l^3-54*l^2+l)).continuousAt).div
        (by fun_prop) (mul_ne_zero (by norm_num) (pow_ne_zero _ hl))
  refine ⟨?_, ?_, s3⟩
  · rw [s1 lam hlam]; field_simp; ring
  · rw [s2 lam hlam]; field_simp; ring

/-- angerA scaled 8. -/
@[dlmf 11.11.E8]
theorem angerA_scaled_8 {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (1*ν) (lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA scaled 10. -/
@[dlmf 11.11.E10]
theorem angerA_scaled_10 {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (-1*ν) (lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerMu. -/
@[dlmf 11.11.E12]
def angerMu (lam : ℂ) : ℂ :=
  (1-lam^2)^(1/2:ℂ)-log ((1+(1-lam^2)^(1/2:ℂ))/lam)

/-- Coefficients of the saddle expansion, with existence provided by the expansion theorem. -/
def angerScaledB (lam : ℝ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((π*v/2:ℂ)^(1/2:ℂ))*exp (v*angerMu lam)*angerA (-v) (lam*v)) k / poch (1/2) k

/-- angerA scaled saddle. -/
@[dlmf 11.11.E11]
theorem angerA_scaled_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp (ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- angerScaledB initial. -/
@[dlmf 11.11.E13]
theorem angerScaledB_initial {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    angerScaledB lam 0 = (1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧ angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ)) := by
  sorry

/-- angerA scaled outer equiv. -/
@[dlmf 11.11.E14]
theorem angerA_scaled_outer_equiv {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1))) := by
  sorry

/-- angerA scaled inner equiv. -/
@[dlmf 11.11.E15]
theorem angerA_scaled_inner_equiv {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)) := by
  sorry

/-- angerA turning equiv. -/
@[dlmf 11.11.E16]
theorem angerA_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) ν) ~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- angerJ turning equiv. -/
@[dlmf 11.11.E18]
theorem angerJ_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerJ ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(2/3:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- weberE turning equiv. -/
@[dlmf 11.11.E19]
theorem weberE_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => weberE ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- Turning-point approximation uniform on bounded complex transition parameters; positive real order. -/
@[dlmf 11.11.E17]
theorem angerA_turning_uniform (M : ℝ) (hM : 0 < M) :
    (fun p : ℝ × ℂ => angerA (-p.1) (p.1+p.2*(p.1:ℂ)^(1/3:ℂ))-2^(1/3:ℂ)*(p.1:ℂ)^(-1/3:ℂ)*scorerHi (-2^(1/3:ℂ)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℂ | ‖p.2‖ ≤ M}] (fun p : ℝ × ℂ => (p.1:ℂ)^(-1:ℤ)) := by
  sorry

/-- The recurrence in DLMF 11.11(iii) has a removable singularity at lambda=1. -/
theorem angerScaledA_removable (k : ℕ) {lam : ℂ} (hlam : lam ≠ -1) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))
      (𝓝[≠] lam) (𝓝 (angerScaledA (k+1) lam)) := by
  sorry

/-- The convergent defining H series is also a generalized large-order expansion, DLMF 11.6(ii). -/
theorem struveH_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveH ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (-1)^n*(z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) :=
  struve_series_tail_isBigO (slitPlane_ne_zero hz) (by simp) hδ hδπ N (fun ν => struveHCore ν z)
    (fun ν => hasSum_struveHCore ν z)

/-- The corresponding generalized L expansion in DLMF 11.6(ii). -/
theorem struveL_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveL ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  have h := struve_series_tail_isBigO (slitPlane_ne_zero hz) (ε := 1) (by simp) hδ hδπ N
    (fun ν => struveLCore ν z) (fun ν => by simpa using hasSum_struveLCore ν z)
  simpa [struveL] using h

end AAR.Struve
