/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.OrthogonalPolynomials.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
public import Mathlib.Analysis.Fourier.AddCircle

/-!
# Chebyshev expansions (Temme §6.9.2)

With `x = cos θ` an expansion `f(x) = c₀/2 + ∑ cₙ Tₙ(x)` is the Fourier cosine series of
`θ ↦ f(cos θ)`, with `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ` (Temme (6.65)–(6.66)). This file
transfers Mathlib's Fourier theory on `AddCircle` to Chebyshev series and adds the facts used
in numerical work.

## Main results

* `chebyshevCoeff_eq_integral_measureT`: the coefficients as integrals against Mathlib's
  Chebyshev measure `dx/√(1-x²)`.
* `hasSum_chebyshevCoeff_mul_T`: for `f` continuous on `[-1,1]` with absolutely summable
  coefficients, the Chebyshev series converges to `f` on `[-1,1]`.
* `abs_chebyshevCoeff_le`: `|cₙ| ≤ 2M ρ^{-n}` for `f` analytic and bounded by `M` in the closed
  Bernstein ellipse `E_ρ`, by a contour shift in `θ`.
* `abs_sub_sum_chebyshevCoeff_mul_T_le`: the resulting uniform truncation error
  `2M ρ^{-N}/(1 - ρ^{-1})`.
* `sum_chebyshevT_eq_clenshaw`: Clenshaw's backward recurrence for evaluating Chebyshev sums,
  from the general three-term form `sum_mul_eq_clenshaw`.
* `hasSum_chebyshevT_inv_add`: Temme's Example 6.3,
  `1/(x+a) = (2/√(a²-1)) (1/2 + ∑_{n≥1} (√(a²-1) - a)ⁿ Tₙ(x))` for `a > 1`.
-/

@[expose] public section

open Complex Filter MeasureTheory Set Polynomial
open scoped Real Topology Nat

noncomputable section

namespace DLMF.OrthogonalPolynomials

/-- The Chebyshev coefficient `cₙ = (2/π) ∫₀^π f(cos θ) cos(nθ) dθ` (Temme (6.66)). -/
def chebyshevCoeff (f : ℝ → ℝ) (n : ℕ) : ℝ :=
  2 / π * ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n * θ)

/-- The coefficients as integrals against the Chebyshev weight `dx/√(1-x²)` (Temme (6.65)). -/
theorem chebyshevCoeff_eq_integral_measureT (f : ℝ → ℝ) (n : ℕ) :
    chebyshevCoeff f n = 2 / π * ∫ x, f x * (Chebyshev.T ℝ n).eval x ∂Chebyshev.measureT := by
  rw [chebyshevCoeff, Chebyshev.integral_measureT_eq_integral_cos]
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have := Chebyshev.T_real_cos θ (n : ℤ)
  push_cast at this ⊢
  rw [this]

/-! ### Clenshaw's algorithm -/

/-- Clenshaw's backward recurrence `b_k = c_k + 2x b_{k+1} - b_{k+2}`, `b_{N+1} = b_{N+2} = 0`,
returning `(b₀, b₁)` for the coefficients `c₀, …, c_N`. -/
def clenshaw {R : Type*} [CommRing R] (x : R) : ℕ → (ℕ → R) → R × R
  | 0, c => (c 0, 0)
  | N + 1, c =>
    let p := clenshaw x N (fun k => c (k + 1))
    (c 0 + 2 * x * p.1 - p.2, p.1)

/-- Clenshaw's identity for any sequence obeying the three-term recurrence
`Y_{k+2} = 2x Y_{k+1} - Y_k`. -/
theorem sum_mul_eq_clenshaw {R : Type*} [CommRing R] (x : R) (N : ℕ) (c Y : ℕ → R)
    (hY : ∀ k, Y (k + 2) = 2 * x * Y (k + 1) - Y k) :
    ∑ k ∈ Finset.range (N + 1), c k * Y k =
      (clenshaw x N c).1 * Y 0 + (clenshaw x N c).2 * (Y 1 - 2 * x * Y 0) := by
  induction N generalizing c Y with
  | zero => simp [clenshaw]
  | succ N ih =>
    rw [Finset.sum_range_succ', ih (fun k => c (k + 1)) (fun k => Y (k + 1)) (fun k => hY (k + 1))]
    simp only [clenshaw, zero_add]
    rw [hY 0]
    ring

/-- **Clenshaw's algorithm** for Chebyshev sums (Temme §6.9.2):
`∑_{k ≤ N} cₖ Tₖ(x) = b₀ - x b₁`. -/
theorem sum_chebyshevT_eq_clenshaw {R : Type*} [CommRing R] (x : R) (N : ℕ) (c : ℕ → R) :
    ∑ k ∈ Finset.range (N + 1), c k * (Chebyshev.T R k).eval x =
      (clenshaw x N c).1 - x * (clenshaw x N c).2 := by
  rw [sum_mul_eq_clenshaw x N c (fun k => (Chebyshev.T R k).eval x) (fun k => by
    have := Chebyshev.T_add_two R (k : ℤ)
    push_cast
    rw [this]; simp)]
  simp [Chebyshev.T_zero, Chebyshev.T_one]
  ring

/-- **Temme's Example 6.3**: for `a > 1` and `|x| ≤ 1`, with `s = √(a²-1)` and `λ = s - a`,
`1/(x+a) = (2/s) (1/2 + ∑_{n≥1} λⁿ Tₙ(x))`. -/
theorem hasSum_chebyshevT_inv_add {a x : ℝ} (ha : 1 < a) (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 else 2) / Real.sqrt (a ^ 2 - 1) *
      (Real.sqrt (a ^ 2 - 1) - a) ^ n * (Chebyshev.T ℝ n).eval x) (1 / (x + a)) := by
  set s := Real.sqrt (a ^ 2 - 1) with hs
  set l := s - a with hl
  have hs2 : s ^ 2 = a ^ 2 - 1 := Real.sq_sqrt (by nlinarith)
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by nlinarith)
  have hsa : s < a := by nlinarith
  have hsa1 : a - 1 < s := by nlinarith
  have hl1 : |l| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hxa : 0 < x + a := by linarith [(abs_le.mp hx).1]
  have hlq : l ^ 2 + 2 * a * l + 1 = 0 := by rw [hl]; nlinarith
  -- the generating function at `z = λ`
  have hG := chebyshevT_generating_function hx (z := (l : ℂ)) (by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hl1)
  have hGr : HasSum (fun n : ℕ => (Chebyshev.T ℝ n).eval x * l ^ n)
      ((1 - x * l) / (1 - 2 * x * l + l ^ 2)) := by
    rw [← Complex.hasSum_ofReal]
    convert hG using 1
    · funext n
      push_cast
      rfl
    · push_cast; ring
  have hden : 1 - 2 * x * l + l ^ 2 = -2 * l * (x + a) := by linear_combination hlq
  have hl0 : l ≠ 0 := by intro h; rw [h] at hlq; norm_num at hlq
  have h := (hGr.mul_left (2 / s)).sub (hasSum_ite_eq 0 (1 / s))
  convert h using 1
  · funext n
    split_ifs with hn
    · subst hn; simp [Chebyshev.T_zero]; ring
    · ring
  · rw [hden]
    have h1 : 1 + l * a = -s * l := by rw [hl]; nlinarith
    field_simp
    linear_combination h1

/-! ### Convergence of Chebyshev series -/

/-- `θ ↦ f(cos θ)` as a continuous function on the circle `ℝ/2πℤ`. -/
def chebyshevCircleFun {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) :
    C(AddCircle (2 * π), ℂ) where
  toFun := (show Function.Periodic (fun θ : ℝ => ((f (Real.cos θ) : ℝ) : ℂ)) (2 * π) from
    fun θ => by simp [Real.cos_add_two_pi]).lift
  continuous_toFun := by
    refine continuous_coinduced_dom.mpr ?_
    have hc : Continuous fun θ : ℝ => f (Real.cos θ) :=
      hf.comp_continuous Real.continuous_cos fun θ =>
        ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    exact Complex.continuous_ofReal.comp hc

lemma chebyshevCircleFun_coe {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (θ : ℝ) :
    chebyshevCircleFun hf (θ : AddCircle (2 * π)) = f (Real.cos θ) := rfl

local instance instTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

/-- The full-period integral `∫₀^{2π} e^{-inθ} f(cos θ) dθ = π c_{|n|}`. -/
lemma integral_exp_mul_comp_cos {f : ℝ → ℝ} (hcf : Continuous fun x : ℝ => f (Real.cos x))
    (n : ℤ) :
    ∫ x in (0 : ℝ)..(2 * π), Complex.exp (-(I * n * x)) * ((f (Real.cos x) : ℝ) : ℂ) =
      π * chebyshevCoeff f n.natAbs := by
  set h : ℝ → ℂ := fun x => Complex.exp (-(I * n * x)) * ((f (Real.cos x) : ℝ) : ℂ) with hh
  have hhc : Continuous h := by
    rw [hh]; exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (-(I * n * x))).mul
      (Complex.continuous_ofReal.comp hcf)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume) (a := 0) (b := π)
    (c := 2 * π) (hhc.intervalIntegrable _ _) (hhc.intervalIntegrable _ _)
  have hrefl := intervalIntegral.integral_comp_sub_left h (a := 0) (b := π) (2 * π)
  rw [show 2 * π - π = π by ring, sub_zero] at hrefl
  have hsym : ∫ x in (0 : ℝ)..π, h (2 * π - x) =
      ∫ x in (0 : ℝ)..π, Complex.exp (I * n * x) * ((f (Real.cos x) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [hh, Real.cos_two_pi_sub]
    congr 1
    rw [show -(I * n * ((2 * π - x : ℝ) : ℂ)) = I * n * x + (-n : ℤ) * (2 * π * I) by
      push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hsum : ∫ x in (0 : ℝ)..(2 * π), h x =
      2 * ∫ x in (0 : ℝ)..π, ((Real.cos (n.natAbs * x) * f (Real.cos x) : ℝ) : ℂ) := by
    have hg : Continuous fun x : ℝ => Complex.exp (I * n * x) * ((f (Real.cos x) : ℝ) : ℂ) :=
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (I * n * x)).mul
        (Complex.continuous_ofReal.comp hcf)
    rw [← hsplit, ← hrefl, hsym, ← intervalIntegral.integral_add (hhc.intervalIntegrable 0 π)
      (hg.intervalIntegrable 0 π), ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x hx => ?_
    have hx0 : 0 ≤ x := by
      rw [uIcc_of_le Real.pi_pos.le] at hx; exact hx.1
    have hcos : Real.cos (n.natAbs * x) = Real.cos (n * x) := by
      rw [Nat.cast_natAbs, Int.cast_abs, ← Real.cos_abs ((n : ℝ) * x), abs_mul, abs_of_nonneg hx0]
    simp only [hh]
    rw [hcos, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
    push_cast
    ring_nf
  rw [hsum, chebyshevCoeff, intervalIntegral.integral_ofReal]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have heq : (∫ x in (0 : ℝ)..π, Real.cos (n.natAbs * x) * f (Real.cos x)) =
      ∫ θ in (0 : ℝ)..π, f (Real.cos θ) * Real.cos (n.natAbs * θ) :=
    intervalIntegral.integral_congr fun x _ => by ring
  rw [heq]
  push_cast
  field_simp

/-- The Fourier coefficients of `θ ↦ f(cos θ)` are half the Chebyshev coefficients. -/
lemma fourierCoeff_chebyshevCircleFun {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1)) (n : ℤ) :
    fourierCoeff (chebyshevCircleFun hf) n = (chebyshevCoeff f n.natAbs / 2 : ℝ) := by
  rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
  have hcf : Continuous fun x : ℝ => f (Real.cos x) :=
    hf.comp_continuous Real.continuous_cos fun θ => ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
  have hint : ∫ x in (0 : ℝ)..(2 * π), fourier (-n) (x : AddCircle (2 * π)) •
      chebyshevCircleFun hf x = ∫ x in (0 : ℝ)..(2 * π),
        Complex.exp (-(I * n * x)) * ((f (Real.cos x) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [fourier_coe_apply, chebyshevCircleFun_coe, smul_eq_mul]
    congr 1
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    congr 1
    push_cast
    field_simp
  rw [hint, integral_exp_mul_comp_cos hcf, Complex.real_smul]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

/-- **Convergence of Chebyshev series** (Temme (6.65)–(6.66)): if `f` is continuous on `[-1,1]`
and its Chebyshev coefficients are absolutely summable, then
`f(x) = c₀/2 + ∑_{n≥1} cₙ Tₙ(x)` for every `x ∈ [-1,1]`. -/
theorem hasSum_chebyshevCoeff_mul_T {f : ℝ → ℝ} (hf : ContinuousOn f (Icc (-1) 1))
    (hs : Summable fun n => |chebyshevCoeff f n|) {x : ℝ} (hx : x ∈ Icc (-1) 1) :
    HasSum (fun n : ℕ => (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
      (Chebyshev.T ℝ n).eval x) (f x) := by
  set g := chebyshevCircleFun hf with hg
  set c := chebyshevCoeff f with hc
  have hsC : Summable fun n : ℕ => ((c n / 2 : ℝ) : ℂ) := by
    refine Summable.of_norm ?_
    refine (hs.div_const 2).congr fun n => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_two]
  have hsum : Summable (fourierCoeff g) := by
    refine Summable.of_nat_of_neg ?_ ?_
    · refine hsC.congr fun n => ?_
      rw [hg, fourierCoeff_chebyshevCircleFun]; simp [hc]
    · refine hsC.congr fun n => ?_
      rw [hg, fourierCoeff_chebyshevCircleFun]; simp [hc]
  set θ := Real.arccos x with hθ
  have hxθ : Real.cos θ = x := Real.cos_arccos hx.1 hx.2
  have hp := (has_pointwise_sum_fourier_series_of_summable hsum (θ : AddCircle (2 * π))).nat_add_neg
  have hterm : ∀ n : ℕ, fourierCoeff g n • fourier (n : ℤ) (θ : AddCircle (2 * π)) +
      fourierCoeff g (-(n : ℤ)) • fourier (-(n : ℤ)) (θ : AddCircle (2 * π)) =
      ((c n * (Chebyshev.T ℝ n).eval x : ℝ) : ℂ) := by
    intro n
    rw [hg, fourierCoeff_chebyshevCircleFun, fourierCoeff_chebyshevCircleFun, fourier_coe_apply,
      fourier_coe_apply, ← hxθ, Chebyshev.T_real_cos]
    simp only [Int.natAbs_neg, Int.natAbs_natCast, smul_eq_mul]
    have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    rw [show 2 * (π : ℂ) * I * ((n : ℤ) : ℂ) * (θ : ℂ) / (2 * π : ℝ) = (n * θ : ℝ) * I by
        push_cast; field_simp,
      show 2 * (π : ℂ) * I * ((-(n : ℤ) : ℤ) : ℂ) * (θ : ℂ) / (2 * π : ℝ) =
        ((-(n * θ) : ℝ) : ℂ) * I by push_cast; field_simp]
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, hc]
    push_cast
    ring
  have hR : HasSum (fun n : ℕ => c n * (Chebyshev.T ℝ n).eval x) (f x + c 0 / 2) := by
    rw [← Complex.hasSum_ofReal]
    convert hp using 1
    · funext n; exact (hterm n).symm
    · rw [hg, chebyshevCircleFun_coe, hxθ, fourierCoeff_chebyshevCircleFun]
      simp [hc]
  have h := hR.sub (hasSum_ite_eq 0 (c 0 / 2))
  rw [add_sub_cancel_right] at h
  refine h.congr_fun fun n => ?_
  split_ifs with hn
  · subst hn; simp [Chebyshev.T_zero]; ring
  · simp

/-! ### Functions analytic in a Bernstein ellipse -/

/-- **Geometric decay of Chebyshev coefficients** (Temme §6.9.2; Rivlin): if `f` extends to a
function `F` analytic on the closed Bernstein ellipse `E_ρ = cos({|Im w| ≤ s})`, `ρ = e^s`, with
`|F| ≤ M` there, then `|cₙ| ≤ 2M ρ^{-n}`. -/
theorem abs_chebyshevCoeff_le {f : ℝ → ℝ} {F : ℂ → ℂ} {s M : ℝ} (hs : 0 ≤ s)
    (hF : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ F (Complex.cos w))
    (hM : ∀ w : ℂ, |w.im| ≤ s → ‖F (Complex.cos w)‖ ≤ M)
    (hFf : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) (n : ℕ) :
    |chebyshevCoeff f n| ≤ 2 * M * Real.exp (-(n * s)) := by
  set G : ℂ → ℂ := fun w => F (Complex.cos w) * Complex.exp (-(I * n * w)) with hG
  have hcosmem : ∀ x : ℝ, Real.cos x ∈ Icc (-1 : ℝ) 1 :=
    fun x => ⟨Real.neg_one_le_cos x, Real.cos_le_one x⟩
  have hreal : ∀ x : ℝ, G x = Complex.exp (-(I * n * x)) * ((f (Real.cos x) : ℝ) : ℂ) := by
    intro x
    simp only [hG]
    rw [← Complex.ofReal_cos, hFf _ (hcosmem x)]
    ring
  have hGd : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ G w := fun w hw =>
    ((hF w hw).comp w Complex.differentiable_cos.differentiableAt).mul
      (by fun_prop : DifferentiableAt ℂ (fun w : ℂ => Complex.exp (-(I * n * w))) w)
  have hcf : Continuous fun x : ℝ => f (Real.cos x) := by
    have hc : Continuous fun x : ℝ => F (Complex.cos x) :=
      continuous_iff_continuousAt.mpr fun x =>
        (((hF x (by simp [hs])).continuousAt.comp Complex.continuous_cos.continuousAt).comp
          Complex.continuous_ofReal.continuousAt)
    refine (Complex.continuous_re.comp hc).congr fun x => ?_
    simp only [Function.comp_apply]
    rw [← Complex.ofReal_cos, hFf _ (hcosmem x), Complex.ofReal_re]
  -- Cauchy's theorem on the rectangle `[0, 2π] × [-s, 0]`
  have hrect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn G
    (⟨0, -s⟩ : ℂ) (⟨2 * π, 0⟩ : ℂ) (fun w hw => (hGd w (by
      rw [mem_reProdIm] at hw
      have h2 := hw.2
      rw [uIcc_of_le (by simp; linarith)] at h2
      simp only at h2
      rw [abs_le]; constructor <;> linarith [h2.1, h2.2])).differentiableWithinAt)
  simp only at hrect
  have hper : ∀ y : ℝ, G ((2 * π : ℝ) + y * I) = G ((0 : ℝ) + y * I) := by
    intro y
    simp only [hG]
    push_cast
    rw [show 2 * (π : ℂ) + y * I = y * I + 2 * π by ring, Complex.cos_add_two_pi, zero_add,
      show -(I * n * (y * I + 2 * π)) = -(I * n * (y * I)) + (-n : ℤ) * (2 * π * I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp only [hper, add_zero, Complex.ofReal_zero, zero_mul] at hrect
  rw [add_sub_cancel_right, sub_eq_zero] at hrect
  have hB : ∫ x : ℝ in (0 : ℝ)..(2 * π), G x = π * chebyshevCoeff f n := by
    rw [intervalIntegral.integral_congr fun x _ => hreal x]
    exact_mod_cast integral_exp_mul_comp_cos hcf n
  rw [hB] at hrect
  have hbound : ∀ x ∈ uIoc (0 : ℝ) (2 * π), ‖G (x + ((-s : ℝ) : ℂ) * I)‖ ≤ M * Real.exp (-(n * s)) := by
    intro x _
    have him : |((x : ℂ) + ((-s : ℝ) : ℂ) * I).im| ≤ s := by simp [abs_of_nonneg hs]
    simp only [hG]
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul (hM _ him) (le_of_eq ?_) (by positivity)
      ((norm_nonneg _).trans (hM _ him))
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.natCast_re, Complex.natCast_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hrect, norm_mul, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le,
    Complex.norm_real, Real.norm_eq_abs, sub_zero, abs_of_pos Real.two_pi_pos] at hI
  have hπ := Real.pi_pos
  nlinarith [abs_nonneg (chebyshevCoeff f n), Real.exp_pos (-(n * s))]

/-- **Truncation error of Chebyshev series** for functions analytic in the Bernstein ellipse
`E_ρ`, `ρ = e^s > 1`, with `|F| ≤ M` there: uniformly on `[-1,1]`,
`|f(x) - (c₀/2 + ∑_{1≤n<N} cₙ Tₙ(x))| ≤ 2M ρ^{-N} / (1 - ρ^{-1})`. -/
theorem abs_sub_sum_chebyshevCoeff_mul_T_le {f : ℝ → ℝ} {F : ℂ → ℂ} {s M : ℝ} (hs : 0 < s)
    (hF : ∀ w : ℂ, |w.im| ≤ s → DifferentiableAt ℂ F (Complex.cos w))
    (hM : ∀ w : ℂ, |w.im| ≤ s → ‖F (Complex.cos w)‖ ≤ M)
    (hFf : ∀ x ∈ Icc (-1 : ℝ) 1, F x = f x) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) (N : ℕ) :
    |f x - ∑ n ∈ Finset.range N, (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
      (Chebyshev.T ℝ n).eval x| ≤ 2 * M * Real.exp (-s) ^ N / (1 - Real.exp (-s)) := by
  set r := Real.exp (-s) with hr
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hdecay : ∀ n : ℕ, |chebyshevCoeff f n| ≤ 2 * M * r ^ n := fun n => by
    rw [hr, ← Real.exp_nat_mul, show (n : ℝ) * -s = -(n * s) by ring]
    exact abs_chebyshevCoeff_le hs.le hF hM hFf n
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp [hs.le]))
  have hgeo : Summable fun n : ℕ => 2 * M * r ^ n :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left _
  -- continuity of `f` on `[-1, 1]`
  have hfc : ContinuousOn f (Icc (-1) 1) := by
    intro y hy
    have hcy : Complex.cos (Real.arccos y) = y := by
      rw [← Complex.ofReal_cos, Real.cos_arccos hy.1 hy.2]
    have hd := hF (Real.arccos y) (by simp [hs.le])
    rw [hcy] at hd
    have hcont : ContinuousAt (fun t : ℝ => (F t).re) y :=
      Complex.continuous_re.continuousAt.comp
        (hd.continuousAt.comp Complex.continuous_ofReal.continuousAt)
    refine (hcont.continuousWithinAt).congr (fun t ht => ?_) ?_
    · rw [hFf t ht, Complex.ofReal_re]
    · rw [hFf y hy, Complex.ofReal_re]
  have hsum := hasSum_chebyshevCoeff_mul_T hfc
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hdecay hgeo) hx
  set a : ℕ → ℝ := fun n => (if n = 0 then 1 / 2 else 1) * chebyshevCoeff f n *
    (Chebyshev.T ℝ n).eval x with ha
  have hab : ∀ n, |a n| ≤ 2 * M * r ^ n := by
    intro n
    have hT := Chebyshev.abs_eval_T_real_le_one (n : ℤ) (abs_le.mpr ⟨hx.1, hx.2⟩)
    have hc : |(if n = 0 then (1 / 2 : ℝ) else 1)| ≤ 1 := by split_ifs <;> norm_num
    calc |a n| = |(if n = 0 then (1 / 2 : ℝ) else 1)| * |chebyshevCoeff f n| *
          |(Chebyshev.T ℝ n).eval x| := by simp only [ha, abs_mul]
      _ ≤ 1 * |chebyshevCoeff f n| * 1 := by gcongr
      _ ≤ 2 * M * r ^ n := by linarith [hdecay n]
  rw [← hsum.tsum_eq, ← (hsum.summable).sum_add_tsum_nat_add N, add_sub_cancel_left]
  have htail : Summable fun n => |a (n + N)| :=
    (Summable.of_nonneg_of_le (fun n => abs_nonneg _) hab hgeo).comp_injective
      (add_left_injective N)
  calc |∑' n, a (n + N)| ≤ ∑' n, |a (n + N)| := by
        have := norm_tsum_le_tsum_norm (f := fun n => a (n + N))
          (by simpa only [Real.norm_eq_abs] using htail)
        simpa only [Real.norm_eq_abs] using this
    _ ≤ ∑' n : ℕ, 2 * M * r ^ N * r ^ n := by
        refine htail.tsum_le_tsum (fun n => ?_)
          ((summable_geometric_of_lt_one hr0 hr1).mul_left _)
        rw [mul_assoc, ← pow_add, add_comm N n]
        exact hab (n + N)
    _ = 2 * M * r ^ N / (1 - r) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, div_eq_mul_inv]

end DLMF.OrthogonalPolynomials
