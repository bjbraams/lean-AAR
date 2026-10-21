/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.IntegralRepresentations
public import AAR.Legendre.Connections

/-!
# Toroidal functions, coordinates and representations

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- toroidalCoordinates. -/
@[dlmf 14.19.E1]
def toroidalCoordinates (c η θ phi : ℝ) : ℝ × ℝ × ℝ :=
  (c*Real.sinh η*Real.cos phi/(Real.cosh η-Real.cos θ),c*Real.sinh η*Real.sin phi/(Real.cosh η-Real.cos θ),c*Real.sin θ/(Real.cosh η-Real.cos θ))

/-- Toroidal function of the first kind. -/
def toroidalP (n : ℕ) (μ : ℂ) (x : ℝ) : ℂ :=
  associatedP (n-1/2) μ x

/-- Regularized toroidal function of the second kind. -/
def toroidalQ (n : ℕ) (μ : ℂ) (x : ℝ) : ℂ :=
  olverQ (n-1/2) μ x

/-! ### Helpers for Whipple's formulas (prefix `legTor_`) -/

/-- For real `t > 1` with `t² - 1 = u²`, `u > 0`: the Whipple point of `t` is `t/u` and
`(t²-1)^{-1/4} = exp(-(log u)/2)`. -/
lemma legTor_point {t u : ℝ} (ht : 1 < t) (hu : 0 < u) (htu : t^2 - 1 = u^2) :
    (t:ℂ)/exp ((log ((t:ℂ)-1)+log ((t:ℂ)+1))/2) = ((t/u:ℝ):ℂ) ∧
      legendreBranchPower (-1/2) t = exp (-(Real.log u:ℂ)/2) := by
  have hl : log ((t:ℂ)-1)+log ((t:ℂ)+1) = 2*(Real.log u:ℂ) := by
    rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring, show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith), show (t-1)*(t+1) = u^2 by linear_combination htu,
      Real.log_pow]
    push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [hl, show 2*(Real.log u:ℂ)/2 = (Real.log u:ℂ) by ring, ← ofReal_exp, Real.exp_log hu]
    push_cast; ring
  · unfold legendreBranchPower
    rw [hl]; congr 1; ring

/-- `P^μ_{-ν-1} = P^μ_ν` (DLMF 14.9.11 for `P`) on `(1,∞)`. -/
lemma legTor_P_neg_degree (ν μ : ℂ) {y : ℝ} (hy : 1 < y) :
    associatedP (-ν-1) μ y = associatedP ν μ y := by
  have hz : 1 + (y:ℂ) ∈ slitPlane := Or.inl (by simp; linarith)
  unfold associatedP
  rw [regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hz)]
  congr 2 <;> ring

/-- `(c/(s))^{1/2}` for positive reals as an exponential of logarithms. -/
lemma legTor_cpow_half {c s : ℝ} (hc : 0 < c) (hs : 0 < s) :
    ((c/s:ℝ):ℂ)^(1/2:ℂ) = (c:ℂ)^(1/2:ℂ) * exp (-(Real.log s:ℂ)/2) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr (div_pos hc hs).ne'),
    cpow_def_of_ne_zero (ofReal_ne_zero.mpr hc.ne'), ← ofReal_log (div_pos hc hs).le,
    ← ofReal_log hc.le, Real.log_div hc.ne' hs.ne', ← exp_add]
  congr 1; push_cast; ring

/-- `Γ(k + 1/2) ≠ 0` for integer `k`. -/
lemma legTor_Gamma_half_ne (k : ℤ) : Gamma ((k:ℂ) + 1/2) ≠ 0 := by
  refine Gamma_ne_zero fun j hj => ?_
  have := congrArg Complex.re hj
  simp at this
  have h' : ((2*k + 1 + 2*j : ℤ):ℝ) = ((0:ℤ):ℝ) := by push_cast; linarith
  have := Int.cast_inj.mp h'
  omega

/-! ### Quadratic transformations for DLMF 14.19.2–3 -/

/-- Complex powers of a positive real as exponentials. -/
lemma legTor_cpow_real {x : ℝ} (hx : 0 < x) (s : ℂ) : (x:ℂ)^s = exp ((Real.log x:ℂ) * s) := by
  rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne'), ofReal_log hx.le]

/-- Composite quadratic transformation (DLMF 15.8.21 then 15.8.13) behind DLMF 14.19.3:
for `0 < q < 1` and `x = (1+q²)/(2q)`,
`F(μ+½, ν+μ+½; ν+1; q²) = (1+q²)^{-(ν+μ+½)} F(a/2, (a+1)/2; ν+1; x^{-2})`, `a = ν+μ+½`. -/
lemma legTor_quad (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)) (ht : ∀ k : ℕ, 2*ν + 1 ≠ -(k:ℂ))
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ₂F₁ (μ+1/2) (ν+μ+1/2) (ν+1) ((q^2:ℝ):ℂ) =
      exp (-(Real.log (1+q^2):ℂ)*(ν+μ+1/2)) *
        ₂F₁ ((ν+μ+1/2)/2) ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) := by
  have hz : ‖((q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith
  have hs : ((q^2:ℝ):ℂ) ∈ slitPlane := Or.inl (by simp only [ofReal_re]; positivity)
  have hsq : ((q^2:ℝ):ℂ)^(1/2:ℂ) = (q:ℂ) := by
    rw [legTor_cpow_real (by positivity), Real.log_pow]; push_cast
    rw [show (2*(Real.log q:ℂ))*(1/2) = Real.log q by ring, ← ofReal_exp, Real.exp_log hq0]
  set w : ℝ := 4*q/(1+q)^2 with hwdef
  have hw0 : 0 < w := by positivity
  have hw1 : w < 1 := by rw [hwdef, div_lt_one (by positivity)]; nlinarith [sq_nonneg (1-q)]
  have hwC : 4*((q^2:ℝ):ℂ)^(1/2:ℂ)/(1+((q^2:ℝ):ℂ)^(1/2:ℂ))^2 = (w:ℂ) := by
    rw [hsq, hwdef]; push_cast; ring
  have hwn : ‖(w:ℂ)‖ < 1 := by rw [norm_real, Real.norm_eq_abs, abs_of_pos hw0]; exact hw1
  have s1 := quadratic_sqrt (a := ν+μ+1/2) (b := μ+1/2) (z := ((q^2:ℝ):ℂ))
    (by intro k; rw [show ν+μ+1/2-(μ+1/2)+1 = ν+1 by ring]; exact hc k)
    (by intro k; rw [show 2*(ν+μ+1/2)-2*(μ+1/2)+1 = 2*ν+1 by ring]; exact ht k) hz hs
    (by rw [hwC]; exact hwn)
  rw [hwC, hsq, show ν+μ+1/2-(μ+1/2)+1 = ν+1 by ring, show ν+μ+1/2-(μ+1/2)+1/2 = ν+1/2 by ring,
    show 2*(ν+μ+1/2)-2*(μ+1/2)+1 = 2*(ν+1/2) by ring] at s1
  have s2 := quadratic_double_denominator (a := ν+μ+1/2) (b := ν+1/2) (z := (w:ℂ))
    (by intro k; rw [show 2*(ν+1/2) = 2*ν+1 by ring]; exact ht k)
    (by intro k; rw [show ν+1/2+1/2 = ν+1 by ring]; exact hc k) hwn
  rw [show ν+1/2+1/2 = ν+1 by ring] at s2
  rw [ordinaryHypergeometric_symm, s1, s2]
  have h2w : (2:ℝ) - w ≠ 0 := by linarith
  have harg : ((w:ℂ)/(2-w))^2 = (((2*q/(1+q^2))^2:ℝ):ℂ) := by
    rw [show ((w:ℂ)/(2-w)) = ((w/(2-w):ℝ):ℂ) by push_cast; ring]
    have : w/(2-w) = 2*q/(1+q^2) := by
      rw [div_eq_div_iff h2w (by positivity), hwdef]; field_simp; ring
    rw [this]; push_cast; ring
  rw [harg]
  have hw2 : (1:ℂ) - (w:ℂ)/2 = ((1-w/2:ℝ):ℂ) := by push_cast; ring
  have h1q : (1:ℂ) + q = ((1+q:ℝ):ℂ) := by push_cast; ring
  rw [hw2, h1q, legTor_cpow_real (by positivity), legTor_cpow_real (by linarith), ← mul_assoc,
    ← exp_add]
  congr 2
  have hl : Real.log (1+q^2) = 2*Real.log (1+q) + Real.log (1-w/2) := by
    rw [show (2:ℝ)*Real.log (1+q) = Real.log ((1+q)^2) by rw [Real.log_pow]; push_cast; ring,
      ← Real.log_mul (by positivity) (by linarith)]
    congr 1; rw [hwdef]; field_simp; ring
  rw [hl]; push_cast; ring

/-- DLMF 14.19.3 off the half-integer degrees `2ν ∈ ℤ`. -/
lemma legTor_Q_hyp_generic (ν μ : ℂ) (hc : ∀ k : ℕ, ν + 1 ≠ -(k:ℂ)) (ht : ∀ k : ℕ, 2*ν + 1 ≠ -(k:ℂ))
    {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ (ν-1/2) μ (Real.cosh ξ)=Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2) (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)) := by
  set q := Real.exp (-ξ) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hqdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : Real.exp (-2*ξ) = q^2 := by
    rw [hqdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx : Real.cosh ξ = (1+q^2)/(2*q) := by
    rw [Real.cosh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hsh : Real.sinh ξ = (1-q^2)/(2*q) := by
    rw [Real.sinh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hx0 : 0 < Real.cosh ξ := by linarith
  -- the hypergeometric factors
  have hn1 : ‖((q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]; nlinarith
  have harg : 1/((Real.cosh ξ:ℝ):ℂ)^2 = (((2*q/(1+q^2))^2:ℝ):ℂ) := by
    rw [hx]; push_cast; field_simp
  have hn2 : ‖(((2*q/(1+q^2))^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [div_pow, div_lt_one (by positivity)]; nlinarith [pow_pos (show 0 < 1-q^2 by nlinarith) 2]
  have hc' : ∀ k : ℕ, ν - 1/2 + 3/2 ≠ -(k:ℂ) := by
    intro k; rw [show ν-1/2+3/2 = ν+1 by ring]; exact hc k
  unfold olverQ
  rw [hq2, harg, show ((q^2:ℝ):ℂ) = ((q^2:ℝ):ℂ) from rfl,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hn2,
    regularizedGaussHGFun_eq_div_Gamma hc, regularizedGaussHGFun_eq_div_Gamma hc',
    legTor_quad ν μ hc ht hq0 hq1, ordinaryHypergeometric_symm,
    show (ν-1/2+μ+2)/2 = (ν+μ+1/2+1)/2 by ring, show (ν-1/2+μ+1)/2 = (ν+μ+1/2)/2 by ring,
    show ν-1/2+3/2 = ν+1 by ring]
  set G := ₂F₁ ((ν+μ+1/2)/2) ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) / Gamma (ν+1)
  -- logarithmic bookkeeping
  have hl : log (((Real.cosh ξ:ℝ):ℂ)-1)+log (((Real.cosh ξ:ℝ):ℂ)+1) = 2*(Real.log (Real.sinh ξ):ℂ) := by
    rw [show ((Real.cosh ξ:ℝ):ℂ)-1 = ((Real.cosh ξ-1:ℝ):ℂ) by push_cast; ring,
      show ((Real.cosh ξ:ℝ):ℂ)+1 = ((Real.cosh ξ+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith),
      show (Real.cosh ξ-1)*(Real.cosh ξ+1) = Real.sinh ξ^2 by linear_combination Real.cosh_sq ξ,
      Real.log_pow]
    push_cast; ring
  have hlq : Real.log q = -ξ := by rw [hqdef, Real.log_exp]
  have hl1 : Real.log (1-q^2) = Real.log 2 + Real.log q + Real.log (Real.sinh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hs.ne', hsh]
    congr 1; field_simp
  have hl2 : Real.log (1+q^2) = Real.log 2 + Real.log q + Real.log (Real.cosh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hx0.ne', hx]
    congr 1; field_simp
  have e1 : (1:ℂ) - ((q^2:ℝ):ℂ) = ((1-q^2:ℝ):ℂ) := by push_cast; ring
  have q21 : q^2 < 1 := by nlinarith
  unfold legendreBranchPower
  rw [hl, e1, legTor_cpow_real (by linarith) μ, show (2:ℂ)^(ν-1/2+1) = ((2:ℝ):ℂ)^(ν-1/2+1) by norm_num,
    legTor_cpow_real (by norm_num : (0:ℝ) < 2),
    legTor_cpow_real hx0]
  have L : ∀ A B C : ℂ, (Real.sqrt π:ℂ) * exp A / (exp B * exp C) * G =
      (Real.sqrt π:ℂ) * G * exp (A + -B + -C) := by
    intro A B C; rw [exp_add, exp_add, exp_neg, exp_neg]; ring
  have R : ∀ A B C : ℂ, (Real.sqrt π:ℂ) * exp A / exp B * (exp C * ₂F₁ ((ν+μ+1/2)/2)
      ((ν+μ+1/2+1)/2) (ν+1) (((2*q/(1+q^2))^2:ℝ):ℂ) / Gamma (ν+1)) =
      (Real.sqrt π:ℂ) * G * exp (A + -B + C) := by
    intro A B C; rw [exp_add, exp_add, exp_neg]; simp only [G]; ring
  rw [L, R]
  congr 2
  rw [hl1, hl2, hlq]; push_cast; ring

/-- DLMF 14.19.2 off the half-integer orders `2μ ∈ ℤ`. -/
lemma legTor_P_hyp_generic (ν μ : ℂ) (hc1 : ∀ k : ℕ, 1 - 2*μ ≠ -(k:ℂ)) (hc2 : ∀ k : ℕ, 1 - μ ≠ -(k:ℂ))
    {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP (ν-1/2) μ (Real.cosh ξ)=Gamma (1/2-μ)/(Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))*regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := by
  set q := Real.exp (-ξ) with hqdef
  have hq0 : 0 < q := Real.exp_pos _
  have hq1 : q < 1 := by rw [hqdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq2 : Real.exp (-2*ξ) = q^2 := by
    rw [hqdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hx : Real.cosh ξ = (1+q^2)/(2*q) := by
    rw [Real.cosh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hsh : Real.sinh ξ = (1-q^2)/(2*q) := by
    rw [Real.sinh_eq, hqdef, show Real.exp ξ = (Real.exp (-ξ))⁻¹ by rw [Real.exp_neg, inv_inv]]
    field_simp
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hx0 : 0 < Real.cosh ξ := by linarith
  have q21 : q^2 < 1 := by nlinarith
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  -- step 1: degree reflection and DLMF 14.3.18
  have hrefl := legTor_P_neg_degree (-ν-1/2) μ ht1
  rw [show -(-ν-1/2)-1 = ν-1/2 by ring] at hrefl
  rw [hrefl]
  rw [show associatedP (-ν-1/2) μ (Real.cosh ξ) = associatedP (-ν-1/2) (-(-μ)) (Real.cosh ξ) by
    rw [neg_neg], associatedP_neg_eq_quadratic (-ν-1/2) (-μ) hz (by simp only [ofReal_re]; linarith)]
  simp only [neg_neg]
  -- step 2: hypergeometric factors
  have hw1 : ‖(1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2‖ < 1 := by
    rw [show (1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2 = ((1 - 1/Real.cosh ξ^2:ℝ):ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_lt]
    have : 0 < 1/Real.cosh ξ^2 := by positivity
    have : 1/Real.cosh ξ^2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    constructor <;> linarith
  have hw2 : ‖((1-q^2:ℝ):ℂ)‖ < 1 := by
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]; nlinarith
  have hc2' : ∀ k : ℕ, -μ + 1 ≠ -(k:ℂ) := fun k => by rw [show -μ+1 = 1-μ by ring]; exact hc2 k
  rw [hq2, show (1:ℂ) - ((q^2:ℝ):ℂ) = ((1-q^2:ℝ):ℂ) by push_cast; ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw1,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw2,
    regularizedGaussHGFun_eq_div_Gamma hc2', regularizedGaussHGFun_eq_div_Gamma hc1,
    ordinaryHypergeometric_symm (1/2-μ), show 1-2*μ = 2*(1/2-μ) by ring,
    quadratic_double_denominator (by intro k; rw [show 2*(1/2-μ) = 1-2*μ by ring]; exact hc1 k)
      (by intro k; rw [show 1/2-μ+1/2 = 1-μ by ring]; exact hc2 k) hw2,
    show 1/2-μ+1/2 = -μ+1 by ring,
    show (-μ-(-ν-1/2))/2 = (1/2+ν-μ)/2 by ring, show (-μ-(-ν-1/2)+1)/2 = (1/2+ν-μ+1)/2 by ring]
  have hr : ((1-q^2)/(2-(1-q^2)))^2 = 1 - 1/Real.cosh ξ^2 := by
    rw [hx, show (2:ℝ)-(1-q^2) = 1+q^2 by ring, div_pow, div_pow, one_div_div]
    have : (1+q^2)^2 ≠ 0 := by positivity
    rw [eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq this]; ring
  have harg : (((1-q^2:ℝ):ℂ)/(2-((1-q^2:ℝ):ℂ)))^2 = (1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2 := by
    rw [show (((1-q^2:ℝ):ℂ)/(2-((1-q^2:ℝ):ℂ)))^2 = ((((1-q^2)/(2-(1-q^2)))^2:ℝ):ℂ) by push_cast; ring,
      hr]; push_cast; ring
  rw [harg]
  set F := ₂F₁ ((1/2+ν-μ)/2) ((1/2+ν-μ+1)/2) (-μ+1) ((1:ℂ) - 1/((Real.cosh ξ:ℝ):ℂ)^2)
  -- step 3: duplication
  have hG1 : Gamma (-μ+1) ≠ 0 := Gamma_ne_zero hc2'
  have hG2 : Gamma (2*(1/2-μ)) ≠ 0 := Gamma_ne_zero (by
    intro k; rw [show 2*(1/2-μ) = 1-2*μ by ring]; exact hc1 k)
  have hdup := Complex.Gamma_mul_Gamma_add_half (1/2-μ)
  rw [show 1/2-μ+1/2 = -μ+1 by ring, show 1-2*(1/2-μ) = 2*μ by ring] at hdup
  have hGam : Gamma (1/2-μ) = Gamma (2*(1/2-μ)) * (2:ℂ)^(2*μ) * Real.sqrt π / Gamma (-μ+1) := by
    rw [eq_div_iff hG1, hdup]
  rw [hGam]
  -- step 4: logarithms
  have hl : log (((Real.cosh ξ:ℝ):ℂ)-1)+log (((Real.cosh ξ:ℝ):ℂ)+1) = 2*(Real.log (Real.sinh ξ):ℂ) := by
    rw [show ((Real.cosh ξ:ℝ):ℂ)-1 = ((Real.cosh ξ-1:ℝ):ℂ) by push_cast; ring,
      show ((Real.cosh ξ:ℝ):ℂ)+1 = ((Real.cosh ξ+1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log (by linarith), ← ofReal_log (by linarith), ← ofReal_add,
      ← Real.log_mul (by linarith) (by linarith),
      show (Real.cosh ξ-1)*(Real.cosh ξ+1) = Real.sinh ξ^2 by linear_combination Real.cosh_sq ξ,
      Real.log_pow]
    push_cast; ring
  have hlq : Real.log q = -ξ := by rw [hqdef, Real.log_exp]
  have hl1 : Real.log (1-q^2) = Real.log 2 + Real.log q + Real.log (Real.sinh ξ) := by
    rw [← Real.log_mul (by norm_num) hq0.ne', ← Real.log_mul (by positivity) hs.ne', hsh]
    congr 1; field_simp
  have hl2 : Real.log (1-(1-q^2)/2) = Real.log q + Real.log (Real.cosh ξ) := by
    rw [← Real.log_mul hq0.ne' hx0.ne', hx]
    congr 1; field_simp; ring
  have e2 : (1:ℂ) - ((1-q^2:ℝ):ℂ)/2 = ((1-(1-q^2)/2:ℝ):ℂ) := by push_cast; ring
  unfold legendreBranchPower
  have h2 : ∀ s : ℂ, (2:ℂ)^s = exp ((Real.log 2:ℂ)*s) := fun s => by
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num]; exact legTor_cpow_real (by norm_num) s
  rw [hl, e2, h2, h2, legTor_cpow_real hx0, legTor_cpow_real (by linarith) μ,
    legTor_cpow_real (by nlinarith)]
  have hpi : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have L : ∀ A B C : ℂ, exp A * exp B * exp C * (F / Gamma (-μ+1)) = F / Gamma (-μ+1) * exp (A+B+C) := by
    intro A B C; rw [exp_add, exp_add]; ring
  have R : ∀ D E G H : ℂ, Gamma (2*(1/2-μ)) * exp D * (Real.sqrt π:ℂ) / Gamma (-μ+1) /
      ((Real.sqrt π:ℂ) * exp E * exp G) * (exp H * F / Gamma (2*(1/2-μ))) =
      F / Gamma (-μ+1) * exp (D + -E + -G + H) := by
    intro D E G H; rw [exp_add, exp_add, exp_add, exp_neg, exp_neg]
    have h2' := hG2; rw [show 2*(1/2-μ) = 1-2*μ by ring] at h2' ⊢; field_simp
  rw [L, R]
  congr 2
  rw [hl1, hl2, hlq]; push_cast; ring

/-- toroidalP hypergeometric. -/
@[dlmf 14.19.E2]
theorem toroidalP_hypergeometric (ν μ : ℂ) (hμ : ∀ n : ℕ, μ ≠ n+1/2) {ξ : ℝ} (hξ : 0 < ξ) :
    associatedP (ν-1/2) μ (Real.cosh ξ)=Gamma (1/2-μ)/(Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))*regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := by
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  have he0 : 0 < Real.exp (-2*ξ) := Real.exp_pos _
  have he1 : Real.exp (-2*ξ) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hcut : (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [show (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) = ((1 - Real.exp (-2*ξ):ℝ):ℂ) by push_cast; ring,
      norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  have hb : (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) ≠ 0 := by
    rw [show (1:ℂ) - ((Real.exp (-2*ξ):ℝ):ℂ) = ((1 - Real.exp (-2*ξ):ℝ):ℂ) by push_cast; ring]
    exact ofReal_ne_zero.mpr (by linarith)
  have hpi : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hD : ∀ μ : ℂ, (Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ) ≠ 0 := fun μ =>
    mul_ne_zero (mul_ne_zero hpi (cpow_ne_zero_iff.mpr (Or.inl hb))) (exp_ne_zero _)
  have key := legendre_eq_of_continuous_off_countable
    (f := fun μ : ℂ => (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ))
    (g := fun μ : ℂ => ((Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))⁻¹ *
      regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)))
    ((differentiable_one_div_Gamma.continuous.comp (continuous_const.sub continuous_id)).mul
      (associatedP_entire_order (ν-1/2) _ hz).continuous)
    (((continuous_const.mul (continuous_const_cpow' hb)).mul (Continuous.cexp (by fun_prop))).inv₀ hD
      |>.mul (differentiable_regularizedGaussHG_comp (A := fun μ : ℂ => 1/2-μ)
      (B := fun μ : ℂ => 1/2+ν-μ) (C := fun μ : ℂ => 1-2*μ) (by fun_prop) (by fun_prop) (by fun_prop)
      hcut).continuous)
    (countable_range (fun n : ℤ => (n:ℂ)/2)) (fun μ hμ' => ?_) μ
  · have hG : Gamma (1/2-μ) ≠ 0 := Gamma_ne_zero fun m hm => hμ m (by linear_combination -hm)
    have key' : (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ) =
        ((Real.sqrt π:ℂ)*(1-Real.exp (-2*ξ):ℂ)^μ*exp ((ν+1/2)*ξ))⁻¹ *
          regularizedGaussHG (1/2-μ) (1/2+ν-μ) (1-2*μ) (1-Real.exp (-2*ξ)) := key
    calc associatedP (ν-1/2) μ (Real.cosh ξ)
        = Gamma (1/2-μ) * ((Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ)) := by
          rw [← mul_assoc, mul_inv_cancel₀ hG, one_mul]
      _ = _ := by rw [key']; ring
  · have hG : Gamma (1/2-μ) ≠ 0 := Gamma_ne_zero fun m hm => hμ' ⟨2*(m:ℤ)+1, by
      push_cast; linear_combination hm⟩
    show (Gamma (1/2-μ))⁻¹ * associatedP (ν-1/2) μ (Real.cosh ξ) = _
    rw [legTor_P_hyp_generic ν μ (fun k hk => hμ' ⟨(k:ℤ)+1, by push_cast; linear_combination hk/2⟩)
      (fun k hk => hμ' ⟨2*(k:ℤ)+2, by push_cast; linear_combination hk⟩) hξ]
    rw [← mul_assoc, ← mul_div_assoc, inv_mul_cancel₀ hG, one_div]

/-- toroidalQ hypergeometric. -/
@[dlmf 14.19.E3]
theorem toroidalQ_hypergeometric (ν μ : ℂ) {ξ : ℝ} (hξ : 0 < ξ) :
    olverQ (ν-1/2) μ (Real.cosh ξ)=Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2) (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)) := by
  have ht1 : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hz : ((Real.cosh ξ:ℝ):ℂ) - 1 ∈ slitPlane := Or.inl (by simp only [sub_re, ofReal_re, one_re]; linarith)
  have hcut : ((Real.exp (-2*ξ):ℝ):ℂ) ∈ cutPlane := by
    refine mem_cutPlane_of_norm_lt_one ?_
    rw [norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  refine legendre_eq_of_continuous_off_countable (f := fun ν : ℂ => olverQ (ν-1/2) μ (Real.cosh ξ))
    (g := fun ν : ℂ => Real.sqrt π*(1-Real.exp (-2*ξ):ℂ)^μ/exp ((ν+1/2)*ξ)*regularizedGaussHG (μ+1/2)
      (ν+μ+1/2) (ν+1) (Real.exp (-2*ξ)))
    ((olverQ_entire_degree μ _ hz).continuous.comp (continuous_id.sub continuous_const)) ?_
    (countable_range (fun n : ℤ => (n:ℂ)/2)) (fun ν hν => ?_) ν
  · refine (continuous_const.div (Continuous.cexp (by fun_prop)) (fun _ => exp_ne_zero _)).mul ?_
    exact (differentiable_regularizedGaussHG_comp (A := fun _ : ℂ => μ+1/2)
      (B := fun ν : ℂ => ν+μ+1/2) (C := fun ν : ℂ => ν+1) (by fun_prop) (by fun_prop) (by fun_prop)
      hcut).continuous
  · refine legTor_Q_hyp_generic ν μ (fun k hk => hν ⟨-2*(k:ℤ)-2, ?_⟩) (fun k hk => hν ⟨-(k:ℤ)-1, ?_⟩) hξ
    · push_cast; linear_combination -hk
    · push_cast; linear_combination -hk/2

/-- toroidalP integral. -/
@[dlmf 14.19.E4]
theorem toroidalP_integral (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalP n m (Real.cosh ξ)=Gamma (n+m+1/2)*(Real.sinh ξ:ℂ)^m/(2^m*Real.sqrt π*Gamma (n-m+1/2)*Gamma (m+1/2))*∫ θ : ℝ in 0..π, (Real.sin θ:ℂ)^(2*m)/(Real.cosh ξ+Real.cos θ*Real.sinh ξ:ℂ)^(n+m+1/2:ℂ) := by
  sorry

/-- toroidalQ integral. -/
@[dlmf 14.19.E5]
theorem toroidalQ_integral (n m : ℕ) (hmn : m ≤ n) {ξ : ℝ} (hξ : 0 < ξ) :
    HasIntegralAtTop (fun t : ℝ => Gamma (n+1/2)/(Gamma (n+m+1/2)*Gamma (n-m+1/2))*Real.cosh (m*t)/(Real.cosh ξ+Real.cosh t*Real.sinh ξ:ℂ)^(n+1/2:ℂ)) 0 (toroidalQ n m (Real.cosh ξ)) := by
  sorry

/-- toroidalQ fourier. -/
@[dlmf 14.19.E6]
theorem toroidalQ_fourier {μ : ℂ} (hμ : -1/2 < μ.re) {ξ : ℝ} (hξ : 0 < ξ) (phi : ℝ) :
    HasSum (fun j : ℕ => let n:=j+1; 2*Gamma (μ+n+1/2)/Gamma (μ+1/2)*olverQ (n-1/2) μ (Real.cosh ξ)*Real.cos (n*phi)) ((π/2:ℂ)^(1/2:ℂ)*(Real.sinh ξ:ℂ)^μ/(Real.cosh ξ-Real.cos phi:ℂ)^(μ+1/2)-olverQ (-1/2) μ (Real.cosh ξ)) := by
  sorry

/-- toroidal whipple P. -/
@[dlmf 14.19.E7]
theorem toroidal_whipple_P (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalP n m (Real.cosh ξ)=Gamma (n+m+1/2)/Gamma (n-m+1/2)*(2/(π*Real.sinh ξ):ℂ)^(1/2:ℂ)*toroidalQ m n (Real.cosh ξ/Real.sinh ξ) := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hcs : Real.cosh ξ^2 - 1 = Real.sinh ξ^2 := by rw [Real.cosh_sq]; ring
  have hy : 1 < Real.cosh ξ / Real.sinh ξ := by
    rw [lt_div_iff₀ hs]; linarith [Real.sinh_lt_cosh ξ]
  have hys : (Real.cosh ξ / Real.sinh ξ)^2 - 1 = (1/Real.sinh ξ)^2 := by
    field_simp; linarith
  obtain ⟨h1, h2⟩ := legTor_point hy (by positivity) hys
  rw [show Real.cosh ξ / Real.sinh ξ / (1 / Real.sinh ξ) = Real.cosh ξ by field_simp] at h1
  have hG1 : Gamma ((n:ℂ)+m+1/2) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)+m); push_cast at this; exact this
  have hG2 : Gamma ((n:ℂ)-m+1/2) ≠ 0 := by
    have := legTor_Gamma_half_ne ((n:ℤ)-m); push_cast at this; exact this
  unfold toroidalQ toroidalP
  rw [olverQ_whipple_real _ _ _ hy, h1, h2, show -((m:ℂ)-1/2)-1/2 = -(m:ℂ) by ring,
    show -(n:ℂ)-1/2 = -((n:ℂ)-1/2)-1 by ring, legTor_P_neg_degree _ _ ht,
    associatedP_negative_integer_order _ m ?_ (Or.inl (by simp; linarith))]
  · rw [show (2/(π*Real.sinh ξ):ℂ) = ((2/π/Real.sinh ξ:ℝ):ℂ) by push_cast; ring,
      legTor_cpow_half (by positivity) hs,
      show (n:ℂ)-1/2-m+1 = n-m+1/2 by ring, show (n:ℂ)-1/2+m+1 = n+m+1/2 by ring,
      Real.log_div one_ne_zero hs.ne', Real.log_one]
    have hpi : ((2/π:ℝ):ℂ)^(1/2:ℂ) * (π/2:ℂ)^(1/2:ℂ) = 1 := by
      rw [show (π/2:ℂ) = ((π/2:ℝ):ℂ) by push_cast; ring,
        ← mul_cpow_ofReal_nonneg (by positivity) (by positivity),
        ← ofReal_mul, show 2/π*(π/2) = (1:ℝ) by field_simp, ofReal_one, one_cpow]
    have he : exp (-(Real.log (Real.sinh ξ):ℂ)/2) * exp (-((0 - Real.log (Real.sinh ξ):ℝ):ℂ)/2) = 1 := by
      rw [← exp_add]; push_cast; ring_nf; exact exp_zero
    have h3 := mul_inv_cancel₀ hG1
    have h4 := mul_inv_cancel₀ hG2
    set P := associatedP ((n:ℂ)-1/2) m (Real.cosh ξ)
    set X := Gamma ((n:ℂ)+m+1/2) * (Gamma ((n:ℂ)+m+1/2))⁻¹
    set Y := Gamma ((n:ℂ)-m+1/2) * (Gamma ((n:ℂ)-m+1/2))⁻¹
    set Z := ((2/π:ℝ):ℂ)^(1/2:ℂ) * (π/2:ℂ)^(1/2:ℂ)
    set W := exp (-(Real.log (Real.sinh ξ):ℂ)/2) * exp (-((0 - Real.log (Real.sinh ξ):ℝ):ℂ)/2)
    linear_combination (-P)*((Y*Z*W)*h3 + (Z*W)*h4 + W*hpi + he)
  · intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h' : ((2*n + 1 + 2*k : ℤ):ℝ) = ((2*m:ℤ):ℝ) := by push_cast; linarith
    have := Int.cast_inj.mp h'
    omega

/-- toroidal whipple Q. -/
@[dlmf 14.19.E8]
theorem toroidal_whipple_Q (n m : ℕ) {ξ : ℝ} (hξ : 0 < ξ) :
    toroidalQ n m (Real.cosh ξ)=Gamma (m-n+1/2)/Gamma (m+n+1/2)*(π/(2*Real.sinh ξ):ℂ)^(1/2:ℂ)*toroidalP m n (Real.cosh ξ/Real.sinh ξ) := by
  have hs : 0 < Real.sinh ξ := Real.sinh_pos_iff.mpr hξ
  have ht : 1 < Real.cosh ξ := Real.one_lt_cosh.mpr hξ.ne'
  have hcs : Real.cosh ξ^2 - 1 = Real.sinh ξ^2 := by rw [Real.cosh_sq]; ring
  have hy : 1 < Real.cosh ξ / Real.sinh ξ := by
    rw [lt_div_iff₀ hs]; linarith [Real.sinh_lt_cosh ξ]
  obtain ⟨h1, h2⟩ := legTor_point ht hs hcs
  unfold toroidalQ toroidalP
  rw [olverQ_whipple_real _ _ _ ht, h1, h2, show -((n:ℂ)-1/2)-1/2 = -(n:ℂ) by ring,
    show -(m:ℂ)-1/2 = -((m:ℂ)-1/2)-1 by ring, legTor_P_neg_degree _ _ hy,
    associatedP_negative_integer_order _ n ?_ (Or.inl (by
      rw [show ((Real.cosh ξ / Real.sinh ξ : ℝ):ℂ) - 1 = ((Real.cosh ξ / Real.sinh ξ - 1 : ℝ):ℂ) by
        push_cast; ring, ofReal_re]; linarith))]
  · rw [show (π/(2*Real.sinh ξ):ℂ) = ((π/2/Real.sinh ξ:ℝ):ℂ) by push_cast; ring,
      legTor_cpow_half (by positivity) hs,
      show ((π/2:ℝ):ℂ) = (π/2:ℂ) by push_cast; ring,
      show (m:ℂ)-1/2-n+1 = m-n+1/2 by ring, show (m:ℂ)-1/2+n+1 = m+n+1/2 by ring]
    ring
  · intro k hk
    have := congrArg Complex.re hk
    simp at this
    have h' : ((2*m + 1 + 2*k : ℤ):ℝ) = ((2*n:ℤ):ℝ) := by push_cast; linarith
    have := Int.cast_inj.mp h'
    omega

end AAR.Legendre
