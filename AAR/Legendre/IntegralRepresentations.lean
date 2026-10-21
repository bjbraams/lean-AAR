/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Hypergeometric
public import AAR.Legendre.AssociatedRecurrences
public import AAR.Legendre.Neumann
public import AAR.Legendre.IntegralTools
public import AAR.Legendre.Singularities

/-!
# Integral representations and fractional integration

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrersP mehler dirichlet. -/
@[dlmf 14.12.E1]
theorem ferrersP_mehler_dirichlet {μ : ℂ} (hμ : μ.re < 1/2) (ν : ℂ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    ferrersP ν μ (Real.cos θ)=Real.sqrt 2*(Real.sin θ:ℂ)^μ/(Real.sqrt π*Gamma (1/2-μ))*∫ t : ℝ in 0..θ, cos ((ν+1/2)*t)/(Real.cos t-Real.cos θ:ℂ)^(μ+1/2) := by
  sorry

/-- ferrersP fractional integral. -/
@[dlmf 14.12.E2]
theorem ferrersP_fractional_integral {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-μ) x=(1-x^2:ℂ)^(-μ/2)/Gamma μ*∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1) := by
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1 - x := by linarith [hx.2]
  set z : ℂ := (1-(x:ℂ))/2 with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, show (1-(x:ℂ))/2 = (((1-x)/2:ℝ):ℂ) by push_cast; ring, norm_real, Real.norm_eq_abs,
      abs_lt]
    constructor <;> linarith [hx.1, hx.2]
  have hfr := fractional_integral (a := ν+1) (b := -ν) (c := 1+μ) (d := 1) (by norm_num)
    (by simpa using hμ) hzn
  rw [show 1+μ-1 = μ by ring] at hfr
  -- the substituted integral
  have hsub : (∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) =
      ((1-x:ℝ):ℂ)^μ * ∫ s : ℝ in (0:ℝ)..1,
        regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) * (s:ℂ)^((1:ℂ)-1) * (1-(s:ℂ))^(μ-1) := by
    have hc : (1-x) ≠ 0 := h2.ne'
    have h := intervalIntegral.integral_comp_sub_mul
      (fun t : ℝ => ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) (a := 0) (b := 1) hc 1
    simp only [mul_one, mul_zero, sub_zero, sub_sub_cancel] at h
    rw [show (∫ t : ℝ in x..1, ferrersP ν 0 t*(t-x:ℂ)^(μ-1)) =
      (1-x) • ∫ s : ℝ in (0:ℝ)..1, ferrersP ν 0 (1-(1-x)*s)*((1-(1-x)*s : ℝ)-x:ℂ)^(μ-1) by
      rw [h, smul_inv_smul₀ hc]]
    rw [real_smul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hzs : ‖z*s‖ < 1 := by
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc ‖z‖*s ≤ ‖z‖*1 := by gcongr; exact hs.2
        _ < 1 := by rw [mul_one]; exact hzn
    have hF : ferrersP ν 0 (1-(1-x)*s) = regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) := by
      simp only [ferrersP, zero_div, cpow_zero, one_mul, sub_zero]
      rw [← regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzs, hz]
      congr 1; push_cast; ring
    have hp : (((1-(1-x)*s : ℝ):ℂ)-x)^(μ-1) = ((1-x:ℝ):ℂ)^(μ-1) * (1-(s:ℂ))^(μ-1) := by
      rw [show (((1-(1-x)*s : ℝ):ℂ)-x) = (((1-x)*(1-s):ℝ):ℂ) by push_cast; ring,
        ofReal_mul, mul_cpow_ofReal_nonneg h2.le (by linarith [hs.2])]
      push_cast; ring_nf
    rw [hF, hp, sub_self, cpow_zero, mul_one]
    have hμ1 : ((1-x:ℝ):ℂ)^μ = ((1-x:ℝ):ℂ) * ((1-x:ℝ):ℂ)^(μ-1) := by
      conv_lhs => rw [show μ = (μ-1)+1 by ring]
      rw [cpow_add _ _ (ofReal_ne_zero.2 hc), cpow_one]; ring
    rw [hμ1]; push_cast; ring
  have hG : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  have hI : (∫ s : ℝ in (0:ℝ)..1,
        regularizedGaussHGFun (ν+1) (-ν) 1 (z*s) * (s:ℂ)^((1:ℂ)-1) * (1-(s:ℂ))^(μ-1)) =
      Gamma μ * regularizedGaussHGFun (ν+1) (-ν) (1+μ) z := by
    rw [hfr]; field_simp
  have hpow : (((1+x)/(1-x):ℝ):ℂ)^(-μ/2) = (1-(x:ℂ)^2)^(-μ/2) * ((1-x:ℝ):ℂ)^μ := by
    rw [show (1-(x:ℂ)^2) = (((1+x)*(1-x):ℝ):ℂ) by push_cast; ring,
      legInt_cpow_ofReal (div_pos h1 h2), legInt_cpow_ofReal (mul_pos h1 h2),
      legInt_cpow_ofReal h2, ← exp_add, Real.log_div h1.ne' h2.ne', Real.log_mul h1.ne' h2.ne']
    congr 1; push_cast; ring
  rw [hsub, hI, ferrersP, show (1:ℂ) - -μ = 1+μ by ring,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hzn, show -μ/2 = (-μ)/2 by ring]
  rw [show (-μ)/2 = -μ/2 by ring, hpow]
  field_simp

/-- associatedP fractional integral. -/
@[dlmf 14.12.E5]
theorem associatedP_fractional_integral {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-μ) x=(x^2-1:ℂ)^(-μ/2)/Gamma μ*∫ t : ℝ in 1..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1) := by
  have h1 : (0:ℝ) < x - 1 := by linarith
  have h2 : (0:ℝ) < x + 1 := by linarith
  set z : ℂ := (1-(x:ℂ))/2 with hz
  have hzc : z ∈ cutPlane := by
    rw [mem_cutPlane, hz]; left; simp; linarith
  have hsub : (∫ t : ℝ in (1:ℝ)..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1)) =
      ((x-1:ℝ):ℂ)^μ * ∫ s : ℝ in (0:ℝ)..1,
        (1-(s:ℂ))^(μ-1) * regularizedGaussHG (ν+1) (-ν) 1 (z * s) := by
    have hc : (x-1) ≠ 0 := h1.ne'
    have h := intervalIntegral.integral_comp_add_mul
      (fun t : ℝ => associatedP ν 0 t*(x-t:ℂ)^(μ-1)) (a := 0) (b := 1) hc 1
    simp only [mul_one, mul_zero, add_zero, add_sub_cancel] at h
    rw [show (∫ t : ℝ in (1:ℝ)..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1)) =
      (x-1) • ∫ s : ℝ in (0:ℝ)..1, associatedP ν 0 ((1+(x-1)*s : ℝ))*(x-((1+(x-1)*s : ℝ)):ℂ)^(μ-1) by
      rw [h, smul_inv_smul₀ hc]]
    rw [real_smul, ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le zero_le_one] at hs
    have hF : associatedP ν 0 ((1+(x-1)*s : ℝ)) = regularizedGaussHG (ν+1) (-ν) 1 (z*s) := by
      simp only [associatedP, zero_div, zero_mul, exp_zero, one_mul, sub_zero]
      rw [hz]; congr 1; push_cast; ring
    have hp : ((x:ℂ)-((1+(x-1)*s : ℝ)))^(μ-1) = ((x-1:ℝ):ℂ)^(μ-1) * (1-(s:ℂ))^(μ-1) := by
      rw [show ((x:ℂ)-((1+(x-1)*s : ℝ))) = (((x-1)*(1-s):ℝ):ℂ) by push_cast; ring,
        ofReal_mul, mul_cpow_ofReal_nonneg h1.le (by linarith [hs.2])]
      push_cast; ring_nf
    rw [hF, hp]
    have hμ1 : ((x-1:ℝ):ℂ)^μ = ((x-1:ℝ):ℂ) * ((x-1:ℝ):ℂ)^(μ-1) := by
      conv_lhs => rw [show μ = (μ-1)+1 by ring]
      rw [cpow_add _ _ (ofReal_ne_zero.2 hc), cpow_one]; ring
    rw [hμ1]; push_cast; ring
  have hG : Gamma μ ≠ 0 := Gamma_ne_zero_of_re_pos hμ
  rw [hsub, ← legInt_fractional_cutPlane _ _ hμ hzc]
  have hpow : exp (-μ/2*(log ((x:ℂ)+1)-log ((x:ℂ)-1))) = ((x:ℂ)^2-1)^(-μ/2) * ((x-1:ℝ):ℂ)^μ := by
    rw [show ((x:ℂ)^2-1) = (((x+1)*(x-1):ℝ):ℂ) by push_cast; ring,
      legInt_cpow_ofReal (mul_pos h2 h1), legInt_cpow_ofReal h1, ← exp_add, Real.log_mul h2.ne' h1.ne',
      show (x:ℂ)+1 = ((x+1:ℝ):ℂ) by push_cast; ring, show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring,
      ← ofReal_log h2.le, ← ofReal_log h1.le]
    congr 1; push_cast; ring
  rw [associatedP, show (1:ℂ) - -μ = 1+μ by ring, show -μ/2 = (-μ)/2 by ring]
  rw [show (-μ)/2 = -μ/2 by ring, hpow, hz]
  field_simp

/-- ferrersQ complex integral. -/
@[dlmf 14.12.E3]
theorem ferrersQ_complex_integral {ν μ : ℂ} (hμ : -1/2 < μ.re) (h0 : -1 < (ν+μ).re) (h1 : -1 < (ν-μ).re) {θ : ℝ} (hθ : 0 < θ) (hπ : θ < π) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*Gamma (ν+μ+1)*(Real.sin θ:ℂ)^μ/(2^(μ+1)*Gamma (μ+1/2)*Gamma (ν-μ+1))*(Real.sinh t:ℂ)^(2*μ)*(1/(Real.cos θ+I*Real.sin θ*Real.cosh t)^(ν+μ+1)+1/(Real.cos θ-I*Real.sin θ*Real.cosh t)^(ν+μ+1))) 0 (ferrersQ ν μ (Real.cos θ)) := by
  sorry

/-- associatedP cosh integral. -/
@[dlmf 14.12.E4]
theorem associatedP_cosh_integral {ν μ : ℂ} (hν : LegendreQRegular ν μ) (h : 0 < (μ-ν).re) (hconv : -1 < (μ+ν).re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt 2*Gamma (μ+1/2)*(x^2-1:ℂ)^(μ/2)/(Real.sqrt π*Gamma (ν+μ+1)*Gamma (μ-ν))*cosh ((ν+1/2)*t)/(x+Real.cosh t:ℂ)^(μ+1/2)) 0 (associatedP ν (-μ) x) := by
  sorry

/-- olverQ real integral. -/
@[dlmf 14.12.E6]
theorem olverQ_real_integral {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*(x^2-1:ℂ)^(μ/2)/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*(Real.sinh t:ℂ)^(2*μ)/(x+Real.sqrt (x^2-1)*Real.cosh t:ℂ)^(ν+μ+1)) 0 (olverQ ν μ x) := by
  sorry

/-- associatedP fourier integral. -/
@[dlmf 14.12.E7]
theorem associatedP_fourier_integral (ν : ℂ) (m : ℕ) {x : ℝ} (hx : 1 < x) :
    associatedP ν m x=poch (ν+1) m/π*∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^ν*Real.cos (m*θ) := by
  have hx1 : ((x:ℂ)-1) ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h0 : ∀ μ : ℂ, associatedP μ 0 x = 1/π * legInt_L μ x 0 := fun μ => by
    rw [associatedP_zero_order _ hx1, legendreP_laplace _ hx.le, legInt_L]
    simp
  have key : ∀ k : ℕ, associatedP ν k x = poch (ν+1) k/π * legInt_L ν x k ∧
      associatedP ν (k+1:ℕ) x = poch (ν+1) (k+1)/π * legInt_L ν x (k+1) := by
    intro k
    induction k with
    | zero =>
      refine ⟨by rw [Nat.cast_zero, h0 ν]; simp [poch], ?_⟩
      have h7 := associatedP_recurrence_7 ν 0 hx1
      have hL : legInt_L (ν+1) x 0 = x * legInt_L ν x 0 + s * legInt_L ν x 1 := by
        simp only [legInt_L, CharP.cast_eq_zero, zero_mul, Real.cos_zero, ofReal_one, mul_one,
          Nat.cast_one, one_mul]
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_add]
        · refine intervalIntegral.integral_congr fun θ _ => ?_
          have hw := legInt_laplace_pos hx θ
          rw [cpow_add _ _ (ofReal_ne_zero.2 hw.ne'), cpow_one]; push_cast; ring
        · exact ((by simpa using legInt_cont_L ν hx 0 : Continuous fun θ : ℝ =>
            (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν).intervalIntegrable _ _).const_mul _
        · exact ((by simpa using legInt_cont_L ν hx 1 : Continuous fun θ : ℝ =>
            (((x + Real.sqrt (x^2-1) * Real.cos θ : ℝ)) : ℂ)^ν * Real.cos θ).intervalIntegrable
              _ _).const_mul _
      rw [h0 ν, h0 (ν+1), hb1, hL, zero_add] at h7
      apply mul_left_cancel₀ hs
      simp only [Nat.cast_zero, zero_add, Nat.cast_one, poch_succ, poch_zero, one_mul]
      linear_combination h7
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := associatedP_recurrence_6 ν (k:ℂ) hx1
      have hr := legInt_L_rec ν hx k
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      apply mul_left_cancel₀ hs
      simp only [poch_succ] at h6 ⊢
      simp only [show k+1+1 = k+2 by ring] at h6 hr ⊢
      push_cast at h6 hr ⊢
      linear_combination (s:ℂ) * h6 - 2*((k:ℂ)+1)*x*(poch (ν+1) k*(ν+1+k)/π*legInt_L ν x (k+1)) * hbm
        - poch (ν+1) k*(ν+1+k)/π * hr
  rw [(key m).1, legInt_L]; push_cast; rfl

/-- associatedP nat integral. -/
@[dlmf 14.12.E8]
theorem associatedP_nat_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    associatedP n m x=2^m*(m.factorial:ℂ)*(n+m).factorial*(x^2-1:ℂ)^((m:ℂ)/2)/(((2*m).factorial:ℂ)*(n-m).factorial*π)*∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^(n-m)*(Real.sin θ:ℂ)^(2*m) := by
  obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hmn
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (Real.sqrt (x^2-1):ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  have hI : (∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^(m+p-m)*(Real.sin θ:ℂ)^(2*m)) =
      legInt_Ks x p m := by
    rw [legInt_Ks, ← intervalIntegral.integral_ofReal, Nat.add_sub_cancel_left]
    refine intervalIntegral.integral_congr fun θ _ => ?_
    simp only [legInt_w]; push_cast; ring
  rw [hI, hpow, legInt_associatedP_Ks hx, legInt_cK, Nat.add_sub_cancel_left,
    show m+p+m = 2*m+p by ring]
  ring

/-- legendreUCoordinate. -/
@[dlmf 14.12.E10]
def legendreUCoordinate (x : ℝ) : ℝ :=
  1/2*Real.log ((x+1)/(x-1))

/-- olverQ nat finite integral. -/
@[dlmf 14.12.E9]
theorem olverQ_nat_finite_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=1/(n.factorial:ℂ)*∫ t : ℝ in 0..legendreUCoordinate x, (x-Real.sqrt (x^2-1)*Real.cosh t:ℂ)^n*Real.cosh (m*t) := by
  rw [show legendreUCoordinate x = legInt_u x from rfl]
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  have hI : (∫ t : ℝ in 0..legInt_u x, (x-Real.sqrt (x^2-1)*Real.cosh t:ℂ)^n*Real.cosh (m*t)) =
      legInt_M x n m := by
    rw [legInt_M, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [legInt_f, legInt_V]; push_cast; ring
  rw [hI]
  have h0 : ∀ k : ℕ, olverQ k 0 x = legInt_M x k 0 / k.factorial := fun k => by
    rw [legInt_olverQ_nat_zero_order _ hx1, legInt_legendreQ_M hx]
  have key : ∀ m : ℕ, olverQ n m x = legInt_M x n m / n.factorial ∧
      olverQ n (m+1:ℕ) x = legInt_M x n (m+1) / n.factorial := by
    intro m
    induction m with
    | zero =>
      refine ⟨by simpa using h0 n, ?_⟩
      have h7 := olverQ_recurrence_7 (n:ℂ) 0 hx1
      have h1 := legInt_M_one x n
      rw [hb1, zero_add, h0 n, show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, h0 (n+1)] at h7
      apply mul_left_cancel₀ hs
      simp only [zero_add, Nat.cast_one]
      apply_fun ((↑) : ℝ → ℂ) at h1
      rw [Nat.factorial_succ] at h7
      push_cast at h1 h7
      have e : ((n:ℂ)+1)*((legInt_M x (n+1) 0:ℂ)/(((n:ℂ)+1)*n.factorial)) =
          (legInt_M x (n+1) 0:ℂ)/n.factorial := by
        have : (n:ℂ)+1 ≠ 0 := by norm_cast
        field_simp
      linear_combination -h7 - e - h1/(n.factorial:ℂ)
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := olverQ_recurrence_6 (n:ℂ) (k:ℂ) hx1
      have hr := legInt_M_ord hx n k
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      have hnk : ((n:ℂ)+((k+1+1:ℕ):ℂ)) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero hnk hs)
      apply_fun ((↑) : ℝ → ℂ) at hr
      push_cast at hr h6 ⊢
      linear_combination (s:ℂ) * h6 + 2*((k:ℂ)+1)*x*((legInt_M x n (k+1):ℂ)/n.factorial)*hbm -
        hr/(n.factorial:ℂ)
  rw [(key m).1]; ring

/-- olverQ nat interval integral. -/
@[dlmf 14.12.E11]
theorem olverQ_nat_interval_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=(x^2-1:ℂ)^((m:ℂ)/2)/(2^(n+1)*(n.factorial:ℂ))*∫ t : ℝ in -1..1, (1-t^2:ℂ)^n/(x-t:ℂ)^(n+m+1) := by
  have hx1 : (x:ℂ)-1 ∈ slitPlane := legInt_one_lt_mem hx
  set s := Real.sqrt (x^2-1) with hs_def
  have hs : (s:ℂ) ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 (by nlinarith)).ne'
  have hss : (s:ℂ)^2 = (x:ℂ)^2-1 := by
    rw [← ofReal_pow, hs_def, Real.sq_sqrt (by nlinarith)]; push_cast; ring
  have hb1 : legendreBranchPower 1 x = s := by
    rw [legInt_legendreBranchPower_real _ hx, show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      hs_def, Real.sqrt_eq_rpow, ofReal_cpow (by nlinarith)]
    push_cast; ring_nf
  have hbm : legendreBranchPower (-1) x * s = 1 := by
    rw [← hb1, legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hpow : ((x:ℂ)^2-1)^((m:ℂ)/2) = (s:ℂ)^m := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring,
      show (m:ℂ)/2 = (((m:ℝ)/2 : ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by nlinarith),
      ← ofReal_pow]
    congr 1
    rw [hs_def, Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast (by nlinarith)]
    ring_nf
  have hI : (∫ t : ℝ in -1..1, (1-t^2:ℂ)^n/(x-t:ℂ)^(n+m+1)) = legInt_A x n (n+m+1) := by
    rw [legInt_A, ← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast; ring
  rw [hI, hpow]
  set C : ℂ := 1/(2^(n+1)*(n.factorial:ℂ)) with hC
  have h0 : ∀ k : ℕ, olverQ k 0 x = legInt_A x k (k+1) / (2^(k+1)*k.factorial) := fun k => by
    rw [legInt_olverQ_nat_zero_order _ hx1, legInt_legendreQ_A hx, div_div]
  have key : ∀ m : ℕ, olverQ n m x = C * s^m * legInt_A x n (n+m+1) ∧
      olverQ n (m+1:ℕ) x = C * s^(m+1) * legInt_A x n (n+(m+1)+1) := by
    intro m
    induction m with
    | zero =>
      refine ⟨by rw [Nat.cast_zero, h0 n, hC]; simp; ring, ?_⟩
      have h7 := olverQ_recurrence_7 (n:ℂ) 0 hx1
      have hb := legInt_A_b hx n
      rw [hb1, zero_add, h0 n, show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, h0 (n+1)] at h7
      apply mul_left_cancel₀ hs
      simp only [zero_add, Nat.cast_one]
      apply_fun ((↑) : ℝ → ℂ) at hb
      rw [Nat.factorial_succ] at h7
      push_cast at hb h7
      have hn1 : (n:ℂ)+1 ≠ 0 := by norm_cast
      have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
      have e : ((n:ℂ)+1)*((legInt_A x (n+1) (n+1+1):ℂ)/(2^(n+1+1)*(((n:ℂ)+1)*n.factorial))) =
          C * (legInt_A x (n+1) (n+2):ℂ)/2 := by
        rw [hC]; field_simp; ring
      rw [show n+1+1 = n+2 by ring] at e h7 ⊢
      have e2 : (legInt_A x n (n+1):ℂ)/(2^(n+1)*n.factorial) = C * legInt_A x n (n+1) := by
        rw [hC]; ring
      rw [e2] at h7
      linear_combination -h7 - e - C/2*hb - C*(legInt_A x n (n+2):ℂ)*hss
    | succ k ih =>
      refine ⟨ih.2, ?_⟩
      have h6 := olverQ_recurrence_6 (n:ℂ) (k:ℂ) hx1
      have hord := legInt_A_ord hx n (n+k+1)
      rw [show (k:ℂ)+1 = ((k+1:ℕ):ℂ) by push_cast; ring, ih.2,
        show (k:ℂ)+2 = ((k+1+1:ℕ):ℂ) by push_cast; ring, ih.1] at h6
      have hnk : ((n:ℂ)+((k+1+1:ℕ):ℂ)) ≠ 0 := by norm_cast
      apply mul_left_cancel₀ (mul_ne_zero hnk hs)
      apply_fun ((↑) : ℝ → ℂ) at hord
      simp only [show n+(k+1)+1 = n+k+1+1 by ring, show n+(k+1+1)+1 = n+k+1+2 by ring] at h6 ⊢
      push_cast at hord h6 ⊢
      linear_combination (s:ℂ) * h6 + 2*((k:ℂ)+1)*x*C*(s:ℂ)^(k+1)*(legInt_A x n (n+k+1+1):ℂ)*hbm
        + C*(s:ℂ)^(k+1)*hord - ((n:ℂ)+k+2)*C*(s:ℂ)^(k+1)*(legInt_A x n (n+k+1+2):ℂ)*hss
  rw [(key m).1, hC]; ring

/-! ### Helpers for DLMF 14.12.12 (prefix `legIR_`) -/

/-- For real `t > 1`, `t - 1` lies in the slit plane. -/
lemma legIR_sub_one_mem {t : ℝ} (ht : 1 < t) : (t:ℂ) - 1 ∈ slitPlane := by
  rw [show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring]
  exact ofReal_mem_slitPlane.2 (by linarith)

/-- A terminating `₂F₁(-N,-n;c+1;w)` sum with `w ≥ 0` has real part at least `1`. -/
lemma legIR_sum_re_ge (N n c : ℕ) {w : ℝ} (hw : 0 ≤ w) :
    1 ≤ (∑ k ∈ Finset.range (N+1), gaussHGCoeff (-(N:ℂ)) (-(n:ℂ)) ((c:ℂ)+1) k * (w:ℂ)^k).re := by
  have hterm : ∀ k, gaussHGCoeff (-(N:ℂ)) (-(n:ℂ)) ((c:ℂ)+1) k * (w:ℂ)^k =
      ((((N.descFactorial k * n.descFactorial k : ℕ):ℝ) / (((c+1).ascFactorial k * k ! : ℕ):ℝ) * w^k : ℝ) : ℂ) := by
    intro k
    have h1 : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    rw [gaussHGCoeff, poch_neg_coe_nat, poch_neg_coe_nat, show (c:ℂ)+1 = ((c+1:ℕ):ℂ) by push_cast; ring,
      poch, ascPochhammer_nat_eq_natCast_ascFactorial]
    push_cast
    linear_combination ((N.descFactorial k:ℂ) * n.descFactorial k / (((c+1).ascFactorial k:ℂ) * k !) * (w:ℂ)^k) * h1
  simp_rw [hterm]
  rw [← ofReal_sum, ofReal_re]
  have h0 : ∀ k ∈ Finset.range (N+1), 0 ≤ (((N.descFactorial k * n.descFactorial k : ℕ):ℝ) / (((c+1).ascFactorial k * k ! : ℕ):ℝ) * w^k) :=
    fun k _ => by positivity
  refine le_trans ?_ (Finset.single_le_sum h0 (Finset.mem_range.2 (Nat.succ_pos N)))
  simp

/-- Norm of the branch power `(t²-1)^{m/2}` for real `t > 1`. -/
lemma legIR_norm_bp (m : ℕ) {t : ℝ} (ht : 1 < t) :
    ‖legendreBranchPower m t‖ = Real.exp (m/2*(Real.log (t-1) + Real.log (t+1))) := by
  rw [legendreBranchPower, norm_exp, show (t:ℂ)-1 = ((t-1:ℝ):ℂ) by push_cast; ring,
    show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring, ← ofReal_log (by linarith), ← ofReal_log (by linarith)]
  simp

/-- For integers `0 ≤ m ≤ n`, `|P^m_n(t)| ≥ C (t²-1)^{m/2}` on `t > 1`, via Pfaff to a
terminating series with nonnegative terms. -/
lemma legIR_norm_associatedP_ge (n m : ℕ) (hmn : m ≤ n) : ∃ C > 0, ∀ t : ℝ, 1 < t →
    C * ‖legendreBranchPower m t‖ ≤ ‖associatedP n m t‖ := by
  obtain ⟨N, rfl⟩ := Nat.exists_eq_add_of_le hmn
  set K := poch (((m+N:ℕ):ℂ) - m + 1) (2*m) / 2^m with hKdef
  have hK : K ≠ 0 := by
    rw [hKdef, show ((m+N:ℕ):ℂ) - m + 1 = ((N+1:ℕ):ℂ) by push_cast; ring, poch,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    have : (N+1).ascFactorial (2*m) ≠ 0 := (Nat.ascFactorial_pos _ _).ne'
    exact div_ne_zero (by exact_mod_cast this) (pow_ne_zero _ two_ne_zero)
  have hc : ∀ k : ℕ, (m:ℂ)+1 ≠ -(k:ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith
  have hΓ : Gamma ((m:ℂ)+1) ≠ 0 := Gamma_ne_zero (fun k h => hc k h)
  refine ⟨‖K‖ / ‖Gamma ((m:ℂ)+1)‖, by positivity, fun t ht => ?_⟩
  have hs := legIR_sub_one_mem ht
  rw [associatedP_integer_hypergeometric_8 _ m hs]
  have h1z : 1 - (1-(t:ℂ))/2 = (((1+t)/2 : ℝ) : ℂ) := by push_cast; ring
  have hz : (1-(t:ℂ))/2 ∈ cutPlane := by
    rw [mem_cutPlane, h1z]; exact ofReal_mem_slitPlane.2 (by linarith)
  have hw : (1-(t:ℂ))/2/((1-(t:ℂ))/2-1) = (((t-1)/(t+1) : ℝ) : ℂ) := by
    have : (t:ℂ)+1 ≠ 0 := by
      rw [show (t:ℂ)+1 = ((t+1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by linarith)
    have hd : (1-(t:ℂ))/2-1 ≠ 0 := by
      rw [show (1-(t:ℂ))/2-1 = -((t:ℂ)+1)/2 by ring]; exact div_ne_zero (neg_ne_zero.2 this) two_ne_zero
    push_cast; rw [div_eq_div_iff hd this]; ring
  have hwn : ‖(1-(t:ℂ))/2/((1-(t:ℂ))/2-1)‖ < 1 := by
    rw [hw, norm_real, Real.norm_eq_abs, abs_lt]
    constructor
    · rw [lt_div_iff₀ (by linarith)]; linarith
    · rw [div_lt_iff₀ (by linarith)]; linarith
  rw [regularizedGaussHG_symm _ _ _ hz, regularizedGaussHG_pfaff _ _ _ hz,
    regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hwn, regularizedGaussHGFun_eq_div_Gamma hc,
    show (m:ℂ) - ((m+N:ℕ):ℂ) = -(N:ℂ) by push_cast; ring,
    show (m:ℂ) + 1 - (((m+N:ℕ):ℂ) + m + 1) = -((m+N:ℕ):ℂ) by push_cast; ring,
    ordinaryHypergeometric_eq_sum_neg_nat, hw, h1z]
  have hsum := le_trans (legIR_sum_re_ge N (m+N) m (w := (t-1)/(t+1))
    (div_nonneg (by linarith) (by linarith))) (re_le_norm _)
  have hpow : 1 ≤ ‖((((1+t)/2 : ℝ)) : ℂ)^(-(-(N:ℂ)))‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.one_le_rpow (by linarith) (by simp)
  rw [norm_mul, norm_mul, norm_mul, norm_div _ (Gamma ((m:ℂ)+1))]
  have hbp : 0 ≤ ‖legendreBranchPower (m:ℂ) (t:ℂ)‖ := norm_nonneg _
  have hΓn : 0 < ‖Gamma ((m:ℂ)+1)‖ := norm_pos_iff.2 hΓ
  calc ‖K‖ / ‖Gamma ((m:ℂ)+1)‖ * ‖legendreBranchPower (m:ℂ) (t:ℂ)‖
      = ‖K‖ * ‖legendreBranchPower (m:ℂ) (t:ℂ)‖ * (1 * (1 / ‖Gamma ((m:ℂ)+1)‖)) := by ring
    _ ≤ _ := by gcongr

/-- `𝑸^m_n(x) → 0` as `x → ∞` (from DLMF 14.8.15). -/
lemma legIR_olverQ_tendsto_zero (n m : ℕ) :
    Tendsto (fun x : ℝ => olverQ n m x) atTop (𝓝 0) := by
  have hν : ∀ k : ℕ, (n:ℂ) ≠ -k-3/2 := fun k h => by
    have := congrArg re h; simp at this; linarith
  refine (legendre_singular_15 (n:ℂ) (m:ℂ) hν).symm.tendsto_nhds ?_
  have h : Tendsto (fun x : ℝ => (Real.sqrt π/Gamma ((n:ℂ)+3/2)) * ((((2*x)^(n+1))⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    have := (continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp
      ((tendsto_pow_atTop (Nat.succ_ne_zero n)).comp (tendsto_id.const_mul_atTop (two_pos (α := ℝ)))))
    simpa using this.const_mul (Real.sqrt π/Gamma ((n:ℂ)+3/2))
  refine h.congr' ?_
  filter_upwards with x
  rw [show (n:ℂ)+1 = ((n+1:ℕ):ℂ) by push_cast; ring, cpow_natCast]
  push_cast; ring


/-- olverQ nat reduction integral. -/
@[dlmf 14.12.E12]
theorem olverQ_nat_reduction_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) x (olverQ n m x) := by
  obtain ⟨C, hC, hPC⟩ := legIR_norm_associatedP_ge n m hmn
  have hPne : ∀ t : ℝ, 1 < t → associatedP n m t ≠ 0 := fun t ht h => by
    have h1 := hPC t ht
    rw [h, norm_zero, legIR_norm_bp m ht] at h1
    have : 0 < C * Real.exp (m/2*(Real.log (t-1) + Real.log (t+1))) := by positivity
    linarith
  have hfac : Gamma ((n:ℂ)-m+1) = ((n-m).factorial:ℂ) := by
    rw [show (n:ℂ)-m+1 = ((n-m:ℕ):ℂ)+1 by push_cast [Nat.cast_sub hmn]; ring, Gamma_nat_eq_factorial]
  have hfac0 : ((n-m).factorial:ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  set F : ℝ → ℂ := fun s => -associatedP n m x * (olverQ n m s / associatedP n m s) with hF
  have hderiv : ∀ t : ℝ, 1 < t → HasDerivAt F
      (associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) t := by
    intro t ht
    have hs := legIR_sub_one_mem ht
    have hQd := ((olverQ_analytic n m) _ hs).differentiableAt.hasDerivAt
    have hPd := ((associatedP_analytic n m) _ hs).differentiableAt.hasDerivAt
    have h := ((hQd.div hPd (hPne t ht)).comp_ofReal).const_mul (-associatedP n m x)
    have hw := olverQ_wronskian_pos (n:ℂ) (m:ℂ) hs
    rw [LegendreWronskian, hfac] at hw
    have ht2 : (t:ℂ)^2-1 ≠ 0 := by
      rw [show (t:ℂ)^2-1 = ((t^2-1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by nlinarith)
    convert h using 1
    have hP := hPne t ht
    rw [show deriv (olverQ n m) t * associatedP n m t - olverQ n m t * deriv (associatedP n m) t
      = associatedP n m t * deriv (olverQ n m) t - olverQ n m t * deriv (associatedP n m) t by ring, hw]
    field_simp
  have hcont : ∀ t : ℝ, 1 < t → ContinuousAt (fun t : ℝ => associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) t := by
    intro t ht
    have hs := legIR_sub_one_mem ht
    have hPc : ContinuousAt (fun s : ℝ => associatedP n m s) t :=
      ((associatedP_analytic n m) _ hs).continuousAt.comp continuous_ofReal.continuousAt
    have ht2 : (t:ℂ)^2-1 ≠ 0 := by
      rw [show (t:ℂ)^2-1 = ((t^2-1:ℝ):ℂ) by push_cast; ring]; exact ofReal_ne_zero.2 (by nlinarith)
    exact continuousAt_const.div (((continuous_ofReal.continuousAt.pow 2).sub continuousAt_const).mul
      (hPc.pow 2)) (mul_ne_zero ht2 (pow_ne_zero _ (hPne t ht)))
  have hint : ∀ R, x ≤ R → ∫ t in x..R, associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2) = F R - F x := by
    intro R hR
    have hmem : ∀ t ∈ uIcc x R, 1 < t := fun t ht => by
      rw [uIcc_of_le hR] at ht; linarith [ht.1]
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hderiv t (hmem t ht))
      (ContinuousOn.intervalIntegrable fun t ht => (hcont t (hmem t ht)).continuousWithinAt)
  have hFx : F x = -olverQ n m x := by
    simp only [hF]; field_simp [hPne x hx]
  have hQP : Tendsto (fun R : ℝ => olverQ n m R / associatedP n m R) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using ((legIR_olverQ_tendsto_zero n m).norm.div_const C))
    filter_upwards [eventually_ge_atTop (2:ℝ)] with R hR
    have h1 := hPC R (by linarith)
    rw [legIR_norm_bp m (by linarith)] at h1
    have he : 1 ≤ Real.exp (m/2*(Real.log (R-1) + Real.log (R+1))) :=
      Real.one_le_exp (by
        have := Real.log_nonneg (show (1:ℝ) ≤ R-1 by linarith)
        have := Real.log_nonneg (show (1:ℝ) ≤ R+1 by linarith)
        positivity)
    rw [norm_div, div_le_div_iff₀ (by nlinarith) hC]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (norm_nonneg _)
  have hlim : Tendsto (fun R => F R - F x) atTop (𝓝 (olverQ n m x)) := by
    have := ((hQP.const_mul (-associatedP n m x)).sub_const (F x))
    rw [hFx, mul_zero, zero_sub, neg_neg] at this
    rw [hFx]
    exact this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  exact (hint R hR).symm

/-- olverQ nat neumann. -/
@[dlmf 14.12.E13]
theorem olverQ_nat_neumann (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ n 0 z=1/(2*(n.factorial:ℂ))*∫ t : ℝ in -1..1, legendreP n t/(z-t) := by
  have hreg : LegendreQRegular (n:ℂ) 0 := fun k hk => by
    have := congrArg re hk; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  have hf : (n.factorial:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hi : ∫ t : ℝ in -1..1, legendreP n t/(z-t) =
      ∫ t : ℝ in -1..1, AAR.OrthogonalPolynomials.legendrePolyP n t/(z-t) := by
    refine intervalIntegral.integral_congr_ae ?_
    have : ∀ᵐ t : ℝ ∂volume, t ≠ -1 := by
      simp [ae_iff]
    filter_upwards [this] with t ht htm
    rw [uIoc_of_le (by norm_num)] at htm
    rw [legendreP_nat n (Or.inl (by simp; linarith [htm.1]))]
  rw [olverQ_normalization hreg, associatedQ_zero_order _ hz, add_zero, Gamma_nat_eq_factorial, hi,
    legendreQ_nat_eq_integral n hz]
  simp
  field_simp

/-- olverQ nat heine. -/
@[dlmf 14.12.E14]
theorem olverQ_nat_heine (n : ℕ) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => 1/((n.factorial:ℂ)*(x+Real.sqrt (x^2-1)*Real.cosh t:ℂ)^(n+1))) 0 (olverQ n 0 x) := by
  rw [legInt_olverQ_nat_zero_order _ (legInt_one_lt_mem hx)]
  refine ((legInt_heine x hx n).div_const (n.factorial:ℂ)).congr fun R => ?_
  rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr fun t _ => ?_
  simp only [legInt_W]; push_cast
  field_simp

/-- associatedP complex integral. -/
@[dlmf 14.25.E1]
theorem associatedP_complex_integral {ν μ : ℂ} (h0 : -1 < ν.re) (h1 : ν.re < μ.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => legendreBranchPower μ z/(2^ν*Gamma (μ-ν)*Gamma (ν+1))*((Real.sinh t:ℂ)^(2*ν+1)/(z+Real.cosh t)^(ν+μ+1))) 0 (associatedP ν (-μ) z) := by
  sorry

/-- olverQ complex integral. -/
@[dlmf 14.25.E2]
theorem olverQ_complex_integral {ν μ : ℂ} (h0 : -1/2 < μ.re) (h1 : μ.re < (ν+1).re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => Real.sqrt π*legendreBranchPower μ z/(2^μ*Gamma (μ+1/2)*Gamma (ν-μ+1))*((Real.sinh t:ℂ)^(2*μ)/(z+exp ((log (z-1)+log (z+1))/2)*Real.cosh t)^(ν+μ+1))) 0 (olverQ ν μ z) := by
  sorry

/-- ferrersP negative order integral. -/
@[dlmf 14.6.E6]
theorem ferrersP_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-m) x=(1-x^2:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in x..1, f t)^[m]) (ferrersP ν 0) x := by
  rw [legInt_iterate_ferrers ν m ⟨hx.1, hx.2.le⟩, legInt_H, ferrersP]
  have h1 : (0:ℝ) < 1 + x := by linarith [hx.1]
  have h2 : (0:ℝ) < 1 - x := by linarith [hx.2]
  have hreal : ((1+x)/(1-x)) ^ (-(m:ℝ)/2) = (1-x^2) ^ (-(m:ℝ)/2) * (1-x)^m := by
    rw [Real.div_rpow h1.le h2.le, show 1 - x^2 = (1+x)*(1-x) by ring,
      Real.mul_rpow h1.le h2.le, ← Real.rpow_natCast (1-x) m, div_eq_mul_inv, mul_assoc,
      ← Real.rpow_neg h2.le, ← Real.rpow_add h2]
    congr 2; ring
  have hc := congrArg (fun r : ℝ => (r:ℂ)) hreal
  rw [ofReal_mul, ofReal_cpow (div_pos h1 h2).le, ofReal_cpow (by nlinarith), ofReal_pow] at hc
  push_cast at hc
  push_cast
  rw [hc, show (1:ℂ) - -(m:ℂ) = m+1 by ring]
  ring

/-- associatedP negative order integral. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-m) x=(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in 1..x, f t)^[m]) (fun x : ℝ => associatedP ν 0 x) x := by
  have hz : (x:ℂ)-1 ∈ slitPlane := Or.inl (by simp; linarith)
  rw [legInt_iterate_associated ν m hx.le, legInt_associatedP_neg_nat ν m hz,
    legInt_legendreBranchPower_real _ hx]

/-- associatedQ negative order integral. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) (hν : (m:ℝ)-1 < ν.re) {x : ℝ} (hx : 1 < x) :
    associatedQ ν (-m) x=(-1)^m*(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[m]) (fun x : ℝ => associatedQ ν 0 x) x := by
  rw [legInt_iterate_Q ν m hν hx, legInt_g, legInt_legendreBranchPower_real _ hx]
  have hne : ((x:ℂ)^2-1) ≠ 0 := by
    rw [show (x:ℂ)^2-1 = ((x^2-1:ℝ):ℂ) by push_cast; ring]
    exact_mod_cast (by nlinarith : (x^2-1:ℝ) ≠ 0)
  have hc : ((x:ℂ)^2-1)^(-(m:ℂ)/2) * ((x:ℂ)^2-1)^((m:ℂ)/2) = 1 := by
    rw [← cpow_add _ _ hne, show -(m:ℂ)/2 + (m:ℂ)/2 = 0 by ring, cpow_zero]
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(associatedQ ν (-m) x)*(-1)^m*(-1)^m) * hc - (associatedQ ν (-m) x) * hsq

/-- DLMF 14.6.7 extended to the principal complex sheet by iterated segment primitives. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f 1 z)^[m]) (associatedP ν 0) z := by
  rw [legInt_iterate_segment ν m (Or.inr hz), legInt_associatedP_neg_nat ν m hz]

/-- DLMF 14.6.8: a tail joined to the positive real axis, with actual convergence. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    (hν : (m:ℝ)-1 < ν.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν (-m) z=(-1)^m*legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[m])
        (associatedQ ν 0) z := by
  rw [legInt_iterate_Qc ν m hν hz, legInt_g]
  have hc : legendreBranchPower (-m) z * legendreBranchPower m z = 1 := by
    rw [legendreBranchPower_mul, neg_add_cancel]; simp [legendreBranchPower]
  have hsq : (-1:ℂ)^m*(-1)^m = 1 := by rw [← mul_pow]; norm_num
  linear_combination (-(associatedQ ν (-m) z)*(-1)^m*(-1)^m) * hc - (associatedQ ν (-m) z) * hsq

end AAR.Legendre
