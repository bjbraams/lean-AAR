/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.DLMF.Framework

/-!
# Incomplete Beta continuation, recurrences and fractions, DLMF §8.17

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Statistical

/-- Continued incomplete Beta; at parameter poles the formula keeps its totalized values. -/
def incBeta (a b z : ℂ) : ℂ :=
  if z=1 then Gamma a*Gamma b/Gamma (a+b) else Gamma a*z^a*AAR.Hypergeometric.regularizedGaussHG a (1-b) (a+1) z

/-- Continued normalized incomplete Beta, preserving the removable a=0 specialization. -/
def normIncBetaI (a b z : ℂ) : ℂ :=
  if z=1 then 1 else Gamma (a+b)/Gamma b*z^a*AAR.Hypergeometric.regularizedGaussHG a (1-b) (a+1) z

/-- incBeta ofReal. -/
@[dlmf 8.17.E1]
theorem incBeta_ofReal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    incBeta a b x=Real.incBeta a b x := by
  sorry

/-- normIncBetaI ofReal. -/
@[dlmf 8.17.E2]
theorem normIncBetaI_ofReal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    normIncBetaI a b x=Real.normIncBetaI a b x := by
  sorry

/-- normIncBetaI quadratic. -/
@[dlmf 8.17.E6]
theorem normIncBetaI_quadratic {a : ℝ} (ha : 0 < a) {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1/2) :
    normIncBetaI a a x=normIncBetaI a (1/2) (4*x*(1-x))/2 := by
  sorry

/-- incBeta hypergeometric euler. -/
@[dlmf 8.17.E8]
theorem incBeta_hypergeometric_euler {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    incBeta a b x=(x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)/a*Gamma (a+1)*AAR.Hypergeometric.regularizedGaussHG (a+b) 1 (a+1) x := by
  sorry

/-- incBeta hypergeometric pfaff. -/
@[dlmf 8.17.E9]
theorem incBeta_hypergeometric_pfaff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    incBeta a b x=(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)/a*Gamma (a+1)*AAR.Hypergeometric.regularizedGaussHG 1 (1-b) (a+1) (x/(x-1)) := by
  sorry

/-- normIncBetaI mellinBarnes. -/
@[dlmf 8.17.E10]
theorem normIncBetaI_mellinBarnes {a b x c : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hxc : x < c) (hc1 : c < 1) :
    HasIntegralWholeLine (fun y : ℝ => let s : ℂ := c+y*I; s^(-(a : ℂ))*(1-s)^(-(b : ℂ))/(s-x)) (2*π*normIncBetaI a b x/((x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ))) := by
  sorry

/-- The complementary argument x prime. -/
@[dlmf 8.17.E11]
def incBetaComplement (x : ℂ) : ℂ :=
  1-x

/-- The parameter c of the contiguous recurrences. -/
@[dlmf 8.17.E11]
def incBetaContiguousParameter (a b : ℂ) : ℂ :=
  a+b-1

/-- normIncBetaI contiguous 12. -/
@[dlmf 8.17.E12]
theorem normIncBetaI_contiguous_12 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hab : a+b ≠ 1) :
    normIncBetaI (a) (b) x=(x : ℂ)*normIncBetaI (a-1) (b) x+(1-x : ℂ)*normIncBetaI (a) (b-1) x := by
  sorry

/-- normIncBetaI contiguous 13. -/
@[dlmf 8.17.E13]
theorem normIncBetaI_contiguous_13 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((a+b : ℝ) : ℂ)*normIncBetaI (a) (b) x=(a : ℂ)*normIncBetaI (a+1) (b) x+(b : ℂ)*normIncBetaI (a) (b+1) x := by
  sorry

/-- normIncBetaI contiguous 14. -/
@[dlmf 8.17.E14]
theorem normIncBetaI_contiguous_14 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((a+b*x : ℝ) : ℂ)*normIncBetaI (a) (b) x=(x : ℂ)*b*normIncBetaI (a-1) (b+1) x+(a : ℂ)*normIncBetaI (a+1) (b) x := by
  sorry

/-- normIncBetaI contiguous 15. -/
@[dlmf 8.17.E15]
theorem normIncBetaI_contiguous_15 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    ((b+a*(1-x) : ℝ) : ℂ)*normIncBetaI (a) (b) x=(a : ℂ)*(1-x)*normIncBetaI (a+1) (b-1) x+(b : ℂ)*normIncBetaI (a) (b+1) x := by
  sorry

/-- normIncBetaI contiguous 16. -/
@[dlmf 8.17.E16]
theorem normIncBetaI_contiguous_16 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hab : a+b ≠ 1) :
    (a : ℂ)*normIncBetaI (a+1) (b) x=((a : ℂ)+(a+b-1)*x)*normIncBetaI (a) (b) x-((a+b-1 : ℝ) : ℂ)*x*normIncBetaI (a-1) (b) x := by
  sorry

/-- normIncBetaI contiguous 17. -/
@[dlmf 8.17.E17]
theorem normIncBetaI_contiguous_17 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) (hab : a+b ≠ 1) :
    (b : ℂ)*normIncBetaI (a) (b+1) x=((b : ℂ)+(a+b-1)*(1-x))*normIncBetaI (a) (b) x-((a+b-1 : ℝ) : ℂ)*(1-x)*normIncBetaI (a) (b-1) x := by
  sorry

/-- normIncBetaI contiguous 18. -/
@[dlmf 8.17.E18]
theorem normIncBetaI_contiguous_18 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    normIncBetaI (a) (b) x=normIncBetaI (a+1) (b-1) x+(x : ℂ)^(a : ℂ)*(1-x : ℂ)^((b : ℂ)-1)/(a*betaIntegral a b) := by
  sorry

/-- normIncBetaI contiguous 19. -/
@[dlmf 8.17.E19]
theorem normIncBetaI_contiguous_19 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    normIncBetaI (a) (b) x=normIncBetaI (a-1) (b+1) x-(x : ℂ)^((a : ℂ)-1)*(1-x : ℂ)^(b : ℂ)/(b*betaIntegral a b) := by
  sorry

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E12]
theorem normIncBetaI_contiguous_limit_12 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun ε : ℂ => (x : ℂ)*normIncBetaI (((a : ℂ)+ε)-1) (b) x+(1-x : ℂ)*normIncBetaI (((a : ℂ)+ε)) (b-1) x) (𝓝[≠] 0) (𝓝 (normIncBetaI (a) (b) x)) := by
  sorry

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E16]
theorem normIncBetaI_contiguous_limit_16 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun ε : ℂ => ((((a : ℂ)+ε) : ℂ)+(((a : ℂ)+ε)+b-1)*x)*normIncBetaI (((a : ℂ)+ε)) (b) x-((((a : ℂ)+ε)+b-1 : ℂ) : ℂ)*x*normIncBetaI (((a : ℂ)+ε)-1) (b) x) (𝓝[≠] 0) (𝓝 ((a : ℂ)*normIncBetaI (a+1) (b) x)) := by
  sorry

/-- Limiting interpretation at the otherwise singular a+b=1 recurrence. -/
@[dlmf 8.17.E17]
theorem normIncBetaI_contiguous_limit_17 {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {x : ℝ} (hx : 0 < x) (hx1 : x < 1) :
    Tendsto (fun ε : ℂ => ((b : ℂ)+(((a : ℂ)+ε)+b-1)*(1-x))*normIncBetaI (((a : ℂ)+ε)) (b) x-((((a : ℂ)+ε)+b-1 : ℂ) : ℂ)*(1-x)*normIncBetaI (((a : ℂ)+ε)) (b-1) x) (𝓝[≠] 0) (𝓝 ((b : ℂ)*normIncBetaI (a) (b+1) x)) := by
  sorry

/-- The Gauss continued-fraction numerators d_k. -/
@[dlmf 8.17.E23]
def incBetaFractionD (a b x : ℝ) (k : ℕ) : ℂ :=
  if Even k then let m : ℂ := (k/2 : ℕ); m*(b-m)*x/((a+2*m-1)*(a+2*m)) else let m : ℂ := ((k-1)/2 : ℕ); -(a+m)*(a+b+m)*x/((a+2*m)*(a+2*m+1))

/-- The N-level scaled continued fraction; N=1 is the initial prefactor. -/
def incBetaFractionConvergent (a b x : ℝ) (N : ℕ) : ℂ :=
  (x : ℂ)^(a : ℂ)*(1-x : ℂ)^(b : ℂ)/(a*betaIntegral a b)*cfTail (fun k => if k=0 then 1 else incBetaFractionD a b x k) (fun _ => 1) 0 N

/-- incBeta continuedFraction. -/
@[dlmf 8.17.E22]
theorem incBeta_continuedFraction {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 ≤ x) (hx1 : x < 1) :
    Tendsto (incBetaFractionConvergent a b x) atTop (𝓝 (normIncBetaI a b x)) := by
  sorry

/-- incBeta continuedFraction endpoint limit. -/
@[dlmf 8.17.E22]
theorem incBeta_continuedFraction_endpoint_limit {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun x : ℝ => normIncBetaI a b x) (𝓝[<] 1) (𝓝 1) := by
  sorry

/-- Counterexample to the unqualified upper-convergent claim following 8.17.23: the second convergent is sqrt(2)/5. -/
theorem incBeta_cf_upper_bound_counterexample  :
    (Real.normIncBetaI 1 (1/2) (1/2)).re > Real.sqrt 2/5 := by
  have h := Real.normIncBetaI_symm (a := 1) (b := 1/2) (x := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.normIncBetaI_one_right (by norm_num)] at h
  norm_num at h
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : ((1/2 : ℂ)^(1/2 : ℂ)).re=Real.sqrt 2/2 := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using congrArg Complex.re hh.symm
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, hp] at hr
  have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  nlinarith [Real.sqrt_nonneg 2]

/-- Exact value of the second continued-fraction convergent in the counterexample. -/
theorem incBeta_cf_second_counterexample_value  :
    incBetaFractionConvergent 1 (1/2) (1/2) 2=(Real.sqrt 2/5 : ℝ) := by
  have hb : betaIntegral (1 : ℂ) (1/2)=2 := by
    rw [betaIntegral_symm (1/2) 1, betaIntegral_eval_one_right (by norm_num)]
    norm_num
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : (1/2 : ℂ)^(1/2 : ℂ)=(Real.sqrt 2/2 : ℝ) := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using hh.symm
  norm_num [incBetaFractionConvergent, cfTail, cfContinuants, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen, incBetaFractionD, hb, hp]
  push_cast
  ring

/-- normIncBetaI negative binomial sum. -/
@[dlmf 8.17.E24]
theorem normIncBetaI_negative_binomial_sum {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun j : ℕ => if m ≤ j then (1-x : ℂ)^n*((n+j-1).choose j : ℂ)*(x : ℂ)^j else 0) (normIncBetaI m n x) := by
  sorry

/-- The three-level convergent is also below I, independently of the indexing convention. -/
theorem incBeta_cf_third_bound_counterexample  :
    (Real.normIncBetaI 1 (1/2) (1/2)).re > 23*Real.sqrt 2/112 := by
  have h := Real.normIncBetaI_symm (a := 1) (b := 1/2) (x := 1/2)
    (by norm_num) (by norm_num) (by norm_num)
  rw [Real.normIncBetaI_one_right (by norm_num)] at h
  norm_num at h
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : ((1/2 : ℂ)^(1/2 : ℂ)).re=Real.sqrt 2/2 := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using congrArg Complex.re hh.symm
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.one_re, hp] at hr
  have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
  nlinarith [Real.sqrt_nonneg 2]

/-- Exact value of the three-level convergent used for the alternative indexing convention. -/
theorem incBeta_cf_third_counterexample_value  :
    incBetaFractionConvergent 1 (1/2) (1/2) 3=(23*Real.sqrt 2/112 : ℝ) := by
  have hb : betaIntegral (1 : ℂ) (1/2)=2 := by
    rw [betaIntegral_symm (1/2) 1, betaIntegral_eval_one_right (by norm_num)]
    norm_num
  have hs : Real.sqrt (1/2) = Real.sqrt 2/2 := by
    have h1 := Real.sq_sqrt (by norm_num : 0 ≤ (1/2 : ℝ))
    have h2 := Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))
    nlinarith [Real.sqrt_nonneg (1/2), Real.sqrt_nonneg 2]
  have hp : (1/2 : ℂ)^(1/2 : ℂ)=(Real.sqrt 2/2 : ℝ) := by
    have hh := Complex.ofReal_cpow (by norm_num : 0 ≤ (1/2 : ℝ)) (1/2)
    rw [← Real.sqrt_eq_rpow, hs] at hh
    simpa using hh.symm
  norm_num [incBetaFractionConvergent, cfTail, cfContinuants, GenContFract.nextConts, GenContFract.nextNum, GenContFract.nextDen, incBetaFractionD, hb, hp]
  push_cast
  ring

end AAR.Statistical
