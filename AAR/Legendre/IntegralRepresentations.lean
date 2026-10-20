/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Hypergeometric
public import AAR.Legendre.AssociatedRecurrences
public import AAR.Legendre.Neumann

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
  sorry

/-- associatedP fractional integral. -/
@[dlmf 14.12.E5]
theorem associatedP_fractional_integral {μ : ℂ} (hμ : 0 < μ.re) (ν : ℂ) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-μ) x=(x^2-1:ℂ)^(-μ/2)/Gamma μ*∫ t : ℝ in 1..x, associatedP ν 0 t*(x-t:ℂ)^(μ-1) := by
  sorry

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
  sorry

/-- associatedP nat integral. -/
@[dlmf 14.12.E8]
theorem associatedP_nat_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    associatedP n m x=2^m*(m.factorial:ℂ)*(n+m).factorial*(x^2-1:ℂ)^((m:ℂ)/2)/(((2*m).factorial:ℂ)*(n-m).factorial*π)*∫ θ : ℝ in 0..π, (x+Real.sqrt (x^2-1)*Real.cos θ:ℂ)^(n-m)*(Real.sin θ:ℂ)^(2*m) := by
  sorry

/-- legendreUCoordinate. -/
@[dlmf 14.12.E10]
def legendreUCoordinate (x : ℝ) : ℝ :=
  1/2*Real.log ((x+1)/(x-1))

/-- olverQ nat finite integral. -/
@[dlmf 14.12.E9]
theorem olverQ_nat_finite_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=1/(n.factorial:ℂ)*∫ t : ℝ in 0..legendreUCoordinate x, (x-Real.sqrt (x^2-1)*Real.cosh t:ℂ)^n*Real.cosh (m*t) := by
  sorry

/-- olverQ nat interval integral. -/
@[dlmf 14.12.E11]
theorem olverQ_nat_interval_integral (n m : ℕ) {x : ℝ} (hx : 1 < x) :
    olverQ n m x=(x^2-1:ℂ)^((m:ℂ)/2)/(2^(n+1)*(n.factorial:ℂ))*∫ t : ℝ in -1..1, (1-t^2:ℂ)^n/(x-t:ℂ)^(n+m+1) := by
  sorry

/-- olverQ nat reduction integral. -/
@[dlmf 14.12.E12]
theorem olverQ_nat_reduction_integral (n m : ℕ) (hmn : m ≤ n) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => associatedP n m x/((n-m).factorial:ℂ)/((t^2-1:ℂ)*(associatedP n m t)^2)) x (olverQ n m x) := by
  sorry

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
  sorry

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
  sorry

/-- associatedP negative order integral. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) {x : ℝ} (hx : 1 < x) :
    associatedP ν (-m) x=(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => ∫ t : ℝ in 1..x, f t)^[m]) (fun x : ℝ => associatedP ν 0 x) x := by
  sorry

/-- associatedQ negative order integral. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral (ν : ℂ) (m : ℕ) (hm : 0 < m) (hν : (m:ℝ)-1 < ν.re) {x : ℝ} (hx : 1 < x) :
    associatedQ ν (-m) x=(-1)^m*(x^2-1:ℂ)^(-(m:ℂ)/2)*((fun f : ℝ → ℂ => fun x => improperAtTop f x)^[m]) (fun x : ℝ => associatedQ ν 0 x) x := by
  sorry

/-- DLMF 14.6.7 extended to the principal complex sheet by iterated segment primitives. -/
@[dlmf 14.6.E7]
theorem associatedP_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f 1 z)^[m]) (associatedP ν 0) z := by
  sorry

/-- DLMF 14.6.8: a tail joined to the positive real axis, with actual convergence. -/
@[dlmf 14.6.E8]
theorem associatedQ_negative_order_integral_complex (ν : ℂ) (m : ℕ) (hm : 0 < m)
    (hν : (m:ℝ)-1 < ν.re) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ ν (-m) z=(-1)^m*legendreBranchPower (-m) z*
      ((fun f : ℂ → ℂ => fun z => segmentIntegral f z 2+improperAtTop (fun t : ℝ => f t) 2)^[m])
        (associatedQ ν 0) z := by
  sorry

end AAR.Legendre
