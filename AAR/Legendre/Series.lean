/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Hypergeometric
public import AAR.Legendre.Integer
public import AAR.Legendre.Neumann
public import AAR.Legendre.AssociatedRecurrences
public import AAR.Legendre.SpecialValues
public import AAR.OrthogonalPolynomials.Series

/-!
# Legendre Fourier series, generating functions and continued fractions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrersP fourier series. -/
@[dlmf 14.13.E1]
theorem ferrersP_fourier_series {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 1/2) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, 2^(μ+1)/Real.sqrt π*(Real.sin θ:ℂ)^μ*Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)) atTop (𝓝 (ferrersP ν μ (Real.cos θ))) := by
  sorry

/-- Absolute convergence in DLMF 14.13. -/
theorem ferrersP_fourier_absolute {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 0) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)‖) := by
  sorry

/-- ferrersP nat fourier. -/
@[dlmf 14.13.E3]
theorem ferrersP_nat_fourier (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, 2^(2*n+2)*(n.factorial:ℂ)^2/(π*((2*n+1).factorial:ℂ))*poch (1/2) k*poch (n+1) k/((k.factorial:ℂ)*poch (n+3/2) k)*sin ((n+2*k+1:ℂ)*θ)) atTop (𝓝 (ferrersP n 0 (Real.cos θ))) := by
  sorry

/-- ferrersQ fourier series. -/
@[dlmf 14.13.E2]
theorem ferrersQ_fourier_series {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 1/2) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, Real.sqrt π*2^μ*(Real.sin θ:ℂ)^μ*Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)) atTop (𝓝 (ferrersQ ν μ (Real.cos θ))) := by
  sorry

/-- Absolute convergence in DLMF 14.13. -/
theorem ferrersQ_fourier_absolute {ν μ : ℂ} (hν : LegendreQRegular ν μ) (hμ : μ.re < 0) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/(k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)‖) := by
  sorry

/-- ferrersQ nat fourier. -/
@[dlmf 14.13.E4]
theorem ferrersQ_nat_fourier (n : ℕ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, 2^(2*n+1)*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*poch (1/2) k*poch (n+1) k/((k.factorial:ℂ)*poch (n+3/2) k)*cos ((n+2*k+1:ℂ)*θ)) atTop (𝓝 (ferrersQ n 0 (Real.cos θ))) := by
  sorry

/-- legendreQPoly convolution. -/
@[dlmf 14.7.E4]
theorem legendreQPoly_convolution (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z=∑ j ∈ Finset.range n, legendreP j z*legendreP (n-j-1) z/(j+1:ℂ) := by
  sorry

/-- legendreQPoly explicit. -/
@[dlmf 14.7.E3]
theorem legendreQPoly_explicit (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z=∑ s ∈ Finset.range n, ((n+s).factorial:ℂ)*(digamma (n+1)-digamma (s+1))/(2^s*(n-s).factorial*(s.factorial:ℂ)^2)*(z-1)^s := by
  sorry

/-- legendreQPoly initial. -/
@[dlmf 14.7.E5]
theorem legendreQPoly_initial  :
    legendreQPoly 1=1 ∧ legendreQPoly 2=Polynomial.C (3/2)*Polynomial.X ∧ legendreQPoly 3=Polynomial.C (5/2)*Polynomial.X^2-Polynomial.C (2/3) := by
  have h2 : legendreQPoly 2=Polynomial.C (3/2)*Polynomial.X := by
    norm_num [legendreQPoly, ← mul_assoc, ← Polynomial.C_mul]
  have h3 : legendreQPoly 3=Polynomial.C (5/2)*Polynomial.X^2-Polynomial.C (2/3) := by
    rw [legendreQPoly, h2]
    norm_num only [legendreQPoly, mul_one]
    rw [show Polynomial.C (1/3:ℂ)*(Polynomial.C 5*Polynomial.X*(Polynomial.C (3/2)*Polynomial.X)-Polynomial.C 2) =
      (Polynomial.C (1/3)*Polynomial.C 5*Polynomial.C (3/2))*Polynomial.X^2-
        Polynomial.C (1/3)*Polynomial.C 2 by ring]
    norm_num [← Polynomial.C_mul]
  exact ⟨rfl,h2,h3⟩

/-- ferrersQ nat logarithm. -/
@[dlmf 14.7.E2]
theorem ferrersQ_nat_logarithm (n : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ n 0 x=1/2*ferrersP n 0 x*log ((1+x)/(1-x):ℂ)-(legendreQPoly n).eval (x:ℂ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
      simp [legendreQPoly, ferrersQ_degree_0 hx, ferrersP_degree_0 hx]
    | 1, _ =>
      simp only [Nat.cast_one, legendreQPoly, Polynomial.eval_one]
      rw [ferrersQ_degree_1 hx, ferrersP_degree_1 hx]; ring
    | n + 2, ih =>
      have hreg : LegendreQRegular (n:ℂ) 0 := fun k hk => by
        have : ((n:ℝ) : ℂ).re = (-((k:ℂ)+1)).re := by rw [← hk]; simp
        simp at this; linarith [(n.cast_nonneg : (0:ℝ) ≤ n), (k.cast_nonneg : (0:ℝ) ≤ k)]
      have hQ := ferrersQ_recurrence_3 (n:ℂ) 0 hreg hx
      have hP := ferrersP_recurrence_3 (n:ℂ) 0 hx
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      push_cast at h1 h0 ⊢
      rw [show (n:ℂ)+2 = n+1+1 by ring] at hQ hP
      simp only [legendreQPoly, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_X]
      have hn : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
      rw [show (n:ℂ)+2 = n+1+1 by ring] at hn ⊢
      have hinv : ((n:ℂ)+1+1)*((n:ℂ)+1+1)⁻¹ = 1 := mul_inv_cancel₀ hn
      linear_combination ((n:ℂ)+1+1)⁻¹*(hQ - 1/2*log ((1+x)/(1-x):ℂ) * hP + (2 * (n : ℂ) + 3) * x * h1 -
        ((n : ℂ) + 1) * h0) - (ferrersQ ((n:ℂ)+1+1) 0 x - 1/2*log ((1+x)/(1-x):ℂ)*ferrersP ((n:ℂ)+1+1) 0 x)*hinv

/-- olverQ nat normalization. -/
@[dlmf 14.7.E6]
theorem olverQ_nat_normalization (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ n 0 z=(n.factorial:ℂ)*olverQ n 0 z := by
  simp [associatedQ, Gamma_nat_eq_factorial]

/-- associatedQ nat logarithm. -/
@[dlmf 14.7.E7]
theorem associatedQ_nat_logarithm (n : ℕ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedQ n 0 z=1/2*associatedP n 0 z*(log (z+1)-log (z-1))-(legendreQPoly n).eval z := by
  rw [associatedQ_zero_order _ hz, associatedP_zero_order _ hz, legendreQ_nat n hz, legendreQ_zero hz,
    log_add_one_sub_log_sub_one hz]
  ring

/-- ferrersP generating. -/
@[dlmf 14.7.E19]
theorem ferrersP_generating {x h : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hh : |h| < 1) :
    HasSum (fun n : ℕ => ferrersP n 0 x*(h:ℂ)^n) ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)) := by
  have hg := AAR.OrthogonalPolynomials.legendre_generating_function (x := x)
    (abs_le.mpr ⟨hx.1.le, hx.2.le⟩) (z := (h:ℂ)) (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hh)
  refine hg.congr_fun fun n => ?_
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  rw [ferrersP_zero _ hx.1, legendreP_nat n hs]

/-- ferrersQ generating. -/
@[dlmf 14.7.E20]
theorem ferrersQ_generating {x h : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) (hh : |h| < 1) :
    HasSum (fun n : ℕ => ferrersQ n 0 x*(h:ℂ)^n) ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)*log ((x-h+(1-2*x*h+h^2:ℂ)^(1/2:ℂ))/(1-x^2:ℂ)^(1/2:ℂ))) := by
  sorry

/-- associatedQ generating. -/
@[dlmf 14.7.E22]
theorem associatedQ_generating {x h : ℝ} (hx : 1 < x) (hh : |h| < x-Real.sqrt (x^2-1)) :
    HasSum (fun n : ℕ => associatedQ n 0 x*(h:ℂ)^n) ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)*log ((x-h+(1-2*x*h+h^2:ℂ)^(1/2:ℂ))/(x^2-1:ℂ)^(1/2:ℂ))) := by
  sorry

/-- associatedP generating complex. -/
@[dlmf 14.7.E19]
theorem associatedP_generating_complex {z h : ℂ} (hz : z-1 ∈ slitPlane) (hh : ‖h‖ < min ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^n) ((1-2*z*h+h^2)^(-1/2:ℂ)) := by
  sorry

/-- The exterior square root is normalized at infinity; principal sqrt of h squared would have the wrong sign for negative h. -/
@[dlmf 14.7.E21]
theorem associatedP_exterior_generating {z h : ℂ} (hz : z-1 ∈ slitPlane) (hh : max ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖ < ‖h‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^(-(n+1:ℤ))) (h⁻¹*(1-2*z/h+1/h^2)^(-1/2:ℂ)) := by
  sorry

/-- legendrePCFNum. -/
@[dlmf 14.14.E2]
def legendrePCFNum (ν μ : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (ν-μ-k+1)*(ν+μ+k)*(x^2-1)/4

/-- legendrePCFDen. -/
@[dlmf 14.14.E2]
def legendrePCFDen (μ : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (μ+k)*x

/-- legendreQCFNum. -/
@[dlmf 14.14.E4]
def legendreQCFNum (ν μ : ℂ) (k : ℕ) : ℂ :=
  (if k=0 then 1 else -1)*(ν+μ+k)*(ν-μ+k)

/-- legendreQCFDen. -/
@[dlmf 14.14.E4]
def legendreQCFDen (ν : ℂ) (x : ℝ) (k : ℕ) : ℂ :=
  (2*ν+2*k+1)*x

/-- associatedP continued fraction. -/
@[dlmf 14.14.E1]
theorem associatedP_continued_fraction (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (hnz : associatedP ν (μ-1) x ≠ 0) (hterm : ∀ k : ℕ, legendrePCFNum ν μ x (k+1) ≠ 0 ∨ legendrePCFDen μ x k ≠ 0) :
    HasContinuedFraction (legendrePCFNum ν μ x) (legendrePCFDen μ x) (Real.sqrt (x^2-1)/2*associatedP ν μ x/associatedP ν (μ-1) x) := by
  sorry

/-- associatedQ continued fraction. -/
@[dlmf 14.14.E3]
theorem associatedQ_continued_fraction {ν μ : ℂ} (hne : ν ≠ μ) {x : ℝ} (hx : 1 < x) (hr : LegendreQRegular (ν-1) μ) (hnz : associatedQ (ν-1) μ x ≠ 0) (hterm : ∀ k : ℕ, legendreQCFNum ν μ (k+1) ≠ 0 ∨ legendreQCFDen ν x k ≠ 0) :
    HasContinuedFraction (legendreQCFNum ν μ) (legendreQCFDen ν x) ((ν-μ)*associatedQ ν μ x/associatedQ (ν-1) μ x) := by
  sorry

/-- DLMF 14.13: outside the central angle, this Fourier series is not absolutely convergent. -/
theorem ferrersP_fourier_not_absolute {ν μ : ℂ} (hν : LegendreQRegular ν μ)
    (hμ0 : 0 ≤ μ.re) (hμ1 : μ.re < 1/2) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) (hmid : θ ≠ π/2) :
    ¬Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/
      (k.factorial:ℂ)*sin ((ν+μ+2*k+1)*θ)‖) := by
  sorry

/-- DLMF 14.13: the analogous second-kind Fourier series converges only conditionally. -/
theorem ferrersQ_fourier_not_absolute {ν μ : ℂ} (hν : LegendreQRegular ν μ)
    (hμ0 : 0 ≤ μ.re) (hμ1 : μ.re < 1/2) {θ : ℝ}
    (h0 : 0 < θ) (hπ : θ < π) (hmid : θ ≠ π/2) :
    ¬Summable (fun k : ℕ => ‖Gamma (ν+μ+k+1)/Gamma (ν+k+3/2)*poch (μ+1/2) k/
      (k.factorial:ℂ)*cos ((ν+μ+2*k+1)*θ)‖) := by
  sorry

/-- Unnumbered combined hypergeometric Fourier representation in DLMF 14.13. -/
theorem ferrersPQ_fourier_hypergeometric (ν μ : ℂ) (hr : LegendreQRegular ν μ)
    {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (s : ℂ) (hs : s=1 ∨ s=-1) :
    s*π*I/2*ferrersP ν μ (Real.cos θ)+ferrersQ ν μ (Real.cos θ)=
      Real.sqrt π*Gamma (ν+μ+1)*(2*Real.sin θ:ℂ)^μ*exp (s*(ν+μ+1)*I*θ)*
        regularizedGaussHG (ν+μ+1) (μ+1/2) (ν+3/2) (exp (s*2*I*θ)) := by
  sorry

end AAR.Legendre
