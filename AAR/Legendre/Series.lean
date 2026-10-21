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
public import AAR.Legendre.SeriesTools

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
  rw [← legSer_U_eq z n, legSer_coeff_U]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj : j < n := Finset.mem_range.mp hj
  simp only [legSerP]
  rw [show ((n-j-1:ℕ):ℂ) = (n:ℂ)-j-1 by rw [Nat.cast_sub (by omega), Nat.cast_sub hj.le]; simp]

/-- legendreQPoly explicit. -/
@[dlmf 14.7.E3]
theorem legendreQPoly_explicit (n : ℕ) (z : ℂ) :
    (legendreQPoly n).eval z=∑ s ∈ Finset.range n, ((n+s).factorial:ℂ)*(digamma (n+1)-digamma (s+1))/(2^s*(n-s).factorial*(s.factorial:ℂ)^2)*(z-1)^s := by
  rw [← legSerW_eq, legSerW]
  refine Finset.sum_congr rfl fun s hs => ?_
  have hs : s < n := Finset.mem_range.mp hs
  rw [Complex.digamma_nat_add_one, Complex.digamma_nat_add_one]
  simp only [legSerE, legSerA, show s ≤ n by omega, ↓reduceIte]
  push_cast
  ring

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
  have hx2 : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  set w : ℝ := √(1-x^2)
  have hw2 : w^2 = 1 - x^2 := Real.sq_sqrt hx2.le
  set ζ₁ : ℂ := x + w * I
  set ζ₂ : ℂ := x - w * I
  have hs : ζ₁ + ζ₂ = 2*x := by simp only [ζ₁, ζ₂]; ring
  have hp : ζ₁ * ζ₂ = 1 := by
    simp only [ζ₁, ζ₂]
    have : ((w:ℂ))^2 = 1 - (x:ℂ)^2 := by exact_mod_cast hw2
    linear_combination (1:ℂ) * this - (w:ℂ)^2 * Complex.I_sq
  have hnz : ∀ ζ : ℂ, (ζ = ζ₁ ∨ ζ = ζ₂) → ‖ζ‖ = 1 := by
    intro ζ hζ
    have hsq : ‖ζ‖^2 = 1 := by
      rcases hζ with rfl | rfl <;>
      · rw [Complex.sq_norm, Complex.normSq_apply]; simp [ζ₁, ζ₂]; nlinarith [hw2]
    nlinarith [norm_nonneg ζ]
  set r : ℝ := (|h| + 1)/2
  have hr : r < 1 := by simp only [r]; linarith
  have hhr : |h| < r := by simp only [r]; linarith
  have hr0 : 0 ≤ r := by simp only [r]; positivity
  have hnr : ∀ ζ : ℂ, (ζ = ζ₁ ∨ ζ = ζ₂) → ‖(r:ℂ)*ζ‖ < 1 := fun ζ hζ => by
    rw [norm_mul, hnz ζ hζ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; linarith
  have hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2 := fun t _ => by nlinarith [sq_nonneg (t-x)]
  have hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2) := fun t ht => by
    have hq' := hq t ht
    have hlt : |x - t| < √(1-2*x*t+t^2) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_lt_sqrt (sq_nonneg _) (by nlinarith)
    linarith [neg_abs_le (x-t)]
  have e := legSer_hasSum_Q_real ζ₁ ζ₂ hs hp (hnr ζ₁ (Or.inl rfl)) (hnr ζ₂ (Or.inr rfl)) hq hl hhr
    (1/2*log ((1+x)/(1-x):ℂ))
  have hP : ∀ n : ℕ, ferrersP n 0 x = legSerP x n := fun n => ferrersP_zero _ hx.1
  convert e using 1
  · funext n; rw [ferrersQ_nat_logarithm n hx, hP n]; ring
  · have hq0 := hq h hhr
    have hl0 := hl h hhr
    rw [mul_comm]
    congr 1
    rw [show (1-2*x*h+h^2:ℂ) = ((1-2*x*h+h^2:ℝ):ℂ) by push_cast; ring, legSer_cpow_half hq0.le,
      show (1-x^2:ℂ) = ((1-x^2:ℝ):ℂ) by push_cast; ring, legSer_cpow_half hx2.le,
      show ((1+x)/(1-x):ℂ) = (((1+x)/(1-x):ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (div_pos (by linarith [hx.1]) (by linarith [hx.2])).le,
      show (x:ℂ) - h + ((√(1-2*x*h+h^2):ℝ):ℂ) = ((x - h + √(1-2*x*h+h^2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, ← Complex.ofReal_log (div_pos hl0 (Real.sqrt_pos.mpr hx2)).le]
    have h1x : 0 < 1 + x := by linarith [hx.1]
    have h1x' : 0 < 1 - x := by linarith [hx.2]
    rw [Real.log_div hl0.ne' (Real.sqrt_pos.mpr hx2).ne', Real.log_sqrt hx2.le,
      Real.log_div h1x.ne' h1x'.ne', show 1 - x^2 = (1+x)*(1-x) by ring,
      Real.log_mul h1x.ne' h1x'.ne']
    push_cast; ring

/-- associatedQ generating. -/
@[dlmf 14.7.E22]
theorem associatedQ_generating {x h : ℝ} (hx : 1 < x) (hh : |h| < x-Real.sqrt (x^2-1)) :
    HasSum (fun n : ℕ => associatedQ n 0 x*(h:ℂ)^n) ((1-2*x*h+h^2:ℂ)^(-1/2:ℂ)*log ((x-h+(1-2*x*h+h^2:ℂ)^(1/2:ℂ))/(x^2-1:ℂ)^(1/2:ℂ))) := by
  have hx2 : 0 < x^2 - 1 := by nlinarith
  set w : ℝ := √(x^2-1)
  have hw2 : w^2 = x^2 - 1 := Real.sq_sqrt hx2.le
  have hw0 : 0 < w := Real.sqrt_pos.mpr hx2
  have hwx : w < x := by nlinarith
  set ρ : ℝ := x - w
  have hρ0 : 0 < ρ := by simp only [ρ]; linarith
  have hρ1 : ρ * (x + w) = 1 := by simp only [ρ]; nlinarith
  have hρ : ρ < 1 := by nlinarith
  set ζ₁ : ℂ := ((x + w : ℝ) : ℂ)
  set ζ₂ : ℂ := ((ρ : ℝ) : ℂ)
  have hs : ζ₁ + ζ₂ = 2*x := by simp only [ζ₁, ζ₂, ρ]; push_cast; ring
  have hp : ζ₁ * ζ₂ = 1 := by simp only [ζ₁, ζ₂]; rw [mul_comm]; exact_mod_cast hρ1
  set r : ℝ := (|h| + ρ)/2
  have hrρ : r < ρ := by simp only [r]; linarith
  have hhr : |h| < r := by simp only [r]; linarith
  have hr0 : 0 < r := by simp only [r]; positivity
  have h1 : ‖(r:ℂ)*ζ₁‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  have h2 : ‖(r:ℂ)*ζ₂‖ < 1 := by
    rw [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    nlinarith
  have hq : ∀ t : ℝ, |t| < r → 0 < 1-2*x*t+t^2 := fun t ht => by
    have := abs_lt.mp ht
    have e : 1-2*x*t+t^2 = (ρ - t) * (x + w - t) := by simp only [ρ]; nlinarith
    rw [e]; exact mul_pos (by linarith) (by linarith)
  have hl : ∀ t : ℝ, |t| < r → 0 < x - t + √(1-2*x*t+t^2) := fun t ht => by
    have := abs_lt.mp ht
    have := Real.sqrt_nonneg (1-2*x*t+t^2)
    linarith
  have e := legSer_hasSum_Q_real ζ₁ ζ₂ hs hp h1 h2 hq hl hhr
    (1/2*(log ((x:ℂ)+1) - log ((x:ℂ)-1)))
  have hz : (x:ℂ) - 1 ∈ slitPlane := Or.inl (by simp; linarith)
  have hP : ∀ n : ℕ, associatedP n 0 x = legSerP x n := fun n => associatedP_zero_order _ hz
  convert e using 1
  · funext n; rw [associatedQ_nat_logarithm n hz, hP n]; ring
  · have hq0 := hq h hhr
    have hl0 := hl h hhr
    rw [mul_comm]
    congr 1
    rw [show (1-2*x*h+h^2:ℂ) = ((1-2*x*h+h^2:ℝ):ℂ) by push_cast; ring, legSer_cpow_half hq0.le,
      show (x^2-1:ℂ) = ((x^2-1:ℝ):ℂ) by push_cast; ring, legSer_cpow_half hx2.le,
      show (x:ℂ) + 1 = ((x+1:ℝ):ℂ) by push_cast; ring,
      show (x:ℂ) - 1 = ((x-1:ℝ):ℂ) by push_cast; ring,
      ← Complex.ofReal_log (by linarith), ← Complex.ofReal_log (by linarith),
      show (x:ℂ) - h + ((√(1-2*x*h+h^2):ℝ):ℂ) = ((x - h + √(1-2*x*h+h^2) : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_div, ← Complex.ofReal_log (div_pos hl0 hw0).le]
    have h1x : 0 < x + 1 := by linarith
    have h1x' : 0 < x - 1 := by linarith
    rw [Real.log_div hl0.ne' hw0.ne', Real.log_sqrt hx2.le, show x^2 - 1 = (x+1)*(x-1) by ring,
      Real.log_mul h1x.ne' h1x'.ne', add_comm 1 x]
    push_cast; ring

/-- associatedP generating complex. -/
@[dlmf 14.7.E19]
theorem associatedP_generating_complex {z h : ℂ} (hz : z-1 ∈ slitPlane) (hh : ‖h‖ < min ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^n) ((1-2*z*h+h^2)^(-1/2:ℂ)) := by
  obtain ⟨hs, hp⟩ := legSer_roots hz
  set s := exp ((log (z-1)+log (z+1))/2)
  have hn : ‖z+s‖ * ‖z-s‖ = 1 := by rw [← norm_mul, hp, norm_one]
  have h1 : ‖h*(z+s)‖ < 1 := by
    rw [norm_mul]
    calc ‖h‖ * ‖z+s‖ < ‖z-s‖ * ‖z+s‖ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hh (min_le_right _ _))
            (by rcases (norm_nonneg (z+s)).lt_or_eq with h0 | h0
                · exact h0
                · rw [← h0, zero_mul] at hn; exact absurd hn zero_ne_one)
      _ = 1 := by rw [mul_comm, hn]
  have h2 : ‖h*(z-s)‖ < 1 := by
    rw [norm_mul]
    calc ‖h‖ * ‖z-s‖ < ‖z+s‖ * ‖z-s‖ :=
          mul_lt_mul_of_pos_right (lt_of_lt_of_le hh (min_le_left _ _))
            (by rcases (norm_nonneg (z-s)).lt_or_eq with h0 | h0
                · exact h0
                · rw [← h0, mul_zero] at hn; exact absurd hn zero_ne_one)
      _ = 1 := hn
  refine (legSer_generating z (z+s) (z-s) h hs hp h1 h2).congr_fun fun n => ?_
  rw [associatedP_zero_order _ hz]; rfl

/-- The exterior square root is normalized at infinity; principal sqrt of h squared would have the wrong sign for negative h. -/
@[dlmf 14.7.E21]
theorem associatedP_exterior_generating {z h : ℂ} (hz : z-1 ∈ slitPlane) (hh : max ‖z+exp ((log (z-1)+log (z+1))/2)‖ ‖z-exp ((log (z-1)+log (z+1))/2)‖ < ‖h‖) :
    HasSum (fun n : ℕ => associatedP n 0 z*h^(-(n+1:ℤ))) (h⁻¹*(1-2*z/h+1/h^2)^(-1/2:ℂ)) := by
  obtain ⟨hs, hp⟩ := legSer_roots hz
  set s := exp ((log (z-1)+log (z+1))/2)
  have hn : ‖z+s‖ * ‖z-s‖ = 1 := by rw [← norm_mul, hp, norm_one]
  have hA : 0 < ‖z+s‖ := by
    rcases (norm_nonneg (z+s)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, zero_mul] at hn; exact absurd hn zero_ne_one
  have hB : 0 < ‖z-s‖ := by
    rcases (norm_nonneg (z-s)).lt_or_eq with h0 | h0
    · exact h0
    · rw [← h0, mul_zero] at hn; exact absurd hn zero_ne_one
  have hpos : 0 < ‖h‖ := lt_of_le_of_lt (le_max_of_le_left hA.le) hh
  have h0 : h ≠ 0 := norm_pos_iff.mp hpos
  have hh' : ‖h⁻¹‖ < min ‖z+s‖ ‖z-s‖ := by
    rw [norm_inv, lt_min_iff]
    constructor
    · rw [inv_lt_iff_one_lt_mul₀ hpos, ← hn]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt (le_max_right _ _) hh) hA
    · rw [inv_lt_iff_one_lt_mul₀ hpos, ← hn, mul_comm (‖z+s‖)]
      exact mul_lt_mul_of_pos_left (lt_of_le_of_lt (le_max_left _ _) hh) hB
  have e := (associatedP_generating_complex hz hh').mul_left h⁻¹
  rw [show (1:ℂ) - 2*z*h⁻¹ + h⁻¹^2 = 1-2*z/h+1/h^2 by field_simp] at e
  refine e.congr_fun fun n => ?_
  rw [zpow_neg, show ((n:ℤ)+1) = ((n+1:ℕ):ℤ) by push_cast; ring, zpow_natCast, pow_succ,
    inv_pow]
  ring

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

/-- associatedP continued fraction, DLMF 14.14.1 corrected.

DLMF 14.14.1 states that the continued fraction with elements 14.14.2 equals
`½(x²-1)^{1/2} P^μ_ν(x)/P^{μ-1}_ν(x)`. That is false: the fraction comes from the order
recurrence 14.10.6, and it converges to the ratio of the recurrence's minimal solution
`w(μ) = Γ(ν+μ+1) P^{-μ}_ν(x)/Γ(ν-μ+1)`, whereas `P^μ_ν` is dominant. The corrected value is
`½(x²-1)^{1/2} (ν+μ)(ν-μ+1) P^{-μ}_ν(x)/P^{1-μ}_ν(x)`. At `(ν, μ, x) = (0.3, 0.4, 1.5)` the
fraction is `0.345161187628545…`, the printed right side `0.812720708269563…`, and the corrected
value agrees with the fraction to 30 digits (also checked at complex `ν`, `μ`). DLMF erratum. -/
@[dlmf 14.14.E1 "source erratum: the limit is the minimal-solution ratio (ν+μ)(ν-μ+1)P^{-μ}/P^{1-μ}"]
theorem associatedP_continued_fraction (ν μ : ℂ) {x : ℝ} (hx : 1 < x) (hnz : associatedP ν (1-μ) x ≠ 0) (hterm : ∀ k : ℕ, legendrePCFNum ν μ x (k+1) ≠ 0 ∨ legendrePCFDen μ x k ≠ 0) :
    HasContinuedFraction (legendrePCFNum ν μ x) (legendrePCFDen μ x) (Real.sqrt (x^2-1)/2*((ν+μ)*(ν-μ+1))*associatedP ν (-μ) x/associatedP ν (1-μ) x) := by
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
