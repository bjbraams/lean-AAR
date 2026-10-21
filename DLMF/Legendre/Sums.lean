/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.Series
public import DLMF.Legendre.Integrals
public import DLMF.Legendre.Harmonics

/-!
# Legendre addition theorems and zonal harmonic series

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

/-- ferrersP addition. -/
@[dlmf 14.18.E1]
theorem ferrersP_addition (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁+θ₂ < π) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*ferrersP ν (-m) (Real.cos θ₁)*ferrersP ν m (Real.cos θ₂)*Real.cos (m*phi)) (ferrersP ν 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)-ferrersP ν 0 (Real.cos θ₁)*ferrersP ν 0 (Real.cos θ₂)) := by
  sorry

/-- ferrersQ addition. -/
@[dlmf 14.18.E3]
theorem ferrersQ_addition (ν : ℂ) {θ₁ θ₂ : ℝ} (h1 : 0 < θ₁) (h2 : 0 < θ₂) (hs : θ₁+θ₂ < π) (hhalf : θ₁ < π/2) (h12 : θ₁ < θ₂) (hr : LegendreQRegular ν 0) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*ferrersP ν (-m) (Real.cos θ₁)*ferrersQ ν m (Real.cos θ₂)*Real.cos (m*phi)) (ferrersQ ν 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)-ferrersP ν 0 (Real.cos θ₁)*ferrersQ ν 0 (Real.cos θ₂)) := by
  sorry

/-- Nonnegative integer order Ferrers P agrees with the polynomial form on `(-1, 1]`. -/
lemma ferrersP_nat_eq_ferrersPNat (n k : ℕ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n k x = ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · simp only [ferrersP, Nat.cast_zero, zero_div, cpow_zero, one_mul, sub_zero, sub_self,
        ite_true]
      have hc : ∀ j : ℕ, (1:ℂ) ≠ -(j:ℂ) := by
        intro j h; have := congrArg Complex.re h; simp at this; linarith [(j.cast_nonneg : (0:ℝ) ≤ j)]
      rw [show ((1:ℂ) - ((1:ℝ):ℂ))/2 = 0 by simp, regularizedGaussHG_zero_of_regular hc]
      simp
    · simp [ferrersP]
      left; exact_mod_cast Nat.succ_ne_zero k
  · exact (ferrersPNat_eq n k ⟨hx.1, hlt⟩).symm

/-- Negative integer order Ferrers P in polynomial form on `(-1, 1]`. -/
lemma ferrersP_neg_nat_eq_ferrersPNat (n k : ℕ) (hk : k ≤ n) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    ferrersP n (-(k:ℂ)) x = (-1)^k * ((n-k).factorial / (n+k).factorial : ℂ) * ferrersPNat n k x := by
  rcases eq_or_lt_of_le hx.2 with rfl | hlt
  · rw [ferrersPNat_one]
    rcases k with _ | k
    · rw [Nat.cast_zero, neg_zero, ← Nat.cast_zero, ferrersP_nat_eq_ferrersPNat n 0 hx,
        ferrersPNat_one]
      simp [Nat.factorial_ne_zero]
    · simp [ferrersP]
      left; intro h; have := congrArg Complex.re h; simp at this; linarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
  · have hG : ∀ j : ℕ, (n:ℂ) - k + 1 ≠ -j := by
      intro j h
      have : ((n - k + 1 + j : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hk]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    rw [ferrersP_negative_integer_order (n:ℂ) k hG ⟨hx.1, hlt⟩, ferrersPNat_eq n k ⟨hx.1, hlt⟩,
      show (n:ℂ) - k + 1 = ((n - k : ℕ) : ℂ) + 1 by push_cast [Nat.cast_sub hk]; ring,
      show (n:ℂ) + k + 1 = ((n + k : ℕ) : ℂ) + 1 by push_cast; ring,
      Gamma_nat_eq_factorial, Gamma_nat_eq_factorial]
    ring

/-- ferrersP nat addition. -/
@[dlmf 14.18.E2]
theorem ferrersP_nat_addition (n : ℕ) {θ₁ θ₂ : ℝ} (h1 : 0 ≤ θ₁) (h2 : 0 ≤ θ₂) (hs : θ₁+θ₂ < π) (phi : ℝ) :
    ferrersP n 0 (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi)=∑ m ∈ Finset.Icc (-(n:ℤ)) n, (-1:ℂ)^m*ferrersP n (-m) (Real.cos θ₁)*ferrersP n m (Real.cos θ₂)*Real.cos (m*phi) := by
  have hθ1 : θ₁ < π := by linarith
  have hθ2 : θ₂ < π := by linarith
  have hcos : ∀ θ, 0 ≤ θ → θ < π → Real.cos θ ∈ Ioc (-1:ℝ) 1 := fun θ h0 hπ =>
    ⟨by rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0 le_rfl hπ, Real.cos_le_one θ⟩
  have hx1 := hcos θ₁ h1 hθ1
  have hx2 := hcos θ₂ h2 hθ2
  have hs1 : 0 ≤ Real.sin θ₁ := Real.sin_nonneg_of_nonneg_of_le_pi h1 hθ1.le
  have hs2 : 0 ≤ Real.sin θ₂ := Real.sin_nonneg_of_nonneg_of_le_pi h2 hθ2.le
  have hsin : ∀ θ, 0 ≤ θ → θ < π → Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h0 hπ =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h0 hπ.le).symm
  have harg : -1 < Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi := by
    have hc : -1 < Real.cos (θ₁+θ₂) := by
      rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi (by linarith) le_rfl hs
    rw [Real.cos_add] at hc
    nlinarith [mul_nonneg hs1 hs2, Real.neg_one_le_cos phi]
  have hsl : 1 + ((Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos phi : ℝ) : ℂ) ∈ slitPlane :=
    Or.inl (by simp only [add_re, one_re, ofReal_re]; linarith)
  rw [ferrersP_zero _ harg, legendreP_nat n hsl]
  have hk := DLMF.OrthogonalPolynomials.LegendreAddition.legendre_eq_kernel n (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁)
    (Real.sin θ₂) (phi:ℂ) (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
    (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
  have hF : ∀ k : ℕ, ∀ θ, 0 ≤ θ → θ < π → ferrersPNat n k (Real.cos θ) =
      (-1)^k * (Real.sin θ:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ) := by
    intro k θ h0 hπ
    rw [ferrersPNat, hsin θ h0 hπ]; rfl
  have hterm : ∀ k : ℕ, k ≤ n →
      ferrersP n (-(k:ℂ)) (Real.cos θ₁) * ferrersP n k (Real.cos θ₂) =
        (-1)^k * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) ∧
      ferrersP n k (Real.cos θ₁) * ferrersP n (-(k:ℂ)) (Real.cos θ₂) =
        (-1)^k * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) := by
    intro k hkn
    rw [ferrersP_neg_nat_eq_ferrersPNat n k hkn hx1, ferrersP_neg_nat_eq_ferrersPNat n k hkn hx2,
      ferrersP_nat_eq_ferrersPNat n k hx1, ferrersP_nat_eq_ferrersPNat n k hx2,
      hF k θ₁ h1 hθ1, hF k θ₂ h2 hθ2]
    have hs : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
    simp only [DLMF.OrthogonalPolynomials.LegendreAddition.coeff, DLMF.OrthogonalPolynomials.LegendreAddition.weight]
    constructor
    · linear_combination ((-1:ℂ)^k * ((n-k).factorial / (n+k).factorial : ℂ) * (Real.sin θ₁:ℂ)^k *
        DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₁) * (Real.sin θ₂:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₂)) * hs
    · linear_combination ((-1:ℂ)^k * ((n-k).factorial / (n+k).factorial : ℂ) * (Real.sin θ₁:ℂ)^k *
        DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₁) * (Real.sin θ₂:ℂ)^k * DLMF.OrthogonalPolynomials.LegendreAddition.jet n k (Real.cos θ₂)) * hs
  push_cast at hk ⊢
  rw [hk, sum_Icc_neg_pair, DLMF.OrthogonalPolynomials.LegendreAddition.kernel, Finset.mul_sum]
  congr 1
  · have := (hterm 0 (Nat.zero_le _)).1
    push_cast at this
    simp only [neg_zero, pow_zero, one_mul] at this
    simp only [Int.cast_zero, neg_zero, zpow_zero, one_mul, zero_mul, Complex.cos_zero, mul_one]
    rw [this]
  · apply Finset.sum_congr rfl
    intro k hk
    have hkl : k+1 ≤ n := by simp at hk; omega
    obtain ⟨h3, h4⟩ := hterm (k+1) hkl
    push_cast at h3 h4
    have hz : ((-1:ℂ))^(-((k:ℤ)+1)) = (-1)^(k+1) := by
      rw [zpow_neg, show ((k:ℤ)+1) = ((k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast, ← inv_pow]; norm_num
    have hz2 : ((-1:ℂ))^((k:ℤ)+1) = (-1)^(k+1) := by
      rw [show ((k:ℤ)+1) = ((k+1:ℕ):ℤ) by push_cast; ring, zpow_natCast]
    have hs : ((-1:ℂ))^(k+1) * (-1)^(k+1) = 1 := by rw [← mul_pow]; norm_num
    push_cast [hz, hz2]
    rw [show -(-((k:ℂ)+1)) = (k:ℂ)+1 by ring, mul_assoc ((-1:ℂ)^(k+1)) (ferrersP _ _ _), h3,
      mul_assoc ((-1:ℂ)^(k+1)) (ferrersP _ _ _), h4, show -((k:ℂ)+1) * phi = -(((k:ℂ)+1)*phi) by ring,
      Complex.cos_neg]
    linear_combination (-2 * DLMF.OrthogonalPolynomials.LegendreAddition.coeff n (k+1) (Complex.cos θ₁) (Complex.cos θ₂) (Complex.sin θ₁) (Complex.sin θ₂) * Complex.cos (((k:ℂ)+1)*phi)) * hs

/-- At coincident arguments and phi zero, the order-zero P value is understood by its regular extension at one. -/
@[dlmf 14.18.E4]
theorem associatedP_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedP ν m (Real.cosh ξ₂)*Real.cos (m*phi)) (associatedP ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedP ν 0 (Real.cosh ξ₂)) := by
  sorry

/-- associatedQ addition. -/
@[dlmf 14.18.E5]
theorem associatedQ_addition (ν : ℂ) {ξ₁ ξ₂ : ℝ} (h1 : 0 < ξ₁) (h2 : 0 < ξ₂) (h12 : ξ₁ < ξ₂) (hr : LegendreQRegular ν 0) (phi : ℝ) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*associatedP ν (-m) (Real.cosh ξ₁)*associatedQ ν m (Real.cosh ξ₂)*Real.cos (m*phi)) (associatedQ ν 0 (Real.cosh ξ₁*Real.cosh ξ₂-Real.sinh ξ₁*Real.sinh ξ₂*Real.cos phi)-associatedP ν 0 (Real.cosh ξ₁)*associatedQ ν 0 (Real.cosh ξ₂)) := by
  sorry

/-- legendre christoffel 6. -/
@[dlmf 14.18.E6]
theorem legendre_christoffel_6 (n : ℕ) {x y : ℂ} (hx : x-1 ∈ slitPlane) (hy : y-1 ∈ slitPlane) :
    (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*associatedP k 0 x*associatedP k 0 y)=(n+1:ℂ)*(associatedP (n+1) 0 x*associatedP n 0 y-associatedP n 0 x*associatedP (n+1) 0 y) := by
  have hP : ∀ z : ℂ, z-1 ∈ slitPlane → ∀ k : ℕ, associatedP k 0 z = DLMF.OrthogonalPolynomials.legendrePolyP k z := by
    intro z hz k
    have hz' : 1+z ∈ slitPlane := by
      rw [mem_slitPlane_iff] at hz ⊢
      simp only [add_re, one_re, add_im, one_im, zero_add, sub_re, sub_im] at hz ⊢
      rcases hz with h | h
      · left; linarith
      · right; simpa using h
    rw [associatedP_zero_order _ hz, legendreP_nat k hz']
  have key : ∀ n : ℕ, (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*DLMF.OrthogonalPolynomials.legendrePolyP k x*DLMF.OrthogonalPolynomials.legendrePolyP k y) =
      (n+1:ℂ)*(DLMF.OrthogonalPolynomials.legendrePolyP (n+1) x*DLMF.OrthogonalPolynomials.legendrePolyP n y-DLMF.OrthogonalPolynomials.legendrePolyP n x*DLMF.OrthogonalPolynomials.legendrePolyP (n+1) y) := by
    intro n
    induction n with
    | zero => simp [DLMF.OrthogonalPolynomials.legendrePolyP_one, DLMF.OrthogonalPolynomials.legendrePolyP_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have hx2 := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n x
      have hy2 := DLMF.OrthogonalPolynomials.legendrePolyP_recurrence n y
      push_cast
      rw [show n+1+1 = n+2 by ring]
      linear_combination DLMF.OrthogonalPolynomials.legendrePolyP (n+1) x * hy2 - DLMF.OrthogonalPolynomials.legendrePolyP (n+1) y * hx2
  have := key n
  simp only [← hP x hx, ← hP y hy] at this
  push_cast at this
  exact this

/-- legendre christoffel 7. -/
@[dlmf 14.18.E7]
theorem legendre_christoffel_7 (n : ℕ) {x y : ℂ} (hx : x-1 ∈ slitPlane) (hy : y-1 ∈ slitPlane) :
    (x-y)*(∑ k ∈ Finset.range (n+1), (2*k+1:ℂ)*associatedP k 0 x*associatedQ k 0 y)=(n+1:ℂ)*(associatedP (n+1) 0 x*associatedQ n 0 y-associatedP n 0 x*associatedQ (n+1) 0 y)-1 := by
  have hx' := one_add_mem_slitPlane_of_sub_one hx
  simp only [associatedP_zero_order _ hx, associatedQ_zero_order _ hy]
  have hP0 : legendreP 0 x = 1 := by
    have := legendreP_nat 0 hx'; simpa [DLMF.OrthogonalPolynomials.legendrePolyP_zero] using this
  have hP1 : legendreP 1 x = x := by
    have := legendreP_nat 1 hx'; simpa [DLMF.OrthogonalPolynomials.legendrePolyP_one] using this
  induction n with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, one_mul]
    rw [hP0, hP1, legendreQ_one hy]; ring
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have hp := legendreP_recurrence ((n:ℂ)+1) hx'
    have hq := legendreQ_recurrence (ν := (n:ℂ)+1) (by exact_mod_cast Nat.succ_ne_zero n) hy
    push_cast
    rw [show (n:ℂ)+1-1 = n by ring] at hp hq
    linear_combination -legendreQ ((n:ℂ)+1) y * hp + legendreP ((n:ℂ)+1) x * hq

/-- ferrersP zonal series. -/
@[dlmf 14.18.E8]
theorem ferrersP_zonal_series {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasSum (fun n : ℕ => sin (ν*π)/π*(2*n+1)/((ν-n)*(ν+n+1))*ferrersP n 0 x) (ferrersP ν 0 (-x)) := by
  sorry

/-- ferrersP dougall series. -/
@[dlmf 14.18.E9]
theorem ferrersP_dougall_series {ν : ℂ} (hν : ∀ n : ℤ, ν ≠ n) {μ : ℝ} (hμ : 0 ≤ μ) {x : ℝ} (hx : x ∈ Ioc (-1:ℝ) 1) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, sin (ν*π)/π*(-1)^n*(2*n+1)/((ν-n)*(ν+n+1))*ferrersP n (-μ) x) atTop (𝓝 (ferrersP ν (-μ) x)) := by
  sorry

/-- Confocal ellipse coordinate, with value two on the focal segment. -/
def legendreEllipseRadius (z : ℂ) : ℝ :=
  ‖z-1‖+‖z+1‖

/-- legendre heine series. -/
@[dlmf 14.28.E2]
theorem legendre_heine_series {z₁ z₂ : ℂ} (hz₁ : z₁-1 ∈ slitPlane) (hr : legendreEllipseRadius z₂ < legendreEllipseRadius z₁) :
    HasSum (fun n : ℕ => (2*n+1:ℂ)*associatedQ n 0 z₁*DLMF.OrthogonalPolynomials.legendrePolyP n z₂) (1/(z₁-z₂)) := by
  sorry

/-- legendre heine uniform. -/
@[dlmf 14.28.E2]
theorem legendre_heine_uniform {R₁ R₂ : ℝ} (hR₂ : 2 < R₂) (hR : R₂ < R₁) :
    TendstoUniformlyOn (fun N : ℕ => fun p : ℂ × ℂ => ∑ n ∈ Finset.range N, (2*n+1:ℂ)*associatedQ n 0 p.1*DLMF.OrthogonalPolynomials.legendrePolyP n p.2) (fun p => 1/(p.1-p.2)) atTop {p : ℂ × ℂ | p.1-1 ∈ slitPlane ∧ R₁ ≤ legendreEllipseRadius p.1 ∧ legendreEllipseRadius p.2 ≤ R₂} := by
  sorry

/-- associatedP complex addition. -/
@[dlmf 14.28.E1]
theorem associatedP_complex_addition (ν : ℂ) {z₁ z₂ : ℂ} (h1 : 0 < z₁.re) (h2 : 0 < z₂.re) (hz1 : z₁-1 ∈ slitPlane) (hz2 : z₂-1 ∈ slitPlane) (phi : ℝ) (harg : z₁*z₂-exp ((log (z₁-1)+log (z₁+1))/2)*exp ((log (z₂-1)+log (z₂+1))/2)*Real.cos phi-1 ∈ slitPlane) :
    HasSum (fun j : ℕ => let m:=j+1; 2*(-1)^m*1/poch (ν-m+1) (2*m)*associatedP ν m z₁*associatedP ν m z₂*Real.cos (m*phi)) (associatedP ν 0 (z₁*z₂-exp ((log (z₁-1)+log (z₁+1))/2)*exp ((log (z₂-1)+log (z₂+1))/2)*Real.cos phi)-associatedP ν 0 z₁*associatedP ν 0 z₂) := by
  sorry

end DLMF.Legendre
