/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Legendre.IntegerTheory
public import DLMF.Legendre.SpecialValues

/-!
# Normalized spherical harmonics and endpoint values

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Legendre

open DLMF.OrthogonalPolynomials

/-- Polynomial definition extends integral-degree Ferrers P continuously to both endpoints. -/
def ferrersPNat (l m : ℕ) (x : ℝ) : ℂ :=
  (-1)^m*(Real.sqrt (1-x^2):ℂ)^m*iteratedDeriv m (legendrePolyP l) x

/-- ferrersPNat eq. -/
@[dlmf 14.7.E8]
theorem ferrersPNat_eq (l m : ℕ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersPNat l m x=ferrersP l m x := by
  have hs : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  have hev : legendreP (l:ℂ) =ᶠ[𝓝 (x:ℂ)] legendrePolyP l := by
    filter_upwards [isOpen_one_add_mem_slitPlane.mem_nhds hs] with w hw
    rw [legendreP_nat l hw]
  rw [ferrersP_nat (l:ℂ) m hx, hev.iteratedDeriv_eq, ferrersPNat]
  have h1 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  congr 2
  rw [← Complex.ofReal_pow, Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul h1]
  congr 2; ring

/-- sphericalHarmonicNonneg. -/
@[dlmf 14.30.E1]
def sphericalHarmonicNonneg (l m : ℕ) (θ phi : ℝ) : ℂ :=
  Real.sqrt (((l-m).factorial:ℝ)*(2*l+1)/(4*π*(l+m).factorial))*exp (I*m*phi)*ferrersPNat l m (Real.cos θ)

/-- sphericalHarmonic. -/
@[dlmf 14.30.E1]
def sphericalHarmonic (l : ℕ) (m : ℤ) (θ phi : ℝ) : ℂ :=
  if l < m.natAbs then 0 else if m < 0 then (-1)^m.natAbs*star (sphericalHarmonicNonneg l m.natAbs θ phi) else sphericalHarmonicNonneg l m.natAbs θ phi

/-- Derivatives of the Legendre polynomial are real on the real axis. -/
lemma iteratedDeriv_legendrePolyP_ofReal (l m : ℕ) (x : ℝ) :
    iteratedDeriv m (legendrePolyP l) (x:ℂ) =
      (((Polynomial.derivative^[m] (legendrePolyR l)).eval x : ℝ) : ℂ) := by
  have hf : legendrePolyP l = fun z => ((legendrePolyR l).map ofRealHom).eval z :=
    funext (legendrePolyP_eq_eval l)
  rw [hf, iteratedDeriv_eval_polynomial, Polynomial.iterate_derivative_map]
  exact eval_ofReal_map_ofRealHom _ _

/-- The polynomial Ferrers function is real-valued. -/
lemma star_ferrersPNat (l m : ℕ) (x : ℝ) : star (ferrersPNat l m x) = ferrersPNat l m x := by
  rw [ferrersPNat, iteratedDeriv_legendrePolyP_ofReal]
  simp only [star_mul', star_pow, star_neg, star_one, Complex.star_def, Complex.conj_ofReal]

/-- sphericalHarmonic ferrers. -/
@[dlmf 14.30.E1]
theorem sphericalHarmonic_ferrers (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (phi : ℝ) :
    sphericalHarmonic l m θ phi=Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*(2*l+1)/(4*π*((l:ℤ)+m).toNat.factorial))*exp (I*m*phi)*ferrersP l m (Real.cos θ) := by
  have hx : Real.cos θ ∈ Ioo (-1:ℝ) 1 := by
    constructor
    · rw [← Real.cos_pi]; exact Real.cos_lt_cos_of_nonneg_of_le_pi h0.le le_rfl hπ
    · rw [← Real.cos_zero]; exact Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl (by linarith) h0
  rw [sphericalHarmonic, ite_eq_right_iff.mpr (fun h => absurd h (not_lt.2 hm))]
  split_ifs with hneg
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = -(k:ℤ) := ⟨m.natAbs, by omega⟩
    subst hk
    have hkl : k ≤ l := by simpa using hm
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
    rw [show ((l:ℤ) - -(k:ℤ)).toNat = l + k by omega, show ((l:ℤ) + -(k:ℤ)).toNat = l - k by omega]
    have hG : ∀ n : ℕ, (l:ℂ) - k + 1 ≠ -n := by
      intro n h
      have : ((l - k + 1 + n : ℕ) : ℂ) = 0 := by push_cast [Nat.cast_sub hkl]; linear_combination h
      exact absurd (Nat.cast_eq_zero.1 this) (by omega)
    have hR := ferrersP_negative_integer_order (l:ℂ) k hG hx
    push_cast
    rw [hR, sphericalHarmonicNonneg, ← ferrersPNat_eq l k hx]
    have e1 : (l:ℂ) - k + 1 = ((l - k : ℕ) : ℂ) + 1 := by push_cast [Nat.cast_sub hkl]; ring
    have e2 : (l:ℂ) + k + 1 = ((l + k : ℕ) : ℂ) + 1 := by push_cast; ring
    rw [e1, e2, Complex.Gamma_nat_eq_factorial, Complex.Gamma_nat_eq_factorial]
    simp only [star_mul', star_ferrersPNat, Complex.star_def, Complex.conj_ofReal, ← Complex.exp_conj]
    set a : ℝ := ((l-k).factorial : ℝ)
    set b : ℝ := ((l+k).factorial : ℝ)
    have ha : 0 < a := by positivity
    have hb : 0 < b := by positivity
    have hc : 0 < (2*(l:ℝ)+1)/(4*π) := by positivity
    have hsq : Real.sqrt (a*(2*l+1)/(4*π*b)) = Real.sqrt (b*(2*l+1)/(4*π*a)) * (a/b) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ a/b), ← Real.sqrt_mul (by positivity)]
      congr 1; field_simp
    rw [hsq]
    have hconj : (starRingEnd ℂ) (I*(k:ℂ)*(phi:ℂ)) = I*(-(k:ℂ))*phi := by
      simp [Complex.conj_ofReal]
    rw [hconj]
    push_cast
    simp only [a, b, Complex.ofReal_natCast]; ring
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k:ℤ) := ⟨m.natAbs, by omega⟩
    subst hk
    simp only [Int.natAbs_natCast]
    rw [show ((l:ℤ) - (k:ℤ)).toNat = l - k by omega, show ((l:ℤ) + (k:ℤ)).toNat = l + k by omega,
      sphericalHarmonicNonneg, ferrersPNat_eq l k hx]
    push_cast; ring_nf

/-- surfaceHarmonic. -/
@[dlmf 14.30.E2]
def surfaceHarmonic (sine : Bool) (l m : ℕ) (θ phi : ℝ) : ℂ :=
  (if sine then Real.sin (m*phi) else Real.cos (m*phi))*ferrersPNat l m (Real.cos θ)

/-- sphericalHarmonic rodrigues. -/
@[dlmf 14.30.E3]
theorem sphericalHarmonic_rodrigues (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) (phi : ℝ) :
    sphericalHarmonic l m θ phi=(-1:ℂ)^((l:ℤ)+m)/(2^l*(l.factorial:ℂ))*Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*(2*l+1)/(4*π*((l:ℤ)+m).toNat.factorial))*exp (I*m*phi)*(Real.sin θ:ℂ)^m*iteratedDeriv ((l:ℤ)+m).toNat (fun x : ℝ => (1-x^2:ℂ)^l) (Real.cos θ) := by
  sorry

/-- The polynomial Ferrers function vanishes at `x = 1` for positive order. -/
lemma ferrersPNat_one (l m : ℕ) : ferrersPNat l m 1 = if m = 0 then 1 else 0 := by
  rcases m with _ | k
  · simp only [ferrersPNat, pow_zero, one_mul, iteratedDeriv_zero, ite_true, ofReal_one]
    rw [legendrePolyP, jacobi_at_one (by norm_num)]
    simp [Nat.cast_ne_zero.mpr l.factorial_ne_zero]
  · simp [ferrersPNat]

/-- sphericalHarmonic north. -/
@[dlmf 14.30.E4]
theorem sphericalHarmonic_north (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) (phi : ℝ) :
    sphericalHarmonic l m 0 phi=if m=0 then (Real.sqrt ((2*l+1)/(4*π)):ℂ) else 0 := by
  rw [sphericalHarmonic, if_neg (not_lt.2 hm)]
  simp only [sphericalHarmonicNonneg, Real.cos_zero, ferrersPNat_one, Int.natAbs_eq_zero]
  by_cases h : m = 0
  · subst h
    have : (l.factorial:ℝ)*(2*l+1)/(4*π*l.factorial) = (2*l+1)/(4*π) := by
      have : (0:ℝ) < l.factorial := by positivity
      field_simp
    simp [this]
  · simp [h]

/-- Gamma at `1/2 - s` for natural `s`, in factorial form. -/
lemma Gamma_one_half_sub_nat_mul (s : ℕ) :
    Gamma (1/2 - s) * ((2*s).factorial : ℂ) = (-4:ℂ)^s * s.factorial * Real.sqrt π := by
  induction s with
  | zero => simpa using legendre_Gamma_one_half
  | succ s ih =>
    have h1 : Gamma (1/2 - s) = (1/2 - ((s+1:ℕ):ℂ)) * Gamma (1/2 - ((s+1:ℕ):ℂ)) := by
      rw [← Gamma_add_one]
      · push_cast; ring_nf
      · intro h
        have := congrArg Complex.re h
        simp at this
        linarith
    rw [h1] at ih
    rw [show 2*(s+1) = 2*s+1+1 by ring, Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]
    push_cast at ih ⊢
    linear_combination (-2*(2*(s:ℂ)+2)) * ih

/-- sphericalHarmonic equator. -/
@[dlmf 14.30.E5]
theorem sphericalHarmonic_equator (l : ℕ) (m : ℤ) (hm : m.natAbs ≤ l) (phi : ℝ) :
    sphericalHarmonic l m (π/2) phi=if Even ((l:ℤ)+m) then (-1:ℂ)^(((l:ℤ)+m)/2)*exp (I*m*phi)/(2^l*((((l:ℤ)-m)/2).toNat.factorial:ℂ)*((((l:ℤ)+m)/2).toNat.factorial:ℂ))*Real.sqrt ((((l:ℤ)-m).toNat.factorial:ℝ)*((l:ℤ)+m).toNat.factorial*(2*l+1)/(4*π)) else 0 := by
  rw [sphericalHarmonic_ferrers l m hm (by positivity) (by linarith [Real.pi_pos]) phi,
    Real.cos_pi_div_two, ferrersP_zero_1]
  split_ifs with he
  · obtain ⟨s, hs⟩ : ∃ s : ℕ, (l:ℤ) + m = 2*s := by
      obtain ⟨t, ht⟩ := he; exact ⟨t.toNat, by omega⟩
    obtain ⟨r, hr⟩ : ∃ r : ℕ, (l:ℤ) - m = 2*r := ⟨((l:ℤ)-m).toNat/2, by omega⟩
    have hl : (l:ℂ) = r + s := by
      have : (l:ℤ) = r + s := by omega
      exact_mod_cast this
    have hmC : (m:ℂ) = s - r := by
      have : m = s - r := by omega
      rw [this]; push_cast; ring
    rw [hs, hr, show (2*(s:ℤ)).toNat = 2*s by omega, show (2*(r:ℤ)).toNat = 2*r by omega,
      show (2*(s:ℤ))/2 = s by omega, show (2*(r:ℤ))/2 = r by omega, Int.toNat_natCast]
    have e1 : ((l:ℂ) - m)/2 + 1 = (r:ℂ) + 1 := by rw [hl, hmC]; ring
    have e2 : (1 - (l:ℂ) - m)/2 = 1/2 - s := by rw [hl, hmC]; ring
    rw [e1, e2, Gamma_nat_eq_factorial]
    have hG := Gamma_one_half_sub_nat_mul s
    have hGne : Gamma (1/2 - s) ≠ 0 := by
      intro h; rw [h, zero_mul] at hG
      have : (Real.sqrt π : ℂ) ≠ 0 := by
        exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
      simp [this, Nat.factorial_ne_zero] at hG
    have h2 : (2:ℂ)^(m:ℂ) * 2^l = 4^s := by
      rw [← Complex.cpow_natCast, ← Complex.cpow_add _ _ (by norm_num), hmC, hl,
        show (s:ℂ) - r + (r+s) = ((2*s : ℕ) : ℂ) by push_cast; ring, Complex.cpow_natCast, pow_mul]
      norm_num
    set A : ℝ := ((2*r).factorial:ℝ)*(2*l+1)/(4*π)
    have hA : 0 ≤ A := by positivity
    have hb : (0:ℝ) < (2*s).factorial := by positivity
    have hsq1 : Real.sqrt (((2*r).factorial:ℝ)*(2*l+1)/(4*π*(2*s).factorial)) =
        Real.sqrt A / Real.sqrt (2*s).factorial := by
      rw [← Real.sqrt_div hA]; congr 1; simp only [A]; field_simp
    have hsq2 : Real.sqrt (((2*r).factorial:ℝ)*(2*s).factorial*(2*l+1)/(4*π)) =
        Real.sqrt A * Real.sqrt ((2*s).factorial) := by
      rw [← Real.sqrt_mul hA]; congr 1; simp only [A]; ring
    rw [hsq1, hsq2]
    have hsb : (Real.sqrt ((2*s).factorial) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 hb).ne'
    have hsb2 : (Real.sqrt ((2*s).factorial) : ℂ)^2 = ((2*s).factorial : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hb.le]; push_cast; ring
    simp only [Int.toNat_natCast, zpow_natCast]
    have hpi : (Real.sqrt π : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 Real.pi_pos).ne'
    have hbC : ((2*s).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hrC : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have hsC : (s.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    push_cast
    rw [eq_div_of_mul_eq hbC hG, eq_div_of_mul_eq (pow_ne_zero _ two_ne_zero) h2, ← hsb2,
      show (-4:ℂ)^s = (-1)^s * 4^s by rw [← mul_pow]; norm_num]
    have h4 : (4:ℂ)^s ≠ 0 := pow_ne_zero _ (by norm_num)
    have hm1 : ((-1:ℂ))^s ≠ 0 := by simp
    have hm2 : ((-1:ℂ))^s * (-1)^s = 1 := by rw [← mul_pow]; norm_num
    field_simp
    linear_combination (-(Real.sqrt A:ℂ)) * hm2
  · obtain ⟨j, hj⟩ : ∃ j : ℕ, (l:ℤ) + m = 2*j + 1 := by
      have := Int.not_even_iff_odd.1 he
      obtain ⟨t, ht⟩ := this; exact ⟨t.toNat, by omega⟩
    have e2 : (1 - (l:ℂ) - m)/2 = -(j:ℂ) := by
      have : ((l:ℤ):ℂ) + (m:ℂ) = 2*j+1 := by exact_mod_cast hj
      push_cast at this; linear_combination -this/2
    rw [e2, Gamma_neg_nat_eq_zero]; simp

/-- sphericalHarmonic negative order. -/
@[dlmf 14.30.E6]
theorem sphericalHarmonic_negative_order (l : ℕ) (m : ℤ) (θ phi : ℝ) :
    sphericalHarmonic l (-m) θ phi=(-1:ℂ)^m*star (sphericalHarmonic l m θ phi) := by
  simp only [sphericalHarmonic, Int.natAbs_neg]
  split_ifs
  all_goals simp
  · omega
  · left
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = (k:ℤ) := ⟨m.natAbs, by omega⟩
    simp
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -(k:ℤ) := ⟨m.natAbs, by omega⟩
    simp only [Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← mul_assoc, inv_mul_cancel₀ (by simp), one_mul]
  · obtain rfl : m = 0 := by omega
    simp only [Int.natAbs_zero, zpow_zero, one_mul, sphericalHarmonicNonneg, map_mul,
      Complex.conj_ofReal, ← Complex.exp_conj]
    have := star_ferrersPNat l 0 (Real.cos θ)
    simp only [Complex.star_def] at this
    rw [this]; simp

/-- Parity of the polynomial Ferrers function. -/
lemma ferrersPNat_neg (l m : ℕ) (x : ℝ) :
    ferrersPNat l m (-x) = (-1)^(l+m) * ferrersPNat l m x := by
  have hP : legendrePolyP l = fun z => (-1:ℂ)^l * legendrePolyP l (-z) := by
    funext z
    have h := jacobi_reflection (α := 0) (β := 0) (by norm_num) (by norm_num) l (-z)
    rw [neg_neg] at h
    change jacobiPolyP 0 0 l z = (-1)^l * jacobiPolyP 0 0 l (-z)
    rw [h]
  have hD : iteratedDeriv m (legendrePolyP l) (-(x:ℂ)) =
      (-1:ℂ)^(l+m) * iteratedDeriv m (legendrePolyP l) (x:ℂ) := by
    conv_lhs => rw [hP]
    rw [iteratedDeriv_const_mul_field, iteratedDeriv_comp_neg, neg_neg, smul_eq_mul]
    ring
  simp only [ferrersPNat, ofReal_neg, hD, neg_sq]
  ring

/-- sphericalHarmonic parity. -/
@[dlmf 14.30.E7]
theorem sphericalHarmonic_parity (l : ℕ) (m : ℤ) (θ phi : ℝ) :
    sphericalHarmonic l m (π-θ) (phi+π)=(-1)^l*sphericalHarmonic l m θ phi := by
  have hY : ∀ k : ℕ, sphericalHarmonicNonneg l k (π-θ) (phi+π) =
      (-1)^l * sphericalHarmonicNonneg l k θ phi := by
    intro k
    simp only [sphericalHarmonicNonneg, Real.cos_pi_sub, ferrersPNat_neg]
    have he : exp (I*k*((phi+π:ℝ):ℂ)) = (-1)^k * exp (I*k*phi) := by
      push_cast
      rw [show I*k*(phi+π) = I*k*phi + k*(π*I) by ring, exp_add, Complex.exp_nat_mul,
        Complex.exp_pi_mul_I]; ring
    rw [he]
    have : ((-1:ℂ))^(l+k)*(-1)^k = (-1)^l := by
      rw [pow_add, mul_assoc, ← pow_add, ← two_mul, pow_mul]; norm_num
    linear_combination (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) *
      exp (I*k*phi) * ferrersPNat l k (Real.cos θ) : ℂ) * this
  simp only [sphericalHarmonic]
  split_ifs
  · simp
  · rw [hY, star_mul', star_pow, star_neg, star_one]; ring
  · rw [hY]

/-- sphericalHarmonic orthonormal. -/
@[dlmf 14.30.E8]
theorem sphericalHarmonic_orthonormal (l₁ l₂ : ℕ) (m₁ m₂ : ℤ) (h1 : m₁.natAbs ≤ l₁) (h2 : m₂.natAbs ≤ l₂) :
    (∫ phi : ℝ in 0..2*π, ∫ θ : ℝ in 0..π, star (sphericalHarmonic l₁ m₁ θ phi)*sphericalHarmonic l₂ m₂ θ phi*Real.sin θ)=if l₁=l₂ ∧ m₁=m₂ then 1 else 0 := by
  sorry

/-- A sum over a symmetric integer interval, paired by sign. -/
lemma sum_Icc_neg_pair (g : ℤ → ℂ) (l : ℕ) :
    ∑ m ∈ Finset.Icc (-(l:ℤ)) l, g m = g 0 + ∑ k ∈ Finset.range l, (g (k+1) + g (-(k+1))) := by
  induction l with
  | zero => simp
  | succ l ih =>
    have hs : Finset.Icc (-((l+1:ℕ):ℤ)) ((l+1:ℕ):ℤ) =
        insert ((l:ℤ)+1) (insert (-((l:ℤ)+1)) (Finset.Icc (-(l:ℤ)) l)) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hs, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    ring

/-- Product of a conjugated and a plain nonnegative-order spherical harmonic. -/
lemma star_mul_sphericalHarmonicNonneg (l k : ℕ) {θ₁ θ₂ : ℝ} (h1 : θ₁ ∈ Icc 0 π) (h2 : θ₂ ∈ Icc 0 π)
    (phi₁ phi₂ : ℝ) :
    star (sphericalHarmonicNonneg l k θ₁ phi₁) * sphericalHarmonicNonneg l k θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₂-phi₁)) := by
  have hsin : ∀ θ ∈ Icc 0 π, Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h.1 h.2).symm
  simp only [sphericalHarmonicNonneg, star_mul', star_ferrersPNat, Complex.star_def, conj_ofReal,
    ← exp_conj, map_mul, conj_I, conj_natCast]
  simp only [ferrersPNat, hsin θ₁ h1, hsin θ₂ h2, LegendreAddition.coeff, LegendreAddition.weight,
    LegendreAddition.jet]
  have hX : 0 ≤ ((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial) := by positivity
  have hc := Real.mul_self_sqrt hX
  have hcC : (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) : ℂ) *
      Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) =
      ((l-k).factorial:ℂ)*(2*l+1)/(4*π*(l+k).factorial) := by
    rw [← ofReal_mul, hc]; push_cast; ring
  have he : exp (-I*k*phi₁) * exp (I*k*phi₂) = exp (I*k*(phi₂-phi₁)) := by
    rw [← exp_add]; ring_nf
  have hs : ((-1:ℂ))^k * (-1)^k = 1 := by rw [← mul_pow]; norm_num
  rw [← he, mul_pow (Real.sin θ₁ : ℂ)]
  set Sq := (Real.sqrt (((l-k).factorial:ℝ)*(2*l+1)/(4*π*(l+k).factorial)) : ℂ)
  linear_combination
    ((-1:ℂ)^k*(-1)^k * (exp (-I*k*phi₁) * exp (I*k*phi₂) * (Real.sin θ₁:ℂ)^k * (Real.sin θ₂:ℂ)^k *
      iteratedDeriv k (legendrePolyP l) (Real.cos θ₁) * iteratedDeriv k (legendrePolyP l) (Real.cos θ₂))) * hcC +
    (((l-k).factorial:ℂ)*(2*l+1)/(4*π*(l+k).factorial) * (exp (-I*k*phi₁) * exp (I*k*phi₂) *
      (Real.sin θ₁:ℂ)^k * (Real.sin θ₂:ℂ)^k *
      iteratedDeriv k (legendrePolyP l) (Real.cos θ₁) * iteratedDeriv k (legendrePolyP l) (Real.cos θ₂))) * hs

/-- sphericalHarmonic addition. -/
@[dlmf 14.30.E9]
theorem sphericalHarmonic_addition (l : ℕ) (θ₁ θ₂ phi₁ phi₂ : ℝ) (h1 : θ₁ ∈ Icc 0 π) (h2 : θ₂ ∈ Icc 0 π) :
    legendrePolyP l (Real.cos θ₁*Real.cos θ₂+Real.sin θ₁*Real.sin θ₂*Real.cos (phi₁-phi₂))=4*π/(2*l+1:ℂ)*∑ m ∈ Finset.Icc (-(l:ℤ)) l, star (sphericalHarmonic l m θ₁ phi₁)*sphericalHarmonic l m θ₂ phi₂ := by
  have hsin : ∀ θ ∈ Icc 0 π, Real.sqrt (1 - Real.cos θ^2) = Real.sin θ := fun θ h =>
    (Real.sin_eq_sqrt_one_sub_cos_sq h.1 h.2).symm
  have hk := LegendreAddition.legendre_eq_kernel l (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁)
    (Real.sin θ₂) ((phi₁-phi₂:ℝ):ℂ) (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
    (by rw [← ofReal_pow, ← ofReal_pow, Real.sin_sq]; push_cast; ring)
  push_cast at hk ⊢
  rw [hk, sum_Icc_neg_pair, LegendreAddition.kernel, mul_add, Finset.mul_sum, Finset.mul_sum]
  -- the term for each order
  have hT : ∀ k : ℕ, k ≤ l → star (sphericalHarmonic l k θ₁ phi₁) * sphericalHarmonic l k θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₂-phi₁)) := by
    intro k hkl
    have hY : ∀ θ phi, sphericalHarmonic l k θ phi = sphericalHarmonicNonneg l k θ phi := by
      intro θ phi; simp [sphericalHarmonic, not_lt.2 hkl]
    rw [hY, hY]; exact star_mul_sphericalHarmonicNonneg l k h1 h2 phi₁ phi₂
  have hTn : ∀ k : ℕ, 0 < k → k ≤ l → star (sphericalHarmonic l (-(k:ℤ)) θ₁ phi₁) * sphericalHarmonic l (-(k:ℤ)) θ₂ phi₂ =
      (2*l+1)/(4*π) * LegendreAddition.coeff l k (Real.cos θ₁) (Real.cos θ₂) (Real.sin θ₁) (Real.sin θ₂) *
        exp (I*k*(phi₁-phi₂)) := by
    intro k hk0 hkl
    have hY : ∀ θ phi, sphericalHarmonic l (-(k:ℤ)) θ phi =
        (-1)^k * star (sphericalHarmonicNonneg l k θ phi) := by
      intro θ phi; simp [sphericalHarmonic, not_lt.2 hkl, hk0]
    rw [hY, hY, star_mul', star_star, star_pow, star_neg, star_one,
      show ∀ a b c : ℂ, a * b * (a * c) = (a*a) * (c * b) by intros; ring, ← mul_pow,
      show (-1:ℂ)*(-1) = 1 by norm_num, one_pow, one_mul,
      star_mul_sphericalHarmonicNonneg l k h2 h1 phi₂ phi₁]
    simp only [LegendreAddition.coeff]; ring
  have hπ : (π:ℂ) ≠ 0 := by exact_mod_cast Real.pi_pos.ne'
  have hl : (2*(l:ℂ)+1) ≠ 0 := by exact_mod_cast (show (2*l+1 : ℕ) ≠ 0 by omega)
  congr 1
  · have := hT 0 (Nat.zero_le _)
    push_cast at this
    rw [this]; field_simp; simp
  · apply Finset.sum_congr rfl
    intro k hk
    have hkl : k+1 ≤ l := by simp at hk; omega
    have h3 := hT (k+1) hkl
    have h4 := hTn (k+1) (by omega) hkl
    push_cast at h3 h4
    have hc : cos (((k:ℂ)+1)*(phi₁-phi₂)) =
        (exp (I*((k:ℂ)+1)*(phi₂-phi₁)) + exp (I*((k:ℂ)+1)*(phi₁-phi₂)))/2 := by
      rw [Complex.cos, add_comm]; congr 3 <;> ring
    rw [h3, h4, hc]
    field_simp

/-- The null vector appearing in the unnumbered Herglotz generating function. -/
def herglotzNullVector (lam : ℂ) : ℂ × ℂ × ℂ :=
  (1/(2*lam)-lam/2,-I/(2*lam)-I*lam/2,1)

/-- Unnumbered Herglotz generating function in DLMF 14.30(ii). -/
theorem herglotz_generating {lam : ℂ} (hlam : lam ≠ 0) (t : ℂ) (r θ phi : ℝ) (hθ : θ ∈ Icc 0 π) :
    HasSum (fun n : ℕ => Real.sqrt (4*π)*∑ m ∈ Finset.Icc (-(n:ℤ)) n, t^n*(r:ℂ)^n*lam^m*sphericalHarmonic n m θ phi/Real.sqrt ((2*n+1:ℝ)*((n:ℤ)+m).toNat.factorial*((n:ℤ)-m).toNat.factorial)) (let a:=herglotzNullVector lam; exp (t*(a.1*(r*Real.sin θ*Real.cos phi)+a.2.1*(r*Real.sin θ*Real.sin phi)+a.2.2*(r*Real.cos θ)))) := by
  sorry

/-- Scaled oblate harmonic of the first kind in DLMF 14.30(i). -/
def scaledOblateR (n m : ℕ) (x : ℝ) : ℂ :=
  exp (-I*π*n/2)*associatedP n m (I*x)

/-- Scaled oblate harmonic of the second kind in DLMF 14.30(i). -/
def scaledOblateT (n m : ℕ) (x : ℝ) : ℂ :=
  I*exp (I*π*n/2)*associatedQ n m (I*x)

/-- Reality of the scaled oblate harmonics. -/
theorem scaledOblate_real (n m : ℕ) {x : ℝ} (hx : 0 < x) :
    (scaledOblateR n m x).im=0 ∧ (scaledOblateT n m x).im=0 := by
  sorry

/- DLMF 14.30(iv), including 14.30.10–13 and the angular-momentum
application discussion, is excluded under the project application-notes policy. -/

end DLMF.Legendre
