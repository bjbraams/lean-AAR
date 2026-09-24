/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Classical
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.NumberTheory.Real.Irrational

/-!
# Topics in orthogonal polynomials (AAR Chapter 7)

Connection coefficients, Turán's inequality, positive summability of ultraspherical series,
and Apéry's theorem on the irrationality of `ζ(3)`. None of these are in Mathlib.
-/

@[expose] public section

open Complex Polynomial
open scoped Real Nat

noncomputable section

/-- Connection coefficients of Jacobi polynomials, AAR Lemma 7.1.1. -/
@[dlmf 18.18.iv]
theorem jacobiP_connection {α β γ δ : ℝ}
    (hα : -1 < α) (hβ : -1 < β) (hγ : -1 < γ) (hδ : -1 < δ) (n : ℕ) (x : ℂ) :
    jacobiP γ δ n x =
      ∑ k ∈ Finset.range (n + 1),
        (poch (n + (γ : ℂ) + δ + 1) k * poch (k + (γ : ℂ) + 1) (n - k) /
          ((n - k).factorial * poch (k + (α : ℂ) + β + 1) k)) *
        (∑ j ∈ Finset.range (n - k + 1),
          poch (-(n - k : ℕ) : ℂ) j * poch (n + k + (γ : ℂ) + δ + 1) j *
            poch (k + (α : ℂ) + 1) j /
            (poch (k + (γ : ℂ) + 1) j * poch (2 * k + (α : ℂ) + β + 2) j * j.factorial)) *
        jacobiP α β k x := by
  sorry

/-- Coefficient recurrence for the Gegenbauer polynomials normalized at one. -/
private lemma gegenbauer_coeff_recurrence {lam : ℂ} (hlam : 0 < lam.re) (n k : ℕ) :
    (n + 1 + 2 * lam) * gaussHGCoeff (-(n + 2 : ℂ)) (n + 2 + 2 * lam)
        (lam + 1 / 2) (k + 1) -
      2 * (n + 1 + lam) * gaussHGCoeff (-(n + 1 : ℂ)) (n + 1 + 2 * lam)
        (lam + 1 / 2) (k + 1) +
      (n + 1) * gaussHGCoeff (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) (k + 1) =
      -4 * (n + 1 + lam) * gaussHGCoeff (-(n + 1 : ℂ)) (n + 1 + 2 * lam)
        (lam + 1 / 2) k := by
  have hc : ∀ j : ℕ, lam + 1 / 2 ≠ -j := not_neg_nat_of_re_pos (by
    simp only [add_re, div_ofNat_re, one_re]; linarith)
  have hpk := poch_ne_zero_of_not_neg_nat hc k
  have hf : (k.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk : (k + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hck : lam + 1 / 2 + k ≠ 0 := by
    intro he
    apply hc k
    linear_combination he
  have hp : (n + 1 + 2 * lam) *
      (poch (-(n + 2 : ℂ)) (k + 1) * poch (n + 2 + 2 * lam) (k + 1)) =
      -(n + 2 : ℂ) * (n + 1 + 2 * lam + k) * (n + 2 + 2 * lam + k) *
        (poch (-(n + 1 : ℂ)) k * poch (n + 1 + 2 * lam) k) := by
    have h := poch_succ_left_mul (n + 1 + 2 * lam) (k + 1)
    rw [show (n : ℂ) + 1 + 2 * lam + 1 = n + 2 + 2 * lam by ring,
      poch_succ (n + 1 + 2 * lam) k] at h
    push_cast at h
    rw [poch_succ_left (-(n + 2 : ℂ)),
      show -(n + 2 : ℂ) + 1 = -(n + 1 : ℂ) by ring]
    linear_combination -(n + 2 : ℂ) * poch (-(n + 1 : ℂ)) k * h
  have hm : (n + 1 : ℂ) *
      (poch (-(n : ℂ)) (k + 1) * poch (n + 2 * lam) (k + 1)) =
      -(n + 2 * lam) * ((k : ℂ) - n - 1) * (k - n) *
        (poch (-(n + 1 : ℂ)) k * poch (n + 1 + 2 * lam) k) := by
    have h := poch_succ_left_mul (-(n + 1 : ℂ)) (k + 1)
    rw [show -(n + 1 : ℂ) + 1 = -(n : ℂ) by ring,
      poch_succ (-(n + 1 : ℂ)) k] at h
    push_cast at h
    rw [poch_succ_left (n + 2 * lam),
      show (n : ℂ) + 2 * lam + 1 = n + 1 + 2 * lam by ring]
    linear_combination -(n + 2 * lam) * poch (n + 1 + 2 * lam) k * h
  simp only [gaussHGCoeff, ← mul_div_assoc]
  rw [hp, hm, poch_succ (-(n + 1 : ℂ)), poch_succ (n + 1 + 2 * lam),
    poch_succ (lam + 1 / 2)]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  generalize hcdef : lam + 1 / 2 = c at hpk hck ⊢
  field_simp [hpk, hck, hf, hk]
  rw [← hcdef]
  ring

/-- Normalizing a Gegenbauer polynomial at one removes its Pochhammer prefactor. -/
theorem gegenbauer_div_at_one {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    gegenbauer lam n x / gegenbauer lam n 1 =
      ₂F₁ (-(n : ℂ)) (n + 2 * lam) (lam + 1 / 2) ((1 - x) / 2) := by
  have hp : poch (2 * lam) n ≠ 0 := poch_ne_zero_of_not_neg_nat
    (not_neg_nat_of_re_pos (by simpa using mul_pos (by norm_num : (0 : ℝ) < 2) hlam)) n
  have hf : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  simp only [gegenbauer, sub_self, zero_div, ordinaryHypergeometric_zero, mul_one]
  field_simp

/-- Three-term recurrence for the Gegenbauer polynomials normalized at one. -/
@[dlmf 18.9.T1]
theorem gegenbauer_normalized_recurrence {lam : ℂ} (hlam : 0 < lam.re) (n : ℕ) (x : ℂ) :
    (n + 1 + 2 * lam) * (gegenbauer lam (n + 2) x / gegenbauer lam (n + 2) 1) =
      2 * (n + 1 + lam) * x * (gegenbauer lam (n + 1) x / gegenbauer lam (n + 1) 1) -
        (n + 1) * (gegenbauer lam n x / gegenbauer lam n 1) := by
  let z := (1 - x) / 2
  let L (m k : ℕ) := gaussHGCoeff (-(m : ℂ)) (m + 2 * lam) (lam + 1 / 2) k
  let G (m : ℕ) := gegenbauer lam m x / gegenbauer lam m 1
  have hs (m : ℕ) : HasSum (fun k => L m k * z ^ k) (G m) := by
    dsimp only [G]
    rw [gegenbauer_div_at_one hlam, ordinaryHypergeometric_eq_sum_neg_nat]
    apply hasSum_sum_of_ne_finset_zero
    intro k hk
    have hmk : m < k := by simpa using hk
    simp [L, gaussHGCoeff, poch_neg_nat_eq_zero hmk]
  let d (k : ℕ) := (n + 1 + 2 * lam) * L (n + 2) k -
    2 * (n + 1 + lam) * L (n + 1) k + (n + 1) * L n k
  have hd0 : d 0 = 0 := by simp [d, L, gaussHGCoeff, poch_zero]; ring
  have hd (k : ℕ) : d (k + 1) = -4 * (n + 1 + lam) * L (n + 1) k := by
    dsimp [d, L]
    simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] using
      gegenbauer_coeff_recurrence hlam n k
  have hsum : HasSum (fun k => d k * z ^ k)
      ((n + 1 + 2 * lam) * G (n + 2) - 2 * (n + 1 + lam) * G (n + 1) +
        (n + 1) * G n) := by
    simpa only [d, sub_mul, add_mul, mul_assoc] using
      (((hs (n + 2)).mul_left (n + 1 + 2 * lam)).sub
        ((hs (n + 1)).mul_left (2 * (n + 1 + lam)))).add ((hs n).mul_left (n + 1 : ℂ))
  have hshift : HasSum (fun k => d (k + 1) * z ^ k) (-4 * (n + 1 + lam) * G (n + 1)) := by
    simpa only [hd, mul_assoc] using (hs (n + 1)).mul_left (-4 * (n + 1 + lam))
  have he := (hshift.mul_pow_shift hd0).unique hsum
  dsimp [z, G] at he
  linear_combination -he

/-- The normalized degree-one Gegenbauer polynomial is the identity function. -/
@[simp] theorem gegenbauer_normalized_one {lam : ℂ} (hlam : 0 < lam.re) (x : ℂ) :
    gegenbauer lam 1 x / gegenbauer lam 1 1 = x := by
  have hc : lam + 1 / 2 ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith
  rw [gegenbauer_div_at_one hlam]
  have h := ordinaryHypergeometric_eq_sum_neg_nat 1 (1 + 2 * lam) (lam + 1 / 2) ((1 - x) / 2)
  norm_num only [Nat.cast_one] at h ⊢
  rw [h]
  norm_num [Finset.sum_range_succ, gaussHGCoeff, poch_succ, poch_zero]
  generalize hcdef : lam + 1 / 2 = c at hc ⊢
  field_simp
  rw [← hcdef]
  ring

/-- Turán's inequality for ultraspherical polynomials normalized at one
(AAR Exercise 6.23(b)). -/
@[dlmf 18.14.E11]
theorem turan_gegenbauer {lam : ℝ} (hlam : 0 < lam) {n : ℕ} (hn : n ≠ 0) {x : ℝ}
    (hx : |x| ≤ 1) :
    0 ≤ ((gegenbauer lam n x / gegenbauer lam n 1).re) ^ 2 -
      (gegenbauer lam (n - 1) x / gegenbauer lam (n - 1) 1).re *
        (gegenbauer lam (n + 1) x / gegenbauer lam (n + 1) 1).re := by
  let G (m : ℕ) := (gegenbauer lam m x / gegenbauer lam m 1).re
  have hl : 0 < (lam : ℂ).re := hlam
  have hG0 : G 0 = 1 := by simp [G]
  have hG1 : G 1 = x := by simp [G, gegenbauer_normalized_one hl]
  have hr (m : ℕ) : (m + 1 + 2 * lam) * G (m + 2) =
      2 * (m + 1 + lam) * x * G (m + 1) - (m + 1) * G m := by
    simpa [G, mul_re] using congrArg Complex.re (gegenbauer_normalized_recurrence hl m x)
  have hx2 : 0 ≤ 1 - x ^ 2 := by
    have := abs_le.mp hx
    nlinarith [sq_nonneg x]
  have hquad (u v : ℝ) : 0 ≤ u ^ 2 + v ^ 2 - 2 * x * u * v := by
    nlinarith [sq_nonneg (u - x * v), mul_nonneg hx2 (sq_nonneg v)]
  have hall : ∀ m : ℕ, 0 ≤ G (m + 1) ^ 2 - G m * G (m + 2) := by
    intro m
    induction m with
    | zero =>
      have hrec := hr 0
      norm_num [hG0, hG1] at hrec ⊢
      have hpos : 0 < 1 + 2 * lam := by linarith
      nlinarith
    | succ m ih =>
      have hrec := hr m
      have hrec' := hr (m + 1)
      simp only [Nat.cast_add, Nat.cast_one] at hrec'
      -- The difference of successive Turán determinants is a nonnegative quadratic form.
      have hstep : (m + 2 + 2 * lam) * (G (m + 2) ^ 2 - G (m + 1) * G (m + 3)) =
          (m + 1) * (G (m + 1) ^ 2 - G m * G (m + 2)) +
          (G (m + 2) ^ 2 + G (m + 1) ^ 2 - 2 * x * G (m + 2) * G (m + 1)) := by
        have hidx : m + 1 + 2 = m + 3 := by omega
        rw [hidx] at hrec'
        linear_combination -G (m + 1) * hrec' + G (m + 2) * hrec
      have hm : (0 : ℝ) ≤ m + 1 := by positivity
      have hpos : (0 : ℝ) < m + 2 + 2 * lam := by positivity
      have hnonneg := mul_nonneg hm ih
      have hq := hquad (G (m + 2)) (G (m + 1))
      have ht : 0 ≤ G (m + 2) ^ 2 - G (m + 1) * G (m + 3) := by
        apply nonneg_of_mul_nonneg_left (by rw [mul_comm, hstep]; linarith) hpos
      simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using ht
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  simpa only [G, Nat.succ_eq_add_one, Nat.add_sub_cancel, Nat.add_assoc] using hall m

/-- Legendre polynomials are the normalized Gegenbauer family at `λ = 1/2`. -/
@[dlmf 18.7.E9]
theorem legendreP_eq_normalized_gegenbauer (n : ℕ) (x : ℂ) :
    legendreP n x = gegenbauer (1 / 2) n x / gegenbauer (1 / 2) n 1 := by
  rw [gegenbauer_div_at_one (by norm_num : 0 < (1 / 2 : ℂ).re)]
  norm_num [legendreP, jacobiP, Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- The first Legendre polynomial. -/
@[simp, dlmf 18.5.E16]
theorem legendreP_one (x : ℂ) : legendreP 1 x = x := by
  rw [legendreP_eq_normalized_gegenbauer,
    gegenbauer_normalized_one (by norm_num : 0 < (1 / 2 : ℂ).re)]

/-- The three-term recurrence for Legendre polynomials, including complex arguments. -/
@[dlmf 18.9.T1]
theorem legendreP_recurrence (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * legendreP (n + 2) x =
      (2 * n + 3) * x * legendreP (n + 1) x - (n + 1) * legendreP n x := by
  simp_rw [legendreP_eq_normalized_gegenbauer]
  have h := gegenbauer_normalized_recurrence (by norm_num : 0 < (1 / 2 : ℂ).re) n x
  convert h using 1 <;> ring

/-- Turán's inequality for Legendre polynomials (AAR Exercise 6.22):
`P_n(x)² - P_{n-1}(x) P_{n+1}(x) ≥ 0` on `[-1,1]`. -/
@[dlmf 18.14.E10]
theorem turan_legendre {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ (legendreP n x).re ^ 2 -
      (legendreP (n - 1) x).re * (legendreP (n + 1) x).re := by
  simpa only [legendreP_eq_normalized_gegenbauer, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] using
    turan_gegenbauer (lam := 1 / 2) (by norm_num) hn hx

/-- Vietoris's inequality (AAR §7.3): the cosine polynomials with coefficients
`a_{2k} = a_{2k+1} = \binom{2k}{k} / 2^{2k}` are nonnegative. -/
theorem vietoris_inequality (n : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (hθπ : θ ≤ π) :
    0 ≤ ∑ k ∈ Finset.range (n + 1),
      (Nat.choose (2 * (k / 2)) (k / 2) / (2 : ℝ) ^ (2 * (k / 2))) * Real.cos (k * θ) := by
  sorry

/-- Positivity of Cesàro sums of ultraspherical polynomials, AAR Corollary 7.6.4. -/
theorem gegenbauer_cesaro_nonneg {lam : ℝ} (hlam : 0 < lam) (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) :
    0 ≤ (∑ k ∈ Finset.range (n + 1),
      poch (2 * (lam : ℂ)) (n - k) / (n - k).factorial * gegenbauer lam k x).re := by
  sorry

/-- Apéry's theorem: `ζ(3)` is irrational (AAR §7.7). -/
theorem irrational_riemannZeta_three : Irrational (riemannZeta 3).re := by
  sorry
