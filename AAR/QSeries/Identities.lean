/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Tactic.CrossRefAttribute
public import AAR.QSeries.Pochhammer
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.NumberTheory.ModularForms.JacobiTheta.OneVariable
public import Mathlib.NumberTheory.SumFourSquares
public import Mathlib.NumberTheory.SumTwoSquares

/-!
# Triple product, Ramanujan `₁ψ₁`, basic hypergeometric series, `q`-beta (AAR §§10.4–10.12)

Mathlib has Jacobi theta functions, the Mellin transform, and the arithmetic theorems on
sums of two and four squares. It does not have the Jacobi triple product as a `q`-Pochhammer
identity, Ramanujan's `₁ψ₁`, or basic hypergeometric series `ᵣφₛ`.
-/

@[expose] public section

open Complex
open scoped Real

noncomputable section

/-- Jacobi triple product (AAR §10.4):
`(q;q)_∞ (z;q)_∞ (q/z;q)_∞ = ∑_{n∈ℤ} (-1)^n q^{n(n-1)/2} z^n`. -/
@[dlmf 17.8.E1]
theorem jacobi_triple_product {q z : ℂ} (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    qPochhammerInf q q * qPochhammerInf z q * qPochhammerInf (q / z) q =
      ∑' n : ℤ, (-1 : ℂ) ^ n * q ^ (n * (n - 1) / 2 : ℂ) * z ^ n := by
  sorry

/-- The triple product gives the product expansion of `jacobiTheta` (AAR §10.7). -/
theorem jacobiTheta_eq_qPochhammer {τ : ℂ} (hτ : 0 < τ.im) :
    jacobiTheta τ =
      qPochhammerInf (cexp (2 * π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ)) (cexp (2 * π * I * τ)) *
        qPochhammerInf (-cexp (π * I * τ)) (cexp (2 * π * I * τ)) := by
  sorry

/-- The integer-index q-Pochhammer symbol, AAR (10.5.2). -/
def qPochhammerInt (a q : ℂ) : ℤ → ℂ
  | .ofNat n => qPochhammer a q n
  | .negSucc n => (qPochhammer (a * q ^ (-(n + 1 : ℤ))) q (n + 1))⁻¹

@[simp] theorem qPochhammerInt_natCast (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q n = qPochhammer a q n := rfl

@[simp] theorem qPochhammerInt_negSucc (a q : ℂ) (n : ℕ) :
    qPochhammerInt a q (Int.negSucc n) =
      (qPochhammer (a * q ^ (-(n + 1 : ℤ))) q (n + 1))⁻¹ := rfl

/-- Ramanujan's `₁ψ₁` summation (AAR §10.5). -/
theorem ramanujan_1psi1 {a b q z : ℂ}
    (hq : ‖q‖ < 1) (hq0 : q ≠ 0) (ha0 : a ≠ 0)
    (ha : ∀ k : ℤ, a * q ^ k ≠ 1) (hb : ∀ k : ℤ, b * q ^ k ≠ 1)
    (hz : ‖b / a‖ < ‖z‖ ∧ ‖z‖ < 1) :
    (∑' n : ℤ, qPochhammerInt a q n / qPochhammerInt b q n * z ^ n) =
      qPochhammerInf q q * qPochhammerInf (b / a) q * qPochhammerInf (a * z) q *
          qPochhammerInf (q / (a * z)) q /
        (qPochhammerInf b q * qPochhammerInf (q / a) q * qPochhammerInf z q *
          qPochhammerInf (b / (a * z)) q) := by
  sorry

/-- Basic hypergeometric series `ᵣφₛ` with `r = s + 1` (AAR §10.9). -/
def basicHG (a b : List ℂ) (q z : ℂ) : ℂ :=
  ∑' n : ℕ,
    (a.map fun ai => qPochhammer ai q n).prod /
        ((b.map fun bi => qPochhammer bi q n).prod * qPochhammer q q n) * z ^ n

/-- Heine's transformation of `₂φ₁` (AAR §10.10). -/
theorem heine_transformation {a b c q z : ℂ}
    (hq : ‖q‖ < 1) (hz : ‖z‖ < 1) (hb : ‖b‖ < 1) (hb0 : b ≠ 0)
    (hc : ∀ k : ℕ, c * q ^ k ≠ 1) (haz : ∀ k : ℕ, a * z * q ^ k ≠ 1) :
    basicHG [a, b] [c] q z =
      qPochhammerInf b q * qPochhammerInf (a * z) q / (qPochhammerInf c q * qPochhammerInf z q) *
        basicHG [c / b, z] [a * z] q b := by
  let A (n : ℕ) := qPochhammer a q n / qPochhammer q q n
  let B (m : ℕ) := qPochhammer (c / b) q m / qPochhammer q q m
  let K := qPochhammerInf b q / qPochhammerInf c q
  let L := qPochhammerInf (a * z) q / qPochhammerInf z q
  let D (n m : ℕ) := (A n * z ^ n) * (B m * b ^ m) * q ^ (n * m)
  have hcf : ∀ k : ℕ, 1 - c * q ^ k ≠ 0 := fun k => sub_ne_zero.mpr (hc k).symm
  have haf : ∀ k : ℕ, 1 - (a * z) * q ^ k ≠ 0 := fun k => sub_ne_zero.mpr (haz k).symm
  have hbf := one_sub_mul_pow_ne_zero_of_norm hb hq
  have hzf := one_sub_mul_pow_ne_zero_of_norm hz hq
  have hleft (n : ℕ) : qPochhammer b q n / qPochhammer c q n =
      K * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    dsimp only [B]
    rw [← q_binomial_theorem hq (norm_mul_pow_lt_one hb hq n)]
    have he : c / b * (b * q ^ n) = c * q ^ n := by field [hb0]
    rw [he]
    dsimp only [K]
    rw [qPochhammerInf_mul_qPochhammer (a := b) hq n,
      qPochhammerInf_mul_qPochhammer (a := c) hq n]
    field [qPochhammer_ne_zero_of_factors hq hcf n,
      qPochhammerInf_shift_ne_zero hq hbf n, qPochhammerInf_shift_ne_zero hq hcf n]
  have hright (m : ℕ) : (∑' n : ℕ, A n * (z * q ^ m) ^ n) =
      L * qPochhammer z q m / qPochhammer (a * z) q m := by
    dsimp only [A]
    rw [← q_binomial_theorem hq (norm_mul_pow_lt_one hz hq m), ← mul_assoc]
    dsimp only [L]
    rw [qPochhammerInf_mul_qPochhammer (a := a * z) hq m,
      qPochhammerInf_mul_qPochhammer (a := z) hq m]
    field [qPochhammer_ne_zero_of_factors hq haf m,
      qPochhammer_ne_zero_of_factors hq hzf m,
      qPochhammerInf_shift_ne_zero hq hzf m]
  have hsumA : Summable (fun n : ℕ => ‖A n * z ^ n‖) :=
    (summable_q_binomial_series (a := a) hq hz).norm
  have hsumB : Summable (fun m : ℕ => ‖B m * b ^ m‖) :=
    (summable_q_binomial_series (a := c / b) hq hb).norm
  have hs : Summable (Function.uncurry D) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun nm => ?_) (hsumA.mul_norm hsumB)
    dsimp only [Function.uncurry, D]
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (pow_le_one₀ (norm_nonneg q) hq.le)
  have hrow (n : ℕ) : (∑' m : ℕ, D n m) =
      A n * z ^ n * ∑' m : ℕ, B m * (b * q ^ n) ^ m := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro m
    dsimp only [D]
    rw [mul_pow, ← pow_mul]
    ring
  have hcol (m : ℕ) : (∑' n : ℕ, D n m) =
      B m * b ^ m * ∑' n : ℕ, A n * (z * q ^ m) ^ n := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro n
    dsimp only [D]
    rw [mul_pow, ← pow_mul, Nat.mul_comm m n]
    ring
  have hlhs : basicHG [a, b] [c] q z = K * ∑' n : ℕ, ∑' m : ℕ, D n m := by
    calc
      _ = ∑' n : ℕ, A n * z ^ n * (qPochhammer b q n / qPochhammer c q n) := by
        simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
        apply tsum_congr
        intro n
        dsimp only [A]
        ring
      _ = _ := by
        rw [← tsum_mul_left]
        apply tsum_congr
        intro n
        rw [hleft, hrow]
        ring
  have hrhs : basicHG [c / b, z] [a * z] q b =
      ∑' m : ℕ, B m * b ^ m * qPochhammer z q m / qPochhammer (a * z) q m := by
    simp only [basicHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    apply tsum_congr
    intro m
    dsimp only [B]
    ring
  rw [hlhs, ← hs.tsum_comm, hrhs, ← tsum_mul_left, ← tsum_mul_left]
  apply tsum_congr
  intro m
  rw [hcol, hright]
  dsimp only [K, L]
  ring

/-- The Laurent form of the `q`-ultraspherical polynomials (AAR (10.11.1)),
with `x = exp(iθ)` corresponding to the polynomial argument `cos θ`. -/
@[dlmf 18.28.E13]
def qGegenbauer (beta q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    qPochhammer beta q k * qPochhammer beta q (n - k) /
        (qPochhammer q q k * qPochhammer q q (n - k)) * x ^ ((n : ℤ) - 2 * k)

theorem qGegenbauer_zero (beta q x : ℂ) : qGegenbauer beta q 0 x = 1 := by
  simp [qGegenbauer]

/-- Jackson's `q`-beta integral (AAR §10.8). -/
@[dlmf 5.18.E12]
theorem q_beta_integral {a b : ℂ} {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (ha : 0 < a.re) (hb : 0 < b.re) :
    jacksonIntegral q 1 (fun t =>
        t ^ (a - 1) * qPochhammerInf (q * t) q / qPochhammerInf (q ^ b * t) q) =
      qGamma q a * qGamma q b / qGamma q (a + b) := by
  have hq : ‖(q : ℂ)‖ < 1 := by simpa [abs_of_pos hq0] using hq1
  have hqz : (q : ℂ) ≠ 0 := ofReal_ne_zero.mpr hq0.ne'
  have hpow_norm (s : ℂ) (hs : 0 < s.re) : ‖(q : ℂ) ^ s‖ < 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos hq0]
    exact Real.rpow_lt_one hq0.le hq1 hs
  have hqa := hpow_norm a ha
  have hqb := hpow_norm b hb
  have hqab := hpow_norm (a + b) (by simpa using add_pos ha hb)
  have hA := qPochhammerInf_ne_zero_of_norm_lt_one hqa hq
  have hB := qPochhammerInf_ne_zero_of_norm_lt_one hqb hq
  have hC := qPochhammerInf_ne_zero_of_norm_lt_one hqab hq
  have hQ := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have hterm (n : ℕ) :
      ((q : ℂ) ^ n) ^ (a - 1) * qPochhammerInf ((q : ℂ) * q ^ n) q /
          qPochhammerInf ((q : ℂ) ^ b * q ^ n) q * q ^ n =
        (qPochhammerInf q q / qPochhammerInf ((q : ℂ) ^ b) q) *
          (qPochhammer ((q : ℂ) ^ b) q n / qPochhammer q q n * ((q : ℂ) ^ a) ^ n) := by
    have hp : ((q : ℂ) ^ n) ^ (a - 1) * (q : ℂ) ^ n = ((q : ℂ) ^ a) ^ n := by
      rw [← cpow_nat_mul' (by simp [arg_ofReal_of_nonneg hq0.le, Real.pi_pos])
        (by simp [arg_ofReal_of_nonneg hq0.le, Real.pi_nonneg]), cpow_nat_mul,
        cpow_sub _ _ hqz, cpow_one, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hqz)]
    have hN := qPochhammer_self_ne_zero hq n
    have hD := qPochhammerInf_ne_zero_of_norm_lt_one (norm_mul_pow_lt_one hqb hq n) hq
    rw [qPochhammerInf_mul_qPochhammer (a := (q : ℂ)) hq n,
      qPochhammerInf_mul_qPochhammer (a := (q : ℂ) ^ b) hq n]
    have hBn := qPochhammer_ne_zero_of_factors hq
      (one_sub_mul_pow_ne_zero_of_norm hqb hq) n
    linear_combination (norm := (field_simp; ring))
      (qPochhammerInf ((q : ℂ) * q ^ n) q /
        qPochhammerInf ((q : ℂ) ^ b * q ^ n) q) * hp
  unfold jacksonIntegral
  simp only [one_mul]
  simp_rw [hterm]
  rw [tsum_mul_left, ← q_binomial_theorem hq hqa,
    ← cpow_add _ _ hqz, add_comm b a]
  have hK : (1 - (q : ℂ)) ≠ 0 := by exact_mod_cast (sub_pos.mpr hq1).ne'
  unfold qGamma
  rw [cpow_sub _ _ hK, cpow_sub _ _ hK, cpow_sub _ _ hK, cpow_add _ _ hK, cpow_one]
  have hKa : (1 - (q : ℂ)) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hK)
  have hKb : (1 - (q : ℂ)) ^ b ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hK)
  field [hA, hB, hC, hQ, hK, hKa, hKb]
