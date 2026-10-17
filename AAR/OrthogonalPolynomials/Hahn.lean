/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import AAR.Hypergeometric.Continuation
public import AAR.OrthogonalPolynomials.BinomialSeries
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Hahn class: definitions, orthogonality, differences, and generating functions

Statements from NIST DLMF Chapter 18, each tagged with its equation number by `@[dlmf]`.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology
open AAR.Hypergeometric
open AAR.Confluent

noncomputable section

set_option autoImplicit false

namespace AAR.OrthogonalPolynomials

/-- A terminating hypergeometric sum, with an explicit cutoff. This implements
DLMF's convention when a lower parameter is a negative integer. -/
def terminatingHG (n : ℕ) (a b : List ℂ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => poch t k)).prod / (b.map (fun t => poch t k)).prod *
      z ^ k / (k.factorial : ℂ)

/-- A negative integral first upper parameter makes the finite sum a genuine infinite sum. -/
lemma terminatingHG_hasSum_neg_nat (n : ℕ) (a b : List ℂ) (z : ℂ) :
    HasSum (fun k : ℕ => (((-(n : ℂ) :: a).map (fun t => poch t k)).prod /
      (b.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ)))
      (terminatingHG n (-(n : ℂ) :: a) b z) := by
  unfold terminatingHG
  apply hasSum_sum_of_ne_finset_zero
  intro k hk
  have hnk : n < k := by simpa using hk
  simp [poch_neg_nat_eq_zero hnk]

/-- Pochhammer symbols at points of positive real part do not vanish. -/
lemma poch_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : poch z k ≠ 0 :=
  poch_ne_zero_of_not_neg_nat (fun j h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]) k

/-- The forward difference of a Pochhammer symbol in a shifted argument. -/
lemma poch_half_sub (w : ℂ) (k : ℕ) :
    poch (w - 1 / 2) (k + 1) - poch (w + 1 / 2) (k + 1) = -(k + 1) * poch (w + 1 / 2) k := by
  rw [poch_succ_left (w - 1 / 2), poch_succ (w + 1 / 2), show w - 1 / 2 + 1 = w + 1 / 2 by ring]
  ring

lemma exp_mul_one_sub_exp (phi : ℂ) :
    exp (I * phi) * (1 - exp (-2 * I * phi)) = 2 * I * sin phi := by
  have h1 : exp (I * phi) * exp (-2 * I * phi) = exp (-phi * I) := by
    rw [← exp_add]; ring_nf
  rw [Complex.sin, mul_sub, mul_one, h1, show I * phi = phi * I by ring]
  linear_combination (exp (phi * I) - exp (-phi * I)) * I_sq

/-- The Meixner–Pollaczek difference operator on the basis `(w)_{k+1}`, `w = λ + i x`. -/
lemma mp_basis_succ (lam phi w : ℂ) (n k : ℕ) :
    exp (I * phi) * (-I * (w - 2 * lam)) * (poch (w - 1) (k + 1) - poch w (k + 1)) +
      exp (-I * phi) * (-I * w) * (poch (w + 1) (k + 1) - poch w (k + 1)) +
      2 * n * sin phi * poch w (k + 1) =
      2 * (n - (k + 1)) * sin phi * poch w (k + 1) -
        I * (k + 1) * exp (I * phi) * (k + 2 * lam) * poch w k := by
  have hS := exp_mul_one_sub_exp phi
  have h1 : exp (I * phi) * exp (-2 * I * phi) = exp (-I * phi) := by rw [← exp_add]; ring_nf
  have hsin : 2 * I * sin phi = exp (I * phi) - exp (-I * phi) := by
    rw [← hS, mul_sub, mul_one, h1]
  have hrel : poch w k * (w + k) = w * poch (w + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (w - 1), show w - 1 + 1 = w by ring, poch_succ w k, poch_succ (w + 1) k]
  linear_combination (-(I) * poch w k * ((k : ℂ) + 1) * (k + w)) * hsin +
    (I * exp (-I * phi) * (k + w + 1)) * hrel +
    (2 * sin phi * poch w k * ((k : ℂ) + 1) * (w + k)) * I_sq

/-- The continuous Hahn difference operator on the basis `(w)_{k+1}`, `w = a + i x`. -/
lemma ch_basis_succ (a b c d w : ℂ) (n k : ℕ) :
    -((w - a - c) * (w - a - d)) * (poch (w - 1) (k + 1) - poch w (k + 1)) -
      w * (w - a + b) * (poch (w + 1) (k + 1) - poch w (k + 1)) +
      n * (n + a + b + c + d - 1) * poch w (k + 1) =
      (n - (k + 1)) * (n + (k + 1) + a + b + c + d - 1) * poch w (k + 1) +
        (k + 1) * (a + c + k) * (a + d + k) * poch w k := by
  have hrel : poch w k * (w + k) = w * poch (w + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (w - 1), show w - 1 + 1 = w by ring, poch_succ w k, poch_succ (w + 1) k]
  linear_combination (w - a + b) * (k + w + 1) * hrel

/-- The Hahn difference operator on the basis `(u)_{k+1}`, `u = -x`. -/
lemma hahn_basis_succ (α β N u : ℂ) (n k : ℕ) :
    (u - α - 1) * (u + N) * (poch (u - 1) (k + 1) - poch u (k + 1)) +
      u * (u + β + N + 1) * (poch (u + 1) (k + 1) - poch u (k + 1)) -
      n * (n + α + β + 1) * poch u (k + 1) =
      (k + 1 - n) * (k + 1 + n + α + β + 1) * poch u (k + 1) +
        (k + 1) * (N - k) * (α + k + 1) * poch u k := by
  have hrel : poch u k * (u + k) = u * poch (u + 1) k := by
    rw [← poch_succ, poch_succ_left]
  rw [poch_succ_left (u - 1), show u - 1 + 1 = u by ring, poch_succ u k, poch_succ (u + 1) k]
  linear_combination (-((k + u + 1) * (N + β + u + 1))) * hrel

@[dlmf 18.20.E5]
def hahn (α β : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + α + β + 1, -x] [α + 1, -(N : ℂ)] 1

@[dlmf 18.20.E6]
def krawtchouk (p : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [-(N : ℂ)] p⁻¹

@[dlmf 18.20.E7]
def meixner (β c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [β] (1 - c⁻¹)

@[dlmf 18.20.E8]
def charlier (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), -x] [] (-a⁻¹)

/-- The four-parameter polynomial; the orthogonality regime has `c = conj a`,
`d = conj b`. -/
@[dlmf 18.20.E9]
def continuousHahn (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  I ^ n * poch (a + c) n * poch (a + d) n / n.factorial *
    terminatingHG n [-(n : ℂ), n + a + b + c + d - 1, a + I * x] [a + c, a + d] 1

@[dlmf 18.20.E10]
def meixnerPollaczek (lam phi : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (2 * lam) n / n.factorial * exp (I * n * phi) *
    terminatingHG n [-(n : ℂ), lam + I * x] [2 * lam] (1 - exp (-2 * I * phi))

@[dlmf 18.19.E2]
def continuousHahnWeight (a b : ℂ) (x : ℂ) : ℂ :=
  Gamma (a + I * x) * Gamma (b + I * x) * Gamma (star a - I * x) * Gamma (star b - I * x)

@[dlmf 18.19.E7]
def meixnerPollaczekWeight (lam phi : ℂ) (x : ℂ) : ℂ :=
  Gamma (lam + I * x) * Gamma (lam - I * x) * exp ((2 * phi - Real.pi) * x)

@[dlmf 18.19.T1]
theorem hahn_orthogonal {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {N m n : ℕ}
    (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ x ∈ Finset.range (N + 1), hahn α β N m x * hahn α β N n x *
      poch (α + 1) x * poch (β + 1) (N - x) / ((x.factorial : ℂ) * (N - x).factorial) = 0 := by
  sorry

@[dlmf 18.19.T1]
theorem krawtchouk_orthogonality {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {N m n : ℕ} (hm : m ≤ N) (hn : n ≤ N) :
    ∑ x ∈ Finset.range (N + 1), krawtchouk p N m x * krawtchouk p N n x *
      N.choose x * (p : ℂ) ^ x * (1 - p : ℂ) ^ (N - x) =
      if m = n then (((1 - p) / p : ℂ) ^ n / N.choose n) else 0 := by
  sorry

@[dlmf 18.19.T1]
theorem meixner_orthogonality {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc1 : c < 1) (m n : ℕ) :
    HasSum (fun x : ℕ => meixner β c m x * meixner β c n x * poch β x *
      (c : ℂ) ^ x / x.factorial)
      (if m = n then (c : ℂ)⁻¹ ^ n * n.factorial / (poch β n * (1 - c : ℂ) ^ (β : ℂ)) else 0) := by
  sorry

@[dlmf 18.19.T1]
theorem charlier_orthogonality {a : ℝ} (ha : 0 < a) (m n : ℕ) :
    HasSum (fun x : ℕ => charlier a m x * charlier a n x * (a : ℂ) ^ x / x.factorial)
      (if m = n then (a : ℂ)⁻¹ ^ n * exp a * n.factorial else 0) := by
  sorry

@[dlmf 18.19.E4]
theorem continuousHahn_orthogonal {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ, continuousHahn a b (star a) (star b) m x *
      continuousHahn a b (star a) (star b) n x * continuousHahnWeight a b x = 0 := by
  sorry

@[dlmf 18.19.E9]
theorem meixnerPollaczek_orthogonality {lam phi : ℝ} (hlam : 0 < lam) (hphi : 0 < phi) (hphiπ : phi < Real.pi) (m n : ℕ) :
    ∫ x : ℝ, meixnerPollaczek lam phi m x * meixnerPollaczek lam phi n x *
      meixnerPollaczekWeight lam phi x =
      if m = n then 2 * Real.pi * Gamma (n + 2 * (lam : ℂ)) /
        ((2 * sin (phi : ℂ)) ^ (2 * (lam : ℂ)) * n.factorial) else 0 := by
  sorry

/-- A two-numerator terminating sum is a terminating Gauss series. -/
lemma terminatingHG_eq_ordinaryHypergeometric (n : ℕ) (b c z : ℂ) :
    terminatingHG n [-(n : ℂ), b] [c] z = ₂F₁ (-(n : ℂ)) b c z := by
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  unfold terminatingHG gaussHGCoeff
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

/-- A second terminating upper parameter permits extending the cutoff to the larger index. -/
lemma terminatingHG_two_neg_nat (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHG n [-(n : ℂ), -(m : ℂ)] b z =
      ∑ k ∈ Finset.range (max n m + 1), poch (-(n : ℂ)) k * poch (-(m : ℂ)) k /
        (b.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) := by
  simp only [terminatingHG, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (le_max_left n m) 1))
  intro k _ hk
  have hnk : n < k := by
    rw [Finset.mem_range] at hk
    omega
  simp [poch_neg_nat_eq_zero hnk]

/-- Symmetry remains valid even when a lower parameter is a nonpositive integer. -/
lemma terminatingHG_two_neg_nat_swap (n m : ℕ) (b : List ℂ) (z : ℂ) :
    terminatingHG n [-(n : ℂ), -(m : ℂ)] b z =
      terminatingHG m [-(m : ℂ), -(n : ℂ)] b z := by
  rw [terminatingHG_two_neg_nat, terminatingHG_two_neg_nat, Nat.max_comm m n]
  apply Finset.sum_congr rfl
  intro k _
  rw [mul_comm (poch (-(n : ℂ)) k)]

@[dlmf 18.21.E2]
theorem krawtchouk_duality (p : ℂ) {N n x : ℕ} (hn : n ≤ N) (hx : x ≤ N) :
    krawtchouk p N n x = krawtchouk p N x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.21.E2]
theorem meixner_duality (β c : ℂ) (n x : ℕ) : meixner β c n x = meixner β c x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.21.E2]
theorem charlier_duality (a : ℂ) (n x : ℕ) : charlier a n x = charlier a x n := by
  exact terminatingHG_two_neg_nat_swap n x _ _

@[dlmf 18.22.E10]
theorem hahn_difference_equation {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    (x + α + 1) * (x - N) * (hahn α β N n (x + 1) - hahn α β N n x) +
      x * (x - β - N - 1) * (hahn α β N n (x - 1) - hahn α β N n x) =
      n * (n + α + β + 1) * hahn α β N n x := by
  have hpA : ∀ k : ℕ, poch (α + 1) k ≠ 0 := fun k =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have hAk : ∀ k : ℕ, α + 1 + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hpN : ∀ k : ℕ, k ≤ N → poch (-(N : ℂ)) k ≠ 0 := fun k hk => by
    rw [poch_neg_coe_nat]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr hk).ne')
  set s : ℂ := (n : ℂ) + α + β + 1 with hs
  set u : ℂ := -x with hu
  set cf : ℕ → ℂ := fun k => poch (-(n : ℂ)) k * poch s k / (poch (α + 1) k * poch (-(N : ℂ)) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((k - n) * (k + n + α + β + 1) * poch u k) with hG
  set B : ℕ → ℂ := fun k => (u - α - 1) * (u + N) * (poch (u - 1) k - poch u k) +
      u * (u + β + N + 1) * (poch (u + 1) k - poch u k) - n * (n + α + β + 1) * poch u k with hB
  have hrec : ∀ k : ℕ, k < n → cf (k + 1) * ((k + 1) * (N - k) * (α + k + 1)) =
      -(cf k * ((k - n) * (s + k))) := by
    intro k hk
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have hNk : -(N : ℂ) + k ≠ 0 := fun h => by
      have : (k : ℂ) = N := by linear_combination h
      exact absurd (by exact_mod_cast this : k = N) (by omega)
    have := hpA k; have := hAk k; have := hpN k (by omega)
    simp only [hcf]
    rw [poch_succ, poch_succ s, poch_succ (α + 1), poch_succ (-(N : ℂ)), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, k < n → cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k hk
    simp only [hB, hG]
    rw [hahn_basis_succ α β N u n k]
    have hr := hrec k hk
    push_cast
    linear_combination (poch u k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    rw [Finset.sum_congr rfl fun k hk => htel k (Finset.mem_range.mp hk)]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, poch_zero, sub_self]
    push_cast
    ring
  unfold hahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show -(x + 1) = u - 1 by rw [hu]; ring, show -(x - 1) = u + 1 by rw [hu]; ring,
    show x + α + 1 = -(u - α - 1) by rw [hu]; ring, show (x : ℂ) - N = -(u + N) by rw [hu]; ring,
    show x - β - N - 1 = -(u + β + N + 1) by rw [hu]; ring, show x = -u by rw [hu]; ring]
  simp only [neg_neg]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (poch ((n : ℂ) + α + β + 1) k * poch v k) / (poch (α + 1) k * poch (-(N : ℂ)) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin]
  clear_value B G cf u s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      (u - α - 1) * (u + N) * (∑ k ∈ Finset.range (n + 1), cf k * poch (u - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch u k) +
      u * (u + β + N + 1) * (∑ k ∈ Finset.range (n + 1), cf k * poch (u + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch u k) -
      n * (n + α + β + 1) * ∑ k ∈ Finset.range (n + 1), cf k * poch u k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination -hexp - (n * ∑ k ∈ Finset.range (n + 1), cf k * poch u k) * hs

/-- 15.5.11 in `b` for the terminating function `₂F₁(-n, b; c; z)`, valid for every `z`
(both sides are polynomials in `z`). -/
lemma contiguous_b_neg_nat (n : ℕ) (b c z : ℂ) (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) :
    (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z = 0 := by
  have key : (fun z : ℂ => (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z) = fun _ => 0 := by
    refine AAR.Hypergeometric.eq_of_analyticOnNhd_univ_of_eqOn ?_ analyticOnNhd_const
      Metric.isOpen_ball ⟨0, Metric.mem_ball_self one_pos⟩ ?_
    · intro z _
      have h1 := analyticAt_gauss_neg_nat n (b - 1) c z
      have h2 := analyticAt_gauss_neg_nat n b c z
      have h3 := analyticAt_gauss_neg_nat n (b + 1) c z
      fun_prop
    intro z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have h := contiguous_a (a := b) (b := -(n : ℂ)) (c := c) hc hz'
    simp only [AAR.Hypergeometric.ordinaryHypergeometric_symm b (-(n : ℂ)) c,
      AAR.Hypergeometric.ordinaryHypergeometric_symm (b - 1) (-(n : ℂ)) c,
      AAR.Hypergeometric.ordinaryHypergeometric_symm (b + 1) (-(n : ℂ)) c] at h
    linear_combination h
  exact congrFun key z

/-- The Meixner polynomial as a terminating `₂F₁`. -/
lemma meixner_eq_hypergeometric (β c : ℂ) (n : ℕ) (x : ℂ) :
    meixner β c n x = ₂F₁ (-(n : ℂ)) (-x) β (1 - c⁻¹) := by
  unfold meixner terminatingHG
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHGCoeff]
  ring

/-- `contiguous_b_neg_nat` for every `c` off `{0, -1, …, -(n-1)}`, by analytic continuation
in `c`; this covers the Krawtchouk case `c = -N` with `n ≤ N`. -/
lemma contiguous_b_neg_nat' (n : ℕ) (b c z : ℂ) (hc : ∀ j : ℕ, j < n → c ≠ -(j : ℂ)) :
    (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z = 0 := by
  set S : Set ℂ := {c : ℂ | ∀ j : ℕ, j < n → c ≠ -(j : ℂ)} with hS
  have hSc : S = ((fun j : ℕ => -(j : ℂ)) '' {j : ℕ | j < n})ᶜ := by
    ext c
    simp only [hS, Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_image, not_exists, not_and]
    constructor
    · intro h j hj hje
      exact h j hj hje.symm
    · intro h j hj hje
      exact h j hj hje.symm
  have hconn : IsPreconnected S := by
    rw [hSc]
    exact (Set.Countable.isConnected_compl_of_one_lt_rank (by
      rw [Complex.rank_real_complex]; norm_num)
      ((Set.finite_Iio n).image _).countable).isPreconnected
  have h1 : (1 : ℂ) ∈ S := fun j _ h => by
    have := congrArg Complex.re h
    simp at this
    linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hf : AnalyticOnNhd ℂ (fun c : ℂ => (c - b) * ₂F₁ (-(n : ℂ)) (b - 1) c z +
      (2 * b - c + (-(n : ℂ) - b) * z) * ₂F₁ (-(n : ℂ)) b c z +
      b * (z - 1) * ₂F₁ (-(n : ℂ)) (b + 1) c z) S := by
    intro c hc
    have g1 := AAR.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n (b - 1) z c hc
    have g2 := AAR.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n b z c hc
    have g3 := AAR.Hypergeometric.analyticOnNhd_gauss_neg_nat_param n (b + 1) z c hc
    fun_prop
  have key := hf.eqOn_of_preconnected_of_eventuallyEq (g := fun _ => 0) analyticOnNhd_const hconn h1
    (by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
        (show (0 : ℝ) < (1 : ℂ).re by simp)] with c hcre
      exact contiguous_b_neg_nat n b c z (not_neg_nat_of_re_pos hcre))
  exact key hc

/-- The Krawtchouk polynomial as a terminating `₂F₁`. -/
lemma krawtchouk_eq_hypergeometric (p : ℂ) (N n : ℕ) (x : ℂ) :
    krawtchouk p N n x = ₂F₁ (-(n : ℂ)) (-x) (-(N : ℂ)) p⁻¹ := by
  unfold krawtchouk terminatingHG
  rw [ordinaryHypergeometric_eq_sum_neg_nat]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, gaussHGCoeff]
  ring

@[dlmf 18.22.T2]
theorem krawtchouk_difference_equation {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    p * (x - N) * (krawtchouk p N n (x + 1) - krawtchouk p N n x) +
      (p - 1) * x * (krawtchouk p N n (x - 1) - krawtchouk p N n x) = n * krawtchouk p N n x := by
  have hc : ∀ j : ℕ, j < n → -(N : ℂ) ≠ -(j : ℂ) := fun j hj h => by
    have : (N : ℂ) = j := by linear_combination -h
    have : N = j := by exact_mod_cast this
    omega
  have R := contiguous_b_neg_nat' n (-x) (-(N : ℂ)) p⁻¹ hc
  simp only [krawtchouk_eq_hypergeometric, show -(x + 1) = -x - 1 by ring,
    show -(x - 1) = -x + 1 by ring]
  have hinv : p * p⁻¹ = 1 := mul_inv_cancel₀ hp
  linear_combination p * R + (-(x - n) * ₂F₁ (-(n : ℂ)) (-x) (-(N : ℂ)) p⁻¹ +
    x * ₂F₁ (-(n : ℂ)) (-x + 1) (-(N : ℂ)) p⁻¹) * hinv

@[dlmf 18.22.T2]
theorem meixner_difference_equation {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    c * (x + β) * (meixner β c n (x + 1) - meixner β c n x) +
      x * (meixner β c n (x - 1) - meixner β c n x) + n * (1 - c) * meixner β c n x = 0 := by
  have hβ' : ∀ k : ℕ, β ≠ -(k : ℂ) := not_neg_nat_of_re_pos hβ
  have R := contiguous_b_neg_nat n (-x) β (1 - c⁻¹) hβ'
  simp only [meixner_eq_hypergeometric, show -(x + 1) = -x - 1 by ring,
    show -(x - 1) = -x + 1 by ring]
  have hinv : c * c⁻¹ = 1 := mul_inv_cancel₀ hc
  linear_combination c * R + (-x * ₂F₁ (-(n : ℂ)) (-x + 1) β (1 - c⁻¹) +
    (x - n) * ₂F₁ (-(n : ℂ)) (-x) β (1 - c⁻¹)) * hinv


/-- Forward difference of `(-x)_{k+1}` in `x`. -/
lemma poch_neg_succ_sub (x : ℂ) (k : ℕ) :
    poch (-(x + 1)) (k + 1) - poch (-x) (k + 1) = -((k : ℂ) + 1) * poch (-x) k := by
  rw [poch_succ_left, poch_succ, show -(x + 1) + 1 = -x by ring]
  ring

lemma prod_map_poch_succ (L : List ℂ) (j : ℕ) :
    (L.map (fun t => poch t (j + 1))).prod =
      L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod := by
  induction L with
  | nil => simp
  | cons t L ih =>
    simp only [List.map_cons, List.prod_cons]
    rw [ih, poch_succ_left]
    ring

/-- The forward difference in `x` of a terminating series whose last numerator parameter is
`-x`: the common step behind 18.22.19–18.22.25. -/
lemma terminatingHG_forward_difference (n : ℕ) (L B : List ℂ) (x z : ℂ) :
    terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])) B z -
      terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])) B z =
    ((n + 1 : ℕ) : ℂ) * L.prod / B.prod * z *
      terminatingHG n (-(n : ℂ) :: (L.map (fun t => t + 1) ++ [-x])) (B.map (fun t => t + 1)) z := by
  unfold terminatingHG
  rw [← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : (((-((n + 1 : ℕ) : ℂ) :: (L ++ [-(x + 1)])).map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      ((-((n + 1 : ℕ) : ℂ) :: (L ++ [-x])).map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [poch_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  simp only [List.map_cons, List.map_append, List.map_nil, List.prod_cons, List.prod_append,
    List.prod_nil, mul_one]
  rw [prod_map_poch_succ L j, prod_map_poch_succ B j, poch_succ_left (-((n + 1 : ℕ) : ℂ)),
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring, Nat.factorial_succ, pow_succ]
  push_cast
  have hd := poch_neg_succ_sub x j
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (((n : ℂ) + 1) * (poch (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * poch (-x) j) * hinv -
    (((n : ℂ) + 1) * (poch (-(n : ℂ)) j * L.prod *
      ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `(-n)_{n+1} = 0`. -/
lemma poch_neg_nat_succ (n : ℕ) : poch (-(n : ℂ)) (n + 1) = 0 := by
  rw [poch_succ]
  simp

/-- The difference of a terminating series in its truncation parameter: the companion of
`terminatingHG_forward_difference` for the first numerator parameter. -/
lemma terminatingHG_first_difference (n : ℕ) (L B : List ℂ) (z : ℂ) :
    terminatingHG (n + 1) (-((n + 1 : ℕ) : ℂ) :: L) B z - terminatingHG n (-(n : ℂ) :: L) B z =
      -(L.prod / B.prod * z) * terminatingHG n (-(n : ℂ) :: L.map (fun t => t + 1)) (B.map (fun t => t + 1)) z := by
  unfold terminatingHG
  have hext : ∑ k ∈ Finset.range (n + 1), ((-(n : ℂ) :: L).map (fun t => poch t k)).prod /
        (B.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) =
      ∑ k ∈ Finset.range (n + 1 + 1), ((-(n : ℂ) :: L).map (fun t => poch t k)).prod /
        (B.map (fun t => poch t k)).prod * z ^ k / (k.factorial : ℂ) := by
    rw [Finset.sum_range_succ _ (n + 1)]
    simp [poch_neg_nat_succ]
  rw [hext, ← Finset.sum_sub_distrib, Finset.sum_range_succ', Finset.mul_sum]
  simp only [List.map_cons, List.prod_cons]
  have h0 : (poch (-((n + 1 : ℕ) : ℂ)) 0 * (L.map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ) -
      poch (-(n : ℂ)) 0 * (L.map (fun t => poch t 0)).prod /
        (B.map (fun t => poch t 0)).prod * z ^ 0 / ((0 : ℕ).factorial : ℂ)) = 0 := by
    simp [poch_zero]
  rw [h0, add_zero]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast j.succ_ne_zero
  rw [prod_map_poch_succ L j, prod_map_poch_succ B j, Nat.factorial_succ, pow_succ]
  have hd := poch_neg_succ_sub (n : ℂ) j
  push_cast
  have hinv : ((j : ℂ) + 1) * ((j : ℂ) + 1)⁻¹ = 1 := mul_inv_cancel₀ hj
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (-(L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * poch (-(n : ℂ)) j) * hinv +
    ((L.prod * ((L.map (fun t => t + 1)).map (fun t => poch t j)).prod * (B.prod)⁻¹ *
      (((B.map (fun t => t + 1)).map (fun t => poch t j)).prod)⁻¹ * z ^ j * z *
      ((j.factorial : ℂ))⁻¹) * ((j : ℂ) + 1)⁻¹) * hd

/-- `C_{n+1}(x) - C_n(x) = -(x/a) C_n(x - 1)`, the Charlier companion of 18.22.25 in `n`. -/
lemma charlier_first_difference (a : ℂ) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) x - charlier a n x = -(x / a) * charlier a n (x - 1) := by
  unfold charlier
  have h := terminatingHG_first_difference n [-x] [] (-a⁻¹)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    show -x + 1 = -(x - 1) by ring] at h
  rw [h]
  ring

@[dlmf 18.22.E19]
theorem hahn_forward_difference {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n + 1 ≤ N + 1) (x : ℂ) :
    hahn α β (N + 1) (n + 1) (x + 1) - hahn α β (N + 1) (n + 1) x =
      -((n + 1) * (n + α + β + 2)) / ((α + 1) * (N + 1)) * hahn (α + 1) (β + 1) N n x := by
  unfold hahn
  have h := terminatingHG_forward_difference n [((n + 1 : ℕ) : ℂ) + α + β + 1]
    [α + 1, -((N + 1 : ℕ) : ℂ)] x 1
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, List.cons_append,
    List.nil_append, mul_one,
    show ((n + 1 : ℕ) : ℂ) + α + β + 1 + 1 = (n : ℂ) + (α + 1) + (β + 1) + 1 by push_cast; ring,
    show -((N + 1 : ℕ) : ℂ) + 1 = -(N : ℂ) by push_cast; ring] at h
  rw [h]
  have hα0 : α + 1 ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
  push_cast
  field_simp
  ring

@[dlmf 18.22.E21]
theorem krawtchouk_forward_difference {p : ℂ} (hp : p ≠ 0) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    krawtchouk p (N + 1) (n + 1) (x + 1) - krawtchouk p (N + 1) (n + 1) x =
      -(n + 1) / (p * (N + 1)) * krawtchouk p N n x := by
  unfold krawtchouk
  have h := terminatingHG_forward_difference n [] [-((N + 1 : ℕ) : ℂ)] x p⁻¹
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons,
    show -((N + 1 : ℕ) : ℂ) + 1 = -(N : ℂ) by push_cast; ring] at h
  rw [h]
  have hN : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast N.succ_ne_zero
  push_cast
  field_simp

@[dlmf 18.22.E23]
theorem meixner_forward_difference {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (n : ℕ) (x : ℂ) :
    meixner β c (n + 1) (x + 1) - meixner β c (n + 1) x =
      -(n + 1) * (1 - c) / (β * c) * meixner (β + 1) c n x := by
  unfold meixner
  have h := terminatingHG_forward_difference n [] [β] x (1 - c⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil, List.map_cons, List.prod_cons] at h
  rw [h]
  have hβ0 : β ≠ 0 := by
    intro h0
    rw [h0] at hβ
    simp at hβ
  push_cast
  field_simp
  ring

@[dlmf 18.22.E25]
theorem charlier_forward_difference {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    charlier a (n + 1) (x + 1) - charlier a (n + 1) x = -(n + 1) / a * charlier a n x := by
  unfold charlier
  have h := terminatingHG_forward_difference n [] [] x (-a⁻¹)
  simp only [List.nil_append, List.map_nil, List.prod_nil] at h
  rw [h]
  push_cast
  field_simp

@[dlmf 18.22.T2]
theorem charlier_difference_equation {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * (charlier a n (x + 1) - charlier a n x) +
      x * (charlier a n (x - 1) - charlier a n x) + n * charlier a n x = 0 := by
  cases n with
  | zero => simp [charlier, terminatingHG, poch_zero]
  | succ m =>
    have h1 := charlier_forward_difference ha m x
    have h2 := charlier_forward_difference ha m (x - 1)
    rw [sub_add_cancel] at h2
    have h3 := charlier_first_difference a m x
    have h1' : a * (charlier a (m + 1) (x + 1) - charlier a (m + 1) x) =
        -((m : ℂ) + 1) * charlier a m x := by
      rw [h1]
      field_simp
    have h2' : a * (charlier a (m + 1) x - charlier a (m + 1) (x - 1)) =
        -((m : ℂ) + 1) * charlier a m (x - 1) := by
      rw [h2]
      field_simp
    have h3' : a * (charlier a (m + 1) x - charlier a m x) = -x * charlier a m (x - 1) := by
      rw [h3]
      field_simp
    push_cast
    apply mul_left_cancel₀ ha
    linear_combination a * h1' - x * h2' + ((m : ℂ) + 1) * h3'

@[dlmf 18.22.E8]
theorem meixnerPollaczek_recurrence {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (n + 2 : ℂ) * meixnerPollaczek lam phi (n + 2) x =
      2 * (x * sin phi + (n + lam + 1) * cos phi) * meixnerPollaczek lam phi (n + 1) x -
      (n + 2 * lam) * meixnerPollaczek lam phi n x := by
  have hc : ∀ k : ℕ, 2 * lam ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hcont :=
    Hypergeometric.contiguous_a_neg_nat hc n (b := lam + I * x) (1 - cexp (-2 * I * phi))
  unfold meixnerPollaczek
  rw [terminatingHG_eq_ordinaryHypergeometric, terminatingHG_eq_ordinaryHypergeometric,
    terminatingHG_eq_ordinaryHypergeometric]
  push_cast at hcont ⊢
  set F2 := ₂F₁ (-((n : ℂ) + 2)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set F1 := ₂F₁ (-((n : ℂ) + 1)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set F0 := ₂F₁ (-(n : ℂ)) (lam + I * x) (2 * lam) (1 - cexp (-2 * I * phi))
  set u := cexp (I * phi) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have e2 : cexp (-2 * I * phi) = (u ^ 2)⁻¹ := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  have en2 : cexp (I * (n + 2) * phi) = cexp (I * n * phi) * u ^ 2 := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_add]; congr 1; push_cast; ring
  have en1 : cexp (I * (n + 1) * phi) = cexp (I * n * phi) * u := by
    rw [hu, ← Complex.exp_add]; congr 1; ring
  have hcos : cos phi = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]; congr 2 <;> ring_nf
  have hsin : sin phi = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, hu, ← Complex.exp_neg]; congr 3 <;> ring_nf
  have hp2 : poch (2 * lam) (n + 2) = poch (2 * lam) n * (2 * lam + n) * (2 * lam + (n + 1)) := by
    rw [poch_succ, poch_succ]; push_cast; ring
  have hp1 : poch (2 * lam) (n + 1) = poch (2 * lam) n * (2 * lam + n) := by
    rw [poch_succ]
  have hf2 : ((n + 2) ! : ℂ) = (n + 2) * (n + 1) * n ! := by
    rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
  have hf1 : ((n + 1) ! : ℂ) = (n + 1) * n ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hf : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  have hn2 : (n : ℂ) + 2 ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  rw [e2] at hcont
  rw [en2, en1, hcos, hsin, hp2, hp1, hf2, hf1]
  set E := cexp (I * n * phi)
  field_simp at hcont ⊢
  linear_combination (poch (2 * lam) n * (2 * lam + n) * E) * hcont

/-- The Meixner–Pollaczek polynomial of degree one. -/
lemma meixnerPollaczek_one {lam : ℂ} (hlam : lam ≠ 0) (phi x : ℂ) :
    meixnerPollaczek lam phi 1 x = 2 * (x * sin phi + lam * cos phi) := by
  unfold meixnerPollaczek terminatingHG
  set u := cexp (I * phi) with hu
  have hu0 : u ≠ 0 := exp_ne_zero _
  have e2 : cexp (-2 * I * phi) = (u ^ 2)⁻¹ := by
    rw [hu, ← Complex.exp_nat_mul, ← Complex.exp_neg]; congr 1; push_cast; ring
  have hcos : cos phi = (u + u⁻¹) / 2 := by
    rw [Complex.cos, hu, ← Complex.exp_neg]; congr 2 <;> ring_nf
  have hsin : sin phi = (u⁻¹ - u) * I / 2 := by
    rw [Complex.sin, hu, ← Complex.exp_neg]; congr 3 <;> ring_nf
  rw [e2]
  simp [Finset.sum_range_succ, poch_zero, poch_one, hcos, hsin, ← hu]
  field_simp
  ring_nf

@[dlmf 18.22.E29]
theorem meixnerPollaczek_central_difference {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (meixnerPollaczek lam phi (n + 1) (x + I / 2) - meixnerPollaczek lam phi (n + 1) (x - I / 2)) / I =
      2 * sin phi * meixnerPollaczek (lam + 1 / 2) phi n x := by
  have h2 : 0 < (2 * lam).re := by simp; linarith
  have h2l : 2 * lam ≠ 0 := fun h => by rw [h] at h2; simp at h2
  have hl0 : lam ≠ 0 := fun h => by rw [h] at hlam; simp at hlam
  have hp : ∀ k : ℕ, poch (2 * lam + 1) k ≠ 0 := fun k =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  unfold meixnerPollaczek terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero,
    pow_zero]
  rw [show lam + I * (x + I / 2) = (lam + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show lam + I * (x - I / 2) = (lam + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_half_sub (lam + I * x) k
  rw [← sub_div, ← sub_mul, ← sub_div, ← mul_sub, key]
  have hS := exp_mul_one_sub_exp phi
  rw [poch_succ_left (2 * lam), poch_succ_left (2 * lam) k, poch_succ_left (-((n + 1 : ℕ) : ℂ)),
    Nat.factorial_succ, Nat.factorial_succ, show 2 * (lam + 1 / 2) = 2 * lam + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show lam + I * x + 1 / 2 = lam + 1 / 2 + I * x by ring, pow_succ,
    show I * ((n + 1 : ℕ) : ℂ) * phi = I * n * phi + I * phi by push_cast; ring, exp_add]
  have hS' : sin phi = exp (I * phi) * (1 - exp (-2 * I * phi)) / (2 * I) := by
    rw [hS]; field_simp
  rw [hS']
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have := hp k; have := hp n
  push_cast
  field_simp

/-- `∑ₙ C(N,n) (-n)ₖ zⁿ w^{N-n} = (-N)ₖ zᵏ (z+w)^{N-k}` for `k ≤ N`: factorial moments of a
binomial distribution. -/
lemma sum_choose_mul_poch_neg_nat_mul_pow {N k : ℕ} (hk : k ≤ N) (z w : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n * w ^ (N - n) =
      poch (-(N : ℂ)) k * z ^ k * (z + w) ^ (N - k) := by
  rw [show N + 1 = k + (N - k + 1) by omega, Finset.sum_range_add]
  rw [Finset.sum_eq_zero fun n hn => by
    rw [poch_neg_nat_eq_zero (by simpa using hn)]; simp, zero_add]
  rw [add_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m ≤ N - k := by simp at hm; omega
  rw [poch_neg_coe_nat, poch_neg_coe_nat, Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose, pow_add, show N - (k + m) = N - k - m by omega]
  have hc := Nat.choose_mul (n := N) (k := k + m) (s := k) (by omega)
  rw [show k + m - k = m by omega] at hc
  have hc' : (N.choose (k + m) : ℂ) * ((k + m).choose k) = N.choose k * (N - k).choose m := by
    exact_mod_cast hc
  push_cast
  linear_combination (-1 : ℂ) ^ k * k ! * z ^ k * z ^ m * w ^ (N - k - m) * hc'

/-- `∑ₙ C(N,n) (-n)ₖ zⁿ = (-N)ₖ zᵏ (1+z)^{N-k}` for `k ≤ N`. -/
lemma sum_choose_mul_poch_neg_nat {N k : ℕ} (hk : k ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n =
      poch (-(N : ℂ)) k * z ^ k * (1 + z) ^ (N - k) := by
  simpa [add_comm z] using sum_choose_mul_poch_neg_nat_mul_pow hk z 1

@[dlmf 18.23.E3]
theorem krawtchouk_generating_function {p : ℂ} (hp : p ≠ 0) {N x : ℕ} (hx : x ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * krawtchouk p N n x * z ^ n =
      (1 - (1 - p) / p * z) ^ x * (1 + z) ^ (N - x) := by
  unfold krawtchouk
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  have hterm : ∀ k ∈ Finset.range (x + 1), ∑ n ∈ Finset.range (N + 1),
      (N.choose n : ℂ) * ((([-(x : ℂ), -(n : ℂ)].map fun t => poch t k).prod /
        ([-(N : ℂ)].map fun t => poch t k).prod * p⁻¹ ^ k / k !)) * z ^ n =
      (1 + z) ^ (N - x) * ((x.choose k : ℂ) * (-(z / p)) ^ k * (1 + z) ^ (x - k)) := by
    intro k hk
    have hkx : k ≤ x := by simp at hk; omega
    have hN : poch (-(N : ℂ)) k ≠ 0 := by
      rw [poch_neg_coe_nat]
      exact mul_ne_zero (pow_ne_zero _ (by norm_num))
        (Nat.cast_ne_zero.mpr (Nat.descFactorial_pos.mpr (by omega)).ne')
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    have hs := sum_choose_mul_poch_neg_nat (show k ≤ N by omega) z
    rw [Finset.sum_congr rfl (g := fun n : ℕ => (poch (-(x : ℂ)) k / poch (-(N : ℂ)) k *
      p⁻¹ ^ k / k !) * ((N.choose n : ℂ) * poch (-(n : ℂ)) k * z ^ n)) (fun n _ => by ring),
      ← Finset.mul_sum, hs, poch_neg_coe_nat x, Nat.descFactorial_eq_factorial_mul_choose,
      show N - k = (N - x) + (x - k) by omega, pow_add]
    have hk' : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, mul_comm]
  congr 1
  rw [show 1 - (1 - p) / p * z = -(z / p) + (1 + z) by field_simp; ring, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- `∑ₙ (β)ₙ (-n)ₖ zⁿ / n! = (β)ₖ (-z)ᵏ (1 - z)^{-β-k}`. -/
lemma hasSum_poch_mul_poch_neg_nat {β z : ℂ} (hz : ‖z‖ < 1) (k : ℕ) :
    HasSum (fun n : ℕ => poch β n / n ! * poch (-(n : ℂ)) k * z ^ n)
      (poch β k * (-z) ^ k * (1 - z) ^ (-(β + k))) := by
  have hb := (hasSum_poch_div_factorial (β := β + k) hz).mul_left (poch β k * (-z) ^ k)
  have h0 : ∑ i ∈ Finset.range k, poch β i / i ! * poch (-(i : ℂ)) k * z ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [poch_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => poch β n / n ! * poch (-(n : ℂ)) k * z ^ n)
    k (g := poch β k * (-z) ^ k * (1 - z) ^ (-(β + k)))).mp ?_
  · rwa [h0, add_zero] at key
  refine hb.congr_fun fun n => ?_
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hnk : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [poch_neg_coe_nat, add_comm n k, poch_add, neg_pow, pow_add, add_comm k n]
  field_simp
  linear_combination (-1) ^ k * poch β k * poch (β + k) n * z ^ n * z ^ k * hd

@[dlmf 18.23.E4]
theorem meixner_generating_function {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (x : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch β n / n.factorial * meixner β c n x * z ^ n)
      ((1 - z / c) ^ x * (1 - z) ^ (-(x : ℂ) - β)) := by
  have hβk : ∀ k, poch β k ≠ 0 := poch_ne_zero_of_not_neg_nat (not_neg_nat_of_re_pos hβ)
  have h1z : (1 : ℂ) - z ≠ 0 := by
    intro h
    have : z = 1 := by linear_combination -h
    rw [this, norm_one] at hz
    exact lt_irrefl _ hz
  set u : ℂ := 1 - c⁻¹
  unfold meixner
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.mul_sum, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_poch_mul_poch_neg_nat (β := β) hz k).mul_left
      (poch (-(x : ℂ)) k / poch β k * u ^ k / k !))
  convert h using 1
  · funext n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    ring
  · have hsplit : ∀ k : ℕ, (1 - z) ^ (-(β + k)) = (1 - z) ^ (-β) * ((1 - z) ^ k)⁻¹ := by
      intro k
      rw [neg_add, cpow_add _ _ h1z, cpow_neg _ (k : ℂ), cpow_natCast]
    have hx : (1 - z) ^ (-(x : ℂ) - β) = (1 - z) ^ (-β) * ((1 - z) ^ x)⁻¹ := by
      rw [show -(x : ℂ) - β = -β + -(x : ℂ) by ring, cpow_add _ _ h1z, cpow_neg _ (x : ℂ),
        cpow_natCast]
    have hbin := sum_poch_neg_nat_div_factorial_mul_pow x (-(u * z) / (1 - z))
    rw [show (1 : ℂ) - -(u * z) / (1 - z) = (1 - z / c) / (1 - z) by
      simp only [u]; field_simp; ring, div_pow] at hbin
    have hterm : ∀ k ∈ Finset.range (x + 1), poch (-(x : ℂ)) k / poch β k * u ^ k / k ! *
        (poch β k * (-z) ^ k * (1 - z) ^ (-(β + k))) =
        (1 - z) ^ (-β) * (poch (-(x : ℂ)) k / k ! * (-(u * z) / (1 - z)) ^ k) := by
      intro k _
      rw [hsplit, div_pow]
      have := hβk k
      field_simp
      rw [show -(z * u) = u * -z by ring, mul_pow]
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, hbin, hx]
    field_simp

/-- `∑ₙ (-n)ₖ wⁿ / n! = (-w)ᵏ eʷ`. -/
lemma hasSum_poch_neg_nat_div_factorial (k : ℕ) (w : ℂ) :
    HasSum (fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) ((-w) ^ k * exp w) := by
  have he : HasSum (fun n : ℕ => w ^ n / n !) (exp w) := by
    simpa only [Complex.exp_eq_exp_ℂ] using NormedSpace.expSeries_div_hasSum_exp w
  have h0 : ∑ i ∈ Finset.range k, poch (-(i : ℂ)) k / i ! * w ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [poch_neg_nat_eq_zero (by simpa using hi)]; simp
  have key := (hasSum_nat_add_iff (f := fun n : ℕ => poch (-(n : ℂ)) k / n ! * w ^ n) k
    (g := (-w) ^ k * exp w)).mp ?_
  · rwa [h0, add_zero] at key
  refine (he.mul_left ((-w) ^ k)).congr_fun fun n => ?_
  have hn : ((n + k) ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hn' : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hd : ((n + k).descFactorial k : ℂ) * n ! = (n + k) ! := by
    have := Nat.factorial_mul_descFactorial (show k ≤ n + k by omega)
    rw [show n + k - k = n by omega] at this
    exact_mod_cast (mul_comm _ _).trans this
  rw [poch_neg_coe_nat, neg_pow, pow_add]
  field_simp
  linear_combination (-1) ^ k * w ^ n * w ^ k * hd

@[dlmf 18.23.E5]
theorem charlier_generating_function (a : ℂ) (x : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => charlier a n x / n.factorial * z ^ n) (exp z * (1 - z / a) ^ x) := by
  unfold charlier
  simp_rw [terminatingHG_two_neg_nat_swap _ x, terminatingHG, Finset.sum_div, Finset.sum_mul]
  have h := hasSum_sum (s := Finset.range (x + 1)) (fun k _ =>
    (hasSum_poch_neg_nat_div_factorial k z).mul_left (poch (-(x : ℂ)) k * (-a⁻¹) ^ k / k !))
  convert h using 1
  · funext n
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
    ring
  · rw [← sum_poch_neg_nat_div_factorial_mul_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show z / a = (-a⁻¹) * (-z) by ring, mul_pow]
    ring

/-- The Meixner–Pollaczek polynomial of degree zero. -/
lemma meixnerPollaczek_zero (lam phi x : ℂ) : meixnerPollaczek lam phi 0 x = 1 := by
  simp [meixnerPollaczek, terminatingHG, poch_zero]

/-- `e^{iφ} + e^{-iφ} = 2 cos φ` and `e^{-iφ} - e^{iφ} = -2 i sin φ`, in the form used below. -/
lemma exp_I_mul_add_inv (phi : ℂ) :
    exp (I * phi) + (exp (I * phi))⁻¹ = 2 * cos phi ∧
      exp (I * phi) - (exp (I * phi))⁻¹ = 2 * I * sin phi := by
  rw [← Complex.exp_neg, Complex.cos, Complex.sin]
  constructor
  · ring_nf
  · ring_nf; rw [I_sq]; ring

@[dlmf 18.23.E7]
theorem meixnerPollaczek_generating_function {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => meixnerPollaczek lam phi n x * z ^ n)
      ((1 - exp (I * phi) * z) ^ (-lam + I * x) * (1 - exp (-I * phi) * z) ^ (-lam - I * x)) := by
  set u := exp (I * phi) with hu
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hu1 : ‖u‖ = 1 := by rw [hu, mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hlam0 : lam ≠ 0 := fun h => by rw [h, Complex.zero_re] at hlam; exact lt_irrefl _ hlam
  obtain ⟨hcos, hsin⟩ := exp_I_mul_add_inv (phi : ℂ)
  have hcoeff : ∀ n, meixnerPollaczek lam phi n x =
      PowerSeries.coeff n (binomProductSeries (lam - I * x) (lam + I * x) u) := by
    refine eq_coeff_binomProductSeries hu0 (meixnerPollaczek_zero _ _ _) ?_ ?_
    · rw [meixnerPollaczek_one hlam0]
      linear_combination (-lam) * hcos + (I * x) * hsin + (2 * x * sin (phi : ℂ)) * I_sq
    · intro n
      rw [meixnerPollaczek_recurrence hlam]
      linear_combination (-(n + 1 + lam : ℂ) * meixnerPollaczek lam phi (n + 1) x) * hcos +
        (I * x * meixnerPollaczek lam phi (n + 1) x) * hsin +
        (2 * x * sin (phi : ℂ) * meixnerPollaczek lam phi (n + 1) x) * I_sq
  have h1 : ‖u * z‖ < 1 := by rwa [norm_mul, hu1, one_mul]
  have h2 : ‖u⁻¹ * z‖ < 1 := by rwa [norm_mul, norm_inv, hu1, inv_one, one_mul]
  have h := hasSum_coeff_binomProductSeries_mul_pow (lam - I * x) (lam + I * x) h1 h2
  rw [show u⁻¹ = exp (-I * phi) by rw [hu, ← Complex.exp_neg]; ring_nf,
    show -(lam - I * x) = -lam + I * x by ring, show -(lam + I * x) = -lam - I * x by ring] at h
  simpa only [hcoeff] using h

/-- Limits propagate through a three-term recurrence whose coefficients converge. -/
lemma tendsto_of_three_term {ι : Type*} {l : Filter ι} {f : ℕ → ι → ℂ} {g : ℕ → ℂ}
    {A B : ℕ → ι → ℂ} {A' B' : ℕ → ℂ}
    (h0 : Tendsto (f 0) l (𝓝 (g 0))) (h1 : Tendsto (f 1) l (𝓝 (g 1)))
    (hA : ∀ n, Tendsto (A n) l (𝓝 (A' n))) (hB : ∀ n, Tendsto (B n) l (𝓝 (B' n)))
    (hf : ∀ n, ∀ᶠ t in l, f (n + 2) t = A n t * f (n + 1) t + B n t * f n t)
    (hg : ∀ n, g (n + 2) = A' n * g (n + 1) + B' n * g n) (n : ℕ) :
    Tendsto (f n) l (𝓝 (g n)) := by
  induction n using Nat.twoStepInduction with
  | zero => exact h0
  | one => exact h1
  | more n ih0 ih1 =>
    rw [hg n]
    exact (((hA n).mul ih1).add ((hB n).mul ih0)).congr' (by
      filter_upwards [hf n] with t ht
      exact ht.symm)

/-- `c / a → 0` for complex `c` as the real `a → ∞`. -/
lemma tendsto_const_div_ofReal_atTop (c : ℂ) :
    Tendsto (fun a : ℝ => c / (a : ℂ)) atTop (𝓝 0) := by
  have := (continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero
  rw [ofReal_zero] at this
  simpa [div_eq_mul_inv] using this.const_mul c

/-- `(c + s t)_k / t^k → s^k` as the real `t → ∞`. -/
lemma tendsto_poch_add_mul_div_pow (c s : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => poch (c + s * t) k / (t : ℂ) ^ k) atTop (𝓝 (s ^ k)) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    have h1 : Tendsto (fun t : ℝ => (c + k) / (t : ℂ) + s) atTop (𝓝 s) := by
      simpa using (tendsto_const_div_ofReal_atTop (c + k)).add_const s
    refine ((ih.mul h1).congr' ?_).trans (by rw [pow_succ])
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [poch_succ, pow_succ]
    field_simp
    ring

@[dlmf 18.21.E3]
theorem hahn_limit_krawtchouk {p : ℝ} (hp : 0 < p) (N n : ℕ) (x : ℂ) :
    Tendsto (fun t : ℝ => hahn (p * t) ((1 - p) * t) N n x) atTop (𝓝 (krawtchouk p N n x)) := by
  unfold hahn krawtchouk terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hpt : Tendsto (fun t : ℝ => p * t) atTop atTop := tendsto_id.const_mul_atTop hp
  have h1 := tendsto_poch_add_div_pow ((n : ℂ) + 1) k
  have h2 := ((tendsto_poch_add_div_pow 1 k).comp hpt).inv₀ one_ne_zero
  rw [inv_one] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k / k.factorial * ((p : ℂ)⁻¹) ^ k)
  rw [mul_one, mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k * (p : ℂ)⁻¹ ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (-(N : ℂ)) k /
      k.factorial * ((p : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hp' : (p : ℂ) ≠ 0 := ofReal_ne_zero.mpr hp.ne'
  simp only [Function.comp_apply, ofReal_mul]
  have e1 : (n : ℂ) + (p * t) + ((1 - p) * t) + 1 = (n + 1) + t := by ring
  have e2 : (p : ℂ) * t + 1 = 1 + p * t := by ring
  rw [e1, e2, mul_pow, inv_pow]
  field_simp
  ring

@[dlmf 18.21.E5]
theorem hahn_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn α β N n (N * x)) atTop (𝓝 (jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -(k : ℂ) := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hP1 : poch ((α : ℂ) + 1) n / (n ! : ℂ) ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hJ : jacobiPolyP α β n (1 - 2 * x) / jacobiPolyP α β n 1 =
      ∑ k ∈ Finset.range (n + 1), gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k * x ^ k := by
    unfold jacobiPolyP
    rw [show (1 - (1 - 2 * x)) / 2 = x by ring, sub_self, zero_div,
      ordinaryHypergeometric_zero, mul_one, mul_div_cancel_left₀ _ hP1,
      ordinaryHypergeometric_eq_sum_neg_nat]
  rw [hJ]
  unfold hahn terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h1 := (tendsto_poch_add_mul_div_pow 0 (-x) k).comp hnat
  have h2 := (tendsto_poch_add_mul_div_pow 0 (-1) k).comp hnat
  have hneg : ((-1 : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 := (h1.div h2 hneg).const_mul (gaussHGCoeff (-(n : ℂ)) (n + α + β + 1) (α + 1) k)
  rw [show (-x) ^ k / (-1 : ℂ) ^ k = x ^ k by rw [neg_pow x, mul_div_cancel_left₀ _ hneg]] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : ((N : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  simp only [Pi.div_apply, Function.comp_apply, zero_add, ofReal_natCast]
  rw [show -1 * (N : ℂ) = -(N : ℂ) by ring, show -x * (N : ℂ) = -(N * x) by ring]
  have hNk : ((N : ℂ)) ^ k ≠ 0 := pow_ne_zero _ (by exact_mod_cast hN.ne')
  unfold gaussHGCoeff
  by_cases hp : poch (-(N : ℂ)) k = 0
  · simp [hp]
  · field_simp

@[dlmf 18.21.E6]
theorem krawtchouk_limit_charlier {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => krawtchouk (a / N) N n x) atTop (𝓝 (charlier a n x)) := by
  unfold krawtchouk charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-a⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-a⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  simp only [inv_div] at hlim ⊢
  have e : (-a⁻¹) ^ k * (-(N : ℂ)) ^ k = ((N : ℂ) / a) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (-(N : ℂ)) k) * e

@[dlmf 18.21.E7]
theorem meixner_limit_charlier {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => meixner b (a / (a + b)) n x) atTop (𝓝 (charlier a n x)) := by
  unfold meixner charlier terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hlim := (tendsto_poch_add_div_pow 0 k).inv₀ one_ne_zero
  rw [inv_one] at hlim
  simp only [inv_div, zero_add] at hlim
  have := hlim.const_mul (poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k)
  rw [mul_one] at this
  rw [show poch (-(n : ℂ)) k * poch (-x) k / 1 * (-(a : ℂ)⁻¹) ^ k / (k.factorial : ℂ) =
      poch (-(n : ℂ)) k * poch (-x) k / k.factorial * (-(a : ℂ)⁻¹) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with b hb
  have hb' : (b : ℂ) ≠ 0 := ofReal_ne_zero.mpr hb.ne'
  have ha' : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hab : (a : ℂ) + b ≠ 0 := by exact_mod_cast (add_pos ha hb).ne'
  have e : (-(a : ℂ)⁻¹) ^ k * (b : ℂ) ^ k = (1 - ((a : ℂ) / (a + b))⁻¹) ^ k := by
    rw [← mul_pow]; congr 1; field_simp; ring
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k / k.factorial / poch (b : ℂ) k) * e

/-- Charlier polynomials as polynomials in `x`. -/
def charlierPoly (a : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C (poch (-(n : ℂ)) k * (-a⁻¹) ^ k / k.factorial) *
    (ascPochhammer ℂ k).comp (-X)

/-- Evaluation of `charlierPoly` is the Charlier polynomial. -/
lemma eval_charlierPoly (a : ℂ) (n : ℕ) (x : ℂ) : (charlierPoly a n).eval x = charlier a n x := by
  simp only [charlierPoly, charlier, terminatingHG, eval_finsetSum, eval_mul, eval_C, eval_comp,
    eval_neg, eval_X, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [poch]; ring

/-- Self-duality of the Charlier polynomials at integer points. -/
lemma charlier_swap (a : ℂ) (n m : ℕ) : charlier a n m = charlier a m n := by
  simp only [charlier]
  exact terminatingHG_two_neg_nat_swap n m [] _

/-- The three-term recurrence of the Charlier polynomials in the degree. -/
theorem charlier_recurrence {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    a * charlier a (n + 2) x =
      (n + 1 + a - x) * charlier a (n + 1) x - (n + 1) * charlier a n x := by
  -- integer points, from the difference equation and duality
  have hint : ∀ m : ℕ, a * charlier a (n + 2) m =
      (n + 1 + a - m) * charlier a (n + 1) m - (n + 1) * charlier a n m := by
    intro m
    have h := charlier_difference_equation ha m ((n + 1 : ℕ) : ℂ)
    rw [show ((n + 1 : ℕ) : ℂ) + 1 = ((n + 2 : ℕ) : ℂ) by push_cast; ring,
      show ((n + 1 : ℕ) : ℂ) - 1 = ((n : ℕ) : ℂ) by push_cast; ring,
      charlier_swap a m (n + 2), charlier_swap a m (n + 1), charlier_swap a m n] at h
    push_cast at h
    linear_combination h
  -- polynomial identity
  have hpoly : C a * charlierPoly a (n + 2) =
      (C (n + 1 + a) - X) * charlierPoly a (n + 1) - C ((n : ℂ) + 1) * charlierPoly a n := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℂ))
      Nat.cast_injective fun m => ?_
    simp only [Set.mem_ofPred_eq, eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly]
    rw [hint m]
  have := congrArg (eval x) hpoly
  simp only [eval_mul, eval_sub, eval_C, eval_X, eval_charlierPoly] at this
  rw [this]


@[dlmf 18.21.E9]
theorem charlier_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop (𝓝 ((-1 : ℂ) ^ n * aeval x (hermitePolyH n))) := by
  set f : ℕ → ℝ → ℂ := fun n a =>
    (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a) with hf
  -- the scaled recurrence coefficient `√(2a)/a`
  have hs : Tendsto (fun a : ℝ => ((Real.sqrt (2 * a) / a : ℝ) : ℂ)) atTop (𝓝 0) := by
    have : Tendsto (fun a : ℝ => Real.sqrt 2 * (Real.sqrt a)⁻¹) atTop (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)).const_mul (Real.sqrt 2)
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by simp]
    refine Complex.continuous_ofReal.continuousAt.tendsto.comp (this.congr' ?_)
    filter_upwards [eventually_gt_atTop 0] with a ha
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), mul_div_assoc]
    congr 1
    have hsa : (0 : ℝ) < Real.sqrt a := Real.sqrt_pos.mpr ha
    field_simp
    rw [Real.sq_sqrt ha.le]
  refine tendsto_of_three_term (f := f) (g := fun n => (-1 : ℂ) ^ n * aeval x (hermitePolyH n))
    (A := fun n a => (n + 1 : ℂ) * ((Real.sqrt (2 * a) / a : ℝ) : ℂ) - 2 * x)
    (B := fun n _ => -2 * (n + 1 : ℂ)) (A' := fun _ => -2 * x) (B' := fun n => -2 * (n + 1 : ℂ))
    ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [hf, charlier, terminatingHG, poch_zero]
  · have h1 : (aeval x (hermitePolyH 1) : ℂ) = 2 * x := by simp [hermitePolyH_succ, map_ofNat]
    simp only [pow_one, h1]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    simp only [hf, charlier, terminatingHG, Finset.sum_range_succ, Finset.sum_range_zero,
      List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, poch_zero, poch_one, pow_one]
    field_simp
    linear_combination x * hsq
  · intro n
    simpa using (hs.const_mul ((n : ℂ) + 1)).sub_const (2 * x)
  · intro n; exact tendsto_const_nhds
  · intro n
    filter_upwards [eventually_gt_atTop 0] with a ha
    have hsq : ((Real.sqrt (2 * a) : ℝ) : ℂ) ^ 2 = 2 * a := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; push_cast; ring
    have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
    have hrec := charlier_recurrence ha0 n ((Real.sqrt (2 * a) : ℂ) * x + a)
    simp only [hf]
    set S : ℂ := ((Real.sqrt (2 * a) : ℝ) : ℂ)
    push_cast
    rw [show S ^ (n + 2) = S ^ n * S ^ 2 by ring, show S ^ (n + 1) = S ^ n * S by ring]
    field_simp
    linear_combination (S ^ n * S ^ 2) * hrec -
      (S * S ^ n * x * charlier (↑a) (n + 1) (S * x + ↑a) +
        S ^ n * (n + 1) * charlier (↑a) n (S * x + ↑a)) * hsq
  · intro n
    rw [aeval_hermitePolyH_succ_succ]
    ring


@[dlmf 18.21.E4]
theorem hahn_limit_meixner {β c : ℝ} (hc : 0 < c) (hc1 : c < 1) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn (β - 1) (N * (c⁻¹ - 1)) N n x) atTop (𝓝 (meixner β c n x)) := by
  unfold hahn meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set d : ℝ := c⁻¹ - 1 with hd
  have hd0 : 0 < d := by rw [hd, sub_pos]; exact one_lt_inv₀ hc |>.mpr hc1
  have hNd : Tendsto (fun N : ℕ => (N : ℝ) * d) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_mul_const hd0
  have h1 := (tendsto_poch_add_div_pow ((n : ℂ) + β) k).comp hNd
  have h2 := (tendsto_poch_neg_div_pow k).inv₀ one_ne_zero
  rw [inv_one] at h2
  simp only [inv_div] at h2
  have := (h1.mul h2).const_mul
    (poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k / k.factorial * (-(d : ℂ)) ^ k)
  rw [mul_one, mul_one] at this
  have hz : (1 : ℂ) - ((c : ℂ))⁻¹ = -(d : ℂ) := by rw [hd]; push_cast; ring
  rw [hz, show poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k * (-(d : ℂ)) ^ k /
      (k.factorial : ℂ) = poch (-(n : ℂ)) k * poch (-x) k / poch (β : ℂ) k /
      k.factorial * (-(d : ℂ)) ^ k by ring]
  refine this.congr' ?_
  filter_upwards [eventually_ne_atTop 0] with N hN
  have hN' : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hd' : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd0.ne'
  simp only [Function.comp_apply, ofReal_mul, ofReal_natCast]
  have e1 : (n : ℂ) + (β - 1) + N * (((c⁻¹ : ℝ) : ℂ) - 1) + 1 = (n + β) + N * d := by
    rw [hd]; push_cast; ring
  have e : (-(d : ℂ)) ^ k * (-(N : ℂ)) ^ k = (N : ℂ) ^ k * d ^ k := by
    rw [← mul_pow, ← mul_pow]; ring_nf
  rw [e1, show (β : ℂ) - 1 + 1 = β by ring, one_pow, mul_pow]
  field_simp
  linear_combination (poch (-(n : ℂ)) k * poch (-x) k * poch ((n : ℂ) + β + d * N) k /
    (poch (β : ℂ) k * k.factorial * poch (-(N : ℂ)) k)) * e

@[dlmf 18.21.E8]
theorem meixner_limit_laguerrePolyL {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun c : ℝ => meixner (α + 1) c n (x / (1 - c : ℂ))) (𝓝[<] 1)
      (𝓝 (laguerrePolyL α n x / laguerrePolyL α n 0)) := by
  have hα' : ∀ k : ℕ, (α : ℂ) + 1 ≠ -k := not_neg_nat_of_re_pos (by simp; linarith)
  have hp : poch ((α : ℂ) + 1) n / n.factorial ≠ 0 :=
    div_ne_zero (poch_ne_zero_of_not_neg_nat hα' n) (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  have hL : laguerrePolyL α n x / laguerrePolyL α n 0 = kummerM (-n) (α + 1) x := by
    unfold laguerrePolyL
    rw [kummerM_zero, mul_one, mul_div_cancel_left₀ _ hp]
  have key : ∀ (c : ℝ), c ≠ 0 → c ≠ 1 → ∀ k : ℕ,
      poch (-(x / (1 - c : ℂ))) k * (1 - (c : ℂ)⁻¹) ^ k =
        ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c) := by
    intro c h0 h1 k
    have h0' : (c : ℂ) ≠ 0 := ofReal_ne_zero.mpr h0
    have h1' : (1 - c : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h1.symm)
    induction k with
    | zero => simp [poch_zero]
    | succ k ih =>
      rw [poch_succ, Finset.prod_range_succ, ← ih, pow_succ]
      field_simp
      ring
  rw [hL, kummerM_eq_sum_neg_nat]
  unfold meixner terminatingHG
  apply tendsto_finsetSum
  intro k _
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hprod : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c))
      (𝓝[<] 1) (𝓝 (x ^ k)) := by
    have h : Tendsto (fun c : ℝ => ∏ i ∈ Finset.range k, ((x - i * (1 - c)) / c)) (𝓝 1)
        (𝓝 (∏ i ∈ Finset.range k, ((x - i * (1 - ((1 : ℝ) : ℂ))) / ((1 : ℝ) : ℂ)))) := by
      apply tendsto_finsetProd
      intro i _
      exact (ContinuousAt.div (by fun_prop) (by fun_prop) (by simp)).tendsto
    simp only [ofReal_one, sub_self, mul_zero, sub_zero, div_one, Finset.prod_const,
      Finset.card_range] at h
    exact h.mono_left nhdsWithin_le_nhds
  have := hprod.const_mul (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k.factorial))
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (lt_mem_nhds zero_lt_one)]
    with c hc1 hc0
  rw [← key c hc0.ne' hc1.ne]
  ring

@[dlmf 18.21.E12]
theorem meixnerPollaczek_limit_laguerrePolyL {α : ℝ} (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => meixnerPollaczek ((α + 1) / 2) phi n (-x / (2 * (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (laguerrePolyL α n x)) := by
  have hE0 : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun t : ℝ => 1 - cexp (-2 * I * t)) (𝓝 0)
        (𝓝 (1 - cexp (-2 * I * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  have hE1 : Tendsto (fun t : ℝ => (1 - cexp (-2 * I * t)) / t) (𝓝[>] 0) (𝓝 (2 * I)) := by
    have hd := (((hasDerivAt_id (0 : ℝ)).ofReal_comp).const_mul (-2 * I)).cexp
    have h := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
      (nhdsWithin_mono _ fun t (ht : 0 < t) => ht.ne')
    have h' := h.neg
    simp only [id, ofReal_one, mul_one, ofReal_zero, mul_zero, Complex.exp_zero, one_mul] at h'
    rw [show -(-2 * I) = 2 * I by ring] at h'
    refine h'.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [slope, sub_zero, vsub_eq_sub, Complex.real_smul, ofReal_inv, ofReal_zero,
      mul_zero, Complex.exp_zero]
    ring
  have hexp : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun t : ℝ => cexp (I * n * t)) (𝓝 0)
        (𝓝 (cexp (I * n * ((0 : ℝ) : ℂ)))) := Continuous.tendsto (by fun_prop) 0
    simpa using h.mono_left nhdsWithin_le_nhds
  unfold meixnerPollaczek laguerrePolyL terminatingHG
  rw [show 2 * (((α : ℂ) + 1) / 2) = α + 1 by ring, kummerM_eq_sum_neg_nat]
  have hpre : Tendsto (fun t : ℝ => poch ((α : ℂ) + 1) n / n ! * cexp (I * n * t)) (𝓝[>] 0)
      (𝓝 (poch ((α : ℂ) + 1) n / n !)) := by
    simpa using (tendsto_const_nhds (x := poch ((α : ℂ) + 1) n / n !)).mul hexp
  refine hpre.mul (tendsto_finsetSum _ fun k _ => ?_)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have hfac : ∀ j : ℕ, Tendsto (fun t : ℝ => (((α : ℂ) + 1) / 2 + j) * (1 - cexp (-2 * I * t)) -
      I * x / 2 * ((1 - cexp (-2 * I * t)) / t)) (𝓝[>] 0) (𝓝 x) := by
    intro j
    have h := (hE0.const_mul (((α : ℂ) + 1) / 2 + j)).sub (hE1.const_mul (I * x / 2))
    convert h using 2
    ring_nf
    rw [I_sq]
    ring
  have hprod := (tendsto_finsetProd (Finset.range k) fun j _ => hfac j).const_mul
    (poch (-(n : ℂ)) k / (poch ((α : ℂ) + 1) k * k !))
  rw [Finset.prod_const, Finset.card_range] at hprod
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt ht)
  rw [Finset.prod_congr rfl (g := fun j : ℕ => ((((α : ℂ) + 1) / 2 + I * (-x / (2 * t))) + j) *
    (1 - cexp (-2 * I * t))) (fun j _ => by field_simp; ring), ← poch_mul_pow]
  ring

@[dlmf 18.21.E13]
theorem meixnerPollaczek_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => n.factorial * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam)) atTop (𝓝 (aeval x (hermitePolyH n))) := by
  have hsc : sin ((Real.pi : ℂ) / 2) = 1 := Complex.sin_pi_div_two
  have hcc : cos ((Real.pi : ℂ) / 2) = 0 := Complex.cos_pi_div_two
  refine tendsto_of_three_term (f := fun n lam => (n ! : ℂ) * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam))
    (g := fun n => aeval x (hermitePolyH n))
    (A := fun n _ => 2 * x) (B := fun n lam => -((n + 1) * (2 + n / (lam : ℂ))))
    (A' := fun n => 2 * x) (B' := fun n => -((n + 1) * 2)) ?_ ?_ ?_ ?_ ?_ ?_ n
  · simp [meixnerPollaczek, terminatingHG, poch_zero]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hl' : (lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr hl.ne'
    rw [meixnerPollaczek_one hl', hsc, hcc]
    simp only [hermitePolyH_one, map_mul, aeval_X, map_ofNat, Nat.factorial_one, Nat.cast_one]
    field_simp
    ring
  · intro n; exact tendsto_const_nhds
  · intro n
    simpa only [add_zero] using
      (((tendsto_const_div_ofReal_atTop (n : ℂ)).const_add 2).const_mul ((n : ℂ) + 1)).neg
  · intro n
    filter_upwards [eventually_gt_atTop 0] with lam hl
    have hs : (Real.sqrt lam : ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hl).ne'
    have hs2 : (lam : ℂ) = (Real.sqrt lam : ℂ) ^ 2 := by
      rw [← ofReal_pow, Real.sq_sqrt hl.le]
    have hr := meixnerPollaczek_recurrence (lam := lam) (by simpa using hl)
      ((Real.pi : ℂ) / 2) n (x * Real.sqrt lam)
    rw [hsc, hcc, mul_comm x] at hr
    have hf2 : ((n + 2) ! : ℂ) = (n + 2) * (n + 1) * n ! := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    have hf1 : ((n + 1) ! : ℂ) = (n + 1) * n ! := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [hf2, hf1, inv_pow]
    rw [hs2] at hr ⊢
    field_simp
    linear_combination ((n ! : ℂ) * (Real.sqrt lam : ℂ) ^ (2 * n + 3)) * hr
  · intro n
    rw [hermitePolyH_succ (n + 1), hermitePolyH_derivative]
    simp only [map_sub, map_mul, aeval_X, aeval_C, map_ofNat]
    push_cast
    ring

@[dlmf 18.22.E14]
theorem continuousHahn_difference_equation {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (n : ℕ) (x : ℂ) :
    (x + I * star a) * (x + I * star b) *
      (continuousHahn a b (star a) (star b) n (x + I) - continuousHahn a b (star a) (star b) n x) +
    (x - I * a) * (x - I * b) *
      (continuousHahn a b (star a) (star b) n (x - I) - continuousHahn a b (star a) (star b) n x) +
    n * (n + a + b + star a + star b - 1) * continuousHahn a b (star a) (star b) n x = 0 := by
  set c : ℂ := star a with hcdef
  set d : ℂ := star b with hddef
  have hAre : 0 < (a + c).re := by simp [hcdef]; linarith
  have hDre : 0 < (a + d).re := by simp [hddef]; linarith
  have hpA : ∀ k : ℕ, poch (a + c) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hAre k
  have hpD : ∀ k : ℕ, poch (a + d) k ≠ 0 := fun k => poch_ne_zero_of_re_pos hDre k
  have hAk : ∀ k : ℕ, a + c + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hAre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have hDk : ∀ k : ℕ, a + d + k ≠ 0 := fun k h => by
    have := congrArg re h; simp only [add_re, natCast_re, zero_re] at this hDre
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  clear_value c d
  set s : ℂ := (n : ℂ) + a + b + c + d - 1 with hs
  set w : ℂ := a + I * x with hw
  set cf : ℕ → ℂ := fun k => poch (-(n : ℂ)) k * poch s k / (poch (a + c) k * poch (a + d) k) /
    k ! with hcf
  set G : ℕ → ℂ := fun k => cf k * ((n - k) * (n + k + a + b + c + d - 1) * poch w k) with hG
  set B : ℕ → ℂ := fun k => -((w - a - c) * (w - a - d)) * (poch (w - 1) k - poch w k) -
      w * (w - a + b) * (poch (w + 1) k - poch w k) +
      n * (n + a + b + c + d - 1) * poch w k with hB
  have hrec : ∀ k : ℕ, cf (k + 1) * ((k + 1) * (a + c + k) * (a + d + k)) =
      cf k * ((k - n) * (s + k)) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hpA k; have := hpD k; have := hAk k; have := hDk k
    simp only [hcf]
    rw [poch_succ, poch_succ s, poch_succ (a + c), poch_succ (a + d), Nat.factorial_succ]
    push_cast
    field_simp
    ring
  have htel : ∀ k : ℕ, cf (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [ch_basis_succ a b c d w n k]
    have hr := hrec k
    push_cast
    linear_combination (poch w k) * hr
  have hkey : ∑ k ∈ Finset.range (n + 1), cf k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hcf, poch_zero, sub_self]
    push_cast
    ring
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [show a + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show a + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show (x + I * c) * (x + I * d) = -((w - a - c) * (w - a - d)) by
      rw [hw]; linear_combination (x ^ 2 + c * d) * I_sq,
    show (x - I * a) * (x - I * b) = -(w * (w - a + b)) by
      rw [hw]; linear_combination (x ^ 2 + a * b) * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (poch ((n : ℂ) + a + b + c + d - 1) k * poch v k) / (poch (a + c) k * poch (a + d) k) /
        (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), cf k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hcf, hs]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G cf w s
  have hexp : ∑ k ∈ Finset.range (n + 1), cf k * B k =
      -((w - a - c) * (w - a - d)) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) -
      w * (w - a + b) * (∑ k ∈ Finset.range (n + 1), cf k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), cf k * poch w k) +
      n * (n + a + b + c + d - 1) * ∑ k ∈ Finset.range (n + 1), cf k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(I ^ n * poch (a + c) n * poch (a + d) n / n !)) * hexp +
    (I ^ n * poch (a + c) n * poch (a + d) n / n ! * n *
      ∑ k ∈ Finset.range (n + 1), cf k * poch w k) * hs

@[dlmf 18.22.E17]
theorem meixnerPollaczek_difference_equation {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    exp (I * phi) * (x + I * lam) * (meixnerPollaczek lam phi n (x + I) - meixnerPollaczek lam phi n x) +
    exp (-I * phi) * (x - I * lam) * (meixnerPollaczek lam phi n (x - I) - meixnerPollaczek lam phi n x) +
    2 * n * sin phi * meixnerPollaczek lam phi n x = 0 := by
  have hp : ∀ k : ℕ, poch (2 * lam) k ≠ 0 := fun k => poch_ne_zero_of_re_pos (by simp; linarith) k
  have h2k : ∀ k : ℕ, 2 * lam + k ≠ 0 := fun k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  set z : ℂ := 1 - exp (-2 * I * phi) with hz
  set w : ℂ := lam + I * x with hw
  set c : ℕ → ℂ := fun k => poch (-(n : ℂ)) k / poch (2 * lam) k * z ^ k / k ! with hc
  set G : ℕ → ℂ := fun k => c k * (2 * (n - k) * sin phi * poch w k) with hG
  have hS := exp_mul_one_sub_exp phi
  -- the coefficient recurrence
  have hrec : ∀ k : ℕ, c (k + 1) * ((k + 1) * (k + 2 * lam)) = c k * ((k - n) * z) := by
    intro k
    have hf : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
    have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    have := hp k; have := h2k k
    simp only [hc]
    rw [poch_succ, poch_succ, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring
  -- the basis action, telescoped
  set B : ℕ → ℂ := fun k => exp (I * phi) * (-I * (w - 2 * lam)) * (poch (w - 1) k - poch w k) +
      exp (-I * phi) * (-I * w) * (poch (w + 1) k - poch w k) + 2 * n * sin phi * poch w k with hB
  have htel : ∀ k : ℕ, c (k + 1) * B (k + 1) = G (k + 1) - G k := by
    intro k
    simp only [hB, hG]
    rw [mp_basis_succ lam phi w n k]
    have hr := hrec k
    have hz' : I * (exp (I * phi) * z) = -2 * sin phi := by
      rw [hz, hS]; linear_combination (2 * sin phi) * I_sq
    push_cast
    linear_combination (-(I * exp (I * phi) * poch w k)) * hr +
      (c k * (n - k) * poch w k) * hz'
  have hkey : ∑ k ∈ Finset.range (n + 1), c k * B k = 0 := by
    rw [Finset.sum_range_succ']
    simp_rw [htel]
    rw [Finset.sum_range_sub]
    simp only [hB, hG, hc, poch_zero, sub_self]
    push_cast
    ring
  unfold meixnerPollaczek terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show lam + I * (x + I) = w - 1 by rw [hw]; linear_combination I_sq,
    show lam + I * (x - I) = w + 1 by rw [hw]; linear_combination -I_sq,
    show x + I * lam = -I * (w - 2 * lam) by rw [hw]; linear_combination x * I_sq,
    show x - I * lam = -I * w by rw [hw]; linear_combination x * I_sq]
  have hfin : ∀ v : ℂ, ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch v k / poch (2 * lam) k *
      z ^ k / (k ! : ℂ) = ∑ k ∈ Finset.range (n + 1), c k * poch v k := fun v =>
    Finset.sum_congr rfl fun k _ => by simp only [hc]; ring
  rw [hfin, hfin, hfin, ← hw]
  clear_value B G c w z
  have hexp : ∑ k ∈ Finset.range (n + 1), c k * B k =
      exp (I * phi) * (-I * (w - 2 * lam)) * (∑ k ∈ Finset.range (n + 1), c k * poch (w - 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      exp (-I * phi) * (-I * w) * (∑ k ∈ Finset.range (n + 1), c k * poch (w + 1) k -
        ∑ k ∈ Finset.range (n + 1), c k * poch w k) +
      2 * n * sin phi * ∑ k ∈ Finset.range (n + 1), c k * poch w k := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hB]
    ring
  rw [hkey] at hexp
  linear_combination (-(poch (2 * lam) n / n ! * exp (I * n * phi))) * hexp

@[dlmf 18.22.E27]
theorem continuousHahn_central_difference {a b c d : ℂ} (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (x : ℂ) :
    (continuousHahn a b c d (n + 1) (x + I / 2) - continuousHahn a b c d (n + 1) (x - I / 2)) / I =
      (n + a + b + c + d) * continuousHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n x := by
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  unfold continuousHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one, sub_self, add_zero]
  rw [show a + I * (x + I / 2) = (a + I * x) - 1 / 2 by linear_combination (1 / 2 : ℂ) * I_sq,
    show a + I * (x - I / 2) = (a + I * x) + 1 / 2 by linear_combination (-1 / 2 : ℂ) * I_sq]
  rw [mul_div_assoc, Finset.sum_div, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_half_sub (a + I * x) k
  rw [← sub_div, ← sub_div, ← mul_sub, ← mul_sub, key]
  rw [poch_succ_left (a + c), poch_succ_left (a + d),
    poch_succ_left (a + c) k, poch_succ_left (a + d) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), poch_succ_left (((n + 1 : ℕ) : ℂ) + a + b + c + d - 1),
    Nat.factorial_succ, Nat.factorial_succ,
    show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring, show a + 1 / 2 + (d + 1 / 2) = a + d + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show ((n + 1 : ℕ) : ℂ) + a + b + c + d - 1 + 1 = (n : ℂ) + (a + 1 / 2) + (b + 1 / 2) +
      (c + 1 / 2) + (d + 1 / 2) - 1 by push_cast; ring,
    show a + I * x + 1 / 2 = a + 1 / 2 + I * x by ring, pow_succ]
  have := h0 _ hac; have := h0 _ had
  have := hp _ k hac; have := hp _ k had
  have := hp _ n hac; have := hp _ n had
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hn : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  push_cast
  field_simp
  ring

@[dlmf 18.23.E6]
theorem continuousHahn_generating_function {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (x z : ℂ) :
    HasSum (fun n : ℕ => continuousHahn a b (star a) (star b) n x /
      (poch (a + star a) n * poch (b + star b) n) * z ^ n)
      (kummerM (a + I * x) (a + star a) (-I * z) * kummerM (star b - I * x) (b + star b) (I * z)) := by
  sorry


end AAR.OrthogonalPolynomials
