/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import AAR.Hypergeometric.Continuation
public import Mathlib.Tactic.CrossRefAttribute

/-!
# The Hahn class: definitions, orthogonality, differences, and generating functions

Statements from NIST DLMF Chapter 18. See `DLMFCoverage.md` for the source inventory.
Jacobi and Gegenbauer statements retain regularity hypotheses because the project's
hypergeometric definitions do not implement continuation in singular parameters.
-/

@[expose] public section

open Complex Polynomial MeasureTheory Filter
open scoped Real Nat Topology

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
  sorry

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
  sorry

@[dlmf 18.22.E29]
theorem meixnerPollaczek_central_difference {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    (meixnerPollaczek lam phi (n + 1) (x + I / 2) - meixnerPollaczek lam phi (n + 1) (x - I / 2)) / I =
      2 * sin phi * meixnerPollaczek (lam + 1 / 2) phi n x := by
  sorry

@[dlmf 18.23.E3]
theorem krawtchouk_generating_function {p : ℂ} (hp : p ≠ 0) {N x : ℕ} (hx : x ≤ N) (z : ℂ) :
    ∑ n ∈ Finset.range (N + 1), (N.choose n : ℂ) * krawtchouk p N n x * z ^ n =
      (1 - (1 - p) / p * z) ^ x * (1 + z) ^ (N - x) := by
  sorry

@[dlmf 18.23.E4]
theorem meixner_generating_function {β c : ℂ} (hβ : 0 < β.re) (hc : c ≠ 0) (x : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => poch β n / n.factorial * meixner β c n x * z ^ n)
      ((1 - z / c) ^ x * (1 - z) ^ (-(x : ℂ) - β)) := by
  sorry

@[dlmf 18.23.E5]
theorem charlier_generating_function {a : ℂ} (ha : a ≠ 0) (x : ℕ) (z : ℂ) :
    HasSum (fun n : ℕ => charlier a n x / n.factorial * z ^ n) (exp z * (1 - z / a) ^ x) := by
  sorry

@[dlmf 18.23.E7]
theorem meixnerPollaczek_generating_function {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => meixnerPollaczek lam phi n x * z ^ n)
      ((1 - exp (I * phi) * z) ^ (-lam + I * x) * (1 - exp (-I * phi) * z) ^ (-lam - I * x)) := by
  sorry

@[dlmf 18.21.E3]
theorem hahn_limit_krawtchouk {p : ℝ} (hp : 0 < p) (hp1 : p < 1) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun t : ℝ => hahn (p * t) ((1 - p) * t) N n x) atTop (𝓝 (krawtchouk p N n x)) := by
  sorry

@[dlmf 18.21.E5]
theorem hahn_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn α β N n (N * x)) atTop (𝓝 (jacobiP α β n (1 - 2 * x) / jacobiP α β n 1)) := by
  sorry

@[dlmf 18.21.E6]
theorem krawtchouk_limit_charlier {a : ℂ} (ha : a ≠ 0) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => krawtchouk (a / N) N n x) atTop (𝓝 (charlier a n x)) := by
  sorry

@[dlmf 18.21.E7]
theorem meixner_limit_charlier {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℂ) :
    Tendsto (fun b : ℝ => meixner b (a / (a + b)) n x) atTop (𝓝 (charlier a n x)) := by
  sorry

@[dlmf 18.21.E9]
theorem charlier_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun a : ℝ => (Real.sqrt (2 * a) : ℂ) ^ n * charlier a n ((Real.sqrt (2 * a) : ℂ) * x + a)) atTop (𝓝 ((-1 : ℂ) ^ n * aeval x (hermitePhys n))) := by
  sorry


@[dlmf 18.21.E4]
theorem hahn_limit_meixner {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) (hc1 : c < 1) (n : ℕ) (x : ℂ) :
    Tendsto (fun N : ℕ => hahn (β - 1) (N * (c⁻¹ - 1)) N n x) atTop (𝓝 (meixner β c n x)) := by
  sorry

@[dlmf 18.21.E8]
theorem meixner_limit_laguerre {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun c : ℝ => meixner (α + 1) c n (x / (1 - c : ℂ))) (𝓝[<] 1)
      (𝓝 (laguerre α n x / laguerre α n 0)) := by
  sorry

@[dlmf 18.21.E12]
theorem meixnerPollaczek_limit_laguerre {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => meixnerPollaczek ((α + 1) / 2) phi n (-x / (2 * (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (laguerre α n x)) := by
  sorry

@[dlmf 18.21.E13]
theorem meixnerPollaczek_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => n.factorial * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      meixnerPollaczek lam (Real.pi / 2) n (x * Real.sqrt lam)) atTop (𝓝 (aeval x (hermitePhys n))) := by
  sorry

@[dlmf 18.22.E14]
theorem continuousHahn_difference_equation {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (n : ℕ) (x : ℂ) :
    (x + I * star a) * (x + I * star b) *
      (continuousHahn a b (star a) (star b) n (x + I) - continuousHahn a b (star a) (star b) n x) +
    (x - I * a) * (x - I * b) *
      (continuousHahn a b (star a) (star b) n (x - I) - continuousHahn a b (star a) (star b) n x) +
    n * (n + a + b + star a + star b - 1) * continuousHahn a b (star a) (star b) n x = 0 := by
  sorry

@[dlmf 18.22.E17]
theorem meixnerPollaczek_difference_equation {lam : ℂ} (hlam : 0 < lam.re) (phi : ℂ) (n : ℕ) (x : ℂ) :
    exp (I * phi) * (x + I * lam) * (meixnerPollaczek lam phi n (x + I) - meixnerPollaczek lam phi n x) +
    exp (-I * phi) * (x - I * lam) * (meixnerPollaczek lam phi n (x - I) - meixnerPollaczek lam phi n x) +
    2 * n * sin phi * meixnerPollaczek lam phi n x = 0 := by
  sorry

@[dlmf 18.22.E27]
theorem continuousHahn_central_difference {a b c d : ℂ} (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (x : ℂ) :
    (continuousHahn a b c d (n + 1) (x + I / 2) - continuousHahn a b c d (n + 1) (x - I / 2)) / I =
      (n + a + b + c + d) * continuousHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n x := by
  sorry

@[dlmf 18.23.E6]
theorem continuousHahn_generating_function {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (x z : ℂ) :
    HasSum (fun n : ℕ => continuousHahn a b (star a) (star b) n x /
      (poch (a + star a) n * poch (b + star b) n) * z ^ n)
      (confluentM (a + I * x) (a + star a) (-I * z) * confluentM (star b - I * x) (b + star b) (I * z)) := by
  sorry


end AAR.OrthogonalPolynomials
