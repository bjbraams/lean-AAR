/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Hahn
/-!
# Wilson, continuous dual Hahn, Racah, and dual Hahn polynomials

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

/-- Wilson polynomials in the polynomial argument `x = y²`. The product form
avoids choosing a square root. -/
@[dlmf 18.26.E1]
def wilson (a b c d : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n * poch (a + d) n *
    ∑ k ∈ Finset.range (n + 1),
      poch (-(n : ℂ)) k * poch (n + a + b + c + d - 1) k *
        (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * poch (a + d) k * k.factorial)

@[dlmf 18.26.E2]
def continuousDualHahn (a b c : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  poch (a + b) n * poch (a + c) n *
    ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
      (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
      (poch (a + b) k * poch (a + c) k * k.factorial)

@[dlmf 18.26.E3]
def racah (α β γ δ : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + α + β + 1) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (α + 1) k * poch (β + δ + 1) k * poch (γ + 1) k * k.factorial)

@[dlmf 18.26.E4]
def dualHahn (γ δ : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
    (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
    (poch (γ + 1) k * poch (-(N : ℂ)) k * k.factorial)

/-- Factoring the quadratic product into two Pochhammer symbols. -/
lemma poch_mul_eq_prod (u v : ℂ) (k : ℕ) :
    poch u k * poch v k = ∏ j ∈ Finset.range k, (u + j) * (v + j) := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, poch_succ, Finset.prod_range_succ, ← ih]
    ring

lemma poch_conjugate_pair (a y : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((a + j) ^ 2 + y ^ 2) = poch (a + I * y) k * poch (a - I * y) k := by
  rw [poch_mul_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  calc
    _ = (a + I * y + j) * (a - I * y + j) + (I ^ 2 + 1) * y ^ 2 := by ring
    _ = _ := by rw [I_sq]; ring

lemma poch_quadratic_pair (v y : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((j : ℂ) * (j + v) - y * (y + v)) =
      poch (-y) k * poch (y + v) k := by
  rw [poch_mul_eq_prod]
  apply Finset.prod_congr rfl
  intro j _
  ring

@[dlmf 18.26.E1]
theorem wilson_hypergeometric (a b c d : ℂ) (n : ℕ) (y : ℂ) :
    wilson a b c d n (y ^ 2) = poch (a + b) n * poch (a + c) n * poch (a + d) n *
      terminatingHG n [-(n : ℂ), n + a + b + c + d - 1, a + I * y, a - I * y] [a + b, a + c, a + d] 1 := by
  unfold wilson terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [poch_conjugate_pair]
  ring

@[dlmf 18.26.E2]
theorem continuousDualHahn_hypergeometric (a b c : ℂ) (n : ℕ) (y : ℂ) :
    continuousDualHahn a b c n (y ^ 2) = poch (a + b) n * poch (a + c) n *
      terminatingHG n [-(n : ℂ), a + I * y, a - I * y] [a + b, a + c] 1 := by
  unfold continuousDualHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [poch_conjugate_pair]
  ring

@[dlmf 18.26.E3]
theorem racah_hypergeometric (α β γ δ : ℂ) (n : ℕ) (y : ℂ) :
    racah α β γ δ n (y * (y + γ + δ + 1)) =
      terminatingHG n [-(n : ℂ), n + α + β + 1, -y, y + γ + δ + 1] [α + 1, β + δ + 1, γ + 1] 1 := by
  unfold racah terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hp := poch_quadratic_pair (γ + δ + 1) y k
  simp only [show y + (γ + δ + 1) = y + γ + δ + 1 by ring,
    show ∀ j : ℕ, (j : ℂ) + (γ + δ + 1) = j + γ + δ + 1 by intro j; ring] at hp
  rw [hp]
  ring

@[dlmf 18.26.E4]
theorem dualHahn_hypergeometric (γ δ : ℂ) (N n : ℕ) (y : ℂ) :
    dualHahn γ δ N n (y * (y + γ + δ + 1)) =
      terminatingHG n [-(n : ℂ), -y, y + γ + δ + 1] [γ + 1, -(N : ℂ)] 1 := by
  unfold dualHahn terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  apply Finset.sum_congr rfl
  intro k _
  have hp := poch_quadratic_pair (γ + δ + 1) y k
  simp only [show y + (γ + δ + 1) = y + γ + δ + 1 by ring,
    show ∀ j : ℕ, (j : ℂ) + (γ + δ + 1) = j + γ + δ + 1 by intro j; ring] at hp
  rw [hp]
  ring

@[dlmf 18.26.E4_1]
theorem dualHahn_hahn_duality (γ δ : ℂ) {N n y : ℕ} (hn : n ≤ N) (hy : y ≤ N) :
    dualHahn γ δ N n ((y : ℂ) * (y + γ + δ + 1)) = hahn γ δ N y n := by
  rw [dualHahn_hypergeometric, hahn]
  have hs := terminatingHG_hasSum_neg_nat n [-(y : ℂ), y + γ + δ + 1] [γ + 1, -(N : ℂ)] 1
  have ht := terminatingHG_hasSum_neg_nat y [y + γ + δ + 1, -(n : ℂ)] [γ + 1, -(N : ℂ)] 1
  apply hs.unique
  convert ht using 1
  funext k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  ring

@[dlmf 18.26.E4_2]
theorem racah_duality (α β γ δ : ℂ) (n y : ℕ) :
    racah α β γ δ n ((y : ℂ) * (y + γ + δ + 1)) = racah γ δ α β y ((n : ℂ) * (n + α + β + 1)) := by
  rw [racah_hypergeometric, racah_hypergeometric]
  have hs := terminatingHG_hasSum_neg_nat n [n + α + β + 1, -(y : ℂ), y + γ + δ + 1]
    [α + 1, β + δ + 1, γ + 1] 1
  have ht := terminatingHG_hasSum_neg_nat y [y + γ + δ + 1, -(n : ℂ), n + α + β + 1]
    [γ + 1, δ + β + 1, α + 1] 1
  apply hs.unique
  convert ht using 1
  funext k
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [show δ + β + 1 = β + δ + 1 by ring]
  ring

@[dlmf 18.25.E2]
theorem wilson_orthogonal {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) {m n : ℕ} (hmn : m ≠ n) :
    ∫ y : ℝ in Set.Ioi 0, wilson a b c d m ((y : ℂ) ^ 2) * wilson a b c d n ((y : ℂ) ^ 2) *
      (‖Gamma (a + I * y) * Gamma (b + I * y) * Gamma (c + I * y) * Gamma (d + I * y) / Gamma (2 * I * y)‖ ^ 2 : ℝ) = 0 := by
  sorry

@[dlmf 18.25.E8]
theorem continuousDualHahn_orthogonality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (m n : ℕ) :
    ∫ y : ℝ in Set.Ioi 0, continuousDualHahn a b c m ((y : ℂ) ^ 2) * continuousDualHahn a b c n ((y : ℂ) ^ 2) *
      (‖Gamma (a + I * y) * Gamma (b + I * y) * Gamma (c + I * y) / Gamma (2 * I * y)‖ ^ 2 : ℝ) =
      if m = n then n.factorial * 2 * Real.pi * Gamma (n + (a : ℂ) + b) *
        Gamma (n + (a : ℂ) + c) * Gamma (n + (b : ℂ) + c) else 0 := by
  sorry

/-- `(u + d)_k / (v + d)_k → 1` as the real `d → ∞`. -/
lemma tendsto_poch_ratio_atTop (u v : ℂ) (k : ℕ) :
    Tendsto (fun d : ℝ => poch (u + d) k / poch (v + d) k) atTop (𝓝 1) := by
  have h := (tendsto_poch_add_div_pow u k).div (tendsto_poch_add_div_pow v k) one_ne_zero
  rw [div_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hd' : (d : ℂ) ^ k ≠ 0 := pow_ne_zero _ (ofReal_ne_zero.mpr hd.ne')
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀ hd']

lemma eventually_poch_add_ne_zero (u : ℂ) (k : ℕ) :
    ∀ᶠ d : ℝ in atTop, poch (u + d) k ≠ 0 := by
  filter_upwards [(tendsto_poch_add_div_pow u k).eventually_ne one_ne_zero] with d hd h
  exact hd (by rw [h, zero_div])

@[dlmf 18.26.E5]
theorem wilson_limit_continuousDualHahn {a b c : ℂ} (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (x : ℂ) :
    Tendsto (fun d : ℝ => wilson a b c d n x / poch (a + d) n) atTop (𝓝 (continuousDualHahn a b c n x)) := by
  unfold wilson continuousDualHahn
  have hT : Tendsto (fun d : ℝ => poch (a + b) n * poch (a + c) n *
      ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
        (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * k.factorial) *
        (poch ((n + a + b + c - 1) + d) k / poch (a + d) k)) atTop
      (𝓝 (poch (a + b) n * poch (a + c) n *
        ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k *
          (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
          (poch (a + b) k * poch (a + c) k * k.factorial))) := by
    refine tendsto_const_nhds.mul (tendsto_finsetSum _ fun k _ => ?_)
    simpa using (tendsto_poch_ratio_atTop (n + a + b + c - 1) a k).const_mul
      (poch (-(n : ℂ)) k * (∏ j ∈ Finset.range k, ((a + j) ^ 2 + x)) /
        (poch (a + b) k * poch (a + c) k * k.factorial))
  refine hT.congr' ?_
  filter_upwards [eventually_poch_add_ne_zero a n] with d hd
  rw [eq_div_iff hd, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (n : ℂ) + a + b + c + d - 1 = n + a + b + c - 1 + d by ring]
  by_cases hk : poch (a + ↑d) k = 0
  · simp [hk]
  · field_simp

@[dlmf 18.26.E9]
theorem racah_limit_dualHahn {γ δ : ℂ} (hγ : -1 < γ.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun b : ℝ => racah (-(N : ℂ) - 1) b γ δ n x) atTop (𝓝 (dualHahn γ δ N n x)) := by
  unfold racah dualHahn
  refine tendsto_finsetSum _ fun k _ => ?_
  have h := (tendsto_poch_ratio_atTop ((n : ℂ) - N) (δ + 1) k).const_mul
    (poch (-(n : ℂ)) k * (∏ j ∈ Finset.range k, ((j : ℂ) * (j + γ + δ + 1) - x)) /
      (poch (γ + 1) k * poch (-(N : ℂ)) k * k.factorial))
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun b => ?_)
  beta_reduce
  rw [show (n : ℂ) + (-(N : ℂ) - 1) + b + 1 = n - N + b by ring,
    show -(N : ℂ) - 1 + 1 = -N by ring, show (b : ℂ) + δ + 1 = δ + 1 + b by ring]
  by_cases hk : poch (δ + 1 + ↑b) k = 0
  · simp [hk]
  · field_simp

@[dlmf 18.26.E10]
theorem racah_limit_hahn {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun d : ℝ => racah α β (-(N : ℂ) - 1) d n (x * (x - N + d))) atTop (𝓝 (hahn α β N n x)) := by
  unfold racah hahn terminatingHG
  refine tendsto_finsetSum _ fun k _ => ?_
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, one_pow]
  have h := (tendsto_poch_ratio_atTop (x - N) (β + 1) k).const_mul
    (poch (-(n : ℂ)) k * (poch (n + α + β + 1) k * poch (-x) k) /
      (poch (α + 1) k * poch (-(N : ℂ)) k) / k.factorial)
  rw [mul_one] at h
  refine h.congr' (Eventually.of_forall fun d => ?_)
  have hprod : ∏ j ∈ Finset.range k, ((j : ℂ) * (j + (-(N : ℂ) - 1) + d + 1) - x * (x - N + d)) =
      poch (-x) k * poch (x - N + d) k := by
    rw [poch_mul_eq_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    ring
  beta_reduce
  rw [hprod, show -(N : ℂ) - 1 + 1 = -N by ring, show (β : ℂ) + d + 1 = β + 1 + d by ring]
  by_cases hk : poch (β + 1 + ↑d) k = 0
  · simp [hk]
  · field_simp

/-- Factoring the shifted Wilson product. -/
lemma prod_sq_add_shift (a y s : ℂ) (k : ℕ) :
    ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + s * I / 2) ^ 2) =
      poch (a + I * y - s / 2) k * poch (a - I * y + s / 2) k := by
  rw [poch_mul_eq_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  linear_combination (y ^ 2 + s ^ 2 / 4) * I_sq

/-- The forward difference of the Wilson product pair. -/
lemma poch_pair_sub (u v : ℂ) (k : ℕ) :
    poch (u - 1 / 2) (k + 1) * poch (v + 1 / 2) (k + 1) -
      poch (u + 1 / 2) (k + 1) * poch (v - 1 / 2) (k + 1) =
      (k + 1) * (u - v) * (poch (u + 1 / 2) k * poch (v + 1 / 2) k) := by
  rw [poch_succ_left (u - 1 / 2), poch_succ (v + 1 / 2), poch_succ (u + 1 / 2),
    poch_succ_left (v - 1 / 2), show u - 1 / 2 + 1 = u + 1 / 2 by ring,
    show v - 1 / 2 + 1 = v + 1 / 2 by ring]
  ring

@[dlmf 18.26.E14]
theorem wilson_central_difference {a b c d : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (y : ℂ) :
    wilson a b c d (n + 1) ((y + I / 2) ^ 2) - wilson a b c d (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * (n + a + b + c + d) *
        wilson (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n (y ^ 2) := by
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  unfold wilson
  have e1 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + I / 2) ^ 2) =
      poch (a + I * y - 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    simpa using prod_sq_add_shift a y 1 k
  have e2 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y - I / 2) ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y - 1 / 2) k := fun k => by
    have := prod_sq_add_shift a y (-1) k
    simp only [neg_mul, one_mul, neg_div] at this
    rw [show y - I / 2 = y + -(I / 2) by ring, this]
    congr 2 <;> ring
  have e3 : ∀ k, ∏ j ∈ Finset.range k, ((a + 1 / 2 + j) ^ 2 + y ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    have := prod_sq_add_shift (a + 1 / 2) y 0 k
    simp only [zero_mul, zero_div, add_zero, sub_zero] at this
    rw [this]; congr 2 <;> ring
  simp_rw [e1, e2, e3]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, one_mul, Nat.factorial_zero, Nat.cast_one, div_one, sub_self,
    add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_pair_sub (a + I * y) (a - I * y) k
  rw [← sub_div, ← mul_sub, key]
  rw [poch_succ_left (a + b), poch_succ_left (a + c), poch_succ_left (a + d),
    poch_succ_left (a + b) k, poch_succ_left (a + c) k, poch_succ_left (a + d) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), poch_succ_left (((n + 1 : ℕ) : ℂ) + a + b + c + d - 1),
    Nat.factorial_succ,
    show a + 1 / 2 + (b + 1 / 2) = a + b + 1 by ring, show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring,
    show a + 1 / 2 + (d + 1 / 2) = a + d + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring,
    show ((n + 1 : ℕ) : ℂ) + a + b + c + d - 1 + 1 = (n : ℂ) + (a + 1 / 2) + (b + 1 / 2) +
      (c + 1 / 2) + (d + 1 / 2) - 1 by push_cast; ring]
  have := h0 _ hab; have := h0 _ hac; have := h0 _ had
  have := hp _ k hab; have := hp _ k hac; have := hp _ k had
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring

@[dlmf 18.26.E15]
theorem continuousDualHahn_central_difference {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (y : ℂ) :
    continuousDualHahn a b c (n + 1) ((y + I / 2) ^ 2) - continuousDualHahn a b c (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * continuousDualHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) n (y ^ 2) := by
  have hp : ∀ (z : ℂ) (k : ℕ), 0 < z.re → poch (z + 1) k ≠ 0 := fun z k hz =>
    poch_ne_zero_of_re_pos (by simp; linarith) k
  have h0 : ∀ z : ℂ, 0 < z.re → z ≠ 0 := fun z hz h => by rw [h] at hz; simp at hz
  unfold continuousDualHahn
  have e1 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y + I / 2) ^ 2) =
      poch (a + I * y - 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    simpa using prod_sq_add_shift a y 1 k
  have e2 : ∀ k, ∏ j ∈ Finset.range k, ((a + j) ^ 2 + (y - I / 2) ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y - 1 / 2) k := fun k => by
    have := prod_sq_add_shift a y (-1) k
    simp only [neg_mul, one_mul, neg_div] at this
    rw [show y - I / 2 = y + -(I / 2) by ring, this]
    congr 2 <;> ring
  have e3 : ∀ k, ∏ j ∈ Finset.range k, ((a + 1 / 2 + j) ^ 2 + y ^ 2) =
      poch (a + I * y + 1 / 2) k * poch (a - I * y + 1 / 2) k := fun k => by
    have := prod_sq_add_shift (a + 1 / 2) y 0 k
    simp only [zero_mul, zero_div, add_zero, sub_zero] at this
    rw [this]; congr 2 <;> ring
  simp_rw [e1, e2, e3]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.sum_range_succ']
  simp only [poch_zero, mul_one, one_mul, Nat.factorial_zero, Nat.cast_one, div_one, sub_self,
    add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have key := poch_pair_sub (a + I * y) (a - I * y) k
  rw [← sub_div, ← mul_sub, key]
  rw [poch_succ_left (a + b), poch_succ_left (a + c),
    poch_succ_left (a + b) k, poch_succ_left (a + c) k,
    poch_succ_left (-((n + 1 : ℕ) : ℂ)), Nat.factorial_succ,
    show a + 1 / 2 + (b + 1 / 2) = a + b + 1 by ring, show a + 1 / 2 + (c + 1 / 2) = a + c + 1 by ring,
    show -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) by push_cast; ring]
  have := h0 _ hab; have := h0 _ hac
  have := hp _ k hab; have := hp _ k hac
  have hk : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hk1 : (k : ℂ) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
  push_cast
  field_simp
  ring

@[dlmf 18.26.E18]
theorem wilson_generating_function {a b c d : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (had : 0 < (a + d).re)
    (hbc : 0 < (b + c).re) (y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => wilson a b c d n (y ^ 2) / (poch (a + d) n * poch (b + c) n * n.factorial) * z ^ n)
      (₂F₁ (a + I * y) (d + I * y) (a + d) z * ₂F₁ (b - I * y) (c - I * y) (b + c) z) := by
  sorry

@[dlmf 18.26.E19]
theorem continuousDualHahn_generating_function {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (y : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => continuousDualHahn a b c n (y ^ 2) / (poch (a + b) n * n.factorial) * z ^ n)
      ((1 - z) ^ (-c + I * y) * ₂F₁ (a + I * y) (b + I * y) (a + b) z) := by
  sorry


end AAR.OrthogonalPolynomials
