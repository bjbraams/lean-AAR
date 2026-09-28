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

@[dlmf 18.26.E5]
theorem wilson_limit_continuousDualHahn {a b c : ℂ} (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (x : ℂ) :
    Tendsto (fun d : ℝ => wilson a b c d n x / poch (a + d) n) atTop (𝓝 (continuousDualHahn a b c n x)) := by
  sorry

@[dlmf 18.26.E9]
theorem racah_limit_dualHahn {γ δ : ℂ} (hγ : -1 < γ.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun b : ℝ => racah (-(N : ℂ) - 1) b γ δ n x) atTop (𝓝 (dualHahn γ δ N n x)) := by
  sorry

@[dlmf 18.26.E10]
theorem racah_limit_hahn {α β : ℂ} (hα : -1 < α.re) {N n : ℕ} (hn : n ≤ N) (x : ℂ) :
    Tendsto (fun d : ℝ => racah α β (-(N : ℂ) - 1) d n (x * (x - N + d))) atTop (𝓝 (hahn α β N n x)) := by
  sorry

@[dlmf 18.26.E14]
theorem wilson_central_difference {a b c d : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (had : 0 < (a + d).re) (n : ℕ) (y : ℂ) :
    wilson a b c d (n + 1) ((y + I / 2) ^ 2) - wilson a b c d (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * (n + a + b + c + d) *
        wilson (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) (d + 1 / 2) n (y ^ 2) := by
  sorry

@[dlmf 18.26.E15]
theorem continuousDualHahn_central_difference {a b c : ℂ}
    (hab : 0 < (a + b).re) (hac : 0 < (a + c).re) (n : ℕ) (y : ℂ) :
    continuousDualHahn a b c (n + 1) ((y + I / 2) ^ 2) - continuousDualHahn a b c (n + 1) ((y - I / 2) ^ 2) =
      -2 * I * y * (n + 1) * continuousDualHahn (a + 1 / 2) (b + 1 / 2) (c + 1 / 2) n (y ^ 2) := by
  sorry

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
