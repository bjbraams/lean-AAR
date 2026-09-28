/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.DiffEq
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma

/-!
# Local solutions and Wronskians (DLMF §15.10)

The ordinary solution and its ODE are already in `DiffEq`. The functions here
are local solutions, not globally continued functions. Swapping `a,b` supplies
the second solution at infinity. Wronskians plus the ODE give fundamental pairs
when the Wronskians are nonzero. The integral-parameter logarithmic pairs are
stated with explicit nonvanishing Wronskians, including empty finite sums.
The four zero/one connection formulas hold on the overlap of their series disks.
See `Kummer` for the other Kummer representations.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

/-- The Gauss differential operator, without division at its singular points. -/
@[dlmf 15.10.E1]
def gaussOperator (a b c : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (1 - z) * iteratedDeriv 2 f z + (c - (a + b + 1) * z) * deriv f z - a * b * f z

/-- Wronskian of two scalar functions, with the order used in DLMF. -/
def solutionWronskian (f g : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * deriv g z - deriv f z * g z

/-- The second solution at zero. The first is Mathlib's `ordinaryHypergeometric`. -/
@[dlmf 15.10.E2]
def zeroSecond (a b c z : ℂ) : ℂ := z ^ (1 - c) * ₂F₁ (a - c + 1) (b - c + 1) (2 - c) z

@[dlmf 15.10.E4]
def oneFirst (a b c z : ℂ) : ℂ := ₂F₁ a b (a + b - c + 1) (1 - z)

@[dlmf 15.10.E4]
def oneSecond (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (c - a - b) * ₂F₁ (c - a) (c - b) (c - a - b + 1) (1 - z)

/-- Interchanging `a,b` gives the second solution at infinity. -/
@[dlmf 15.10.E6]
def infinityFirst (a b c z : ℂ) : ℂ := z ^ (-a) * ₂F₁ a (a - c + 1) (a - b + 1) (1 / z)

@[dlmf 15.10.E2]
theorem zero_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (zeroSecond a b c) z = 0 := by
  sorry

/-- The coefficient recurrence also gives the equation at the regular point zero. -/
private lemma gaussOperator_hg {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ)) (hz : ‖z‖ < 1) :
    gaussOperator a b c (₂F₁ a b c) z = 0 := by
  have h := (hasFPowerSeriesOnBall_ordinaryHypergeometric a b c).ode_of_recurrence
    (A := 1) (B := a + b + 1) (C := a * b) (D := c) (fun n => ?_)
    (mem_eball_one_of_norm_lt_one hz)
  · simpa [gaussOperator, iteratedDeriv_succ, iteratedDeriv_zero] using h
  · rw [gaussHGCoeff_recurrence hc]
    ring

@[dlmf 15.10.E4]
theorem one_first_ode {a b c z : ℂ} (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ)) (hz : ‖1 - z‖ < 1) :
    gaussOperator a b c (oneFirst a b c) z = 0 := by
  have he : oneFirst a b c = (fun w => ₂F₁ a b (a + b - c + 1) (1 - w)) := by
    funext w
    rw [oneFirst]
  have hd : deriv (oneFirst a b c) z = -deriv (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 1)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa [iteratedDeriv_one] using h
  have hdd : iteratedDeriv 2 (oneFirst a b c) z =
      iteratedDeriv 2 (₂F₁ a b (a + b - c + 1)) (1 - z) := by
    have h := congrFun (iteratedDeriv_comp_const_sub (n := 2)
      (f := (₂F₁ a b (a + b - c + 1) : ℂ → ℂ)) (s := 1)) z
    rw [he]
    simpa using h
  have h := gaussOperator_hg (a := a) (b := b) hc hz
  rw [gaussOperator, hd, hdd, oneFirst]
  unfold gaussOperator at h
  linear_combination h

@[dlmf 15.10.E4]
theorem one_second_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    gaussOperator a b c (oneSecond a b c) z = 0 := by
  sorry

@[dlmf 15.10.E6]
theorem infinity_first_ode
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hs : z ∈ slitPlane) :
    gaussOperator a b c (infinityFirst a b c) z = 0 := by
  sorry

@[dlmf 15.10.E3]
theorem zero_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    solutionWronskian (₂F₁ a b c) (zeroSecond a b c) z = (1 - c) * z ^ (-c) * (1 - z) ^ (c - a - b - 1) := by
  sorry

@[dlmf 15.10.E5]
theorem one_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane) :
    solutionWronskian (oneFirst a b c) (oneSecond a b c) z = (a + b - c) * z ^ (-c) * (1 - z) ^ (c - a - b -
      1) := by
  sorry

@[dlmf 15.10.E7]
theorem infinity_wronskian
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hd : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < z.re) :
    solutionWronskian (infinityFirst a b c) (infinityFirst b a c) z = (a - b) * z ^ (-c) * (z - 1) ^ (c - a
      - b - 1) := by
  sorry

/-- The logarithmic second solution for a positive integral denominator (generic numerators). -/
@[dlmf 15.10.E8]
def logarithmicSecond (a b : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ a b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (1 - a) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    ∑' k : ℕ, gaussHGCoeff a b n k * z ^ k *
      (digamma (a + k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))

/-- The logarithmic second solution with one terminating numerator. -/
@[dlmf 15.10.E9]
def logarithmicSecondTerminating (b : ℂ) (m n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) b (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (1 - b) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (m + 1), gaussHGCoeff (-m) b n k * z ^ k *
      (digamma (1 + m - k) + digamma (b + k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ m * (m.factorial : ℂ) * ∑' j : ℕ,
      (j.factorial : ℂ) * poch b (m + 1 + j) /
        (poch n (m + 1 + j) * ((m + 1 + j).factorial : ℂ)) * z ^ (m + 1 + j)

/-- The logarithmic second solution with two terminating numerators. -/
@[dlmf 15.10.E10]
def logarithmicSecondBothTerminating (m l n : ℕ) (z : ℂ) : ℂ :=
  ₂F₁ (-m : ℂ) (-l) (n : ℂ) z * log z -
    (∑ j ∈ Finset.range (n - 1),
      ((n - 1).factorial : ℂ) * (j.factorial : ℂ) /
        (((n - j - 2).factorial : ℂ) * poch (m + 1) (j + 1) * poch (l + 1) (j + 1)) * ((-z)⁻¹) ^ (j + 1)) +
    (∑ k ∈ Finset.range (l + 1), gaussHGCoeff (-m) (-l) n k * z ^ k *
      (digamma (1 + m - k) + digamma (1 + l - k) - digamma (1 + k) - digamma (n + k))) +
    (-1 : ℂ) ^ l * (l.factorial : ℂ) * ∑ j ∈ Finset.range (m - l),
      (j.factorial : ℂ) * poch (-m) (l + 1 + j) /
        (poch n (l + 1 + j) * ((l + 1 + j).factorial : ℂ)) * z ^ (l + 1 + j)

@[dlmf 15.10.E8]
theorem logarithmic_second_fundamental
    {a b : ℂ}
    (n : ℕ)
    (hn : 0 < n)
    (ha : ∀ k : ℤ, a ≠
    (k : ℂ))
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator a b n (logarithmicSecond a b n) z = 0 ∧
      solutionWronskian (₂F₁ a b (n : ℂ)) (logarithmicSecond a b n) z ≠ 0 := by
  sorry

@[dlmf 15.10.E9]
theorem logarithmic_second_terminating_fundamental
    {b : ℂ}
    (m n : ℕ)
    (hn : 0 < n)
    (hb : ∀ k : ℤ, b ≠
    (k : ℂ))
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) b n (logarithmicSecondTerminating b m n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) b (n : ℂ)) (logarithmicSecondTerminating b m n) z ≠ 0 := by
  sorry

@[dlmf 15.10.E10]
theorem logarithmic_second_both_terminating_fundamental
    (m l n : ℕ)
    (hn : 0 < n)
    (hl : l ≤ m)
    {z : ℂ}
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane) :
    gaussOperator (-m) (-l) n (logarithmicSecondBothTerminating m l n) z = 0 ∧
      solutionWronskian (₂F₁ (-m : ℂ) (-l : ℂ) (n : ℂ)) (logarithmicSecondBothTerminating m l n) z ≠ 0 := by
  sorry

@[dlmf 15.10.E17]
theorem one_first_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneFirst a b c z =
      Gamma (1 - c) * Gamma (a + b - c + 1) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * ₂F₁ a b c z + Gamma
        (c - 1) * Gamma (a + b - c + 1) / (Gamma a * Gamma b) * zeroSecond a b c z := by
  sorry

@[dlmf 15.10.E18]
theorem one_second_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    oneSecond a b c z =
      Gamma (1 - c) * Gamma (c - a - b + 1) / (Gamma (1 - a) * Gamma (1 - b)) * ₂F₁ a b c z + Gamma (c - 1)
        * Gamma (c - a - b + 1) / (Gamma (c - a) * Gamma (c - b)) * zeroSecond a b c z := by
  sorry

@[dlmf 15.10.E21]
theorem zero_first_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    ₂F₁ a b c z =
      Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b)) * oneFirst a b c z + Gamma c * Gamma (a
        + b - c) / (Gamma a * Gamma b) * oneSecond a b c z := by
  sorry

@[dlmf 15.10.E22]
theorem zero_second_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hz : ‖z‖ < 1) (hw : ‖1 - z‖ < 1) :
    zeroSecond a b c z =
      Gamma (2 - c) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (1 - b)) * oneFirst a b c z + Gamma (2 - c)
        * Gamma (a + b - c) / (Gamma (a - c + 1) * Gamma (b - c + 1)) * oneSecond a b c z := by
  sorry

end AAR.Hypergeometric
