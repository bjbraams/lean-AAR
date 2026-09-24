/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Hahn
public import AAR.OrthogonalPolynomials.Explicit
/-!
# Associated, Bessel, Pollaczek, Freud, and exceptional polynomials

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

/-- General associated family. The shift may be real, as in DLMF §18.30.
The `n = 0` step is written separately to avoid a negative natural index. -/
@[dlmf 18.30.E3]
def associated (A B C : ℝ → ℂ) (c : ℝ) : ℕ → ℂ → ℂ
  | 0, _ => 1
  | 1, x => A c * x + B c
  | n + 2, x => (A (n + 1 + c) * x + B (n + 1 + c)) * associated A B C c (n + 1) x -
      C (n + 1 + c) * associated A B C c n x

@[dlmf 18.30.E9]
def associatedLaguerre (lam : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => -(t + 1 : ℂ)⁻¹)
    (fun t => (2 * t + lam + 1) / (t + 1)) (fun t => (t + lam) / (t + 1)) c

@[dlmf 18.30.E13]
def associatedHermite (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun _ => 2) (fun _ => 0) (fun t => 2 * t) c

@[dlmf 18.30.E16]
def associatedMeixnerPollaczek (lam phi : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * sin phi / (t + 1))
    (fun t => 2 * (t + lam) * cos phi / (t + 1))
    (fun t => (t + 2 * lam - 1) / (t + 1)) c

@[dlmf 18.35.E2]
def pollaczek (lam a b : ℂ) (c : ℝ) : ℕ → ℂ → ℂ :=
  associated (fun t => 2 * (t + lam + a) / (t + 1))
    (fun t => 2 * b / (t + 1)) (fun t => (t + 2 * lam - 1) / (t + 1)) c

@[dlmf 18.34.E1]
def besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingHG n [-(n : ℂ), n + a - 1] [] (-x / 2)

/-- Polynomial form of the reversal, valid also at zero. -/
@[dlmf 18.34.E2]
def reverseBesselPolynomial (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), poch (-(n : ℂ)) k * poch (n + 1) k *
    (-1 / 2 : ℂ) ^ k * x ^ (n - k) / k.factorial

@[dlmf 18.32.E2]
def freudWeight (α : ℝ) (Q : ℝ → ℝ) (x : ℝ) : ℝ :=
  |x| ^ α * Real.exp (-Q x)

/-- Degree `n + 1`: exceptional Laguerre has no degree-zero member. -/
@[dlmf 18.36.E5]
def exceptionalLaguerre (k : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  -(x + k + 1) * laguerre k n x + if n = 0 then 0 else laguerre k (n - 1) x

@[dlmf 18.36.E3]
def exceptionalLaguerreWeight (k x : ℝ) : ℝ := x ^ k * Real.exp (-x) / (x + k) ^ 2

/-- The exceptional Hermite degrees are 0, 3, 4, …; the index type omits 1 and 2. -/
@[dlmf 18.36.E9]
def exceptionalHermite : Option ℕ → ℝ → ℝ
  | none, _ => (2 : ℝ) ^ (3 / 2 : ℝ) * Real.pi ^ (-1 / 4 : ℝ)
  | some n, x => ((4 * x ^ 2 + 2) * aeval x (hermitePhys (n + 1)) +
      8 * x * aeval x (hermitePhys n)) /
      (Real.pi ^ (1 / 4 : ℝ) * Real.sqrt (2 ^ (n + 1) * (n + 3) * n.factorial))

@[dlmf 18.30.E2]
theorem associated_zero (A B C : ℝ → ℂ) (c : ℝ) (x : ℂ) : associated A B C c 0 x = 1 := by
  rfl

@[dlmf 18.30.E19]
theorem associatedPollaczek_limit_laguerre (lam : ℂ) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun phi : ℝ => associatedMeixnerPollaczek ((lam + 1) / 2) phi c n (-x / (2 * sin (phi : ℂ))))
      (𝓝[>] 0) (𝓝 (associatedLaguerre lam c n x)) := by
  sorry

@[dlmf 18.30.E20]
theorem associatedPollaczek_limit_hermite {c : ℝ} (hc : 0 ≤ c) (n : ℕ) (x : ℂ) :
    Tendsto (fun lam : ℝ => poch (c + 1) n * (Real.sqrt lam : ℂ)⁻¹ ^ n *
      associatedMeixnerPollaczek lam (Real.pi / 2) c n (x * Real.sqrt lam)) atTop
      (𝓝 (associatedHermite c n x)) := by
  sorry

@[dlmf 18.34.E1]
theorem besselPolynomial_eq_laguerre (a : ℂ) (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    besselPolynomial a n x = (n.factorial : ℂ) * (-x / 2) ^ n * laguerreExtended (1 - a - 2 * n) n (2 / x) := by
  sorry

@[dlmf 18.34.E2]
theorem reverseBesselPolynomial_eq (n : ℕ) {x : ℂ} (hx : x ≠ 0) :
    reverseBesselPolynomial n x = x ^ n * besselPolynomial 2 n x⁻¹ := by
  unfold reverseBesselPolynomial besselPolynomial terminatingHG
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, div_one]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hp : x ^ n = x ^ (n - k) * x ^ k := by
    rw [← pow_add, Nat.sub_add_cancel hkn]
  rw [show (n : ℂ) + 2 - 1 = n + 1 by ring, hp]
  rw [show -x⁻¹ / 2 = (-1 / 2 : ℂ) * x⁻¹ by ring, mul_pow, inv_pow]
  field_simp

@[dlmf 18.34.E4]
theorem besselPolynomial_recurrence (a : ℂ) (n : ℕ) (x : ℂ) :
    2 * (n + a) * (2 * n + a) * besselPolynomial a (n + 2) x =
      ((2 * n + a + 2) * (2 * n + a + 1) * (2 * n + a) * x +
        2 * (a - 2) * (2 * n + a + 1)) * besselPolynomial a (n + 1) x +
      2 * (n + 1) * (2 * n + a + 2) * besselPolynomial a n x := by
  sorry

@[dlmf 18.34.E7]
theorem besselPolynomial_differential_equation (a : ℂ) (n : ℕ) (x : ℂ) :
    x ^ 2 * deriv (deriv (besselPolynomial a n)) x + (a * x + 2) * deriv (besselPolynomial a n) x -
      n * (n + a - 1) * besselPolynomial a n x = 0 := by
  sorry

@[dlmf 18.34.E5_5]
theorem besselPolynomial_finite_orthogonality {a : ℝ} (m n : ℕ) (ha : a < 1 - 2 * max m n) :
    (2 : ℂ) ^ (1 - (a : ℂ)) / Gamma (1 - (a : ℂ)) *
      (∫ x : ℝ in Set.Ioi 0, besselPolynomial a m x * besselPolynomial a n x *
        (Real.rpow x (a - 2) * Real.exp (-2 / x) : ℝ)) =
      if m = n then (1 - a) / (1 - a - 2 * (n : ℂ)) * n.factorial / poch (2 - a - n) n else 0 := by
  sorry

@[dlmf 18.34.E8]
theorem jacobi_limit_besselPolynomial (a : ℂ) (n : ℕ) (x : ℂ) :
    Tendsto (fun α : ℝ => jacobiP α (a - α - 2) n (1 + α * x) / jacobiP α (a - α - 2) n 1) atTop
      (𝓝 (besselPolynomial a n x)) := by
  sorry

@[dlmf 18.35.E2_5]
theorem pollaczek_reflection (lam a b : ℂ) (c : ℝ) (n : ℕ) (x : ℂ) :
    pollaczek lam a b c n (-x) = (-1 : ℂ) ^ n * pollaczek lam a (-b) c n x := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pollaczek, associated]
  | one => simp [pollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + a) / ((n + 1 + c : ℝ) + 1) * (-x) +
      2 * b / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c (n + 1) (-x) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam a b c n (-x) = _
    rw [ih0, ih1]
    simp only [pollaczek, associated, pow_succ]
    ring

@[dlmf 18.35.E4]
theorem pollaczek_finite_sum (lam a b : ℂ) (n : ℕ) {θ : ℂ} (hθ : sin θ ≠ 0) :
    pollaczek lam a b 0 n (cos θ) = ∑ k ∈ Finset.range (n + 1),
      poch (lam + I * (a * cos θ + b) / sin θ) k / k.factorial *
      (poch (lam - I * (a * cos θ + b) / sin θ) (n - k) / (n - k).factorial) *
      exp (I * ((n : ℂ) - 2 * k) * θ) := by
  sorry

@[dlmf 18.35.E7]
theorem pollaczek_generating_function (lam a b : ℂ) (θ : ℝ) (hθ : Real.sin θ ≠ 0) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => pollaczek lam a b 0 n (Real.cos θ) * z ^ n)
      ((1 - z * exp (I * θ)) ^ (-lam + I * (a * Real.cos θ + b) / Real.sin θ) *
       (1 - z * exp (-I * θ)) ^ (-lam - I * (a * Real.cos θ + b) / Real.sin θ)) := by
  sorry

@[dlmf 18.35.E8]
theorem pollaczek_eq_gegenbauer {lam : ℂ} (hlam : -1 / 2 < lam.re) (n : ℕ) (x : ℂ) :
    pollaczek lam 0 0 0 n x = gegenbauer lam n x := by
  sorry

@[dlmf 18.35.E9]
theorem pollaczek_eq_meixnerPollaczek {lam : ℂ} (hlam : 0 < lam.re) (phi x : ℂ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) 0 n (cos phi) = meixnerPollaczek lam phi n x := by
  sorry

@[dlmf 18.35.E10]
theorem pollaczek_eq_associatedMeixnerPollaczek (lam phi x : ℂ) (c : ℝ) (n : ℕ) :
    pollaczek lam 0 (x * sin phi) c n (cos phi) = associatedMeixnerPollaczek lam phi c n x := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => simp [pollaczek, associatedMeixnerPollaczek, associated]; ring
  | more n ih0 ih1 =>
    change (2 * ((n + 1 + c : ℝ) + lam + 0) / ((n + 1 + c : ℝ) + 1) * cos phi +
      2 * (x * sin phi) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c (n + 1) (cos phi) -
      (((n + 1 + c : ℝ) + 2 * lam - 1) / ((n + 1 + c : ℝ) + 1)) * pollaczek lam 0 (x * sin phi) c n (cos phi) = _
    rw [ih0, ih1]
    simp only [associatedMeixnerPollaczek, associated]
    ring

@[dlmf 18.36.E2]
theorem laguerre_negative_integer_parameter {n k : ℕ} (hk : k ≤ n) (x : ℂ) :
    laguerreExtended (-(k : ℂ)) n x = (-1 : ℂ) ^ k * (n - k).factorial / n.factorial * x ^ k * laguerre k (n - k) x := by
  sorry

@[dlmf 18.36.E6]
theorem exceptionalLaguerre_orthogonality {k : ℝ} (hk : 0 < k) (m n : ℕ) :
    ∫ x : ℝ in Set.Ioi 0, exceptionalLaguerre k m x * exceptionalLaguerre k n x * exceptionalLaguerreWeight k x =
      if m = n then (n + 1 + (k : ℂ)) * Gamma (n + (k : ℂ)) / n.factorial else 0 := by
  sorry

@[dlmf 18.36.E7]
theorem exceptionalLaguerre_differential_equation {k : ℝ} (hk : 0 < k) (n : ℕ) {x : ℂ} (hx : x + k ≠ 0) :
    -x * deriv (deriv (exceptionalLaguerre k n)) x + (x - k) / (x + k) *
      ((x + k + 1) * deriv (exceptionalLaguerre k n) x - exceptionalLaguerre k n x) =
      n * exceptionalLaguerre k n x := by
  sorry

@[dlmf 18.36.E10]
theorem exceptionalHermite_orthonormal (m n : Option ℕ) :
    ∫ x : ℝ, exceptionalHermite m x * exceptionalHermite n x *
      (Real.exp (-(x ^ 2)) / (4 * x ^ 2 + 2) ^ 2) = if m = n then 1 else 0 := by
  sorry


@[dlmf 18.35.E3]
def pollaczekTau (a b θ : ℝ) : ℝ := (a * Real.cos θ + b) / Real.sin θ

/-- Angular density, including the Jacobian `sin θ` for `x = cos θ`. -/
@[dlmf 18.35.E6]
def pollaczekAngularWeight (lam a b θ : ℝ) : ℝ :=
  Real.pi⁻¹ * Real.exp ((2 * θ - Real.pi) * pollaczekTau a b θ) *
    (2 * Real.sin θ) ^ (2 * lam - 1) * ‖Gamma (lam + I * pollaczekTau a b θ)‖ ^ 2 * Real.sin θ

@[dlmf 18.35.E5]
theorem pollaczek_orthogonality {lam a b : ℝ} (hlam : 0 < lam) (hab : |b| ≤ a) (m n : ℕ) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, pollaczek lam a b 0 m (Real.cos θ) *
      pollaczek lam a b 0 n (Real.cos θ) * pollaczekAngularWeight lam a b θ =
      if m = n then Gamma (2 * (lam : ℂ) + n) / (n.factorial * (lam + a + n)) else 0 := by
  sorry

/-- The finite family related to the Morse differential equation. -/
@[dlmf 18.34.E7_1]
def morsePolynomialFunction (lam : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  Real.exp (-lam * Real.exp (-x)) * (2 * lam * Real.exp (-x) : ℂ) ^ (lam - 1 / 2 : ℂ) *
    besselPolynomial (2 - 2 * lam) n (lam⁻¹ * Real.exp x) / n.factorial

@[dlmf 18.34.E7_2]
theorem morsePolynomialFunction_ode {lam : ℝ} (hlam : 0 < lam) (n : ℕ) (x : ℝ) :
    deriv (deriv (morsePolynomialFunction lam n)) x -
      (lam ^ 2 * (Real.exp (-2 * x) - 2 * Real.exp (-x)) + (lam - (n + 1 / 2)) ^ 2 : ℝ) *
        morsePolynomialFunction lam n x = 0 := by
  sorry

@[dlmf 18.34.E7_3]
theorem morsePolynomialFunction_orthogonality {lam : ℝ} (m n : ℕ) (hm : (m : ℝ) < lam - 1 / 2) (hn : (n : ℝ) < lam - 1 / 2) :
    ∫ x : ℝ, morsePolynomialFunction lam m x * morsePolynomialFunction lam n x =
      if m = n then Gamma (2 * (lam : ℂ) - n) / ((2 * lam - 2 * n - 1) * n.factorial) else 0 := by
  sorry


end AAR.OrthogonalPolynomials
