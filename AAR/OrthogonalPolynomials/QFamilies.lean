/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Topics
public import Mathlib.Tactic.CrossRefAttribute
public import AAR.OrthogonalPolynomials.Wilson
public import AAR.QSeries.Identities
/-!
# The q-Hahn and Askey–Wilson classes

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

/-- Terminating basic hypergeometric sum with the standard integer exponent
`1 + s - r`; in particular this handles both ₁phi₁ and balanced ₄phi₃. -/
def terminatingBasicHG (n : ℕ) (a b : List ℂ) (q z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1),
    (a.map (fun t => qPochhammer t q k)).prod /
      ((b.map (fun t => qPochhammer t q k)).prod * qPochhammer q q k) *
      ((-1 : ℂ) ^ k * q ^ (k * (k - 1) / 2)) ^ (1 + (b.length : ℤ) - a.length) * z ^ k

@[dlmf 18.27.E3]
def qHahn (a b q : ℂ) (N n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, q⁻¹ ^ N] q q

@[dlmf 18.27.E5]
def bigQJacobi (a b c q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1), x] [a * q, c * q] q q

@[dlmf 18.27.E13]
def littleQJacobi (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * q ^ (n + 1)] [a * q] q (q * x)

@[dlmf 18.27.E14_5]
def littleQLaguerre (a q : ℂ) (n : ℕ) (x : ℂ) : ℂ := littleQJacobi a 0 q n x

@[dlmf 18.27.E15]
def qLaguerre (α q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer (q ^ (α + 1)) q n / qPochhammer q q n *
    terminatingBasicHG n [q⁻¹ ^ n] [q ^ (α + 1)] q (-x * q ^ (n + α + 1))

@[dlmf 18.27.E18]
def stieltjesWigert (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ (k ^ 2) * (-x) ^ k /
    (qPochhammer q q k * qPochhammer q q (n - k))

@[dlmf 18.27.E21]
def discreteQHermiteI (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q ^ (k * (k - 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

@[dlmf 18.27.E23]
def discreteQHermiteII (q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  qPochhammer q q n * ∑ k ∈ Finset.range (n / 2 + 1),
    (-1 : ℂ) ^ k * q⁻¹ ^ (2 * n * k) * q ^ (k * (2 * k + 1)) * x ^ (n - 2 * k) /
      (qPochhammer (q ^ 2) (q ^ 2) k * qPochhammer q q (n - 2 * k))

/-- Finite polynomial form. The displayed formula requires `a ≠ 0`; claims below
retain that hypothesis rather than assigning continuation values at `a = 0`. -/
@[dlmf 18.28.E1]
def askeyWilson (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  a⁻¹ ^ n * ∑ k ∈ Finset.range (n + 1), q ^ k *
    qPochhammer (a * b * q ^ k) q (n - k) * qPochhammer (a * c * q ^ k) q (n - k) *
    qPochhammer (a * d * q ^ k) q (n - k) * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * c * d * q ^ ((n : ℤ) - 1)) q k / qPochhammer q q k *
    ∏ j ∈ Finset.range k, (1 - 2 * a * q ^ j * x + a ^ 2 * q ^ (2 * j))

@[dlmf 18.28.E1_5]
def askeyWilsonLaurent (a b c d q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  terminatingBasicHG n [q⁻¹ ^ n, a * b * c * d * q ^ ((n : ℤ) - 1), a * z, a / z]
    [a * b, a * c, a * d] q q

@[dlmf 18.28.E7]
def alSalamChihara (a b q : ℂ) (n : ℕ) (x : ℂ) : ℂ := askeyWilson a b 0 0 q n x

/-- Laurent argument `z`, representing the polynomial argument `(z + z⁻¹)/2`. -/
@[dlmf 18.28.E16]
def continuousQHermiteLaurent (q : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  qPochhammer q q n * qGegenbauer 0 q n z

@[dlmf 18.28.E19]
def qRacah (a b c d q : ℂ) (n : ℕ) (x : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), q ^ k * qPochhammer (q⁻¹ ^ n) q k *
    qPochhammer (a * b * q ^ (n + 1)) q k /
      (qPochhammer (a * q) q k * qPochhammer (b * d * q) q k *
        qPochhammer (c * q) q k * qPochhammer q q k) *
      ∏ j ∈ Finset.range k, (1 - q ^ j * x + c * d * q ^ (2 * j + 1))

@[dlmf 18.27.E4]
theorem qHahn_orthogonal {a b q : ℝ} (hq : 0 < q) (hq1 : q < 1) (ha : 0 < a)
    (haq : a * q < 1) (hb : 0 < b) (hbq : b * q < 1) {N m n : ℕ}
    (hm : m ≤ N) (hn : n ≤ N) (hmn : m ≠ n) :
    ∑ y ∈ Finset.range (N + 1), qHahn a b q N m ((q : ℂ)⁻¹ ^ y) *
      qHahn a b q N n ((q : ℂ)⁻¹ ^ y) * qPochhammer q q N /
        (qPochhammer q q y * qPochhammer q q (N - y)) *
      qPochhammer (a * q) q y * qPochhammer (b * q) q (N - y) / ((a * q : ℂ) ^ y) = 0 := by
  sorry

@[dlmf 18.27.E14]
theorem littleQJacobi_orthogonal {a b q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha : 0 < a) (haq : a * q < 1) (hb : b * q < 1) {m n : ℕ} (hmn : m ≠ n) :
    HasSum (fun y : ℕ => littleQJacobi a b q m ((q : ℂ) ^ y) *
      littleQJacobi a b q n ((q : ℂ) ^ y) * qPochhammer (b * q) q y *
      ((a * q : ℂ) ^ y) / qPochhammer q q y) 0 := by
  sorry

@[dlmf 18.27.E16]
theorem qLaguerre_orthogonal {α q : ℝ} (hα : -1 < α) (hq : 0 < q) (hq1 : q < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi 0, qLaguerre α q m x * qLaguerre α q n x *
      (Real.rpow x α : ℂ) / qPochhammerInf (-x) q = 0 := by
  sorry

@[dlmf 18.27.E20]
theorem stieltjesWigert_orthogonal {q : ℝ} (hq : 0 < q) (hq1 : q < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ x : ℝ in Set.Ioi 0, stieltjesWigert q m (Real.sqrt q * x) *
      stieltjesWigert q n (Real.sqrt q * x) *
      Real.exp (-(Real.log x) ^ 2 / (2 * Real.log q⁻¹)) = 0 := by
  sorry

@[dlmf 18.28.E1_5]
theorem askeyWilson_laurent_representation {a b c d q : ℂ} (ha : a ≠ 0) (hq : q ≠ 0)
    (hq1 : ‖q‖ < 1) (hab : ‖a * b‖ < 1) (hac : ‖a * c‖ < 1) (had : ‖a * d‖ < 1) (n : ℕ) {z : ℂ} (hz : z ≠ 0) :
    askeyWilson a b c d q n ((z + z⁻¹) / 2) = a⁻¹ ^ n * qPochhammer (a * b) q n *
      qPochhammer (a * c) q n * qPochhammer (a * d) q n * askeyWilsonLaurent a b c d q n z := by
  sorry

@[dlmf 18.28.E2]
theorem askeyWilson_orthogonal {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, askeyWilson a b c d q m (Real.cos θ) *
      askeyWilson a b c d q n (Real.cos θ) *
      (‖qPochhammerInf (exp (2 * I * θ)) q /
        (qPochhammerInf (a * exp (I * θ)) q * qPochhammerInf (b * exp (I * θ)) q *
         qPochhammerInf (c * exp (I * θ)) q * qPochhammerInf (d * exp (I * θ)) q)‖ ^ 2 : ℝ) = 0 := by
  sorry

@[dlmf 18.28.E15]
theorem qGegenbauer_orthogonal {β q : ℝ} (hq : 0 < q) (hq1 : q < 1) (hβ : |β| < 1) {m n : ℕ} (hmn : m ≠ n) :
    ∫ θ : ℝ in (0 : ℝ)..Real.pi, qGegenbauer β q m (exp (I * θ)) * qGegenbauer β q n (exp (I * θ)) *
      (‖qPochhammerInf (exp (2 * I * θ)) q / qPochhammerInf (β * exp (2 * I * θ)) q‖ ^ 2 : ℝ) = 0 := by
  sorry

@[dlmf 18.28.E17]
theorem continuousQHermite_orthogonality {q : ℝ} (hq : 0 < q) (hq1 : q < 1) (m n : ℕ) :
    (∫ θ : ℝ in (0 : ℝ)..Real.pi, continuousQHermiteLaurent q m (exp (I * θ)) *
      continuousQHermiteLaurent q n (exp (I * θ)) *
      (‖qPochhammerInf (exp (2 * I * θ)) q‖ ^ 2 : ℝ)) / (2 * Real.pi) =
      if m = n then (qPochhammerInf ((q : ℂ) ^ (n + 1)) q)⁻¹ else 0 := by
  sorry

@[dlmf 18.28.E23]
theorem qRacah_duality {a b c d q : ℂ} (hq : q ≠ 0) (hq1 : ‖q‖ < 1) (n y : ℕ) :
    qRacah a b c d q n (q⁻¹ ^ y + c * d * q ^ (y + 1)) =
      qRacah c d a b q y (q⁻¹ ^ n + a * b * q ^ (n + 1)) := by
  sorry

@[dlmf 18.27.E4_2]
theorem qHahn_limit_hahn {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) {N n : ℕ} (hn : n ≤ N) (x : ℝ) :
    Tendsto (fun q : ℝ => qHahn (Real.rpow q α) (Real.rpow q β) q N n (Real.rpow q (-x))) (𝓝[<] 1) (𝓝 (hahn α β N n x)) := by
  sorry

@[dlmf 18.27.E14_4]
theorem littleQJacobi_limit_jacobi {α β : ℝ} (hα : -1 < α) (hβ : -1 < β) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQJacobi (Real.rpow q α) (Real.rpow q β) q n x) (𝓝[<] 1) (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * jacobiP α β n (1 - 2 * x))) := by
  sorry

@[dlmf 18.27.E14_6]
theorem littleQLaguerre_limit_laguerre {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => littleQLaguerre (Real.rpow q α) q n ((1 - q : ℂ) * x)) (𝓝[<] 1) (𝓝 ((n.factorial : ℂ) / poch (α + 1) n * laguerre α n x)) := by
  sorry

@[dlmf 18.27.E17_3]
theorem qLaguerre_limit_laguerre {α : ℝ} (hα : -1 < α) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => qLaguerre α q n ((1 - q : ℂ) * x)) (𝓝[<] 1) (𝓝 (laguerre α n x)) := by
  sorry

@[dlmf 18.28.E29]
theorem askeyWilson_limit_wilson {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => askeyWilson (Real.rpow q a) (Real.rpow q b) (Real.rpow q c) (Real.rpow q d) q n (1 - x * (1 - q : ℂ) ^ 2 / 2) / (1 - q : ℂ) ^ (3 * n)) (𝓝[<] 1) (𝓝 (wilson a b c d n x)) := by
  sorry

@[dlmf 18.28.E31]
theorem qGegenbauer_limit_gegenbauer {lam : ℝ} (hlam : -1 / 2 < lam) (n : ℕ) (θ : ℝ) :
    Tendsto (fun q : ℝ => qGegenbauer (Real.rpow q lam) q n (exp (I * θ))) (𝓝[<] 1) (𝓝 (gegenbauer lam n (Real.cos θ))) := by
  sorry


@[dlmf 18.27.E25]
theorem discreteQHermiteI_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteI q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePhys n))) := by
  sorry


@[dlmf 18.27.E26]
theorem discreteQHermiteII_limit_hermite (n : ℕ) (x : ℂ) :
    Tendsto (fun q : ℝ => discreteQHermiteII q n ((Real.sqrt (1 - q ^ 2) : ℂ) * x) /
      (Real.sqrt (1 - q ^ 2) : ℂ) ^ n) (𝓝[<] 1) (𝓝 ((2 : ℂ)⁻¹ ^ n * aeval x (hermitePhys n))) := by
  sorry


/-- The coefficient in the Askey–Wilson q-difference operator. -/
@[dlmf 18.28.E6_2]
def askeyWilsonDifferenceCoefficient (a b c d q z : ℂ) : ℂ :=
  (1 - a * z) * (1 - b * z) * (1 - c * z) * (1 - d * z) / ((1 - z ^ 2) * (1 - q * z ^ 2))

@[dlmf 18.28.E6_1]
theorem askeyWilson_difference_equation {a b c d q : ℂ} (hq0 : q ≠ 0) (hq : ‖q‖ < 1)
    (hab : ‖a * b‖ < 1) (hac : ‖a * c‖ < 1) (had : ‖a * d‖ < 1) (n : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : z ^ 2 ≠ 1) (hzq : q * z ^ 2 ≠ 1) (hzqi : q * z⁻¹ ^ 2 ≠ 1) :
    askeyWilsonDifferenceCoefficient a b c d q z *
      (askeyWilsonLaurent a b c d q n (q * z) - askeyWilsonLaurent a b c d q n z) +
    askeyWilsonDifferenceCoefficient a b c d q z⁻¹ *
      (askeyWilsonLaurent a b c d q n (z / q) - askeyWilsonLaurent a b c d q n z) =
    (q⁻¹ ^ n - 1) * (1 - a * b * c * d * q ^ ((n : ℤ) - 1)) * askeyWilsonLaurent a b c d q n z := by
  sorry

/-- Leading asymptotic coefficient; its argument is on the unit circle. -/
@[dlmf 18.29.E2]
def askeyWilsonAsymptoticCoefficient (a b c d q z : ℂ) : ℂ :=
  qPochhammerInf (a / z) q * qPochhammerInf (b / z) q *
    qPochhammerInf (c / z) q * qPochhammerInf (d / z) q / qPochhammerInf (z⁻¹ ^ 2) q

@[dlmf 18.29.E1]
theorem askeyWilson_asymptotic {a b c d q : ℝ} (hq : 0 < q) (hq1 : q < 1)
    (ha0 : a ≠ 0) (ha : |a| < 1) (hb : |b| < 1) (hc : |c| < 1) (hd : |d| < 1)
    {θ : ℝ} (hθ : 0 < θ) (hθπ : θ < Real.pi) :
    Tendsto (fun n : ℕ => askeyWilson a b c d q n (Real.cos θ) -
      (exp (I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (I * θ)) +
       exp (-I * n * θ) * askeyWilsonAsymptoticCoefficient a b c d q (exp (-I * θ)))) atTop (𝓝 0) := by
  sorry


end AAR.OrthogonalPolynomials
