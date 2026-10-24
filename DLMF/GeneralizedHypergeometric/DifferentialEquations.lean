/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.AnalyticProperties
public import DLMF.GeneralizedHypergeometric.Derivatives
public import ToMathlib.Analysis.ODE.Singularities
public import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# Differential equations and confluence: DLMF §16.8

The existing proved theta equation is reused and extended to principal continuation.
Stirling numbers convert theta polynomials to ordinary derivative coefficients.
Singularities are classified by their coefficient germs: removable parameter
specializations are allowed, and q=0 is not falsely declared singular at zero.
Fundamental systems include resonant logarithmic Frobenius series. Connection
formulas retain correlated logarithm sheets; an arbitrary displaced center uses
the common connected principal component rather than unrelated cut determinations.
-/

@[expose] public section
open Complex Filter Set Finset Polynomial
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- Normalized scalar ODE value (16.8.1). -/
@[dlmf 16.8.E1]
def genNormalizedODE {n : ℕ} (c : Fin n → ℂ → ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.linearODEValue c f z

/-- Differentiation operator; theta itself is the existing `eulerTheta` (16.8.2). -/
@[dlmf 16.8.E2]
def genD (f : ℂ → ℂ) : ℂ → ℂ := deriv f

/-- Upper-parameter theta polynomial. -/
def genThetaA (a : Multiset ℂ) : Polynomial ℂ := (a.map fun x => X + C x).prod

/-- Lower-parameter theta polynomial. -/
def genThetaB (b : Multiset ℂ) : Polynomial ℂ := X * (b.map fun x => X + C (x - 1)).prod

/-- Ordinary derivative coefficient of a theta polynomial, with the power of z removed. -/
def genThetaDCoeff (P : Polynomial ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ range (P.natDegree + 1), P.coeff k * (Nat.stirlingSecond k j : ℂ)

/-- The alpha constants in the expanded equation. -/
def genODEAlpha (a : Multiset ℂ) (j : ℕ) : ℂ := -genThetaDCoeff (genThetaA a) j

/-- The beta constants in the expanded equation. -/
def genODEBeta (b : Multiset ℂ) (j : ℕ) : ℂ := genThetaDCoeff (genThetaB b) j

/-- Nominal order of the full generalized hypergeometric operator. -/
def genODEOrder (a b : Multiset ℂ) : ℕ := max a.card (b.card + 1)

/-- Normalized derivative coefficients of the generalized hypergeometric operator. -/
def genODECoeff (a b : Multiset ℂ) (j : Fin (genODEOrder a b)) (z : ℂ) : ℂ :=
  (genThetaDCoeff (genThetaB b) j.val * z ^ j.val -
    genThetaDCoeff (genThetaA a) j.val * z ^ (j.val + 1)) /
  (genThetaDCoeff (genThetaB b) (genODEOrder a b) * z ^ genODEOrder a b -
    genThetaDCoeff (genThetaA a) (genODEOrder a b) * z ^ (genODEOrder a b + 1))

/-- Vanishing of the generalized hypergeometric theta operator. -/
def genODESolution (a b : Multiset ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  thetaPoly (genThetaB b) f z = z * thetaPoly (genThetaA a) f z

/-- A fundamental system on an open domain, expressed by independence and full span. -/
def genFundamentalSystem {n : ℕ} (a b : Multiset ℂ) (D : Set ℂ)
    (F : Fin n → ℂ → ℂ) : Prop :=
  (∀ i, AnalyticOnNhd ℂ (F i) D ∧ ∀ z ∈ D, genODESolution a b (F i) z) ∧
  LinearIndependent ℂ (fun i => fun z : D => F i z) ∧
  ∀ f : ℂ → ℂ, AnalyticOnNhd ℂ f D → (∀ z ∈ D, genODESolution a b f z) →
    ∃ c : Fin n → ℂ, ∀ z ∈ D, f z = ∑ i, c i * F i z

/-- The common principal zero-to-one slit domain for Frobenius solutions at zero. -/
def genFrobeniusDomain : Set ℂ := Complex.slitPlane ∩ cutPlane

/-- The q+1 Frobenius exponents at zero. -/
def genFrobeniusRoot {q : ℕ} (b : Fin q → ℂ) : Fin (q + 1) → ℂ :=
  Fin.cases 0 (fun j => 1 - b j)

/-- The nonresonant Frobenius solutions at zero (16.8.6). -/
@[dlmf 16.8.E6]
def genFrobeniusZero {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ)
    (i : Fin (q + 1)) (z : ℂ) : ℂ := by
  classical
  exact Fin.cases (genHG (genParams a) (genParams b) z)
    (fun j => z ^ (1 - b j) *
      genHG (genShift (genParams a) (1 - b j))
        ((2 - b j) ::ₘ genShift ((genParams b).erase (b j)) (1 - b j)) z) i

/-- A closed log(-z) sheet: the upper edge corresponds to the lower z-cut value. -/
def genHGNegativeLog (a b : Multiset ℂ) (w : ℂ) : ℂ := by
  classical
  exact if w.im = Real.pi then genHGLower a b (-Complex.exp w)
    else genHG a b (-Complex.exp w)

/-- The nonresonant infinity solutions with an explicit log(-z) sheet (16.8.7). -/
@[dlmf 16.8.E7]
def genFrobeniusInfinityLog {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) (w : ℂ) : ℂ := by
  classical
  exact Complex.exp (-a j * w) *
    genHGNegativeLog ((a j) ::ₘ genShift (genParams b) (1 + a j))
      (genShift ((genParams a).erase (a j)) (1 + a j)) (-w)

/-- Connection coefficient to the jth infinity solution. -/
def genInfinityConnectionCoeff {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (j : Fin (q + 1)) : ℂ :=
  (∏ k ∈ univ.erase j, Gamma (a k - a j)) * genGamma (genParams b) /
    ((∏ k ∈ univ.erase j, Gamma (a k)) * genGamma (genShift (genParams b) (-a j)))

/-- Principal component for the displaced-center infinity expansion. -/
def genCenteredInfinityDomain (z₀ : ℂ) : Set ℂ :=
  let R := max ‖z₀‖ ‖z₀ - 1‖
  connectedComponentIn {z : ℂ | R < ‖z - z₀‖ ∧ z₀ - z ∈ Complex.slitPlane ∧ z ∈ cutPlane}
    (z₀ - (R + 1))

/-- The nth inner coefficient of the displaced-center expansion, regularized before
multiplication to preserve the shifted exceptional lower parameters. -/
def genCenteredInfinityTerm {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (z₀ z : ℂ) (j : Fin (q + 1)) (n : ℕ) : ℂ :=
  Gamma (a j + n) / n.factorial * (∏ k ∈ univ.erase j, Gamma (a k - a j - n)) *
    (∑ k ∈ range (n + 1),
      Complex.regularizedHGFunCoeff (genShift (genParams a) (-a j - n))
        (genShift (genParams b) (-a j - n)) k * z₀ ^ k) * (z - z₀) ^ (-(n : ℤ))

/-- The proved theta equation continued throughout the ordinary principal analytic domain. -/
@[dlmf 16.8.E3]
theorem genHG_theta_ode (a b : Multiset ℂ) (hb : genDenRegular b)
    (h : a.card ≤ b.card + 1 ∨ genTerminates a) {z : ℂ} (hz : z ∈ genAnalyticDomain a b) :
    genODESolution a b (genHG a b) z := by
  sorry

/-- The full expanded equation for p≤q with the explicit alpha and beta constants. -/
@[dlmf 16.8.E4]
theorem genHG_expanded_ode_entire (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    z ^ b.card * iteratedDeriv (b.card + 1) (genHG a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j (genHG a b) z) +
      genODEAlpha a 0 * genHG a b z = 0 := by
  sorry

/-- The full expanded equation for p=q+1. -/
@[dlmf 16.8.E5]
theorem genHG_expanded_ode_balanced (a b : Multiset ℂ) (h : a.card = b.card + 1) (hb : genDenRegular b)
    {z : ℂ} (hz : z ∈ cutPlane) :
    z ^ b.card * (1 - z) * iteratedDeriv (b.card + 1) (genHG a b) z +
      (∑ j ∈ Finset.Icc 1 b.card, z ^ (j - 1) *
        (genODEAlpha a j * z + genODEBeta b j) * iteratedDeriv j (genHG a b) z) +
      genODEAlpha a 0 * genHG a b z = 0 := by
  sorry

/-- Zero is at most regular, infinity is irregular, and there are no other singularities for p≤q. -/
theorem genHG_ode_singularities_entire (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) :
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.linearODEIrregularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → Complex.linearODEOrdinaryAt (genODECoeff a b) z := by
  sorry

/-- Zero, one and infinity are at most regular; removable parameter degeneracies are retained. -/
theorem genHG_ode_singularities_balanced (a b : Multiset ℂ) (h : a.card = b.card + 1) (hb : genDenRegular b) :
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 0 ∧
    Complex.linearODEAtMostRegularAt (genODECoeff a b) 1 ∧
    Complex.linearODEAtMostRegularAtInfinity (genODECoeff a b) ∧
    ∀ z : ℂ, z ≠ 0 → z ≠ 1 → Complex.linearODEOrdinaryAt (genODECoeff a b) z := by
  sorry

/-- The nominal operator order is max(p,q+1), independently of lower-order equations for special solutions. -/
theorem genHG_ode_nominal_order (a b : Multiset ℂ) :
    max (genThetaA a).natDegree (genThetaB b).natDegree = genODEOrder a b := by
  sorry

/-- The full nonresonant fundamental system at zero. -/
@[dlmf 16.8.E6]
theorem genFrobeniusZero_fundamental {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p ≤ q + 1)
    (hb : ∀ j, ∀ n : ℤ, b j ≠ n)
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, b i - b j ≠ n) :
    genFundamentalSystem (genParams a) (genParams b) genFrobeniusDomain (genFrobeniusZero a b) := by
  sorry

/-- All resonant cases admit logarithmic Frobenius series, with analytic power series and logs through order q. -/
theorem genFrobeniusZero_resonant {p q : ℕ} (a : Fin p → ℂ) (b : Fin q → ℂ) (hpq : p ≤ q + 1)
    (hb : genDenRegular (genParams b)) :
    ∃ r : ℝ, 0 < r ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      genFundamentalSystem (genParams a) (genParams b)
        (Complex.slitPlane ∩ Metric.ball 0 r) F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 r)) ∧
        ∀ i z, z ∈ Complex.slitPlane ∩ Metric.ball 0 r →
          F i z = ∑ j, ∑ k, z ^ genFrobeniusRoot b j *
            Complex.log z ^ k.val * A i j k z := by
  sorry

/-- The nonresonant infinity solutions form a fundamental system in their principal exterior domain. -/
@[dlmf 16.8.E7]
theorem genFrobeniusInfinity_fundamental {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n) :
    genFundamentalSystem (genParams a) (genParams b)
      {z : ℂ | 1 < ‖z‖ ∧ -z ∈ Complex.slitPlane}
      (fun j z => genFrobeniusInfinityLog a b j (Complex.log (-z))) := by
  sorry

/-- The connection formula on both correlated closed log(-z) cut sides. -/
@[dlmf 16.8.E8]
theorem genHG_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    {w : ℂ} (hw : |w.im| ≤ Real.pi) (hz : -Complex.exp w ≠ 1) :
    genHGNegativeLog (genParams a) (genParams b) w =
      ∑ j, genInfinityConnectionCoeff a b j * genFrobeniusInfinityLog a b j w := by
  sorry

/-- The convergent displaced-center expansion with correlated principal branches and all regularized finite inner polynomials. -/
@[dlmf 16.8.E9]
theorem genHG_centered_infinity_connection {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (ha : genDenRegular (genParams a)) (hb : genDenRegular (genParams b))
    (hdiff : ∀ i j, i ≠ j → ∀ n : ℤ, a i - a j ≠ n)
    (z₀ : ℂ) {z : ℂ} (hz : z ∈ genCenteredInfinityDomain z₀) :
    ∃ v : Fin (q + 1) → ℂ,
      (∀ j, HasSum (genCenteredInfinityTerm a b z₀ z j) (v j)) ∧
      genGamma (genParams a) * genRegularizedHG (genParams a) (genParams b) z =
        ∑ j, (z₀ - z) ^ (-a j) * v j := by
  sorry

/-- Upper-parameter confluence along every complex direction to infinity. -/
@[dlmf 16.8.E10]
theorem genHG_upper_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card) (hb : genDenRegular b) (z : ℂ) :
    Tendsto (fun α : ℂ => genHG (α ::ₘ a) b (z / α)) (Bornology.cobounded ℂ)
      (𝓝 (genHG a b z)) := by
  sorry

/-- Lower-parameter confluence with the full angle-dependent z restriction from the source. -/
@[dlmf 16.8.E11]
theorem genHG_lower_confluence (a b : Multiset ℂ) (h : a.card ≤ b.card + 1) (hb : genDenRegular b)
    (z : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ ≤ Real.pi) :
    Tendsto (fun β : ℂ => genHG a (β ::ₘ b) (β * z))
      (comap norm atTop ⊓ 𝓟 {β : ℂ | β ≠ 0 ∧ |β.arg| ≤ Real.pi - δ ∧
        (a.card ≤ b.card ∨ (|β.arg| ≤ Real.pi / 2 ∧ ‖z‖ < 1) ∨
          (Real.pi / 2 ≤ |β.arg| ∧ ‖z‖ < |Real.sin β.arg|))})
      (𝓝 (genHG a b z)) := by
  sorry

/-- Resonant infinity exponents admit a fundamental system with power series in 1/z
and logarithms of degree at most q, without integer-difference exclusions. -/
theorem genFrobeniusInfinity_resonant {q : ℕ} (a : Fin (q + 1) → ℂ) (b : Fin q → ℂ)
    (hb : genDenRegular (genParams b)) :
    ∃ R : ℝ, 1 < R ∧ ∃ F : Fin (q + 1) → ℂ → ℂ,
      genFundamentalSystem (genParams a) (genParams b)
        {z : ℂ | R < ‖z‖ ∧ -z ∈ Complex.slitPlane} F ∧
      ∃ A : Fin (q + 1) → Fin (q + 1) → Fin (q + 1) → ℂ → ℂ,
        (∀ i j k, AnalyticOnNhd ℂ (A i j k) (Metric.ball 0 (1 / R))) ∧
        ∀ i z, R < ‖z‖ → -z ∈ Complex.slitPlane →
          F i z = ∑ j, ∑ k, (-z) ^ (-a j) *
            Complex.log (-z) ^ k.val * A i j k z⁻¹ := by
  sorry

end DLMF.Hypergeometric
