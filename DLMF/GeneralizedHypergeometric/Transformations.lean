/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.GeneralizedHypergeometric.Basic
public import DLMF.Hypergeometric.Clausen

/-!
# Transformations, expansions, and products: DLMF §§16.6,16.10,16.12

Variable transformations use the component containing zero of the simultaneous
principal domains. This retains analytic continuation without equating unrelated
branches on disconnected preimages of cuts. The Fields–Wimp expansion has an
unrestricted formal coefficient identity and a precise analytic statement under
absolute convergence of its expanded double series; DLMF does not print a sharper
convergence region. All terminating auxiliary functions are finite retained sums.
-/

@[expose] public section
open Complex Filter Set Finset
open scoped Topology Real
noncomputable section
namespace DLMF.Hypergeometric

/-- Simultaneous principal domain for the quadratic variable transformation. -/
def genQuadraticDomain : Set ℂ := connectedComponentIn
  {z : ℂ | z ∈ cutPlane ∧ 1 - z ∈ Complex.slitPlane ∧ -4 * z / (1 - z) ^ 2 ∈ cutPlane} 0

/-- Simultaneous principal domain for the cubic variable transformation. -/
def genCubicDomain : Set ℂ := connectedComponentIn
  {z : ℂ | z / 4 ∈ cutPlane ∧ 1 - z ∈ Complex.slitPlane ∧
    -27 * z / (4 * (1 - z) ^ 3) ∈ cutPlane} 0

/-- Fields–Wimp prefactor with the power of z removed. -/
def genFieldsWimpCoeff (a b : Multiset ℂ) (α β γ : ℂ) (k : ℕ) : ℂ :=
  genPoch a k * poch α k * poch β k * (-1 : ℂ) ^ k /
    (genPoch b k * poch (γ + k) k * k.factorial)

/-- The kth Fields–Wimp summand, including its terminating auxiliary polynomial. -/
def genFieldsWimpTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (k : ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ k * z ^ k *
    genHG ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
      ((γ + 2 * k + 1) ::ₘ genShift b k) z *
    genFiniteHG k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- The expanded two-index Fields–Wimp term used for its convergence condition. -/
def genFieldsWimpDoubleTerm (a b c d : Multiset ℂ) (α β γ z ζ : ℂ) (kn : ℕ × ℕ) : ℂ :=
  genFieldsWimpCoeff a b α β γ kn.1 * z ^ kn.1 *
    genCoeff ((α + kn.1) ::ₘ (β + kn.1) ::ₘ genShift a kn.1)
      ((γ + 2 * kn.1 + 1) ::ₘ genShift b kn.1) kn.2 * z ^ kn.2 *
    genFiniteHG kn.1 ((-kn.1 : ℂ) ::ₘ (γ + kn.1) ::ₘ c) (α ::ₘ β ::ₘ d) ζ

/-- Quadratic transformation on the full common principal component. -/
@[dlmf 16.6.E1]
theorem genHG_quadratic_transformation (a b c : ℂ) (hb : genDenRegular {a - b + 1, a - c + 1})
    {z : ℂ} (hz : z ∈ genQuadraticDomain) :
    genHG {a, b, c} {a - b + 1, a - c + 1} z = (1 - z) ^ (-a) *
      genHG {a - b - c + 1, a / 2, (a + 1) / 2}
        {a - b + 1, a - c + 1} (-4 * z / (1 - z) ^ 2) := by
  sorry

/-- Cubic transformation on the full common principal component. -/
@[dlmf 16.6.E2]
theorem genHG_cubic_transformation (a b : ℂ) (hb : genDenRegular {b, a - b + 3 / 2})
    {z : ℂ} (hz : z ∈ genCubicDomain) :
    genHG {a, 2 * b - a - 1, 2 - 2 * b + a} {b, a - b + 3 / 2} (z / 4) =
      (1 - z) ^ (-a) * genHG {a / 3, a / 3 + 1 / 3, a / 3 + 2 / 3}
        {b, a - b + 3 / 2} (-27 * z / (4 * (1 - z) ^ 3)) := by
  sorry

/-- The formal coefficient identity has no analytic convergence restriction. -/
@[dlmf 16.10.E1]
theorem genHG_fields_wimp_coeff (a b c d : Multiset ℂ) (α β γ ζ : ℂ)
    (hb : genDenRegular (b + d)) (hαβ : genDenRegular {α, β})
    (hγ : ∀ k : ℕ, poch (γ + k) k ≠ 0 ∧ genDenRegular {γ + 2 * k + 1}) (N : ℕ) :
    genCoeff (a + c) (b + d) N * ζ ^ N =
      ∑ k ∈ range (N + 1), genFieldsWimpCoeff a b α β γ k *
        genCoeff ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
          ((γ + 2 * k + 1) ::ₘ genShift b k) (N - k) *
        genFiniteHG k ((-k : ℂ) ::ₘ (γ + k) ::ₘ c) (α ::ₘ β ::ₘ d) ζ := by
  sorry

/-- The analytic expansion under explicit absolute double-series convergence and valid original germs. -/
@[dlmf 16.10.E1]
theorem genHG_fields_wimp_hasSum (a b c d : Multiset ℂ) (α β γ z ζ : ℂ)
    (hb : genDenRegular (b + d)) (hαβ : genDenRegular {α, β})
    (hγ : ∀ k : ℕ, poch (γ + k) k ≠ 0 ∧ genDenRegular {γ + 2 * k + 1})
    (hleft : HasSum (fun n => genCoeff (a + c) (b + d) n * (z * ζ) ^ n)
      (genHG (a + c) (b + d) (z * ζ)))
    (hinner : ∀ k : ℕ, HasSum (fun n =>
        genCoeff ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
          ((γ + 2 * k + 1) ::ₘ genShift b k) n * z ^ n)
      (genHG ((α + k) ::ₘ (β + k) ::ₘ genShift a k)
        ((γ + 2 * k + 1) ::ₘ genShift b k) z))
    (habs : Summable (fun kn : ℕ × ℕ => ‖genFieldsWimpDoubleTerm a b c d α β γ z ζ kn‖)) :
    HasSum (genFieldsWimpTerm a b c d α β γ z ζ) (genHG (a + c) (b + d) (z * ζ)) := by
  sorry

/-- Norlund expansion with the full printed convergence half-plane and zeta disk. -/
@[dlmf 16.10.E2]
theorem genHG_norlund_expansion (a : ℂ) (A B : Multiset ℂ) (hcard : A.card = B.card) (hb : genDenRegular B)
    {z ζ : ℂ} (hζ : ‖ζ - 1‖ < 1) (hz : z.re < 1 / 2) :
    HasSum (fun k : ℕ => (1 - z) ^ (-a) * poch a k / k.factorial *
      genFiniteHG k ((-k : ℂ) ::ₘ A) B ζ * (z / (z - 1)) ^ k)
      (genHG (a ::ₘ A) B (z * ζ)) := by
  sorry

/-- The product of two 0F1 functions for every complex z. -/
@[dlmf 16.12.E1]
theorem genHG_0F1_product (a b z : ℂ) (hb : genDenRegular {a, b, a + b - 1}) :
    genHG ∅ {a} z * genHG ∅ {b} z =
      genHG {(a + b) / 2, (a + b - 1) / 2} {a, b, a + b - 1} (4 * z) := by
  sorry

/-- The existing Clausen germ identity continued to its whole principal slit. -/
@[dlmf 16.12.E2]
theorem genHG_clausen_principal (a b : ℂ) (hb : genDenRegular {a + b + 1 / 2, 2 * a + 2 * b})
    {z : ℂ} (hz : z ∈ cutPlane) :
    genHG {a, b} {a + b + 1 / 2} z ^ 2 =
      genHG {2 * a, 2 * b, a + b} {a + b + 1 / 2, 2 * a + 2 * b} z := by
  sorry

/-- The full generalized square series; terminating inner sums preserve lower exceptions after termination. -/
@[dlmf 16.12.E3]
theorem genHG_general_square_hasSum (a b c : ℂ) (hb : genDenRegular {c, 2 * c - 1, a + 1 / 2, b + 1 / 2})
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ => poch (2 * a) k * poch (2 * b) k * poch (c - 1 / 2) k /
      (poch c k * poch (2 * c - 1) k * k.factorial) *
      genFiniteHG k {-(k : ℂ) / 2, (1 - (k : ℂ)) / 2, a + b - c + 1 / 2, 1 / 2}
        {a + 1 / 2, b + 1 / 2, 3 / 2 - (k : ℂ) - c} 1 * z ^ k) (genHG {a, b} {c} z ^ 2) := by
  sorry

end DLMF.Hypergeometric
