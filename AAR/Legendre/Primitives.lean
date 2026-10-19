/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Integrals

/-!
# Indefinite Ferrers integrals as derivative identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Select either Ferrers solution in the source primitive formulas. -/
def ferrersSolution (second : Bool) (ν μ : ℂ) (x : ℝ) : ℂ :=
  if second then ferrersQ ν μ x else ferrersP ν μ x

/-- ferrers primitive 1. -/
@[dlmf 14.17.E1]
theorem ferrers_primitive_1 (second : Bool) (ν μ : ℂ) (hr : second=true → ∀ k ∈ Finset.Icc (-1:ℤ) 1, LegendreQRegular ν (μ+k))  {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun x : ℝ => -(1-x^2:ℂ)^(-(μ-1)/2)*ferrersSolution second ν (μ-1) x) ((1-x^2:ℂ)^(-μ/2)*ferrersSolution second ν μ x) x := by
  sorry

/-- ferrers primitive 2. -/
@[dlmf 14.17.E2]
theorem ferrers_primitive_2 (second : Bool) (ν μ : ℂ) (hr : second=true → ∀ k ∈ Finset.Icc (-1:ℤ) 1, LegendreQRegular ν (μ+k)) (h0 : μ ≠ ν) (h1 : μ ≠ -ν-1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (fun x : ℝ => (1-x^2:ℂ)^((μ+1)/2)/((ν-μ)*(ν+μ+1))*ferrersSolution second ν (μ+1) x) ((1-x^2:ℂ)^(μ/2)*ferrersSolution second ν μ x) x := by
  sorry

/-- ferrersProductPrimitive. -/
@[dlmf 14.17.E3, dlmf 14.17.E4]
def ferrersProductPrimitive (singular : Bool) (F G : ℂ → ℂ → ℝ → ℂ) (ν μ : ℂ) (x : ℝ) : ℂ :=
  if singular then ((1-2*μ^2+2*ν*(ν+1))*F ν μ x*G ν μ x+(2*ν+1)*(μ-ν-1)*x*(F ν μ x*G (ν+1) μ x+F (ν+1) μ x*G ν μ x)+2*(μ-ν-1)^2*F (ν+1) μ x*G (ν+1) μ x)/((1-4*μ^2)*(1-x^2:ℂ)^(1/2:ℂ)) else ((μ^2-(ν+1)*(ν+x^2))*F ν μ x*G ν μ x+(ν+1)*(ν-μ+1)*x*(F ν μ x*G (ν+1) μ x+F (ν+1) μ x*G ν μ x)-(ν-μ+1)^2*F (ν+1) μ x*G (ν+1) μ x)/(2*ν*(ν+1))

/-- ferrers product primitive 3. -/
@[dlmf 14.17.E3]
theorem ferrers_product_primitive_3 (second₁ second₂ : Bool) (ν μ : ℂ) (hr : (second₁=true ∨ second₂=true) → LegendreQRegular ν μ) (hν0 : ν ≠ 0) (hν1 : ν ≠ -1) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersProductPrimitive false (ferrersSolution second₁) (ferrersSolution second₂) ν μ) (x*ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x) x := by
  sorry

/-- ferrers product primitive 4. -/
@[dlmf 14.17.E4]
theorem ferrers_product_primitive_4 (second₁ second₂ : Bool) (ν μ : ℂ) (hr : (second₁=true ∨ second₂=true) → LegendreQRegular ν μ) (hμ : μ ≠ 1/2) (hmμ : μ ≠ -1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (ferrersProductPrimitive true (ferrersSolution second₁) (ferrersSolution second₂) ν μ) (x/(1-x^2:ℂ)^(3/2:ℂ)*ferrersSolution second₁ ν μ x*ferrersSolution second₂ ν μ x) x := by
  sorry

end AAR.Legendre
