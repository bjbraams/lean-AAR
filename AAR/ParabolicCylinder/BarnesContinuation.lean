/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Integrals

/-!
# Cylinder Barnes integrals with crossed-pole corrections

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Residue at the right-pole family t=(A+n)/2; the minus one half Jacobian is retained. -/
def pcfBarnesResidue (second : Bool) (a z : ℂ) (n : ℕ) : ℂ :=
  let A:=if second then 1/2-a else a+1/2; let r:=(A+n)/2; (-1)^(n+1)/(2*(n.factorial:ℂ))*Gamma r*2^r*z^(A+n)*(if second then cos (π*r) else 1)

/-- The finite set of right-family poles crossed by replacing a separating contour with the vertical line Re t=c. -/
def pcfBarnesResidueSum (second : Bool) (a z : ℂ) (c : ℝ) : ℂ :=
  let A:=if second then 1/2-a else a+1/2; ∑ n ∈ Finset.range ((⌈2*c-A.re⌉:ℤ).toNat), pcfBarnesResidue second a z n

/-- All regular parameters: crossed residues encode the deformed separating contour instead of strengthening the real-part hypothesis. -/
@[dlmf 12.5.E8]
theorem pcfU_barnes_continued {a z : ℂ} (ha : ∀ n : ℕ, 1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < 3*π/4) {c : ℝ} (hc : 0 < c) (havoid : ∀ n : ℕ, 2*c ≠ 1/2+1*a.re+n) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+1*a-2*t)*2^t*z^(2*t)*1) (2*π*(Gamma (1/2+1*a)*(exp (z^2/4)*z^(a+1/2))*pcfU a z+pcfBarnesResidueSum false a z c)) := by
  sorry

/-- All regular parameters: crossed residues encode the deformed separating contour instead of strengthening the real-part hypothesis. -/
@[dlmf 12.5.E9]
theorem pcfV_barnes_continued {a z : ℂ} (ha : ∀ n : ℕ, -1*a ≠ -n-1/2) (hz0 : z ≠ 0) (hz : |arg z| < π/4) {c : ℝ} (hc : 0 < c) (havoid : ∀ n : ℕ, 2*c ≠ 1/2+-1*a.re+n) :
    HasIntegralWholeLine (fun y : ℝ => let t : ℂ := c+y*I; Gamma t*Gamma (1/2+-1*a-2*t)*2^t*z^(2*t)*cos (π*t)) (2*π*(Gamma (1/2+-1*a)*((Real.sqrt (π/2):ℂ)*exp (-z^2/4)*z^(-a+1/2))*pcfV a z+pcfBarnesResidueSum true a z c)) := by
  sorry

end AAR.Confluent
