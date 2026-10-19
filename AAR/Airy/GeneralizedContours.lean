/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Scorer

/-!
# Reid generalized Airy contours, DLMF §9.13(ii)

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The integrand on the logarithmic t plane; the contour arguments lie in [0,2π]. -/
def reidKernel (z p w : ℂ) : ℂ := exp (-p * w + z * exp w - exp (3 * w) / 3)
/-- A ray integral of the lifted Reid kernel, starting at radius r. -/
def reidRay (z p : ℂ) (θ r : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi r, exp (θ * I) * reidKernel z p (log t + θ * I)
/-- A unit-circle arc of the lifted kernel. -/
def reidArc (z p : ℂ) (α β : ℝ) : ℂ :=
  ∫ θ : ℝ in α..β, I * exp (θ * I) * reidKernel z p (θ * I)
/-- A Reid contour from infinity to infinity, with its prescribed orientation. -/
def reidContour (z p : ℂ) (α β : ℝ) : ℂ := -reidRay z p α 1 + reidArc z p α β + reidRay z p β 1
/-- Reid's A1,A2,A3 on L1,L2,L3 of Figure 9.13.1. -/
@[dlmf 9.13.E25]
def reidAiryA (k : Fin 3) (z p : ℂ) : ℂ :=
  (match k.val with
    | 0 => reidContour z p (4 * π / 3) (2 * π / 3)
    | 1 => reidContour z p (2 * π) (4 * π / 3)
    | _ => reidContour z p (2 * π / 3) 0) / (2 * π * I)
/-- The positively oriented closed contour L0, for integral p. -/
@[dlmf 9.13.E26]
def reidAiryB0 (z : ℂ) (p : ℤ) : ℂ := reidArc z p 0 (2 * π) / (2 * π * I)
/-- Coefficients of exp(zt-t³/3), used to specify the finite part at t=0. -/
def reidTaylorCoeff (z : ℂ) (j : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (j / 3 + 1), (-1 / 3 : ℂ) ^ k * z ^ (j - 3 * k) / (k.factorial * (j - 3 * k).factorial)
/-- The ordinary ray integral when p≤0; for p>0 the explicitly subtracted Hadamard
finite part, with the inherited logarithm at the lower endpoint. The printed positive-p
integrals in 9.13.27 do not converge as ordinary integrals. -/
def reidAiryB (k : Fin 3) (z : ℂ) (p : ℤ) : ℂ :=
  let θ : ℝ := 2 * k.val * π / 3
  if p ≤ 0 then reidRay z p θ 0 else
    let n := p.toNat
    reidRay z p θ 1 +
      (∫ t : ℝ in 0..1, exp (θ * I) * ((t : ℂ) * exp (θ * I)) ^ (-(p : ℂ)) *
        (exp (z * ((t : ℂ) * exp (θ * I)) - ((t : ℂ) * exp (θ * I)) ^ 3 / 3) -
          ∑ j ∈ Finset.range n, reidTaylorCoeff z j * ((t : ℂ) * exp (θ * I)) ^ j)) +
      (∑ j ∈ Finset.range (n - 1), reidTaylorCoeff z j * exp (θ * I * ((j : ℂ) + 1 - p)) /
        ((j : ℂ) + 1 - p)) + θ * I * reidTaylorCoeff z (n - 1)

/-- Ordinary convergence range of the printed ray integrals (DLMF 9.13.27). -/
@[dlmf 9.13.E27]
theorem reidAiryB_ordinary_ray (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    reidAiryB k z p = reidRay z p (2 * k.val * π / 3) 0 := by
  simp only [reidAiryB, hp, ↓reduceIte]

/-- reidAiryA zero parameter (DLMF 9.13.28). -/
@[dlmf 9.13.E28]
theorem reidAiryA_zero_parameter (z : ℂ) :
    reidAiryA 0 z 0 = airyAi z := by
  sorry

/-- reidAiryA zero rotations (DLMF 9.13.29). -/
@[dlmf 9.13.E29]
theorem reidAiryA_zero_rotations (z : ℂ) :
    reidAiryA 1 z 0 = exp (2 * π * I / 3) * airyAi (z * exp (2 * π * I / 3)) ∧
      reidAiryA 2 z 0 = exp (-2 * π * I / 3) * airyAi (z * exp (-2 * π * I / 3)) := by
  sorry

/-- reidAiryB zero parameter (DLMF 9.13.30). -/
@[dlmf 9.13.E30]
theorem reidAiryB_zero_parameter (z : ℂ) :
    reidAiryB0 z 0 = 0 ∧ reidAiryB 0 z 0 = π * scorerHi z := by
  sorry

/-- reidAiryA ode (DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryA_ode (k : Fin 3) (z p : ℂ) :
    iteratedDeriv 3 (fun t => reidAiryA k t p) z - z * deriv (fun t => reidAiryA k t p) z + (p - 1) * reidAiryA k z p = 0 := by
  sorry

/-- reidAiryB ode (DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryB_ode (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    iteratedDeriv 3 (fun t => reidAiryB k t p) z - z * deriv (fun t => reidAiryB k t p) z + ((p : ℂ) - 1) * reidAiryB k z p = 0 := by
  sorry

/-- reidAiryB0 ode (DLMF 9.13.31). -/
@[dlmf 9.13.E31]
theorem reidAiryB0_ode (z : ℂ) (p : ℤ) :
    iteratedDeriv 3 (fun t => reidAiryB0 t p) z - z * deriv (fun t => reidAiryB0 t p) z + ((p : ℂ) - 1) * reidAiryB0 z p = 0 := by
  sorry

/-- reidAiryA difference (DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryA_difference (k : Fin 3) (z p : ℂ) :
    reidAiryA k z (p - 3) - z * reidAiryA k z (p - 1) + (p - 1) * reidAiryA k z p = 0 := by
  sorry

/-- reidAiryB difference (DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryB_difference (k : Fin 3) (z : ℂ) {p : ℤ} (hp : p ≤ 0) :
    reidAiryB k z (p - 3) - z * reidAiryB k z (p - 1) + ((p : ℂ) - 1) * reidAiryB k z p = 0 := by
  sorry

/-- reidAiryB0 difference (DLMF 9.13.32). -/
@[dlmf 9.13.E32]
theorem reidAiryB0_difference (z : ℂ) (p : ℤ) :
    reidAiryB0 z (p - 3) - z * reidAiryB0 z (p - 1) + ((p : ℂ) - 1) * reidAiryB0 z p = 0 := by
  sorry

/-- reidAiryA rotations (DLMF 9.13.33). -/
@[dlmf 9.13.E33]
theorem reidAiryA_rotations (z p : ℂ) :
    reidAiryA 1 z p = exp (-2 * (p - 1) * π * I / 3) * reidAiryA 0 (z * exp (2 * π * I / 3)) p ∧
      reidAiryA 2 z p = exp (2 * (p - 1) * π * I / 3) * reidAiryA 0 (z * exp (-2 * π * I / 3)) p := by
  sorry

/-- reidAiry connection sum (DLMF 9.13.34). -/
@[dlmf 9.13.E34]
theorem reidAiry_connection_sum (z : ℂ) (p : ℤ) :
    reidAiryA 0 z p + reidAiryA 1 z p + reidAiryA 2 z p + reidAiryB0 z p = 0 := by
  sorry

/-- reidAiry connection 35 (DLMF 9.13.35). -/
@[dlmf 9.13.E35]
theorem reidAiry_connection_35 (z : ℂ) (p : ℤ) :
    reidAiryB 1 z p - reidAiryB 2 z p = 2 * π * I * reidAiryA 0 z p := by
  sorry

/-- reidAiry connection 36 (DLMF 9.13.36). -/
@[dlmf 9.13.E36]
theorem reidAiry_connection_36 (z : ℂ) (p : ℤ) :
    reidAiryB 2 z p - reidAiryB 0 z p = 2 * π * I * reidAiryA 1 z p := by
  sorry

/-- reidAiry connection 37 (DLMF 9.13.37). -/
@[dlmf 9.13.E37]
theorem reidAiry_connection_37 (z : ℂ) (p : ℤ) :
    reidAiryB 0 z p - reidAiryB 1 z p = 2 * π * I * reidAiryA 2 z p := by
  sorry

/-- Positive-p finite-part correction: the lower endpoint contributes a polynomial forcing. -/
theorem reidAiryB_finitePart_ode (k : Fin 3) (z : ℂ) {p : ℤ} (hp : 1 ≤ p) :
    iteratedDeriv 3 (fun t => reidAiryB k t p) z - z * deriv (fun t => reidAiryB k t p) z +
      ((p : ℂ) - 1) * reidAiryB k z p = reidTaylorCoeff z (p.toNat - 1) := by
  sorry

end AAR.Airy
