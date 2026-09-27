/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.OrthogonalPolynomials.Classical
public import AAR.SphericalHarmonics.Basic
public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Addition theorems, Funk–Hecke, Poisson, and `SU(2)` (AAR §§9.6–9.16)

Mathlib has the Poisson kernel of the *disk* (`poissonKernel`) and `Matrix.specialUnitaryGroup`,
but not the spherical addition theorem, Funk–Hecke, or the identification of Jacobi polynomials
with matrix coefficients of `SU(2)`.
-/

@[expose] public section

open Complex Matrix MeasureTheory intervalIntegral
open scoped Real

noncomputable section

/-- AAR Theorem 9.6.3, (9.6.6), p. 456, specialized to three dimensions:
`(2k+1)/(4π) P_k(x·y) = ∑_m S_m(x) S_m(y)` for an orthonormal family of `2k+1`
real spherical harmonics of degree `k`. The inner product uses surface measure as in
(9.4.4), p. 452. -/
theorem spherical_addition {k : ℕ}
    (S : Fin (2 * k + 1) → MvPolynomial (Fin 3) ℝ)
    (hS : ∀ m, IsHarmonicHomogeneous k (S m))
    (horth : ∀ i j, sphericalHarmonicInner (S i) (S j) = if i = j then 1 else 0)
    (x y : Fin 3 → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) (hy : ∑ i, y i ^ 2 = 1) :
    (2 * k + 1 : ℂ) / (4 * π) * legendreP k (∑ i, x i * y i : ℝ) =
      ∑ m : Fin (2 * k + 1),
        (MvPolynomial.eval x (S m) : ℂ) * (MvPolynomial.eval y (S m) : ℂ) := by
  sorry

/-- Funk–Hecke formula (AAR Theorem 9.7.1), in three dimensions. -/
theorem funk_hecke {k : ℕ} {f : ℝ → ℂ}
    (hf : ContinuousOn f (Set.Icc (-1) 1))
    (S : MvPolynomial (Fin 3) ℝ) (hS : IsHarmonicHomogeneous k S)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      f (∑ i, x.val i * y.val i) * (MvPolynomial.eval (fun i => y.val i) S : ℂ)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) =
      (2 * π : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, f t * legendreP k t) *
        (MvPolynomial.eval (fun i => x.val i) S : ℂ) := by
  sorry

/-- Gegenbauer addition theorem, AAR (9.8.5'), for `λ > 1/2`. -/
theorem gegenbauer_addition {lam : ℝ} (hlam : 1 / 2 < lam)
    (n : ℕ) (theta phi psi : ℝ) :
    gegenbauer lam n
        (Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi * Real.cos psi) =
      ∑ j ∈ Finset.range (n + 1),
        (Gamma (2 * lam - 1) * 4 ^ j * (n - j).factorial *
          Gamma (j + (lam : ℂ)) ^ 2 * (2 * j + 2 * (lam : ℂ) - 1) /
            (Gamma (lam : ℂ) ^ 2 * Gamma (j + n + 2 * (lam : ℂ)))) *
        (Real.sin theta : ℂ) ^ j * gegenbauer (j + (lam : ℂ)) (n - j) (Real.cos theta) *
        (Real.sin phi : ℂ) ^ j * gegenbauer (j + (lam : ℂ)) (n - j) (Real.cos phi) *
        gegenbauer ((lam : ℂ) - 1 / 2) j (Real.cos psi) := by
  sorry

/-- Poisson kernel of the unit ball in `ℝⁿ` (AAR §9.9), before division by sphere area.
In the supplied printing, (9.9.2) and Theorem 9.9.1 put an extra `cos` around the
Euclidean inner product. The denominator intended there is `1 - 2r(α·η) + r²`. -/
def poissonKernelBall {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (1 - ∑ i, x i ^ 2) / (∑ i, (x i - y i) ^ 2) ^ (n / 2 : ℝ)

/-- Poisson representation of a harmonic function continuous on the closed unit ball. -/
theorem poissonKernelBall_reproduces {n : ℕ} (hn : 2 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f (Metric.ball 0 1))
    (hcont : ContinuousOn f (Metric.closedBall 0 1))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1) :
    (∫ y : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      poissonKernelBall (fun i => x i) (fun i => y.val i) * f y.val
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere) =
      ((volume : Measure (EuclideanSpace ℝ (Fin n))).toSphere.real Set.univ) * f x := by
  sorry

/-- Special unitary group `SU(2)`. -/
abbrev SU2 := specialUnitaryGroup (Fin 2) ℂ

/-! The Jacobi-polynomial interpretation as matrix coefficients of irreducible
`SU(2)` representations (AAR §9.14) remains to be formulated using a representation
and a specified basis. The former reflexive placeholder has been removed: it
provided no representation-theoretic content. -/

/-- The double cover `SU(2) → SO(3)` (AAR §9.16). -/
theorem su2_covers_so3 :
    ∃ Φ : SU2 →* specialOrthogonalGroup (Fin 3) ℝ, Function.Surjective Φ ∧
      (∀ g, Φ g = 1 ↔ g = 1 ∨ g.1 = (-1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  sorry
