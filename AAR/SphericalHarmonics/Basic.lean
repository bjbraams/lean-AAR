/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Tactic.IntervalCases

/-!
# Harmonic polynomials (AAR §§9.1–9.5)

Mathlib has harmonic *functions* (`InnerProductSpace.HarmonicAt`) and the Laplacian, but
not the finite-dimensional spaces of homogeneous harmonic polynomials (spherical harmonics).
-/

@[expose] public section

open MvPolynomial
open scoped BigOperators

noncomputable section

namespace AAR.SphericalHarmonics

/-- Laplacian on multivariate polynomials. -/
def laplacianMv {n : ℕ} (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i : Fin n, pderiv i (pderiv i p)

/-- Homogeneous harmonic polynomials of degree `k` in `n` variables. -/
def IsHarmonicHomogeneous {n : ℕ} (k : ℕ) (p : MvPolynomial (Fin n) ℝ) : Prop :=
  p.IsHomogeneous k ∧ laplacianMv p = 0

/-- The real surface inner product of polynomial restrictions to the Euclidean unit sphere,
AAR (9.4.4), p. 452. Mathlib's `Measure.toSphere` supplies surface measure from Lebesgue
measure. -/
def sphericalHarmonicInner {n : ℕ} (p q : MvPolynomial (Fin n) ℝ) : ℝ :=
  ∫ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
    eval (fun i => x.val i) p * eval (fun i => x.val i) q
      ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))).toSphere

/-- The surface inner product has the unnormalized area `4π` in three dimensions,
as required by the coefficient in AAR's addition theorem. -/
theorem sphericalHarmonicInner_one_three :
    sphericalHarmonicInner (n := 3) 1 1 = 4 * Real.pi := by
  simp [sphericalHarmonicInner, MeasureTheory.measureReal_def,
    MeasureTheory.Measure.toSphere_apply_univ]
  rw [ENNReal.toReal_ofReal (by positivity)]
  ring

/-- Combinatorial dimension of the space of harmonic homogeneous polynomials of
degree `k` in `n` variables (AAR §9.3): `\binom{n+k-1}{k} - \binom{n+k-3}{k-2}`. -/
def harmonicHomogeneousDim (n k : ℕ) : ℕ :=
  (n + k - 1).choose k - if 2 ≤ k then (n + k - 3).choose (k - 2) else 0

/-- In three variables the dimension is `2k + 1`. -/
theorem harmonicHomogeneousDim_three (k : ℕ) :
    harmonicHomogeneousDim 3 k = 2 * k + 1 := by
  -- Already follows from Mathlib's symmetry and Pascal identities for `Nat.choose`.
  unfold harmonicHomogeneousDim
  split_ifs with h
  · have h1 : 3 + k - 1 = k + 2 := by omega
    have h2 : 3 + k - 3 = k := by omega
    rw [h1, h2, Nat.choose_symm_add, Nat.choose_symm h]
    have hp := Nat.choose_succ_succ' (k + 1) 1
    have hq := Nat.choose_succ_succ' k 1
    norm_num [Nat.choose_one_right, Nat.add_assoc] at hp hq
    omega
  · have : k = 0 ∨ k = 1 := by omega
    rcases this with rfl | rfl <;> norm_num

/-- Constants are harmonic. -/
theorem laplacianMv_C {n : ℕ} (r : ℝ) : laplacianMv (C r : MvPolynomial (Fin n) ℝ) = 0 := by
  simp [laplacianMv]

theorem isHarmonicHomogeneous_C (n : ℕ) (r : ℝ) :
    IsHarmonicHomogeneous (n := n) 0 (C r) := by
  refine ⟨?_, laplacianMv_C r⟩
  exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) r

/-- Orthogonality of harmonic homogeneous polynomials of different degrees on the sphere
(AAR §9.4). -/
theorem harmonicHomogeneous_orthogonal {n k l : ℕ} {p q : MvPolynomial (Fin n) ℝ}
    (hp : IsHarmonicHomogeneous k p) (hq : IsHarmonicHomogeneous l q) (hkl : k ≠ l) :
    sphericalHarmonicInner p q = 0 := by
  sorry

end AAR.SphericalHarmonics
