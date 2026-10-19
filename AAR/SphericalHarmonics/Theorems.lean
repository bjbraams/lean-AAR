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
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Three
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Real.Basic
public import TauCeti.LinearAlgebra.QuadraticForm.SpecialOrthogonal.WeightedSumSquares
public import TauCeti.Analysis.PDE.PoissonIntegral.Ball
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Comparison

/-!
# Addition theorems, Funk–Hecke, Poisson, and `SU(2)` (AAR §§9.6–9.16)

Mathlib has the Poisson kernel of the *disk* (`poissonKernel`) and `Matrix.specialUnitaryGroup`,
but not the spherical addition theorem, Funk–Hecke, or the identification of Jacobi polynomials
with matrix coefficients of `SU(2)`.
The ball Poisson representation uses the Tau Ceti contributors’ Poisson kernel,
boundary convergence and Dirichlet uniqueness. The continuous extension argument
is adapted from their unit-ball Dirichlet theorem. The `SU(2)` double cover transports
their compact Spin cover through their Spin–unitary and coordinate equivalences.
-/

@[expose] public section

open Complex Matrix MeasureTheory intervalIntegral Metric Set Filter InnerProductSpace
open scoped Real Topology
open AAR.OrthogonalPolynomials

noncomputable section

namespace AAR.SphericalHarmonics

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
    (2 * k + 1 : ℂ) / (4 * π) * legendrePolyP k (∑ i, x i * y i : ℝ) =
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
      (2 * π : ℂ) * (∫ t : ℝ in (-1 : ℝ)..1, f t * legendrePolyP k t) *
        (MvPolynomial.eval (fun i => x.val i) S : ℂ) := by
  sorry

/-- Gegenbauer addition theorem, AAR (9.8.5'), for `λ > 1/2`. -/
theorem ultrasphPoly_addition {lam : ℝ} (hlam : 1 / 2 < lam)
    (n : ℕ) (theta phi psi : ℝ) :
    ultrasphPoly lam n
        (Real.cos theta * Real.cos phi +
          Real.sin theta * Real.sin phi * Real.cos psi) =
      ∑ j ∈ Finset.range (n + 1),
        (Gamma (2 * lam - 1) * 4 ^ j * (n - j).factorial *
          Gamma (j + (lam : ℂ)) ^ 2 * (2 * j + 2 * (lam : ℂ) - 1) /
            (Gamma (lam : ℂ) ^ 2 * Gamma (j + n + 2 * (lam : ℂ)))) *
        (Real.sin theta : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos theta) *
        (Real.sin phi : ℂ) ^ j * ultrasphPoly (j + (lam : ℂ)) (n - j) (Real.cos phi) *
        ultrasphPoly ((lam : ℂ) - 1 / 2) j (Real.cos psi) := by
  sorry

/-- Poisson kernel of the unit ball in `ℝⁿ` (AAR §9.9), before division by sphere area.
In the supplied printing, (9.9.2) and Theorem 9.9.1 put an extra `cos` around the
Euclidean inner product. The denominator intended there is `1 - 2r(α·η) + r²`. -/
def poissonKernelBall {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  (1 - ∑ i, x i ^ 2) / (∑ i, (x i - y i) ^ 2) ^ (n / 2 : ℝ)

/-- The Poisson extension of existing harmonic boundary data is the original function. -/
lemma ballPoissonIntegral_reproduces {n : ℕ} (hn : n ≠ 0)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HarmonicOnNhd f (ball 0 1)) (hcont : ContinuousOn f (closedBall 0 1))
    {x : EuclideanSpace ℝ (Fin n)} (hx : ‖x‖ < 1) :
    TauCeti.ballPoissonIntegral (fun y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 => f y) x = f x := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  let g : sphere (0 : EuclideanSpace ℝ (Fin n)) 1 → ℝ := fun y => f y
  have hg : Continuous g := (hcont.mono sphere_subset_closedBall).comp_continuous
    continuous_subtype_val (fun y => y.2)
  have hgi : Integrable g volume.toSphere :=
    hg.integrable_of_hasCompactSupport (.of_compactSpace g)
  let u : EuclideanSpace ℝ (Fin n) → ℝ := fun z =>
    if hz : z ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 then g ⟨z, hz⟩
    else TauCeti.ballPoissonIntegral g z
  have hball : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1, z ∉ sphere 0 1 := fun z hz hs =>
    (mem_ball_zero_iff.mp hz).ne (mem_sphere_zero_iff_norm.mp hs)
  have hu : EqOn u (TauCeti.ballPoissonIntegral g) (ball 0 1) :=
    fun z hz => dite_eq_right (hball z hz)
  have hP : HarmonicOnNhd (TauCeti.ballPoissonIntegral g) (ball 0 1) :=
    (TauCeti.harmonicOnNhd_ballPoissonIntegral hgi).mono hball
  have huP : ∀ z ∈ ball (0 : EuclideanSpace ℝ (Fin n)) 1,
      u =ᶠ[𝓝 z] TauCeti.ballPoissonIntegral g :=
    fun z hz => Filter.eventually_of_mem (isOpen_ball.mem_nhds hz) hu
  have hhu : HarmonicOnNhd u (ball 0 1) :=
    fun z hz => (harmonicAt_congr_nhds (huP z hz)).2 (hP z hz)
  have hcu : ContinuousOn u (closedBall 0 1) := by
    rw [← ball_union_sphere]
    intro z hz
    rcases hz with hz | hz
    · exact ((hP z hz).1.continuousAt.congr (huP z hz).symm).continuousWithinAt
    · have huz : u z = g ⟨z, hz⟩ := dite_eq_left hz
      refine continuousWithinAt_union.2 ⟨?_, ?_⟩
      · rw [ContinuousWithinAt, huz]
        exact (TauCeti.tendsto_ballPoissonIntegral hg ⟨z, hz⟩).congr'
          (Filter.eventually_of_mem self_mem_nhdsWithin fun y hy => (hu hy).symm)
      · have hres : (sphere (0 : EuclideanSpace ℝ (Fin n)) 1).domRestrict u = g :=
          funext fun y => dite_eq_left y.2
        exact (continuousOn_iff_continuous_domRestrict.2 (hres ▸ hg)) z hz
  have he : EqOn u f (closedBall 0 1) :=
    TauCeti.eqOn_of_harmonicOnNhd_of_eqOn_frontier (isCompact_closedBall _ _) hcu hcont
      (by simpa only [interior_closedBall _ one_ne_zero] using hhu)
      (by simpa only [interior_closedBall _ one_ne_zero] using hf) (by
        intro z hz
        have hz' : z ∈ sphere (0 : EuclideanSpace ℝ (Fin n)) 1 := by simpa only [frontier_closedBall _ one_ne_zero] using hz
        exact dite_eq_left hz')
  exact (hu (mem_ball_zero_iff.mpr hx)).symm.trans
    (he (mem_closedBall_zero_iff.mpr hx.le))

/-- The unnormalized AAR kernel is sphere area times the Tau Ceti kernel. -/
lemma poissonKernelBall_eq_area_mul {n : ℕ} (hn : n ≠ 0) (x y : EuclideanSpace ℝ (Fin n)) :
    poissonKernelBall (fun i => x i) (fun i => y i) =
      volume.toSphere.real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) *
        TauCeti.ballPoissonKernel n x y := by
  rw [poissonKernelBall, ← EuclideanSpace.real_norm_sq_eq x]
  have hsq : ∑ i, (x i - y i) ^ 2 = ‖x - y‖ ^ 2 :=
    (EuclideanSpace.real_norm_sq_eq (x - y)).symm
  rw [hsq]
  have hpow : (‖x - y‖ ^ 2) ^ (n / 2 : ℝ) = ‖x - y‖ ^ n := by
    rw [← Real.rpow_natCast (‖x - y‖) 2]
    change (‖x - y‖ ^ (2 : ℝ)) ^ (n / 2 : ℝ) = _
    rw [← Real.rpow_mul (norm_nonneg _)]
    rw [show (2 : ℝ) * (n / 2 : ℝ) = n by ring, Real.rpow_natCast]
  rw [hpow]
  rw [Measure.toSphere_real_apply_univ, finrank_euclideanSpace_fin, TauCeti.ballPoissonKernel_def]
  have hp := TauCeti.volume_real_unitBall_pos n
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  field_simp

/-- Poisson representation of a harmonic function continuous on the closed unit ball. -/
theorem poissonKernelBall_reproduces {n : ℕ} (hn : 2 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : HarmonicOnNhd f (ball 0 1)) (hcont : ContinuousOn f (closedBall 0 1))
    (x : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ < 1) :
    (∫ y : sphere (0 : EuclideanSpace ℝ (Fin n)) 1,
      poissonKernelBall (fun i => x i) (fun i => y.val i) * f y.val ∂volume.toSphere) =
      volume.toSphere.real (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin n)) 1)) * f x := by
  have hn0 : n ≠ 0 := by omega
  simp_rw [poissonKernelBall_eq_area_mul hn0 x, mul_assoc]
  rw [MeasureTheory.integral_const_mul, ← TauCeti.ballPoissonIntegral_def, ballPoissonIntegral_reproduces hn0 hf hcont hx]

/-- Special unitary group `SU(2)`. -/
abbrev SU2 := specialUnitaryGroup (Fin 2) ℂ

/-! The Jacobi-polynomial interpretation as matrix coefficients of irreducible
`SU(2)` representations (AAR §9.14) remains to be formulated using a representation
and a specified basis. The former reflexive placeholder has been removed: it
provided no representation-theoretic content. -/

open CliffordAlgebra TauCeti

/-- The Tau Ceti Clifford-form special orthogonal group in matrix coordinates. -/
def compactSO3EquivMatrix :
    QuadraticMap.specialOrthogonalGroup (realCliffordForm 3 0) ≃*
      Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [realCliffordForm_zero_eq_weightedSumSquares_one]
  exact (TauCeti.QuadraticMap.matrixSpecialOrthogonalEquivWeightedSumSquaresOne (Fin 3)).symm

/-- The distinguished negative Spin scalar has special unitary matrix `-1`. -/
lemma realSpinThreeEquivSpecialUnitary_negOne :
    (realSpinThreeEquivSpecialUnitary
      (spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero) :
        Matrix (Fin 2) (Fin 2) ℂ) = -1 := by
  rw [coe_realSpinThreeEquivSpecialUnitary_apply, coe_realSpinThreeEquivQuaternionUnitary_apply]
  have he : evenUnitaryGroupEvenPart (realCliffordForm 3 0)
      (spinGroupToEvenUnitary (realCliffordForm 3 0)
        (spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero)) = -1 := by
    apply Subtype.ext
    simp
  rw [he, map_neg, map_one, map_neg, map_one]


/-- The double cover `SU(2) → SO(3)` (AAR §9.16). -/
theorem su2_covers_so3 :
    ∃ Φ : SU2 →* specialOrthogonalGroup (Fin 3) ℝ, Function.Surjective Φ ∧
      (∀ g, Φ g = 1 ↔ g = 1 ∨ g.1 = (-1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
  let E := realSpinThreeEquivSpecialUnitary
  let C := compactSO3EquivMatrix
  let P := spinToSpecialOrthogonal (realCliffordForm 3 0)
  let Φ := C.toMonoidHom.comp (P.comp E.symm.toMonoidHom)
  refine ⟨Φ, C.surjective.comp
    ((spinToSpecialOrthogonal_surjective_of_posDef _ (posDef_realCliffordForm_zero 3)).comp
      E.symm.surjective), ?_⟩
  intro g
  have hker : Φ g = 1 ↔ E.symm g = 1 ∨ E.symm g =
      spinGroup.negOne (realCliffordForm 3 0) (nondegenerate_realCliffordForm 3 0).ne_zero := by
    change C (P (E.symm g)) = 1 ↔ _
    rw [← C.map_one, C.injective.eq_iff]
    exact mem_ker_spinToSpecialOrthogonal_iff _ (nondegenerate_realCliffordForm 3 0) _
  rw [hker]
  constructor
  · rintro (hg | hg)
    · left
      have hh := congrArg E hg
      simpa using hh
    · right
      have hh := congrArg (fun s => (E s : Matrix (Fin 2) (Fin 2) ℂ)) hg
      simpa only [MulEquiv.apply_symm_apply, E, realSpinThreeEquivSpecialUnitary_negOne] using hh
  · rintro (rfl | hg)
    · left
      exact E.symm.map_one
    · right
      apply E.injective
      apply Subtype.ext
      simpa only [MulEquiv.apply_symm_apply, E, realSpinThreeEquivSpecialUnitary_negOne] using hg

end AAR.SphericalHarmonics
