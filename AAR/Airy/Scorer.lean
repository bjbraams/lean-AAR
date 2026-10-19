/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Scorer functions, DLMF §9.12

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- Maclaurin coefficient of Hi, DLMF 9.12.17. -/
def scorerHiCoeff (k : ℕ) : ℂ :=
  (3 : ℂ) ^ (((k : ℂ) - 2) / 3) * Gamma (((k : ℂ) + 1) / 3) / (π * k.factorial)
/-- The entire Scorer function Hi, specified by its Maclaurin series. -/
@[dlmf 9.12.E17]
def scorerHi (z : ℂ) : ℂ := ∑' k : ℕ, scorerHiCoeff k * z ^ k
/-- The complementary Scorer function Gi, with Gi+Hi=Bi. -/
def scorerGi (z : ℂ) : ℂ := airyBi z - scorerHi z
/-- The derivative of Hi. -/
def scorerHiDeriv : ℂ → ℂ := deriv scorerHi
/-- The derivative of Gi. -/
def scorerGiDeriv : ℂ → ℂ := deriv scorerGi
/-- The inhomogeneous Airy equation with forcing 1/π. -/
def IsScorerSol (w w' : ℂ → ℂ) : Prop :=
  ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z * w z + 1 / π) z
/-- The determinant of the value/first-derivative/second-derivative matrix. -/
def airyWronskian3 (f g h : ℂ → ℂ) (z : ℂ) : ℂ :=
  f z * (deriv g z * deriv (deriv h) z - deriv h z * deriv (deriv g) z) -
    g z * (deriv f z * deriv (deriv h) z - deriv h z * deriv (deriv f) z) +
    h z * (deriv f z * deriv (deriv g) z - deriv g z * deriv (deriv f) z)
/-- Uniform numerical separation of a third-order fundamental system. -/
def IsWellConditionedTripleOn (f g h : ℂ → ℂ) (s : Set ℂ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ z ∈ s,
    ‖f z‖ * (‖deriv g z‖ * ‖deriv (deriv h) z‖ + ‖deriv h z‖ * ‖deriv (deriv g) z‖) +
      ‖g z‖ * (‖deriv f z‖ * ‖deriv (deriv h) z‖ + ‖deriv h z‖ * ‖deriv (deriv f) z‖) +
      ‖h z‖ * (‖deriv f z‖ * ‖deriv (deriv g) z‖ + ‖deriv g z‖ * ‖deriv (deriv f) z‖) ≤
        C * ‖airyWronskian3 f g h z‖

/-- Hi is entire, DLMF §9.12(i). -/
theorem scorerHi_entire  :
    Differentiable ℂ scorerHi := by
  sorry

/-- Gi is entire, DLMF §9.12(i). -/
theorem scorerGi_entire  :
    Differentiable ℂ scorerGi := by
  sorry

/-- scorerHi ode (DLMF 9.12.1). -/
@[dlmf 9.12.E1]
theorem scorerHi_ode  :
    IsScorerSol scorerHi scorerHiDeriv := by
  sorry

/-- scorerGi ode (DLMF 9.12.3). -/
@[dlmf 9.12.E3]
theorem scorerGi_ode  :
    IsScorerSol (fun z => -scorerGi z) (fun z => -scorerGiDeriv z) := by
  sorry

/-- scorerHi rotated ode (DLMF 9.12.3). -/
@[dlmf 9.12.E3]
theorem scorerHi_rotated_ode {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    IsScorerSol (fun z => exp (-ε * (2 * π * I / 3)) * scorerHi (z * exp (-ε * (2 * π * I / 3))))
      (fun z => exp (-ε * (4 * π * I / 3)) * scorerHiDeriv (z * exp (-ε * (2 * π * I / 3)))) := by
  sorry

/-- scorer general solution (DLMF 9.12.2). -/
@[dlmf 9.12.E2]
theorem scorer_general_solution {w w' p p' f f' g g' : ℂ → ℂ} (hw : IsScorerSol w w') (hp : IsScorerSol p p')
    (hf : IsAirySol f f') (hg : IsAirySol g g') (hind : f 0 * g' 0 - f' 0 * g 0 ≠ 0) :
    ∃ a b : ℂ, ∀ z, w z = a * f z + b * g z + p z := by
  sorry

/-- scorerGi variation (DLMF 9.12.4). -/
@[dlmf 9.12.E4]
theorem scorerGi_variation (z : ℂ) :
    scorerGi z = airyBi z * (1 / 3 - primitive airyAi z) + airyAi z * primitive airyBi z := by
  sorry

/-- scorerHi variation (DLMF 9.12.5). -/
@[dlmf 9.12.E5]
theorem scorerHi_variation (z : ℂ) :
    scorerHi z = airyBi z * (2 / 3 + primitive airyAi z) - airyAi z * primitive airyBi z := by
  sorry

/-- scorer zero (DLMF 9.12.6). -/
@[dlmf 9.12.E6]
theorem scorer_zero  :
    scorerGi 0 = scorerHi 0 / 2 ∧ scorerGi 0 = airyBi 0 / 3 ∧
      scorerGi 0 = 1 / ((3 : ℂ) ^ (7 / 6 : ℂ) * Gamma (2 / 3)) := by
  sorry

/-- scorerDeriv zero (DLMF 9.12.7). -/
@[dlmf 9.12.E7]
theorem scorerDeriv_zero  :
    scorerGiDeriv 0 = scorerHiDeriv 0 / 2 ∧ scorerGiDeriv 0 = airyBiDeriv 0 / 3 ∧
      scorerGiDeriv 0 = 1 / ((3 : ℂ) ^ (5 / 6 : ℂ) * Gamma (1 / 3)) := by
  sorry

/-- The standard particular and complementary system in 9.12.8. -/
@[dlmf 9.12.E8]
theorem scorerGi_standard_system (z : ℂ) :
    airyWronskian3 (fun t => -scorerGi t) airyAi airyBi z ≠ 0 := by
  sorry

/-- The rotated complementary system of 9.12.9. -/
@[dlmf 9.12.E9]
theorem scorerHi_standard_system (z : ℂ) :
    airyWronskian3 scorerHi (fun t => airyAi (t * exp (-2 * π * I / 3)))
      (fun t => airyAi (t * exp (2 * π * I / 3))) z ≠ 0 := by
  sorry

/-- The two systems in 9.12.10; their sectorial expansions are recorded separately. -/
@[dlmf 9.12.E10]
theorem scorerHi_rotated_standard_system (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyWronskian3 (fun t => exp (-ε * (2 * π * I / 3)) * scorerHi (t * exp (-ε * (2 * π * I / 3))))
      airyAi (fun t => airyAi (t * exp (ε * (2 * π * I / 3)))) z ≠ 0 := by
  sorry

/-- scorerGi add scorerHi (DLMF 9.12.11). -/
@[dlmf 9.12.E11]
theorem scorerGi_add_scorerHi (z : ℂ) :
    scorerGi z + scorerHi z = airyBi z := by
  simp [scorerGi]

/-- scorerGi rotations (DLMF 9.12.12). -/
@[dlmf 9.12.E12]
theorem scorerGi_rotations (z : ℂ) :
    scorerGi z = exp (π * I / 3) / 2 * scorerHi (z * exp (-2 * π * I / 3)) +
      exp (-π * I / 3) / 2 * scorerHi (z * exp (2 * π * I / 3)) := by
  sorry

/-- scorerGi eq rotated scorerHi (DLMF 9.12.13). -/
@[dlmf 9.12.E13]
theorem scorerGi_eq_rotated_scorerHi (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerGi z = exp (-ε * (π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) + ε * I * airyAi z := by
  sorry

/-- scorerHi connection (DLMF 9.12.14). -/
@[dlmf 9.12.E14]
theorem scorerHi_connection (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    scorerHi z = exp (ε * (2 * π * I / 3)) * scorerHi (z * exp (ε * (2 * π * I / 3))) +
      2 * exp (-ε * (π * I / 6)) * airyAi (z * exp (-ε * (2 * π * I / 3))) := by
  sorry

/-- hasSum scorerGi (DLMF 9.12.15). -/
@[dlmf 9.12.E15]
theorem hasSum_scorerGi (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-2 / 3 : ℂ) / π * cos ((2 * (k : ℂ) - 1) * π / 3) *
      Gamma (((k : ℂ) + 1) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerGi z) := by
  sorry

/-- hasSum scorerGiDeriv (DLMF 9.12.16). -/
@[dlmf 9.12.E16]
theorem hasSum_scorerGiDeriv (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-1 / 3 : ℂ) / π * cos ((2 * (k : ℂ) + 1) * π / 3) *
      Gamma (((k : ℂ) + 2) / 3) * ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerGiDeriv z) := by
  sorry

/-- hasSum scorerHi (DLMF 9.12.17). -/
@[dlmf 9.12.E17]
theorem hasSum_scorerHi (z : ℂ) :
    HasSum (fun k : ℕ => scorerHiCoeff k * z ^ k) (scorerHi z) := by
  sorry

/-- hasSum scorerHiDeriv (DLMF 9.12.18). -/
@[dlmf 9.12.E18]
theorem hasSum_scorerHiDeriv (z : ℂ) :
    HasSum (fun k : ℕ => (3 : ℂ) ^ (-1 / 3 : ℂ) / π * Gamma (((k : ℂ) + 2) / 3) *
      ((3 : ℂ) ^ (1 / 3 : ℂ) * z) ^ k / k.factorial) (scorerHiDeriv z) := by
  sorry

/-- scorerGi sin integral (DLMF 9.12.19). -/
@[dlmf 9.12.E19]
theorem scorerGi_sin_integral (x : ℝ) :
    HasIntegralAtTop (fun t : ℝ => (Real.sin (t ^ 3 / 3 + x * t) : ℂ)) 0 (π * scorerGi x) := by
  sorry

/-- scorerHi exp integral (DLMF 9.12.20). -/
@[dlmf 9.12.E20]
theorem scorerHi_exp_integral (z : ℂ) :
    IntegrableOn (fun t : ℝ => exp (-(t : ℂ) ^ 3 / 3 + z * t)) (Ioi 0) ∧
      scorerHi z = (∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 + z * t)) / π := by
  sorry

/-- scorerGi exp cos integral (DLMF 9.12.21). -/
@[dlmf 9.12.E21]
theorem scorerGi_exp_cos_integral (z : ℂ) :
    scorerGi z = -(∫ t : ℝ in Ioi 0, exp (-(t : ℂ) ^ 3 / 3 - z * t / 2) *
      cos (Real.sqrt 3 * z * t / 2 + 2 * π / 3)) / π := by
  sorry

/-- scorerHi stieltjes integral (DLMF 9.12.22). -/
@[dlmf 9.12.E22]
theorem scorerHi_stieltjes_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π / 3) :
    scorerHi (-z) = 4 * z ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      ∫ t : ℝ in Ioi 0, AAR.Bessel.besselK (1 / 3) t / (airyZetaComplex z ^ 2 + (t : ℂ) ^ 2) := by
  sorry

/-- scorerGi principalValue (DLMF 9.12.23). -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue {x : ℝ} (hx : 0 < x) :
    scorerGi x = 4 * (x : ℂ) ^ 2 / ((3 : ℂ) ^ (3 / 2 : ℂ) * π ^ 2) *
      principalValueIoi (fun t : ℝ => AAR.Bessel.besselK (1 / 3) t /
        ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)) (airyZeta x) := by
  sorry

/-- Barnes contour on a separating vertical line; boundary values are ordinary improper integrals (DLMF 9.12.24). -/
@[dlmf 9.12.E24]
theorem scorerHi_mellinBarnes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg (-z)| < 2 * π / 3) {σ : ℝ} (hσ0 : -1 < σ) (hσ1 : σ < 0) :
    HasIntegralWholeLine (fun y : ℝ => Gamma (1 / 3 + ((σ : ℂ) + y * I) / 3) *
      Gamma (-((σ : ℂ) + y * I)) *
        exp (((σ : ℂ) + y * I) * (log (3 : ℂ) / 3 + log (-z))))
      (2 * π ^ 2 * (3 : ℂ) ^ (2 / 3 : ℂ) * scorerHi z) := by
  sorry

/-- scorerGi asymptotic (DLMF 9.12.25). -/
@[dlmf 9.12.E25]
theorem scorerGi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGi z - 1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  sorry

/-- scorerGiDeriv asymptotic (DLMF 9.12.26). -/
@[dlmf 9.12.E26]
theorem scorerGiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => z) (airySector (π / 3 - δ)))
      (fun z : ℂ => scorerGiDeriv z - -1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  sorry

/-- scorerHi asymptotic (DLMF 9.12.27). -/
@[dlmf 9.12.E27]
theorem scorerHi_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHi z - -1 / (π * z ^ 1) *
        ∑ k ∈ Finset.range N, (((3 * k + 0).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 1))) := by
  sorry

/-- scorerHiDeriv asymptotic (DLMF 9.12.28). -/
@[dlmf 9.12.E28]
theorem scorerHiDeriv_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * π / 3) (N : ℕ) :
    IsBigO (comap (fun z : ℂ => -z) (airySector (2 * π / 3 - δ)))
      (fun z : ℂ => scorerHiDeriv z - 1 / (π * z ^ 2) *
        ∑ k ∈ Finset.range N, (((3 * k + 1).factorial : ℂ) / k.factorial) / (3 * z ^ 3) ^ k)
      (fun z : ℂ => z ^ (-(3 * (N : ℂ) + 2))) := by
  sorry

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerGi_simple_zeros {z : ℂ} (hz : scorerGi z = 0) :
    deriv scorerGi z ≠ 0 := by
  sorry

/-- All complex zeros are simple, DLMF §9.12(ix). -/
theorem scorerHi_simple_zeros {z : ℂ} (hz : scorerHi z = 0) :
    deriv scorerHi z ≠ 0 := by
  sorry

/-- There are no real zeros, DLMF §9.12(ix). -/
theorem scorerHi_real_ne_zero (x : ℝ) :
    scorerHi x ≠ 0 := by
  sorry

/-- There are no real zeros, DLMF §9.12(ix). -/
theorem scorerHiDeriv_real_ne_zero (x : ℝ) :
    scorerHiDeriv x ≠ 0 := by
  sorry

/-- Gi has no nonnegative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_nonneg_ne_zero {x : ℝ} (hx : 0 ≤ x) :
    scorerGi x ≠ 0 := by
  sorry

/-- Gi' has exactly one nonnegative real zero, DLMF §9.12(ix). -/
theorem scorerGiDeriv_unique_nonneg_zero  :
    ∃! x : ℝ, 0 ≤ x ∧ scorerGiDeriv x = 0 := by
  sorry

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGi_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGi x = 0} := by
  sorry

/-- Infinitely many negative real zeros, DLMF §9.12(ix). -/
theorem scorerGiDeriv_infinite_negative_zeros  :
    Set.Infinite {x : ℝ | x < 0 ∧ scorerGiDeriv x = 0} := by
  sorry

/-- Negative zeros of Gi and Gi' interlace, DLMF §9.12(ix). -/
theorem scorerGi_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGi a = 0) (hb0 : scorerGi b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGi x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGiDeriv x = 0 := by
  sorry

/-- The reverse interlacing of the two negative real Scorer zero families. -/
theorem scorerGiDeriv_zeros_interlace {a b : ℝ} (hab : a < b) (hb : b < 0)
    (ha0 : scorerGiDeriv a = 0) (hb0 : scorerGiDeriv b = 0)
    (hgap : ∀ x ∈ Ioo a b, scorerGiDeriv x ≠ 0) :
    ∃! x : ℝ, x ∈ Ioo a b ∧ scorerGi x = 0 := by
  sorry

/-- Convergence of the symmetric principal value in DLMF 9.12.23. -/
@[dlmf 9.12.E23]
theorem scorerGi_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => AAR.Bessel.besselK (1 / 3) t /
      ((airyZeta x : ℂ) ^ 2 - (t : ℂ) ^ 2)
    HasPrincipalValueIoi f (airyZeta x) (principalValueIoi f (airyZeta x)) := by
  sorry

end AAR.Airy
