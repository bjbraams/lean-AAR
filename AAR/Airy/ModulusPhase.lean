/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Airy modulus and continuous phase, DLMF §9.8

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- Airy modulus M. -/
@[dlmf 9.8.E3]
def airyModulus (x : ℝ) : ℝ := Real.sqrt (airyAiReal x ^ 2 + airyBiReal x ^ 2)
/-- Derivative modulus N. -/
@[dlmf 9.8.E7]
def airyDerivModulus (x : ℝ) : ℝ := Real.sqrt (airyAiDerivReal x ^ 2 + airyBiDerivReal x ^ 2)
/-- The unwrapped phase θ, normalized to θ(0)=π/6. -/
def airyPhase (x : ℝ) : ℝ := π / 6 - ∫ t in (0 : ℝ)..x, 1 / (π * airyModulus t ^ 2)
/-- The unwrapped derivative phase φ, normalized to φ(0)=-π/6. -/
def airyDerivPhase (x : ℝ) : ℝ := -π / 6 + ∫ t in (0 : ℝ)..x, t / (π * airyDerivModulus t ^ 2)
/-- Coefficients of M² at negative infinity. -/
def airyModulusCoeff (k : ℕ) : ℝ :=
  (∏ j ∈ Finset.range (3 * k), (2 * (j : ℝ) + 1)) / (k.factorial * 96 ^ k)
/-- Coefficients of N² at negative infinity. -/
def airyDerivModulusCoeff (k : ℕ) : ℝ :=
  airyModulusCoeff k * (1 + 6 * (k : ℝ)) / (1 - 6 * (k : ℝ))
/-- Formal reciprocal coefficients, with unit constant term. -/
def airyReciprocalCoeff (c : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => -∑ j ∈ Finset.range (n + 1), c (j + 1) * airyReciprocalCoeff c (n - j)
termination_by n => n
/-- The all-order θ expansion coefficients, obtained by integrating 1/M². -/
def airyPhaseCoeff (k : ℕ) : ℝ := airyReciprocalCoeff airyModulusCoeff k / (1 - 2 * (k : ℝ))
/-- The all-order φ expansion coefficients, obtained by integrating x/N². -/
def airyDerivPhaseCoeff (k : ℕ) : ℝ := airyReciprocalCoeff airyDerivModulusCoeff k / (1 - 2 * (k : ℝ))
/-- Modulus-square truncation, before its algebraic prefactor. -/
def airyModulusSum (derivative : Bool) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (if derivative then airyDerivModulusCoeff k else airyModulusCoeff k) * x ^ (-(3 * k : ℤ))
/-- Phase truncation, before its leading algebraic prefactor. -/
def airyPhaseSum (derivative : Bool) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, (if derivative then airyDerivPhaseCoeff k else airyPhaseCoeff k) * x ^ (-(3 * k : ℤ))

/-- airyAiReal modulus phase (DLMF 9.8.1). -/
@[dlmf 9.8.E1]
theorem airyAiReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyAiReal x = airyModulus x * Real.sin (airyPhase x) := by
  sorry

/-- airyBiReal modulus phase (DLMF 9.8.2). -/
@[dlmf 9.8.E2]
theorem airyBiReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyBiReal x = airyModulus x * Real.cos (airyPhase x) := by
  sorry

/-- airyAiDerivReal modulus phase (DLMF 9.8.5). -/
@[dlmf 9.8.E5]
theorem airyAiDerivReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyAiDerivReal x = airyDerivModulus x * Real.sin (airyDerivPhase x) := by
  sorry

/-- airyBiDerivReal modulus phase (DLMF 9.8.6). -/
@[dlmf 9.8.E6]
theorem airyBiDerivReal_modulus_phase {x : ℝ} (hx : x ≤ 0) :
    airyBiDerivReal x = airyDerivModulus x * Real.cos (airyDerivPhase x) := by
  sorry

/-- The arctangent formula with its continuous branch retained (DLMF 9.8.4). -/
@[dlmf 9.8.E4]
theorem airyPhase_atan_branch {x : ℝ} (hx : x ≤ 0) (hb : airyBiReal x ≠ 0) :
    ∃ k : ℤ, airyPhase x = Real.arctan (airyAiReal x / airyBiReal x) + k * π := by
  sorry

/-- The phase is continuous, DLMF §9.8(i). -/
theorem airyPhase_continuous  :
    Continuous airyPhase := by
  sorry

/-- Phase normalization in DLMF §9.8(i). -/
theorem airyPhase_zero  :
    airyPhase 0 = π / 6 := by
  simp [airyPhase]

/-- The arctangent formula with its continuous branch retained (DLMF 9.8.8). -/
@[dlmf 9.8.E8]
theorem airyDerivPhase_atan_branch {x : ℝ} (hx : x ≤ 0) (hb : airyBiDerivReal x ≠ 0) :
    ∃ k : ℤ, airyDerivPhase x = Real.arctan (airyAiDerivReal x / airyBiDerivReal x) + k * π := by
  sorry

/-- The phase is continuous, DLMF §9.8(i). -/
theorem airyDerivPhase_continuous  :
    Continuous airyDerivPhase := by
  sorry

/-- Phase normalization in DLMF §9.8(i). -/
theorem airyDerivPhase_zero  :
    airyDerivPhase 0 = -π / 6 := by
  simp [airyDerivPhase]

/-- airyModulus bessel (DLMF 9.8.9). -/
@[dlmf 9.8.E9]
theorem airyModulus_bessel {x : ℝ} (hx : x < 0) :
    ((|x| ^ (1 / 2 : ℝ) * airyModulus x ^ 2 : ℝ) : ℂ) =
      airyZeta |x| / 2 * (Complex.besselJ (1 / 3) (airyZeta |x|) ^ 2 +
        AAR.Bessel.besselY (1 / 3) (airyZeta |x|) ^ 2) := by
  sorry

/-- airyPhase bessel atan (DLMF 9.8.11). -/
@[dlmf 9.8.E11]
theorem airyPhase_bessel_atan {x : ℝ} (hx : x < 0)
    (hJ : (Complex.besselJ (1 / 3) (airyZeta |x|)).re ≠ 0) :
    ∃ k : ℤ, airyPhase x = 2 * π / 3 +
      Real.arctan ((AAR.Bessel.besselY (1 / 3) (airyZeta |x|)).re /
        (Complex.besselJ (1 / 3) (airyZeta |x|)).re) + k * π := by
  sorry

/-- airyDerivModulus bessel (DLMF 9.8.10). -/
@[dlmf 9.8.E10]
theorem airyDerivModulus_bessel {x : ℝ} (hx : x < 0) :
    ((|x| ^ (-1 / 2 : ℝ) * airyDerivModulus x ^ 2 : ℝ) : ℂ) =
      airyZeta |x| / 2 * (Complex.besselJ (2 / 3) (airyZeta |x|) ^ 2 +
        AAR.Bessel.besselY (2 / 3) (airyZeta |x|) ^ 2) := by
  sorry

/-- airyDerivPhase bessel atan (DLMF 9.8.12). -/
@[dlmf 9.8.E12]
theorem airyDerivPhase_bessel_atan {x : ℝ} (hx : x < 0)
    (hJ : (Complex.besselJ (2 / 3) (airyZeta |x|)).re ≠ 0) :
    ∃ k : ℤ, airyDerivPhase x = 1 * π / 3 +
      Real.arctan ((AAR.Bessel.besselY (2 / 3) (airyZeta |x|)).re /
        (Complex.besselJ (2 / 3) (airyZeta |x|)).re) + k * π := by
  sorry

/-- airy modulus phase wronskian (DLMF 9.8.13). -/
@[dlmf 9.8.E13]
theorem airy_modulus_phase_wronskian {x : ℝ} (hx : x ≤ 0) :
    airyModulus x * airyDerivModulus x * Real.sin (airyPhase x - airyDerivPhase x) = 1 / π := by
  sorry

/-- airy modulus phase derivatives (DLMF 9.8.14). -/
@[dlmf 9.8.E14]
theorem airy_modulus_phase_derivatives {x : ℝ} (hx : x ≤ 0) :
    airyModulus x ^ 2 * deriv airyPhase x = -1 / π ∧
      airyDerivModulus x ^ 2 * deriv airyDerivPhase x = x / π ∧
      airyDerivModulus x * deriv airyDerivModulus x = x * airyModulus x * deriv airyModulus x := by
  sorry

/-- airy derivModulus identity (DLMF 9.8.15). -/
@[dlmf 9.8.E15]
theorem airy_derivModulus_identity {x : ℝ} (hx : x ≤ 0) :
    airyDerivModulus x ^ 2 = deriv airyModulus x ^ 2 + airyModulus x ^ 2 * deriv airyPhase x ^ 2 ∧
      airyDerivModulus x ^ 2 = deriv airyModulus x ^ 2 + 1 / (π ^ 2 * airyModulus x ^ 2) := by
  sorry

/-- airy modulus identity (DLMF 9.8.16). -/
@[dlmf 9.8.E16]
theorem airy_modulus_identity {x : ℝ} (hx : x ≤ 0) :
    x ^ 2 * airyModulus x ^ 2 = deriv airyDerivModulus x ^ 2 + airyDerivModulus x ^ 2 * deriv airyDerivPhase x ^ 2 ∧
      x ^ 2 * airyModulus x ^ 2 = deriv airyDerivModulus x ^ 2 + x ^ 2 / (π ^ 2 * airyDerivModulus x ^ 2) := by
  sorry

/-- airy phase difference tan (DLMF 9.8.17). -/
@[dlmf 9.8.E17]
theorem airy_phase_difference_tan {x : ℝ} (hx : x ≤ 0) :
    Real.tan (airyPhase x - airyDerivPhase x) = 1 / (π * airyModulus x * deriv airyModulus x) ∧
      Real.tan (airyPhase x - airyDerivPhase x) = -airyModulus x * deriv airyPhase x / deriv airyModulus x := by
  sorry

/-- airy modulus ode (DLMF 9.8.18). -/
@[dlmf 9.8.E18]
theorem airy_modulus_ode {x : ℝ} (hx : x ≤ 0) :
    deriv (deriv airyModulus) x = x * airyModulus x + 1 / (π ^ 2 * airyModulus x ^ 3) ∧
      iteratedDeriv 3 (fun t => airyModulus t ^ 2) x -
        4 * x * deriv (fun t => airyModulus t ^ 2) x - 2 * airyModulus x ^ 2 = 0 := by
  sorry

/-- airy phase ode (DLMF 9.8.19). -/
@[dlmf 9.8.E19]
theorem airy_phase_ode {x : ℝ} (hx : x ≤ 0) :
    deriv airyPhase x ^ 2 + iteratedDeriv 3 airyPhase x / (2 * deriv airyPhase x) -
      3 / 4 * (iteratedDeriv 2 airyPhase x / deriv airyPhase x) ^ 2 = -x := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_modulus_monotone  :
    StrictMonoOn (airyModulus) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_modulus_deriv_monotone  :
    StrictMonoOn (deriv airyModulus) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_weighted_derivModulus_monotone  :
    StrictMonoOn (fun x : ℝ => |x| ^ (-1 / 4 : ℝ) * airyDerivModulus x) (Iio 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_modulus_product_monotone  :
    StrictMonoOn (fun x => airyModulus x * airyDerivModulus x) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_phase_deriv_monotone  :
    StrictMonoOn (deriv airyPhase) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_derivPhase_deriv_monotone  :
    StrictMonoOn (deriv airyDerivPhase) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_weighted_modulus_monotone  :
    StrictAntiOn (fun x : ℝ => |x| ^ (1 / 4 : ℝ) * airyModulus x) (Iio 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_phase_monotone  :
    StrictAntiOn (airyPhase) (Iic 0) := by
  sorry

/-- Monotonicity in DLMF §9.8(iii); singular endpoints are excluded from weighted expressions. -/
theorem airy_derivPhase_monotone  :
    StrictAntiOn (airyDerivPhase) (Iic 0) := by
  sorry

/-- airyModulus asymptotic (DLMF 9.8.20). -/
@[dlmf 9.8.E20]
theorem airyModulus_asymptotic  :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (-1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyModulusCoeff (fun x => airyModulus x ^ 2) := by
  sorry

/-- airyPhase asymptotic (DLMF 9.8.22). -/
@[dlmf 9.8.E22]
theorem airyPhase_asymptotic  :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyPhaseCoeff (fun x => airyPhase x - (π / 4)) := by
  sorry

/-- airyDerivModulus asymptotic (DLMF 9.8.21). -/
@[dlmf 9.8.E21]
theorem airyDerivModulus_asymptotic  :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => (-x) ^ (1 / 2 : ℝ) / π * x ^ (-(3 * k : ℤ)))
      airyDerivModulusCoeff (fun x => airyDerivModulus x ^ 2) := by
  sorry

/-- airyDerivPhase asymptotic (DLMF 9.8.23). -/
@[dlmf 9.8.E23]
theorem airyDerivPhase_asymptotic  :
    HasAsymptoticExpansion atBot (fun k (x : ℝ) => 2 / 3 * (-x) ^ (3 / 2 : ℝ) * x ^ (-(3 * k : ℤ)))
      airyDerivPhaseCoeff (fun x => airyDerivPhase x - (-π / 4)) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x| ≤ |((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyModulus x ^ 2) - ((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusSum false N x) * (((-x) ^ (-1 / 2 : ℝ) / π) * airyModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyPhase x - (π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum false (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyDerivModulus_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 1 ≤ N) :
    |(airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x| ≤ |((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))| ∧
      0 ≤ ((airyDerivModulus x ^ 2) - ((-x) ^ (1 / 2 : ℝ) / π) * airyModulusSum true N x) * (((-x) ^ (1 / 2 : ℝ) / π) * airyDerivModulusCoeff N * x ^ (-(3 * N : ℤ))) := by
  sorry

/-- Signed first-neglected-term bounds, DLMF §9.8(iv). -/
theorem airyDerivPhase_error {x : ℝ} (hx : x < 0) {N : ℕ} (hN : 0 ≤ N) :
    |(airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x| ≤ |(2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))| ∧
      0 ≤ ((airyDerivPhase x - (-π / 4)) - (2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyPhaseSum true (N + 1) x) * ((2 / 3 * (-x) ^ (3 / 2 : ℝ)) * airyDerivPhaseCoeff (N + 1) * x ^ (-(3 * (N + 1) : ℤ))) := by
  sorry

/-- Every printed coefficient in the phase expansions 9.8.22 and 9.8.23. -/
@[dlmf 9.8.E22, dlmf 9.8.E23]
theorem airy_phase_printed_coefficients :
    (∀ n < 5, airyPhaseCoeff n = ([1, 5/32, 1105/6144, 82825/65536, 1282031525/58720256] : List ℝ)[n]!) ∧
    (∀ n < 5, airyDerivPhaseCoeff n = ([1, -7/32, -1463/6144, -495271/327680, -206530429/8388608] : List ℝ)[n]!) := by
  constructor <;> intro n hn <;> interval_cases n <;>
    norm_num [airyPhaseCoeff, airyDerivPhaseCoeff, airyReciprocalCoeff,
      airyModulusCoeff, airyDerivModulusCoeff, Finset.sum_range_succ, Finset.prod_range_succ]

end AAR.Airy
