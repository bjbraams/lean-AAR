/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Generalized Airy equations and normalizations, DLMF §9.13(i)

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The fractional Bessel order p=1/(n+2). -/
@[dlmf 9.13.E3]
def generalizedAiryOrder (n : ℕ) : ℝ := 1 / (n + 2 : ℝ)
/-- The generalized Airy argument. -/
@[dlmf 9.13.E3]
def generalizedAiryZeta (n : ℕ) (z : ℂ) : ℂ := 2 / (n + 2 : ℂ) * z ^ (((n : ℂ) + 2) / 2)
/-- The even-at-zero generalized fundamental function. -/
def generalizedAiryF (n : ℕ) (z : ℂ) : ℂ :=
  regularizedHGFun ∅ {1 - (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / (n + 2 : ℂ) ^ 2)
/-- The odd-at-zero generalized fundamental function, including its factor z. -/
def generalizedAiryG (n : ℕ) (z : ℂ) : ℂ :=
  z * regularizedHGFun ∅ {1 + (generalizedAiryOrder n : ℂ)} (z ^ (n + 2) / (n + 2 : ℂ) ^ 2)
/-- Swanson–Headley's entire generalized A_n. -/
def generalizedAiryA (n : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := generalizedAiryOrder n
  p ^ (1 - p) * generalizedAiryF n z - p ^ (p + 1) * generalizedAiryG n z
/-- Swanson–Headley's entire generalized B_n. -/
def generalizedAiryB (n : ℕ) (z : ℂ) : ℂ :=
  let p : ℂ := generalizedAiryOrder n
  p ^ (-1 / 2 : ℂ) * (p ^ (1 - p) * generalizedAiryF n z + p ^ (p + 1) * generalizedAiryG n z)
/-- The scaled independent variable t in Olver's normalization. -/
@[dlmf 9.13.E14]
def olverAiryVariable (m : ℕ) (z : ℂ) : ℂ := ((m : ℂ) / 2) ^ (-2 / (m : ℂ)) * z
/-- Olver's U_m (even m) or V_m (odd m), with one entire formula. -/
def olverAiryU (m : ℕ) (t : ℂ) : ℂ :=
  (2 * π : ℂ) ^ (1 / 2 : ℂ) * ((m : ℂ) / 2) ^ (((m : ℂ) - 1) / m) / sin (π / m) *
    generalizedAiryA (m - 2) (((m : ℂ) / 2) ^ (2 / (m : ℂ)) * t)
/-- The separately normalized second solution; for odd m its bar is not complex conjugation. -/
def olverAiryVBar (m : ℕ) (t : ℂ) : ℂ :=
  (π : ℂ) ^ (1 / 2 : ℂ) * ((m : ℂ) / 2) ^ (((m : ℂ) - 2) / (2 * m)) / sin (π / m) *
    generalizedAiryB (m - 2) (((m : ℂ) / 2) ^ (2 / (m : ℂ)) * t)
/-- Smirnov's normalized first solution on the positive real axis. -/
@[dlmf 9.13.E20]
def smirnovAiryU1 (x α : ℝ) : ℂ :=
  ((α + 2 : ℝ) : ℂ) ^ (-1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 1) / (α + 2)) *
    (x : ℂ) ^ (1 / 2 : ℂ) * besselJ (-1 / ((α : ℂ) + 2))
      (2 / ((α : ℂ) + 2) * (x : ℂ) ^ (((α : ℂ) + 2) / 2))
/-- Smirnov's normalized second solution on the positive real axis. -/
@[dlmf 9.13.E21]
def smirnovAiryU2 (x α : ℝ) : ℂ :=
  ((α + 2 : ℝ) : ℂ) ^ (1 / ((α : ℂ) + 2)) * Gamma (((α : ℂ) + 3) / (α + 2)) *
    (x : ℂ) ^ (1 / 2 : ℂ) * besselJ (1 / ((α : ℂ) + 2))
      (2 / ((α : ℂ) + 2) * (x : ℂ) ^ (((α : ℂ) + 2) / 2))
/-- The normalized oscillatory W_m, specified by its two entire initial-data solutions. -/
def olverAiryW (m : ℕ) (t : ℂ) : ℂ :=
  let p : ℂ := (m : ℂ)⁻¹
  let z := ((m : ℂ) / 2) ^ (2 * p) * t
  let F := Gamma (1 - p) * regularizedHGFun ∅ {1 - p} (-z ^ m / (m : ℂ) ^ 2)
  let G := z * Gamma (1 + p) * regularizedHGFun ∅ {1 + p} (-z ^ m / (m : ℂ) ^ 2)
  (2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) / (2 * (π : ℂ) ^ (1 / 2 : ℂ)) *
    (Gamma p * F + Gamma (-p) / (m : ℂ) ^ (2 * p) * G)

/-- All generalized Airy solutions are entire, DLMF §9.13(i). -/
theorem generalizedAiryA_entire (n : ℕ) :
    Differentiable ℂ (generalizedAiryA n) := by
  have hF : Differentiable ℂ (generalizedAiryF n) := by
    intro z
    exact ((AAR.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _)).differentiableAt
  have hG : Differentiable ℂ (generalizedAiryG n) := by
    intro z
    exact ((hasDerivAt_id z).mul ((AAR.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _))).differentiableAt
  unfold generalizedAiryA
  fun_prop

/-- generalizedAiryA ode (DLMF 9.13.1). -/
@[dlmf 9.13.E1]
theorem generalizedAiryA_ode {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    deriv (deriv (generalizedAiryA n)) z = z ^ n * generalizedAiryA n z := by
  sorry

/-- All generalized Airy solutions are entire, DLMF §9.13(i). -/
theorem generalizedAiryB_entire (n : ℕ) :
    Differentiable ℂ (generalizedAiryB n) := by
  have hF : Differentiable ℂ (generalizedAiryF n) := by
    intro z
    exact ((AAR.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _)).differentiableAt
  have hG : Differentiable ℂ (generalizedAiryG n) := by
    intro z
    exact ((hasDerivAt_id z).mul ((AAR.Bessel.hasDerivAt_regularized0F1 _ _).comp z
      ((hasDerivAt_pow (n + 2) z).div_const _))).differentiableAt
  unfold generalizedAiryB
  fun_prop

/-- generalizedAiryB ode (DLMF 9.13.1). -/
@[dlmf 9.13.E1]
theorem generalizedAiryB_ode {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    deriv (deriv (generalizedAiryB n)) z = z ^ n * generalizedAiryB n z := by
  sorry

/-- generalizedAiry bessel basis (DLMF 9.13.2). -/
@[dlmf 9.13.E2]
theorem generalizedAiry_bessel_basis {n : ℕ} (hn : 1 ≤ n) (a b : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (deriv (fun z : ℂ => z ^ (1 / 2 : ℂ) *
      (a * AAR.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n z) +
        b * AAR.Bessel.besselK (generalizedAiryOrder n) (generalizedAiryZeta n z))))
      ((x : ℂ) ^ n * (x : ℂ) ^ (1 / 2 : ℂ) *
        (a * AAR.Bessel.besselI (generalizedAiryOrder n) (generalizedAiryZeta n x) +
          b * AAR.Bessel.besselK (generalizedAiryOrder n) (generalizedAiryZeta n x))) x := by
  sorry

/-- generalizedAiryA bessel (DLMF 9.13.4). -/
@[dlmf 9.13.E4]
theorem generalizedAiryA_bessel {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    generalizedAiryA n x = 2 * (generalizedAiryOrder n : ℂ) / π * sin ((generalizedAiryOrder n : ℂ) * π) * (x : ℂ) ^ (1 / 2 : ℂ) * AAR.Bessel.besselK (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x) := by
  sorry

/-- generalizedAiryB bessel (DLMF 9.13.4). -/
@[dlmf 9.13.E4]
theorem generalizedAiryB_bessel {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    generalizedAiryB n x = ((generalizedAiryOrder n : ℂ) * x) ^ (1 / 2 : ℂ) * (AAR.Bessel.besselI (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) + AAR.Bessel.besselI (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) := by
  sorry

/-- generalizedAiry initial values (DLMF 9.13.5). -/
@[dlmf 9.13.E5]
theorem generalizedAiry_initial_values {n : ℕ} (hn : 1 ≤ n) :
    generalizedAiryA n 0 = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * generalizedAiryB n 0 ∧
      generalizedAiryA n 0 = (generalizedAiryOrder n : ℂ) ^ (1 - (generalizedAiryOrder n : ℂ)) / Gamma (1 - (generalizedAiryOrder n : ℂ)) ∧
      -deriv (generalizedAiryA n) 0 = (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * deriv (generalizedAiryB n) 0 ∧
      -deriv (generalizedAiryA n) 0 = (generalizedAiryOrder n : ℂ) ^ (generalizedAiryOrder n : ℂ) / Gamma (generalizedAiryOrder n) := by
  sorry

/-- generalizedAiryA negative (DLMF 9.13.6). -/
@[dlmf 9.13.E6]
theorem generalizedAiryA_negative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    generalizedAiryA n (-x) = if Odd n then (generalizedAiryOrder n : ℂ) * (x : ℂ) ^ (1 / 2 : ℂ) * (besselJ (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) + besselJ (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) else (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * generalizedAiryB n x := by
  sorry

/-- generalizedAiryB negative (DLMF 9.13.7). -/
@[dlmf 9.13.E7]
theorem generalizedAiryB_negative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    generalizedAiryB n (-x) = if Odd n then ((generalizedAiryOrder n : ℂ) * x) ^ (1 / 2 : ℂ) * (besselJ (-(generalizedAiryOrder n : ℂ)) (generalizedAiryZeta n x) - besselJ (generalizedAiryOrder n : ℂ) (generalizedAiryZeta n x)) else (generalizedAiryOrder n : ℂ) ^ (-1 / 2 : ℂ) * generalizedAiryA n x := by
  sorry

/-- generalizedAiry wronskian (DLMF 9.13.8). -/
@[dlmf 9.13.E8]
theorem generalizedAiry_wronskian {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    generalizedAiryA n z * deriv (generalizedAiryB n) z - deriv (generalizedAiryA n) z * generalizedAiryB n z =
      2 / π * (generalizedAiryOrder n : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π) := by
  sorry

/-- The n=1 specialization, DLMF §9.13(i). -/
theorem generalizedAiryA_one (z : ℂ) :
    generalizedAiryA 1 z = airyAi z := by
  sorry

/-- The n=1 specialization, DLMF §9.13(i). -/
theorem generalizedAiryB_one (z : ℂ) :
    generalizedAiryB 1 z = airyBi z := by
  sorry

/-- generalizedAiryA asymptotic (DLMF 9.13.9). -/
@[dlmf 9.13.E9]
theorem generalizedAiryA_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n z - ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π)) * z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- generalizedAiryA negative odd asymptotic (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) - (2 * ((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ) * cos ((generalizedAiryOrder n : ℂ) * π / 2) * z ^ (-(n : ℂ) / 4) * cos (generalizedAiryZeta n z - π / 4))) (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ * Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- generalizedAiryA negative even asymptotic (DLMF 9.13.10). -/
@[dlmf 9.13.E10]
theorem generalizedAiryA_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryA n (-z) - ((((generalizedAiryOrder n : ℂ) / π) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- generalizedAiryB asymptotic (DLMF 9.13.11). -/
@[dlmf 9.13.E11]
theorem generalizedAiryB_asymptotic {n : ℕ} (hn : 1 ≤ n)  {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 1 * generalizedAiryOrder n * π) :
    IsBigO (airySector (1 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n z - ((1 / (π : ℂ) ^ (1 / 2 : ℂ)) * z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- generalizedAiryB negative odd asymptotic (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_odd_asymptotic {n : ℕ} (hn : 1 ≤ n)  (hodd : Odd n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 2 * generalizedAiryOrder n * π) :
    IsBigO (airySector (2 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) - (-2 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π / 2) * z ^ (-(n : ℂ) / 4) * sin (generalizedAiryZeta n z - π / 4))) (fun z => ‖z ^ (-(n : ℂ) / 4) / (generalizedAiryZeta n z)‖ * Real.exp |(generalizedAiryZeta n z).im|) := by
  sorry

/-- generalizedAiryB negative even asymptotic (DLMF 9.13.12). -/
@[dlmf 9.13.E12]
theorem generalizedAiryB_negative_even_asymptotic {n : ℕ} (hn : 1 ≤ n)  (heven : Even n) {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < 3 * generalizedAiryOrder n * π) :
    IsBigO (airySector (3 * generalizedAiryOrder n * π - δ))
      (fun z => generalizedAiryB n (-z) - ((1 / (π : ℂ) ^ (1 / 2 : ℂ) * sin ((generalizedAiryOrder n : ℂ) * π)) * z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z))) (fun z => ‖z ^ (-(n : ℂ) / 4) * exp (-generalizedAiryZeta n z) / (generalizedAiryZeta n z)‖) := by
  sorry

/-- olverAiryU ode (DLMF 9.13.13). -/
@[dlmf 9.13.E13]
theorem olverAiryU_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryU m)) t = (m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryU m t := by
  sorry

/-- olverAiryVBar ode (DLMF 9.13.13). -/
@[dlmf 9.13.E13]
theorem olverAiryVBar_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryVBar m)) t = (m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryVBar m t := by
  sorry

/-- olverAiry normalization first (DLMF 9.13.15). -/
@[dlmf 9.13.E15]
theorem olverAiry_normalization_first {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (2 * π : ℂ) ^ (1 / 2 : ℂ) * ((n + 2 : ℂ) / 2) ^ ((n + 1 : ℂ) / (n + 2 : ℂ)) /
      sin (π / (n + 2 : ℂ)) * generalizedAiryA n z = olverAiryU (n + 2) (olverAiryVariable (n + 2) z) := by
  sorry

/-- olverAiry normalization second (DLMF 9.13.16). -/
@[dlmf 9.13.E16]
theorem olverAiry_normalization_second {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    (π : ℂ) ^ (1 / 2 : ℂ) * ((n + 2 : ℂ) / 2) ^ ((n : ℂ) / (2 * (n + 2 : ℂ))) /
      sin (π / (n + 2 : ℂ)) * generalizedAiryB n z = olverAiryVBar (n + 2) (olverAiryVariable (n + 2) z) := by
  sorry

/-- olverAiry even second (DLMF 9.13.16). -/
@[dlmf 9.13.E16]
theorem olverAiry_even_second {m : ℕ} (hm : 3 ≤ m) (heven : Even m) (t : ℂ) :
    olverAiryVBar m t = olverAiryU m (-t) := by
  sorry

/-- olverAiryW ode (DLMF 9.13.17). -/
@[dlmf 9.13.E17]
theorem olverAiryW_ode {m : ℕ} (hm : 3 ≤ m) (t : ℂ) :
    deriv (deriv (olverAiryW m)) t = -(m : ℂ) ^ 2 / 4 * t ^ (m - 2) * olverAiryW m t := by
  sorry

/-- olverAiry rotated solution (DLMF 9.13.18). -/
@[dlmf 9.13.E18]
theorem olverAiry_rotated_solution {m : ℕ} (hm : 3 ≤ m) (j : ℤ) (z : ℂ) :
    deriv (deriv (fun t => olverAiryU m (t * exp (-2 * j * π * I / m)))) z =
      (m : ℂ) ^ 2 / 4 * z ^ (m - 2) * olverAiryU m (z * exp (-2 * j * π * I / m)) := by
  sorry

/-- smirnovAiryU1 ode (DLMF 9.13.19). -/
@[dlmf 9.13.E19]
theorem smirnovAiryU1_ode {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    deriv (deriv (fun t : ℝ => smirnovAiryU1 t α)) x + (x ^ α : ℝ) • smirnovAiryU1 x α = 0 := by
  sorry

/-- smirnovAiryU2 ode (DLMF 9.13.19). -/
@[dlmf 9.13.E19]
theorem smirnovAiryU2_ode {α x : ℝ} (hα : -2 < α) (hx : 0 < x) :
    deriv (deriv (fun t : ℝ => smirnovAiryU2 t α)) x + (x ^ α : ℝ) • smirnovAiryU2 x α = 0 := by
  sorry

/-- smirnovAiryU1 olver (DLMF 9.13.23). -/
@[dlmf 9.13.E23]
theorem smirnovAiryU1_olver {m : ℕ} (hm : 3 ≤ m) {t : ℝ} (ht : 0 < t) :
    smirnovAiryU1 (((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t) (m - 2 : ℝ) =
      ((π : ℂ) ^ (1 / 2 : ℂ) / ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) * Gamma (1 / (m : ℂ)))) * (olverAiryW m t + olverAiryW m (-t)) := by
  sorry

/-- smirnovAiryU2 olver (DLMF 9.13.24). -/
@[dlmf 9.13.E24]
theorem smirnovAiryU2_olver {m : ℕ} (hm : 3 ≤ m) {t : ℝ} (ht : 0 < t) :
    smirnovAiryU2 (((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t) (m - 2 : ℝ) =
      ((π : ℂ) ^ (1 / 2 : ℂ) * (m : ℂ) ^ (2 / (m : ℂ)) / ((2 : ℂ) ^ (((m : ℂ) + 2) / (2 * m)) * Gamma (-1 / (m : ℂ)))) * (olverAiryW m t - olverAiryW m (-t)) := by
  sorry

/-- Smirnov/Olver variable conversion, DLMF 9.13.22. -/
@[dlmf 9.13.E22]
def smirnovAiryVariable (m : ℕ) (t : ℝ) : ℝ := ((m : ℝ) / 2) ^ (2 / (m : ℝ)) * t

/-- The generalized equation's global initial-data solution space. -/
@[dlmf 9.13.E2]
theorem generalizedAiry_general_solution {n : ℕ} (hn : 1 ≤ n) {w w' : ℂ → ℂ}
    (hw : ∀ z, HasDerivAt w (w' z) z ∧ HasDerivAt w' (z ^ n * w z) z) :
    ∃ a b : ℂ, ∀ z, w z = a * generalizedAiryA n z + b * generalizedAiryB n z := by
  sorry

/-- Olver's rotated solution is recessive relative to its dominant companion in every
closed subsector of its stated recessive sector, DLMF §9.13(i). -/
@[dlmf 9.13.E18]
theorem olverAiry_rotated_recessive {m : ℕ} (hm : 3 ≤ m) (j : ℤ)
    {δ : ℝ} (hδ : 0 < δ) (hδ' : δ < π / m) :
    IsLittleO (comap (fun z : ℂ => z * exp (-2 * j * π * I / m)) (airySector (π / m - δ)))
      (fun z => olverAiryU m (z * exp (-2 * j * π * I / m)))
      (fun z => olverAiryVBar m (z * exp (-2 * j * π * I / m))) := by
  sorry

end AAR.Airy
