/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Framework

/-!
# Complete branch-aware Bessel and confluent relations, DLMF §9.6

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The inverse substitution on the logarithmic ζ plane. -/
@[dlmf 9.6.E10]
def airyInverseZetaOnLog (w : ℂ) : ℂ := exp (2 / 3 * (log (3 / 2 : ℂ) + w))

/-- airyInverseZeta logZeta (DLMF 9.6.10). -/
@[dlmf 9.6.E10]
theorem airyInverseZeta_logZeta {z : ℂ} (hz : z ≠ 0) :
    airyInverseZetaOnLog (airyLogZeta z) = z := by
  sorry

/-- airyAi eq besselK complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselK_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAi z = ((z / 3) ^ (1 / 2 : ℂ)) / π * airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z) := by
  sorry

/-- airyAi eq besselI complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = z ^ (1 / 2 : ℂ) / 3 * (airyBesselIOnLog (-(1 / 3)) (airyLogZeta z) - airyBesselIOnLog (1 / 3) (airyLogZeta z)) := by
  sorry

/-- airyAi eq hankel1 pos complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel1_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (2 * π * I / 3) * airyHankel1OnLog (1 * (1 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  sorry

/-- airyAi eq hankel1 neg complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel1_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (π * I / 3) * airyHankel1OnLog (-1 * (1 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  sorry

/-- airyAi eq hankel2 pos complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel2_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (-(2 * π * I / 3)) * airyHankel2OnLog (1 * (1 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  sorry

/-- airyAi eq hankel2 neg complex (DLMF 9.6.2). -/
@[dlmf 9.6.E2]
theorem airyAi_eq_hankel2_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) * exp (-(π * I / 3)) * airyHankel2OnLog (-1 * (1 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  sorry

/-- airyAiDeriv eq besselK complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_besselK_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyAiDeriv z = -(z / Real.sqrt 3) / π * airyBesselKOnLog (ε * (2 / 3)) (airyLogZeta z) := by
  sorry

/-- airyAiDeriv eq besselI complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = z / 3 * (airyBesselIOnLog (2 / 3) (airyLogZeta z) - airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyAiDeriv eq hankel1 pos complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel1_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-π * I / 6) * airyHankel1OnLog (1 * (2 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  sorry

/-- airyAiDeriv eq hankel1 neg complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel1_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-5 * π * I / 6) * airyHankel1OnLog (-1 * (2 / 3))
      (airyLogZeta z + 1 * (π * I / 2)) := by
  sorry

/-- airyAiDeriv eq hankel2 pos complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel2_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-(-π * I / 6)) * airyHankel2OnLog (1 * (2 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  sorry

/-- airyAiDeriv eq hankel2 neg complex (DLMF 9.6.3). -/
@[dlmf 9.6.E3]
theorem airyAiDeriv_eq_hankel2_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = 1 / 2 * (z / Real.sqrt 3) * exp (-(-5 * π * I / 6)) * airyHankel2OnLog (-1 * (2 / 3))
      (airyLogZeta z + -1 * (π * I / 2)) := by
  sorry

/-- airyBi eq besselI complex (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z = ((z / 3) ^ (1 / 2 : ℂ)) * (airyBesselIOnLog (1 / 3) (airyLogZeta z) + airyBesselIOnLog (-(1 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBi eq hankel pos complex (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (1 * (π * I / 6)) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(1 * (π * I / 6))) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z + π * I / 2)) := by
  sorry

/-- airyBi eq hankel neg complex (DLMF 9.6.4). -/
@[dlmf 9.6.E4]
theorem airyBi_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi z = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (-1 * (π * I / 6)) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(-1 * (π * I / 6))) * airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z + π * I / 2)) := by
  sorry

/-- airyBiDeriv eq besselI complex (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_besselI_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = (z / Real.sqrt 3) * (airyBesselIOnLog (2 / 3) (airyLogZeta z) + airyBesselIOnLog (-(2 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBiDeriv eq hankel pos complex (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = 1 / 2 * (z / Real.sqrt 3) *
      (exp (1 * (π * I / 3)) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(1 * (π * I / 3))) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z + π * I / 2)) := by
  sorry

/-- airyBiDeriv eq hankel neg complex (DLMF 9.6.5). -/
@[dlmf 9.6.E5]
theorem airyBiDeriv_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-1 * (π * I / 3)) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z - π * I / 2) +
        exp (-(-1 * (π * I / 3))) * airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z + π * I / 2)) := by
  sorry

/-- airyAi neg eq besselJ complex (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) = z ^ (1 / 2 : ℂ) / 3 * (airyBesselJOnLog (1 / 3) (airyLogZeta z) + airyBesselJOnLog (-1 / 3) (airyLogZeta z)) := by
  sorry

/-- airyAi neg eq hankel pos complex (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (π * I / 6) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z) +
        exp (-(π * I / 6)) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyAi neg eq hankel neg complex (DLMF 9.6.6). -/
@[dlmf 9.6.E6]
theorem airyAi_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (-π * I / 6) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 6)) * airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyAiDeriv neg eq besselJ complex (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) = z / 3 * (airyBesselJOnLog (2 / 3) (airyLogZeta z) - airyBesselJOnLog (-2 / 3) (airyLogZeta z)) := by
  sorry

/-- airyAiDeriv neg eq hankel pos complex (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-π * I / 6) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 6)) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyAiDeriv neg eq hankel neg complex (DLMF 9.6.7). -/
@[dlmf 9.6.E7]
theorem airyAiDeriv_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-5 * π * I / 6) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-5 * π * I / 6)) * airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBi neg eq besselJ complex (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) = ((z / 3) ^ (1 / 2 : ℂ)) * (airyBesselJOnLog (-(1 / 3)) (airyLogZeta z) - airyBesselJOnLog (1 / 3) (airyLogZeta z)) := by
  sorry

/-- airyBi neg eq hankel pos complex (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (2 * π * I / 3) * airyHankel1OnLog (1 * (1 / 3)) (airyLogZeta z) +
        exp (-(2 * π * I / 3)) * airyHankel2OnLog (1 * (1 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBi neg eq hankel neg complex (DLMF 9.6.8). -/
@[dlmf 9.6.E8]
theorem airyBi_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBi (-z) = 1 / 2 * ((z / 3) ^ (1 / 2 : ℂ)) *
      (exp (π * I / 3) * airyHankel1OnLog (-1 * (1 / 3)) (airyLogZeta z) +
        exp (-(π * I / 3)) * airyHankel2OnLog (-1 * (1 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBiDeriv neg eq besselJ complex (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_besselJ_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) = (z / Real.sqrt 3) * (airyBesselJOnLog (-(2 / 3)) (airyLogZeta z) + airyBesselJOnLog (2 / 3) (airyLogZeta z)) := by
  sorry

/-- airyBiDeriv neg eq hankel pos complex (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_hankel_pos_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (π * I / 3) * airyHankel1OnLog (1 * (2 / 3)) (airyLogZeta z) +
        exp (-(π * I / 3)) * airyHankel2OnLog (1 * (2 / 3)) (airyLogZeta z)) := by
  sorry

/-- airyBiDeriv neg eq hankel neg complex (DLMF 9.6.9). -/
@[dlmf 9.6.E9]
theorem airyBiDeriv_neg_eq_hankel_neg_complex {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv (-z) = 1 / 2 * (z / Real.sqrt 3) *
      (exp (-π * I / 3) * airyHankel1OnLog (-1 * (2 / 3)) (airyLogZeta z) +
        exp (-(-π * I / 3)) * airyHankel2OnLog (-1 * (2 / 3)) (airyLogZeta z)) := by
  sorry

/-- besselJ third eq airy complex (DLMF 9.6.11). -/
@[dlmf 9.6.E11]
theorem besselJ_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselJOnLog (ε * (1 / 3)) (airyLogZeta z) =
      1 / 2 * ((3 / z) ^ (1 / 2 : ℂ)) * (-1 * ε * Real.sqrt 3 * airyAi (-z) + airyBi (-z)) := by
  sorry

/-- besselJ two thirds eq airy complex (DLMF 9.6.12). -/
@[dlmf 9.6.E12]
theorem besselJ_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselJOnLog (ε * (2 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 / z) * (1 * ε * Real.sqrt 3 * airyAiDeriv (-z) + airyBiDeriv (-z)) := by
  sorry

/-- besselI third eq airy complex (DLMF 9.6.13). -/
@[dlmf 9.6.E13]
theorem besselI_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselIOnLog (ε * (1 / 3)) (airyLogZeta z) =
      1 / 2 * ((3 / z) ^ (1 / 2 : ℂ)) * (-1 * ε * Real.sqrt 3 * airyAi z + airyBi z) := by
  sorry

/-- besselI two thirds eq airy complex (DLMF 9.6.14). -/
@[dlmf 9.6.E14]
theorem besselI_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselIOnLog (ε * (2 / 3)) (airyLogZeta z) =
      1 / 2 * (Real.sqrt 3 / z) * (1 * ε * Real.sqrt 3 * airyAiDeriv z + airyBiDeriv z) := by
  sorry

/-- besselK third eq airy complex (DLMF 9.6.15). -/
@[dlmf 9.6.E15]
theorem besselK_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselKOnLog (ε * (1 / 3)) (airyLogZeta z) = (π * (3 / z) ^ (1 / 2 : ℂ)) * airyAi z := by
  sorry

/-- besselK two thirds eq airy complex (DLMF 9.6.16). -/
@[dlmf 9.6.E16]
theorem besselK_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    airyBesselKOnLog (ε * (2 / 3)) (airyLogZeta z) = (-π * Real.sqrt 3 / z) * airyAiDeriv z := by
  sorry

/-- hankel1 third eq airy complex (DLMF 9.6.17). -/
@[dlmf 9.6.E17]
theorem hankel1_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel1OnLog (1 / 3) (airyLogZeta z) = exp (-π * I / 6) * ((3 / z) ^ (1 / 2 : ℂ)) *
      (airyAi (-z) - I * airyBi (-z)) := by
  sorry

/-- hankel1 third neg order (DLMF 9.6.17). -/
@[dlmf 9.6.E17]
theorem hankel1_third_neg_order (w : ℂ) :
    airyHankel1OnLog (1 / 3) w = exp (-(1 / 3) * π * I) * airyHankel1OnLog (-(1 / 3)) w := by
  sorry

/-- hankel1 two thirds eq airy complex (DLMF 9.6.18). -/
@[dlmf 9.6.E18]
theorem hankel1_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel1OnLog (2 / 3) (airyLogZeta z) = exp (π * I / 6) * (Real.sqrt 3 / z) *
      (airyAiDeriv (-z) - I * airyBiDeriv (-z)) := by
  sorry

/-- hankel1 two thirds neg order (DLMF 9.6.18). -/
@[dlmf 9.6.E18]
theorem hankel1_two_thirds_neg_order (w : ℂ) :
    airyHankel1OnLog (2 / 3) w = exp (-(2 / 3) * π * I) * airyHankel1OnLog (-(2 / 3)) w := by
  sorry

/-- hankel2 third eq airy complex (DLMF 9.6.19). -/
@[dlmf 9.6.E19]
theorem hankel2_third_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel2OnLog (1 / 3) (airyLogZeta z) = exp (-(-π * I / 6)) * ((3 / z) ^ (1 / 2 : ℂ)) *
      (airyAi (-z) + I * airyBi (-z)) := by
  sorry

/-- hankel2 third neg order (DLMF 9.6.19). -/
@[dlmf 9.6.E19]
theorem hankel2_third_neg_order (w : ℂ) :
    airyHankel2OnLog (1 / 3) w = exp ((1 / 3) * π * I) * airyHankel2OnLog (-(1 / 3)) w := by
  sorry

/-- hankel2 two thirds eq airy complex (DLMF 9.6.20). -/
@[dlmf 9.6.E20]
theorem hankel2_two_thirds_eq_airy_complex {z : ℂ} (hz : z ≠ 0) :
    airyHankel2OnLog (2 / 3) (airyLogZeta z) = exp (-(π * I / 6)) * (Real.sqrt 3 / z) *
      (airyAiDeriv (-z) + I * airyBiDeriv (-z)) := by
  sorry

/-- hankel2 two thirds neg order (DLMF 9.6.20). -/
@[dlmf 9.6.E20]
theorem hankel2_two_thirds_neg_order (w : ℂ) :
    airyHankel2OnLog (2 / 3) w = exp ((2 / 3) * π * I) * airyHankel2OnLog (-(2 / 3)) w := by
  sorry

/-- airyAi eq whittakerW (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_whittakerW {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = (1 / (2 * Real.sqrt π)) * z ^ (-1 / 4 : ℂ) * whittakerW 0 (1 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- airyAi eq kummerU (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_kummerU {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerU (5 / 6) (5 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- airyAiDeriv eq whittakerW (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_whittakerW {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAiDeriv z = -(1 / (2 * Real.sqrt π)) * z ^ (1 / 4 : ℂ) * whittakerW 0 (2 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- airyAiDeriv eq kummerU (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_kummerU {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAiDeriv z = -((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerU (7 / 6) (7 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- airyBi eq whittakerM (DLMF 9.6.23). -/
@[dlmf 9.6.E23]
theorem airyBi_eq_whittakerM {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyBi z = z ^ (-1 / 4 : ℂ) *
      (whittakerM 0 (-1 / 3) (2 * airyZetaComplex z) / ((2 : ℂ) ^ (1 / 3 : ℂ) * Gamma (2 / 3)) +
        3 * whittakerM 0 (1 / 3) (2 * airyZetaComplex z) / ((2 : ℂ) ^ (5 / 3 : ℂ) * Gamma (1 / 3))) := by
  sorry

/-- airyBiDeriv eq whittakerM (DLMF 9.6.24). -/
@[dlmf 9.6.E24]
theorem airyBiDeriv_eq_whittakerM {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyBiDeriv z = z ^ (1 / 4 : ℂ) *
      ((2 : ℂ) ^ (1 / 3 : ℂ) * whittakerM 0 (-2 / 3) (2 * airyZetaComplex z) / Gamma (1 / 3) +
        3 * whittakerM 0 (2 / 3) (2 * airyZetaComplex z) / ((2 : ℂ) ^ (10 / 3 : ℂ) * Gamma (2 / 3))) := by
  sorry

/-- airyBi eq kummerM (DLMF 9.6.25). -/
@[dlmf 9.6.E25]
theorem airyBi_eq_kummerM {z : ℂ} (hz : z ≠ 0) :
    airyBi z = (1 / ((3 : ℂ) ^ (1 / 6 : ℂ) * Gamma (2 / 3))) * exp (-airyZetaComplex z) * kummerM (1 / 6) (1 / 3) (2 * airyZetaComplex z) +
      ((3 : ℂ) ^ (5 / 6 : ℂ) / ((2 : ℂ) ^ (2 / 3 : ℂ) * Gamma (1 / 3))) * exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerM (5 / 6) (5 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- airyBiDeriv eq kummerM (DLMF 9.6.26). -/
@[dlmf 9.6.E26]
theorem airyBiDeriv_eq_kummerM {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = ((3 : ℂ) ^ (1 / 6 : ℂ) / Gamma (1 / 3)) * exp (-airyZetaComplex z) * kummerM (-1 / 6) (-1 / 3) (2 * airyZetaComplex z) +
      ((3 : ℂ) ^ (7 / 6 : ℂ) / ((2 : ℂ) ^ (7 / 3 : ℂ) * Gamma (2 / 3))) * exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerM (7 / 6) (7 / 3) (2 * airyZetaComplex z) := by
  sorry

/-- Whittaker M on the logarithmic argument plane. -/
def airyWhittakerMOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2 + (μ + 1 / 2) * w) * kummerM (μ - κ + 1 / 2) (1 + 2 * μ) (exp w)
/-- Whittaker W on the logarithmic plane at nonintegral second Kummer parameter. -/
def airyWhittakerWOnLog (κ μ w : ℂ) : ℂ :=
  exp (-exp w / 2 + (μ + 1 / 2) * w) * kummerUOnLog (μ - κ + 1 / 2) (1 + 2 * μ) w

/-- The continued Whittaker representation without reducing the argument of ζ (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_whittakerW_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAi z = (1 / (2 * Real.sqrt π)) * z ^ (-1 / 4 : ℂ) *
      airyWhittakerWOnLog 0 (1 / 3) (log 2 + airyLogZeta z) := by
  sorry

/-- The continued Tricomi representation with the inherited logarithm (DLMF 9.6.21). -/
@[dlmf 9.6.E21]
theorem airyAi_eq_kummerU_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAi z = ((3 : ℂ) ^ (-1 / 6 : ℂ) / Real.sqrt π) *
      exp ((2 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerUOnLog (5 / 6) (5 / 3) (log 2 + airyLogZeta z) := by
  sorry

/-- The continued Whittaker representation without reducing the argument of ζ (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_whittakerW_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = -(1 / (2 * Real.sqrt π)) * z ^ (1 / 4 : ℂ) *
      airyWhittakerWOnLog 0 (2 / 3) (log 2 + airyLogZeta z) := by
  sorry

/-- The continued Tricomi representation with the inherited logarithm (DLMF 9.6.22). -/
@[dlmf 9.6.E22]
theorem airyAiDeriv_eq_kummerU_onLog {z : ℂ} (hz : z ≠ 0) :
    airyAiDeriv z = -((3 : ℂ) ^ (1 / 6 : ℂ) / Real.sqrt π) *
      exp ((4 / 3) * airyLogZeta z - airyZetaComplex z) *
        kummerUOnLog (7 / 6) (7 / 3) (log 2 + airyLogZeta z) := by
  sorry

/-- The full logarithmic-plane Whittaker M representation (DLMF 9.6.23). -/
@[dlmf 9.6.E23]
theorem airyBi_eq_whittakerM_onLog {z : ℂ} (hz : z ≠ 0) :
    airyBi z = z ^ (-1 / 4 : ℂ) * (airyWhittakerMOnLog 0 (-1 / 3) (log 2 + airyLogZeta z) / ((2 : ℂ) ^ (1 / 3 : ℂ) * Gamma (2 / 3)) +
        3 * airyWhittakerMOnLog 0 (1 / 3) (log 2 + airyLogZeta z) / ((2 : ℂ) ^ (5 / 3 : ℂ) * Gamma (1 / 3))) := by
  sorry

/-- The full logarithmic-plane Whittaker M representation (DLMF 9.6.24). -/
@[dlmf 9.6.E24]
theorem airyBiDeriv_eq_whittakerM_onLog {z : ℂ} (hz : z ≠ 0) :
    airyBiDeriv z = z ^ (1 / 4 : ℂ) * ((2 : ℂ) ^ (1 / 3 : ℂ) * airyWhittakerMOnLog 0 (-2 / 3) (log 2 + airyLogZeta z) / Gamma (1 / 3) +
        3 * airyWhittakerMOnLog 0 (2 / 3) (log 2 + airyLogZeta z) / ((2 : ℂ) ^ (10 / 3 : ℂ) * Gamma (2 / 3))) := by
  sorry

end AAR.Airy
