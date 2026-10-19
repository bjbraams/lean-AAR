/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Zeros
public import AAR.Airy.Scorer
public import AAR.Airy.Asymptotics

/-!
# DLMF Airy numerical tables and initial decimal intervals

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- The rounded χ(1) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_1  :
    |airyChi 1 - (1.57 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(6) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_6  :
    |airyChi 6 - (3.20 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(11) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_11  :
    |airyChi 11 - (4.25 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(16) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_16  :
    |airyChi 16 - (5.09 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(2) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_2  :
    |airyChi 2 - (2.00 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(7) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_7  :
    |airyChi 7 - (3.44 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(12) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_12  :
    |airyChi 12 - (4.43 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(17) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_17  :
    |airyChi 17 - (5.24 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(3) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_3  :
    |airyChi 3 - (2.36 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(8) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_8  :
    |airyChi 8 - (3.66 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(13) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_13  :
    |airyChi 13 - (4.61 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(18) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_18  :
    |airyChi 18 - (5.39 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(4) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_4  :
    |airyChi 4 - (2.67 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(9) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_9  :
    |airyChi 9 - (3.87 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(14) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_14  :
    |airyChi 14 - (4.77 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(19) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_19  :
    |airyChi 19 - (5.54 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(5) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_5  :
    |airyChi 5 - (2.95 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(10) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_10  :
    |airyChi 10 - (4.06 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(15) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_15  :
    |airyChi 15 - (4.94 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The rounded χ(20) entry in DLMF Table 9.7.1, with its two-decimal accuracy. -/
theorem airyChi_table_20  :
    |airyChi 20 - (5.68 : ℝ)| ≤ 1 / 200 := by
  sorry

/-- The four rounded entries in row 1 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_1  :
    |(airyAiZero 1) - (-2.3381074105 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 1)) - (0.7012108227 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 1) - (-1.0187929716 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 1)) - (0.5356566560 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 2 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_2  :
    |(airyAiZero 2) - (-4.0879494441 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 2)) - (-0.8031113697 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 2) - (-3.2481975822 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 2)) - (-0.4190154780 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 3 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_3  :
    |(airyAiZero 3) - (-5.5205598281 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 3)) - (0.8652040259 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 3) - (-4.8200992112 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 3)) - (0.3804064686 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 4 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_4  :
    |(airyAiZero 4) - (-6.7867080901 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 4)) - (-0.9108507370 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 4) - (-6.1633073556 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 4)) - (-0.3579079437 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 5 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_5  :
    |(airyAiZero 5) - (-7.9441335871 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 5)) - (0.9473357094 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 5) - (-7.3721772550 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 5)) - (0.3423012444 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 6 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_6  :
    |(airyAiZero 6) - (-9.0226508533 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 6)) - (-0.9779228086 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 6) - (-8.4884867340 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 6)) - (-0.3304762291 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 7 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_7  :
    |(airyAiZero 7) - (-10.0401743416 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 7)) - (1.0043701227 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 7) - (-9.5354490524 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 7)) - (0.3210222882 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 8 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_8  :
    |(airyAiZero 8) - (-11.0085243037 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 8)) - (-1.0277386888 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 8) - (-10.5276603970 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 8)) - (-0.3131853910 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 9 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_9  :
    |(airyAiZero 9) - (-11.9360155632 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 9)) - (1.0487206486 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 9) - (-11.4750566335 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 9)) - (0.3065172939 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 10 of DLMF Table 9.9.1, to ten decimal places. -/
theorem airy_zero_table_1_row_10  :
    |(airyAiZero 10) - (-12.8287767529 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivReal (airyAiZero 10)) - (-1.0677938592 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiDerivZero 10) - (-12.3847883718 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyAiReal (airyAiDerivZero 10)) - (-0.3007308293 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 1 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_1  :
    |(airyBiZero 1) - (-1.1737132227 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 1)) - (0.6019578880 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 1) - (-2.2944396826 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 1)) - (-0.4549443836 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 2 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_2  :
    |(airyBiZero 2) - (-3.2710933028 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 2)) - (-0.7603101415 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 2) - (-4.0731550891 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 2)) - (0.3965228361 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 3 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_3  :
    |(airyBiZero 3) - (-4.8307378417 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 3)) - (0.8369910126 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 3) - (-5.5123957297 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 3)) - (-0.3679691615 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 4 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_4  :
    |(airyBiZero 4) - (-6.1698521283 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 4)) - (-0.8894799014 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 4) - (-6.7812944460 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 4)) - (0.3494991168 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 5 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_5  :
    |(airyBiZero 5) - (-7.3767620794 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 5)) - (0.9299836386 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 5) - (-7.9401786892 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 5)) - (-0.3360262401 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 6 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_6  :
    |(airyBiZero 6) - (-8.4919488465 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 6)) - (-0.9632344302 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 6) - (-9.0195833588 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 6)) - (0.3255097364 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 7 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_7  :
    |(airyBiZero 7) - (-9.5381943793 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 7)) - (0.9915863705 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 7) - (-10.0376963349 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 7)) - (-0.3169346537 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 8 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_8  :
    |(airyBiZero 8) - (-10.5299135067 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 8)) - (-1.0163896592 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 8) - (-11.0064626677 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 8)) - (0.3097259408 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 9 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_9  :
    |(airyBiZero 9) - (-11.4769535513 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 9)) - (1.0384942860 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 9) - (-11.9342616450 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 9)) - (-0.3035276648 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 10 of DLMF Table 9.9.2, to ten decimal places. -/
theorem airy_zero_table_2_row_10  :
    |(airyBiZero 10) - (-12.3864171386 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivReal (airyBiZero 10)) - (-1.0584718444 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiDerivZero 10) - (-12.8272583092 : ℝ)| ≤ 1 / 20000000000 ∧
      |(airyBiReal (airyBiDerivZero 10)) - (0.2981049111 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 1 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_1  :
    |(‖airyBiComplexZero 1‖) - (2.3538733809 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 1))) - (0.0953349591 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 1)‖) - (0.9931068457 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 1))) - (2.6406002521 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 2 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_2  :
    |(‖airyBiComplexZero 2‖) - (4.0932873094 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 2))) - (0.0417855604 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 2)‖) - (1.1361283345 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 2))) - (-0.5132828720 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 3 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_3  :
    |(‖airyBiComplexZero 3‖) - (5.5235035011 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 3))) - (0.0266805442 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 3)‖) - (1.2237437881 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 3))) - (2.6246283591 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 4 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_4  :
    |(‖airyBiComplexZero 4‖) - (6.7886595301 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 4))) - (0.0195869751 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 4)‖) - (1.2882292493 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 4))) - (-0.5187163829 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 5 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_5  :
    |(‖airyBiComplexZero 5‖) - (7.9455590160 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 5))) - (0.0154708228 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 5)‖) - (1.3397947726 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 5))) - (2.6218544560 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 6 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_6  :
    |(‖airyBiComplexZero 6‖) - (9.0237563663 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 6))) - (0.0127834808 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 6)‖) - (1.3830339005 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 6))) - (-0.5204069437 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 7 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_7  :
    |(‖airyBiComplexZero 7‖) - (10.0410673680 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 7))) - (0.0108912610 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 7)‖) - (1.4204253456 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 7))) - (2.6207141895 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 8 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_8  :
    |(‖airyBiComplexZero 8‖) - (11.0092672579 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 8))) - (0.0094868445 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 8)‖) - (1.4534664633 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 8))) - (-0.5212287219 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 9 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_9  :
    |(‖airyBiComplexZero 9‖) - (11.9366476131 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 9))) - (0.0084031785 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 9)‖) - (1.4831345656 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 9))) - (2.6200935195 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 10 of DLMF Table 9.9.3, to ten decimal places. -/
theorem airy_zero_table_3_row_10  :
    |(‖airyBiComplexZero 10‖) - (12.8293239388 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiComplexZero 10))) - (0.0075416607 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBiDeriv (airyBiComplexZero 10)‖) - (1.5101046383 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBiDeriv (airyBiComplexZero 10))) - (-0.5217141947 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 1 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_1  :
    |(‖airyBiDerivComplexZero 1‖) - (1.1213932942 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 1))) - (0.3307266208 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 1)‖) - (0.7500414897 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 1))) - (0.4659778930 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 2 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_2  :
    |(‖airyBiDerivComplexZero 2‖) - (3.2569082266 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 2))) - (0.0593899367 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 2)‖) - (0.5922166315 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 2))) - (-2.6323540329 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 3 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_3  :
    |(‖airyBiDerivComplexZero 3‖) - (4.8240026102 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 3))) - (0.0327856423 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 3)‖) - (0.5378706321 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 3))) - (0.5154932992 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 4 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_4  :
    |(‖airyBiDerivComplexZero 4‖) - (6.1656866408 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 4))) - (0.0226624588 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 4)‖) - (0.5061102160 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 4))) - (-2.6236285920 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 5 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_5  :
    |(‖airyBiDerivComplexZero 5‖) - (7.3738379870 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 5))) - (0.0173196481 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 5)‖) - (0.4840600643 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 5))) - (0.5192828169 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 6 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_6  :
    |(‖airyBiDerivComplexZero 6‖) - (8.4897385596 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 6))) - (0.0140165283 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 6)‖) - (0.4673468449 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 6))) - (-2.6214905716 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 7 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_7  :
    |(‖airyBiDerivComplexZero 7‖) - (9.5364407072 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 7))) - (0.0117719311 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 7)‖) - (0.4539823240 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 7))) - (0.5206602139 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 8 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_8  :
    |(‖airyBiDerivComplexZero 8‖) - (10.5284737502 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 8))) - (0.0101471783 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 8)‖) - (0.4429025018 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 8))) - (-2.6205278353 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 9 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_9  :
    |(‖airyBiDerivComplexZero 9‖) - (11.4757411237 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 9))) - (0.0089166153 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 9)‖) - (0.4334744668 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 9))) - (0.5213715495 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The four rounded entries in row 10 of DLMF Table 9.9.4, to ten decimal places. -/
theorem airy_zero_table_4_row_10  :
    |(‖airyBiDerivComplexZero 10‖) - (12.3853759341 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (exp (-π * I / 3) * (airyBiDerivComplexZero 10))) - (0.0079522843 : ℝ)| ≤ 1 / 20000000000 ∧
      |(‖airyBi (airyBiDerivComplexZero 10)‖) - (0.4252925837 : ℝ)| ≤ 1 / 20000000000 ∧
      |(arg (airyBi (airyBiDerivComplexZero 10))) - (-2.6199805803 : ℝ)| ≤ 1 / 20000000000 := by
  sorry

/-- The truncated decimal initial value in DLMF §9.2(ii). -/
theorem airyAiReal_decimal_zero  :
    (0.3550280538 : ℝ) ≤ airyAiReal 0 ∧ airyAiReal 0 < (0.3550280538 : ℝ) + 1 / 10000000000 := by
  sorry

/-- The truncated decimal initial value in DLMF §9.2(ii). -/
theorem airyAiDerivReal_decimal_zero  :
    (-0.2588194037 : ℝ) - 1 / 10000000000 < airyAiDerivReal 0 ∧ airyAiDerivReal 0 ≤ (-0.2588194037 : ℝ) := by
  sorry

/-- The truncated decimal initial value in DLMF §9.2(ii). -/
theorem airyBiReal_decimal_zero  :
    (0.6149266274 : ℝ) ≤ airyBiReal 0 ∧ airyBiReal 0 < (0.6149266274 : ℝ) + 1 / 10000000000 := by
  sorry

/-- The truncated decimal initial value in DLMF §9.2(ii). -/
theorem airyBiDerivReal_decimal_zero  :
    (0.4482883573 : ℝ) ≤ airyBiDerivReal 0 ∧ airyBiDerivReal 0 < (0.4482883573 : ℝ) + 1 / 10000000000 := by
  sorry

/-- The truncated decimal initial value in DLMF §9.12(iii). -/
theorem scorerGi_decimal_zero  :
    (0.2049755424 : ℝ) ≤ (scorerGi 0).re ∧ (scorerGi 0).re < (0.2049755424 : ℝ) + 1 / 10000000000 := by
  sorry

/-- The truncated decimal initial value in DLMF §9.12(iii). -/
theorem scorerGiDeriv_decimal_zero  :
    (0.1494294524 : ℝ) ≤ (scorerGiDeriv 0).re ∧ (scorerGiDeriv 0).re < (0.1494294524 : ℝ) + 1 / 10000000000 := by
  sorry

/-- The nonnegative Gi' zero stated in DLMF §9.12(ix). -/
theorem scorerGiDeriv_positive_zero_decimal  :
    ∃ x : ℝ, (0.60907541707 : ℝ) ≤ x ∧ x < (0.60907541707 : ℝ) + 1 / 100000000000 ∧ scorerGiDeriv x = 0 := by
  sorry

end AAR.Airy
