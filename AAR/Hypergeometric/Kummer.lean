/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Hypergeometric.Solutions
public import AAR.Hypergeometric.Continuation

/-!
# Kummer's representations and connections (DLMF §15.10(ii))

E11 is already the Euler/Pfaff family in `Transformations` and
`FurtherTransformations`. E12–E16 give the remaining representations, on
overlaps of series disks. Explicit upper-half-plane hypotheses fix the phases
in E15–E16 and in connections involving infinity. Separate charts avoid
assigning analytic-continuation values to divergent Mathlib series.
E17–E18/E21–E22 are in `Solutions`. E19–E20/E25–E26 use the left chart;
E23–E24/E27–E28 use the chart at infinity. E29–E36 mix all three centers;
their series charts have no common open domain and need global continuation.
-/

@[expose] public section

open Complex Filter
open scoped Real Topology

noncomputable section

namespace AAR.Hypergeometric

/-- Kummer's fifth solution on the local chart at infinity. -/
@[dlmf 15.10.E15]
def kummerFive (a b c z : ℂ) : ℂ := exp (a * Real.pi * I) * infinityFirst a b c z

/-- Kummer's sixth solution on the local chart at infinity. -/
@[dlmf 15.10.E16]
def kummerSix (a b c z : ℂ) : ℂ := exp (b * Real.pi * I) * infinityFirst b a c z

/-- A second chart for Kummer's fifth solution, overlapping the disk at zero. -/
@[dlmf 15.10.E15]
def kummerFiveLeft (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (-a) * ₂F₁ a (c - b) (a - b + 1) (1 / (1 - z))

/-- A second chart for Kummer's sixth solution. -/
@[dlmf 15.10.E16]
def kummerSixLeft (a b c z : ℂ) : ℂ :=
  (1 - z) ^ (-b) * ₂F₁ b (c - a) (b - a + 1) (1 / (1 - z))

@[dlmf 15.10.E12]
theorem zero_second_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, 2 - c ≠ -(k : ℂ))
    (hz : ‖z‖ < 1)
    (hs : z ∈ slitPlane)
    (hw : ‖z /
    (z - 1)‖ < 1) :
    zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (1 - b) (2 - c) z ∧
      zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - 1) * ₂F₁ (a - c + 1) (1 - b) (2 - c) (z / (z - 1)) ∧
      zeroSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - b - 1) * ₂F₁ (1 - a) (b - c + 1) (2 - c) (z / (z -
        1)) := by
  refine ⟨?_, ?_, ?_⟩
  · unfold zeroSecond
    rw [euler_transformation_of_ne_neg_nat hc hz,
      show 2 - c - (a - c + 1) - (b - c + 1) = c - a - b by ring,
      show 2 - c - (a - c + 1) = 1 - a by ring, show 2 - c - (b - c + 1) = 1 - b by ring]
    ring
  · unfold zeroSecond
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw, show -(a - c + 1) = c - a - 1 by ring,
      show 2 - c - (b - c + 1) = 1 - b by ring]
    ring
  · unfold zeroSecond
    rw [show (₂F₁ (a - c + 1) (b - c + 1) (2 - c) : ℂ → ℂ) = ₂F₁ (b - c + 1) (a - c + 1) (2 - c) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw,
      show -(b - c + 1) = c - b - 1 by ring, show 2 - c - (a - c + 1) = 1 - a by ring,
      show (₂F₁ (b - c + 1) (1 - a) (2 - c) : ℂ → ℂ) = ₂F₁ (1 - a) (b - c + 1) (2 - c) from
      ordinaryHypergeometric_symm _ _ _]
    ring

@[dlmf 15.10.E13]
theorem one_first_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a + b - c + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hw : ‖1 - 1 / z‖ < 1) :
    oneFirst a b c z = z ^ (1 - c) * ₂F₁ (a - c + 1) (b - c + 1) (a + b - c + 1) (1 - z) ∧
      oneFirst a b c z = z ^ (-a) * ₂F₁ a (a - c + 1) (a + b - c + 1) (1 - 1 / z) ∧
      oneFirst a b c z = z ^ (-b) * ₂F₁ b (b - c + 1) (a + b - c + 1) (1 - 1 / z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hw
  have hmap : (1 - z) / (1 - z - 1) = 1 - 1 / z := by
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    field_simp
    try ring
  have hw' : ‖(1 - z) / (1 - z - 1)‖ < 1 := by rwa [hmap]
  refine ⟨?_, ?_, ?_⟩
  · unfold oneFirst
    rw [euler_transformation_of_ne_neg_nat hc hz, sub_sub_cancel,
      show a + b - c + 1 - a - b = 1 - c by ring, show a + b - c + 1 - a = b - c + 1 by ring,
      show a + b - c + 1 - b = a - c + 1 by ring,
      show (₂F₁ (b - c + 1) (a - c + 1) (a + b - c + 1) : ℂ → ℂ) =
        ₂F₁ (a - c + 1) (b - c + 1) (a + b - c + 1) from ordinaryHypergeometric_symm _ _ _]
  · unfold oneFirst
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw', sub_sub_cancel, hmap,
      show a + b - c + 1 - b = a - c + 1 by ring]
  · unfold oneFirst
    rw [show (₂F₁ a b (a + b - c + 1) : ℂ → ℂ) = ₂F₁ b a (a + b - c + 1) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw',
      sub_sub_cancel, hmap, show a + b - c + 1 - a = b - c + 1 by ring]

@[dlmf 15.10.E14]
theorem one_second_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, c - a - b + 1 ≠ -(k : ℂ))
    (hz : ‖1 - z‖ < 1)
    (hs : 1 - z ∈ slitPlane)
    (hw : ‖1 - 1 / z‖ < 1) :
    oneSecond a b c z = z ^ (1 - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (1 - b) (c - a - b + 1) (1 - z) ∧
      oneSecond a b c z = z ^ (a - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (c - a) (c - a - b + 1) (1 - 1 /
        z) ∧
      oneSecond a b c z = z ^ (b - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - b) (c - b) (c - a - b + 1) (1 - 1 /
        z) := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hw
  have hmap : (1 - z) / (1 - z - 1) = 1 - 1 / z := by
    rw [show (1 : ℂ) - z - 1 = -z by ring]
    field_simp
    try ring
  have hw' : ‖(1 - z) / (1 - z - 1)‖ < 1 := by rwa [hmap]
  refine ⟨?_, ?_, ?_⟩
  · unfold oneSecond
    rw [euler_transformation_of_ne_neg_nat hc hz, sub_sub_cancel,
      show c - a - b + 1 - (c - a) - (c - b) = 1 - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring, show c - a - b + 1 - (c - b) = 1 - a by ring,
      show (₂F₁ (1 - b) (1 - a) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - a) (1 - b) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring
  · unfold oneSecond
    rw [pfaff_transformation_of_ne_neg_nat hc hz hw', sub_sub_cancel, hmap,
      show -(c - a) = a - c by ring, show c - a - b + 1 - (c - b) = 1 - a by ring,
      show (₂F₁ (c - a) (1 - a) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - a) (c - a) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring
  · unfold oneSecond
    rw [show (₂F₁ (c - a) (c - b) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (c - b) (c - a) (c - a - b + 1) from
      ordinaryHypergeometric_symm _ _ _, pfaff_transformation_of_ne_neg_nat hc hz hw',
      sub_sub_cancel, hmap, show -(c - b) = b - c by ring,
      show c - a - b + 1 - (c - a) = 1 - b by ring,
      show (₂F₁ (c - b) (1 - b) (c - a - b + 1) : ℂ → ℂ) = ₂F₁ (1 - b) (c - b) (c - a - b + 1) from
        ordinaryHypergeometric_symm _ _ _]
    ring

@[dlmf 15.10.E15]
theorem kummer_five_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, a - b + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hw : 1 < ‖1 - z‖)
    (hi : 0 < z.im) :
    kummerFive a b c z = exp ((c - b) * Real.pi * I) * z ^ (b - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - b) (c
      - b) (a - b + 1) (1 / z) ∧
      kummerFive a b c z = kummerFiveLeft a b c z ∧
      kummerFive a b c z = exp ((c - 1) * Real.pi * I) * z ^ (1 - c) * (1 - z) ^ (c - a - 1) * ₂F₁ (1 - b)
        (a - c + 1) (a - b + 1) (1 / (1 - z)) := by
  sorry

@[dlmf 15.10.E16]
theorem kummer_six_representations
    {a b c z : ℂ}
    (hc : ∀ k : ℕ, b - a + 1 ≠ -(k : ℂ))
    (hz : 1 < ‖z‖)
    (hw : 1 < ‖1 - z‖)
    (hi : 0 < z.im) :
    kummerSix a b c z = exp ((c - a) * Real.pi * I) * z ^ (a - c) * (1 - z) ^ (c - a - b) * ₂F₁ (1 - a) (c -
      a) (b - a + 1) (1 / z) ∧
      kummerSix a b c z = kummerSixLeft a b c z ∧
      kummerSix a b c z = exp ((c - 1) * Real.pi * I) * z ^ (1 - c) * (1 - z) ^ (c - b - 1) * ₂F₁ (1 - a) (b
        - c + 1) (b - a + 1) (1 / (1 - z)) := by
  sorry

@[dlmf 15.10.E19]
theorem kummer_five_left_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    kummerFiveLeft a b c z =
      Gamma (1 - c) * Gamma (a - b + 1) / (Gamma (a - c + 1) * Gamma (1 - b)) * ₂F₁ a b c z + exp ((c - 1) *
        Real.pi * I) * Gamma (c - 1) * Gamma (a - b + 1) / (Gamma a * Gamma (c - b)) * zeroSecond a b c z :=
        by
  sorry

@[dlmf 15.10.E20]
theorem kummer_six_left_connection_zero {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    kummerSixLeft a b c z =
      Gamma (1 - c) * Gamma (b - a + 1) / (Gamma (b - c + 1) * Gamma (1 - a)) * ₂F₁ a b c z + exp ((c - 1) *
        Real.pi * I) * Gamma (c - 1) * Gamma (b - a + 1) / (Gamma b * Gamma (c - a)) * zeroSecond a b c z :=
        by
  sorry

@[dlmf 15.10.E25]
theorem zero_first_connection_left {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    ₂F₁ a b c z =
      Gamma c * Gamma (b - a) / (Gamma b * Gamma (c - a)) * kummerFiveLeft a b c z + Gamma c * Gamma (a - b)
        / (Gamma a * Gamma (c - b)) * kummerSixLeft a b c z := by
  sorry

@[dlmf 15.10.E26]
theorem zero_second_connection_left {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : ‖z‖ < 1) (hw : 1 < ‖1 - z‖) (hi : 0 < z.im) :
    zeroSecond a b c z =
      exp ((1 - c) * Real.pi * I) * Gamma (2 - c) * Gamma (b - a) / (Gamma (1 - a) * Gamma (b - c + 1)) *
        kummerFiveLeft a b c z + exp ((1 - c) * Real.pi * I) * Gamma (2 - c) * Gamma (a - b) / (Gamma (1 -
        b) * Gamma (a - c + 1)) * kummerSixLeft a b c z := by
  sorry

@[dlmf 15.10.E23]
theorem kummer_five_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    kummerFive a b c z =
      exp (a * Real.pi * I) * Gamma (a - b + 1) * Gamma (c - a - b) / (Gamma (1 - b) * Gamma (c - b)) *
        oneFirst a b c z + exp ((c - b) * Real.pi * I) * Gamma (a - b + 1) * Gamma (a + b - c) / (Gamma a *
        Gamma (a - c + 1)) * oneSecond a b c z := by
  sorry

@[dlmf 15.10.E24]
theorem kummer_six_connection_one {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    kummerSix a b c z =
      exp (b * Real.pi * I) * Gamma (b - a + 1) * Gamma (c - a - b) / (Gamma (1 - a) * Gamma (c - a)) *
        oneFirst a b c z + exp ((c - a) * Real.pi * I) * Gamma (b - a + 1) * Gamma (a + b - c) / (Gamma b *
        Gamma (b - c + 1)) * oneSecond a b c z := by
  sorry

@[dlmf 15.10.E27]
theorem one_first_connection_infinity {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    oneFirst a b c z =
      exp (-a * Real.pi * I) * Gamma (a + b - c + 1) * Gamma (b - a) / (Gamma b * Gamma (b - c + 1)) *
        kummerFive a b c z + exp (-b * Real.pi * I) * Gamma (a + b - c + 1) * Gamma (a - b) / (Gamma a *
        Gamma (a - c + 1)) * kummerSix a b c z := by
  sorry

@[dlmf 15.10.E28]
theorem one_second_connection_infinity {a b c z : ℂ} (hc : ∀ k : ℤ, c ≠ (k : ℂ))
    (he : ∀ k : ℤ, c - a - b ≠ (k : ℂ)) (hab : ∀ k : ℤ, a - b ≠ (k : ℂ))
    (hz : 1 < ‖z‖) (hw : ‖1 - z‖ < 1) (hi : 0 < z.im) :
    oneSecond a b c z =
      exp ((b - c) * Real.pi * I) * Gamma (c - a - b + 1) * Gamma (b - a) / (Gamma (1 - a) * Gamma (c - a))
        * kummerFive a b c z + exp ((a - c) * Real.pi * I) * Gamma (c - a - b + 1) * Gamma (a - b) / (Gamma
        (1 - b) * Gamma (c - b)) * kummerSix a b c z := by
  sorry

end AAR.Hypergeometric
