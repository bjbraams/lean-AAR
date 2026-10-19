/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Conical
public import AAR.Legendre.SpecialValues

/-!
# Real Legendre zero counts and interlacing

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

attribute [local instance] Classical.propDecidable

/-- legendreIntegerPart. -/
@[dlmf 14.16.E1]
def legendreIntegerPart (μ : ℝ) : ℤ :=
  ⌊μ⌋

/-- legendreFractionalPart. -/
@[dlmf 14.16.E1]
def legendreFractionalPart (μ : ℝ) : ℝ :=
  μ-⌊μ⌋

/-- ferrersZeroSet. -/
def ferrersZeroSet (second : Bool) (ν μ : ℝ) : Set ℝ :=
  {x : ℝ | x ∈ Ioo (-1:ℝ) 1 ∧ (if second then ferrersQ ν μ x else ferrersP ν μ x)=0}

/-- Extra-zero cases in DLMF 14.16(ii), away from integer parameters. -/
def ferrersPExtraZero (ν μ : ℝ) : Bool :=
  decide (0 < μ ∧ ((⌊μ⌋ < ⌊ν⌋ ∧ legendreFractionalPart ν ≤ legendreFractionalPart μ) ∨ (⌊ν⌋ < ⌊μ⌋ ∧ Even (⌊μ⌋-⌊ν⌋))))

/-- Nonintegral parameter zero count from DLMF 14.16(ii). -/
theorem ferrersP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hνn : ∀ n : ℤ, ν ≠ n) (hμn : ∀ n : ℤ, μ ≠ n) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat+(if ferrersPExtraZero ν μ then 1 else 0) := by
  sorry

/-- The nonpositive-order case, including integral parameters. -/
theorem ferrersP_nonpositive_order_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hμ : μ ≤ 0) :
    Set.Finite (ferrersZeroSet false ν μ) ∧ (ferrersZeroSet false ν μ).ncard=(max (⌈ν-|μ|⌉:ℤ) 0).toNat := by
  sorry

/-- Integer-degree case excludes the identically zero solution when integral order exceeds degree. -/
theorem ferrersP_nat_degree_zero_count (n : ℕ) (μ : ℝ) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP n μ x ≠ 0) :
    Set.Finite (ferrersZeroSet false n μ) ∧ (ferrersZeroSet false n μ).ncard=(max (⌈(n:ℝ)-|μ|⌉:ℤ) 0).toNat := by
  sorry

/-- DLMF 14.16(ii): the n+1 zeros of Q_n. -/
theorem ferrersQ_nat_zero_count (n : ℕ) :
    Set.Finite (ferrersZeroSet true n 0) ∧ (ferrersZeroSet true n 0).ncard=n+1 := by
  sorry

/-- Separation of successive distinct zeros in both directions. -/
def InterlacesZeros (S T : Set ℝ) : Prop :=
  (∀ a ∈ S, ∀ b ∈ S, a < b → (¬∃ c ∈ S, a < c ∧ c < b) → ∃! c : ℝ, c ∈ T ∧ a < c ∧ c < b) ∧ (∀ a ∈ T, ∀ b ∈ T, a < b → (¬∃ c ∈ T, a < c ∧ c < b) → ∃! c : ℝ, c ∈ S ∧ a < c ∧ c < b)

/-- The Wronskian must be nonzero; degenerate proportional solutions do not interlace. -/
theorem ferrersPQ_interlace {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    InterlacesZeros (ferrersZeroSet false ν μ) (ferrersZeroSet true ν μ) := by
  sorry

/-- Count range and parity in DLMF 14.16(ii), on the nondegenerate domain. -/
theorem ferrersQ_zero_count_range {ν μ : ℝ} (hν : -1/2 ≤ ν) (hr : LegendreQRegular ν μ) (hind : Gamma (ν+μ+1)/Gamma (ν-μ+1) ≠ 0) :
    Set.Finite (ferrersZeroSet true ν μ) ∧ ∃ k : ℤ, k ∈ Finset.Icc (-1) 2 ∧ ((ferrersZeroSet true ν μ).ncard:ℤ)=max (⌈ν-|μ|⌉:ℤ) 0+k ∧ (Real.cos (ν*π)*Real.cos (μ*π) < 0 → Even ((ferrersZeroSet true ν μ).ncard:ℤ)) ∧ (0 < Real.cos (ν*π)*Real.cos (μ*π) → Odd ((ferrersZeroSet true ν μ).ncard:ℤ)) := by
  sorry

/-- associatedPOneZero. -/
def associatedPOneZero (ν μ : ℝ) : Prop :=
  (0 < μ ∧ ν < μ ∧ (∀ n : ℤ, μ ≠ n) ∧ Real.sin ((μ-ν)*π)*Real.sin (μ*π) < 0) ∨ (μ ≤ ν ∧ (∀ n : ℤ, μ ≠ n) ∧ Odd (⌊μ⌋:ℤ))

/-- Exactly one or no exterior zeros, excluding an identically zero solution. -/
theorem associatedP_zero_count {ν μ : ℝ} (hν : -1/2 ≤ ν) (hnondeg : ∃ x : ℝ, 1 < x ∧ associatedP ν μ x ≠ 0) :
    Set.Finite {x : ℝ | 1 < x ∧ associatedP ν μ x=0} ∧ ({x : ℝ | 1 < x ∧ associatedP ν μ x=0}:Set ℝ).ncard=if associatedPOneZero ν μ then 1 else 0 := by
  sorry

/-- DLMF 14.16(iii): no exterior zeros for degree greater than minus one. -/
theorem olverQ_no_exterior_zero {ν μ : ℝ} (hν : -1 < ν) {x : ℝ} (hx : 1 < x) :
    olverQ ν μ x ≠ 0 := by
  sorry

/-- At most one exterior zero; the identically zero regularized solution is excluded. -/
theorem olverQ_at_most_one_exterior_zero {ν μ : ℝ} (hν : ν < -1) (hnondeg : ∃ x : ℝ, 1 < x ∧ olverQ ν μ x ≠ 0) :
    ∀ x y : ℝ, 1 < x → 1 < y → olverQ ν μ x=0 → olverQ ν μ y=0 → x=y := by
  sorry

end AAR.Legendre
