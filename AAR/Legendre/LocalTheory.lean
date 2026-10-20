/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Zeros
public import AAR.Legendre.Continuation

/-!
# Singular exponents and independence of Legendre solutions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Normalized first-derivative coefficient of the associated Legendre equation. -/
def legendreEquationP (z : ℂ) : ℂ :=
  -2*z/(1-z^2)

/-- Normalized zeroth-derivative coefficient. -/
def legendreEquationQ (ν μ z : ℂ) : ℂ :=
  (ν*(ν+1)-μ^2/(1-z^2))/(1-z^2)

/-- Regular singularity and the exponent pair minus/plus order over two, DLMF 14.2(iii). -/
theorem legendre_finite_singular_exponents_1 (ν μ : ℂ) :
    Tendsto (fun z : ℂ => (z-1)*legendreEquationP z) (𝓝[≠] (1:ℂ)) (𝓝 1) ∧ Tendsto (fun z : ℂ => (z-1)^2*legendreEquationQ ν μ z) (𝓝[≠] (1:ℂ)) (𝓝 (-μ^2/4)) ∧ ∀ r : ℂ, r*(r-1)+r-μ^2/4=(r-μ/2)*(r+μ/2) := by
  have hev : ∀ᶠ z in 𝓝[≠] (1:ℂ), z ≠ 1 ∧ z + 1 ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (1:ℂ), z + 1 ≠ 0 :=
      (continuous_id.add continuous_const).continuousAt.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz h2 using ⟨hz, h2⟩
  refine ⟨?_, ?_, fun r => by ring⟩
  · have heq : (fun z : ℂ => (z-1)*legendreEquationP z) =ᶠ[𝓝[≠] 1] (fun z => 2*z/(1+z)) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      have h3 : 1 + z ≠ 0 := by rwa [add_comm]
      rw [legendreEquationP, show (1:ℂ) - z^2 = -(z-1)*(1+z) by ring]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => 2*z/(1+z)) 1).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  · have heq : (fun z : ℂ => (z-1)^2*legendreEquationQ ν μ z) =ᶠ[𝓝[≠] 1]
        (fun z => (ν*(ν+1)*(1-z^2)-μ^2)/(1+z)^2) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z - 1 ≠ 0 := sub_ne_zero.2 hz1
      have h3 : 1 + z ≠ 0 := by rwa [add_comm]
      rw [legendreEquationQ, show (1:ℂ) - z^2 = -(z-1)*(1+z) by ring]
      field_simp
      ring
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => (ν*(ν+1)*(1-z^2)-μ^2)/(1+z)^2) 1).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds

/-- Regular singularity and the exponent pair minus/plus order over two, DLMF 14.2(iii). -/
theorem legendre_finite_singular_exponents_2 (ν μ : ℂ) :
    Tendsto (fun z : ℂ => (z-(-1))*legendreEquationP z) (𝓝[≠] (-1:ℂ)) (𝓝 1) ∧ Tendsto (fun z : ℂ => (z-(-1))^2*legendreEquationQ ν μ z) (𝓝[≠] (-1:ℂ)) (𝓝 (-μ^2/4)) ∧ ∀ r : ℂ, r*(r-1)+r-μ^2/4=(r-μ/2)*(r+μ/2) := by
  have hev : ∀ᶠ z in 𝓝[≠] (-1:ℂ), z ≠ -1 ∧ 1 - z ≠ 0 := by
    have h1 : ∀ᶠ z in 𝓝 (-1:ℂ), 1 - z ≠ 0 :=
      (continuous_const.sub continuous_id).continuousAt.eventually_ne (by norm_num)
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds h1] with z hz h2 using ⟨hz, h2⟩
  refine ⟨?_, ?_, fun r => by ring⟩
  · have heq : (fun z : ℂ => (z-(-1))*legendreEquationP z) =ᶠ[𝓝[≠] (-1)] (fun z => -(2*z)/(1-z)) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z + 1 ≠ 0 := by intro h; apply hz1; linear_combination h
      rw [legendreEquationP, show (1:ℂ) - z^2 = (1-z)*(z+1) by ring, sub_neg_eq_add]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => -(2*z)/(1-z)) (-1)).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds
  · have heq : (fun z : ℂ => (z-(-1))^2*legendreEquationQ ν μ z) =ᶠ[𝓝[≠] (-1)]
        (fun z => (ν*(ν+1)*(1-z^2)-μ^2)/(1-z)^2) := by
      filter_upwards [hev] with z ⟨hz1, hz2⟩
      have : z + 1 ≠ 0 := by intro h; apply hz1; linear_combination h
      rw [legendreEquationQ, show (1:ℂ) - z^2 = (1-z)*(z+1) by ring, sub_neg_eq_add]
      field_simp
    apply Tendsto.congr' heq.symm
    have := (by fun_prop (disch := norm_num) : ContinuousAt (fun z : ℂ => (ν*(ν+1)*(1-z^2)-μ^2)/(1-z)^2) (-1)).tendsto
    norm_num at this
    exact this.mono_left nhdsWithin_le_nhds

/-- Reciprocal-coordinate equation has exponents minus degree and degree plus one at infinity. -/
theorem legendre_infinite_singular_exponents (ν μ : ℂ) :
    Tendsto (fun t : ℂ => t*(2*t/(t^2-1))) (𝓝[≠] 0) (𝓝 0) ∧ Tendsto (fun t : ℂ => t^2*(ν*(ν+1)/(t^2*(t^2-1))-μ^2/(t^2-1)^2)) (𝓝[≠] 0) (𝓝 (-ν*(ν+1))) ∧ ∀ r : ℂ, r*(r-1)-ν*(ν+1)=(r+ν)*(r-ν-1) := by
  constructor
  · simpa using (by fun_prop (disch := norm_num) : ContinuousAt (fun t : ℂ => t*(2*t/(t^2-1))) 0).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
  · constructor
    · have heq : (fun t : ℂ => t^2*(ν*(ν+1)/(t^2*(t^2-1))-μ^2/(t^2-1)^2)) =ᶠ[𝓝[≠] 0]
          (fun t => ν*(ν+1)/(t^2-1)-t^2*μ^2/(t^2-1)^2) := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht0 : t ≠ 0 := ht
        field_simp
      apply Tendsto.congr' heq.symm
      simpa [div_neg] using (by fun_prop (disch := norm_num) : ContinuousAt (fun t : ℂ => ν*(ν+1)/(t^2-1)-t^2*μ^2/(t^2-1)^2) 0).tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0:ℂ) ≤ 𝓝 (0:ℂ))
    · intro r; ring

/-- The reflected first-kind pair is dependent exactly at the exceptional parameters in DLMF 14.2(iii). -/
theorem ferrersP_reflected_dependence (ν μ : ℂ) :
    (∃ A B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x ∈ Ioo (-1:ℝ) 1, A*ferrersP ν (-μ) x+B*ferrersP ν (-μ) (-x)=0) ↔ (∃ n : ℕ, μ-ν=-n) ∨ (∃ n : ℕ, μ+ν=-(n+1)) := by
  sorry

/-- Independence of the recessive principal pair in DLMF 14.2(iii) and 14.21(ii). -/
theorem associatedPQ_independent {ν μ : ℂ} (hν : -1/2 ≤ ν.re) (hμ : 0 ≤ μ.re) :
    ¬∃ A B : ℂ, (A ≠ 0 ∨ B ≠ 0) ∧ ∀ x : ℝ, 1 < x → A*associatedP ν (-μ) x+B*olverQ ν μ x=0 := by
  sorry

/-- Integral-order completion of the interior zero count in DLMF 14.16(ii). -/
theorem ferrersP_positive_integer_order_zero_count {ν : ℝ} (hν : -1/2 ≤ ν) (m : ℕ) (hnondeg : ∃ x ∈ Ioo (-1:ℝ) 1, ferrersP ν m x ≠ 0) :
    Set.Finite (ferrersZeroSet false ν m) ∧ (ferrersZeroSet false ν m).ncard=(max (⌈ν-m⌉:ℤ) 0).toNat := by
  sorry

end AAR.Legendre
