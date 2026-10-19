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
  sorry

/-- Regular singularity and the exponent pair minus/plus order over two, DLMF 14.2(iii). -/
theorem legendre_finite_singular_exponents_2 (ν μ : ℂ) :
    Tendsto (fun z : ℂ => (z-(-1))*legendreEquationP z) (𝓝[≠] (-1:ℂ)) (𝓝 1) ∧ Tendsto (fun z : ℂ => (z-(-1))^2*legendreEquationQ ν μ z) (𝓝[≠] (-1:ℂ)) (𝓝 (-μ^2/4)) ∧ ∀ r : ℂ, r*(r-1)+r-μ^2/4=(r-μ/2)*(r+μ/2) := by
  sorry

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
