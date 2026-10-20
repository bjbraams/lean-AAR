/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations

/-!
# Zero distributions, asymptotics and tables, DLMF §7.13

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- The selected upper-half-plane error-function zeros, indexed from one. -/
def errorFunctionZero (complement : Bool) (k : ℕ) : ℂ :=
  orderedZero (if complement then erfc else erf) (if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else {z : ℂ | 0 < z.re ∧ 0 < z.im}) k

/-- Fresnel representatives in the first octant; the other octants follow by symmetry. -/
def fresnelFunctionZero (sine : Bool) (k : ℕ) : ℂ :=
  orderedZero (if sine then fresnelSinInt else fresnelCosInt) {z : ℂ | 0 < arg z ∧ arg z < π/4} k

/-- erf zero simple. -/
theorem erf_zero_simple  :
    erf 0=0 ∧ deriv erf 0=2/Real.sqrt π := by
  refine ⟨erf_zero, ?_⟩
  rw [(hasDerivAt_erf_complex 0).deriv]
  simp

/-- The simple C zero and triple S zero at the origin. -/
theorem fresnel_zero_orders  :
    fresnelCosInt 0=0 ∧ deriv fresnelCosInt 0=1 ∧ fresnelSinInt 0=0 ∧ deriv fresnelSinInt 0=0 ∧ iteratedDeriv 2 fresnelSinInt 0=0 ∧ iteratedDeriv 3 fresnelSinInt 0=π := by
  have hS1 : deriv fresnelSinInt = fun z => sin (π*z^2/2) :=
    funext fun z => (hasDerivAt_fresnelSinInt_complex z).deriv
  have hd2 (z : ℂ) : HasDerivAt (fun z : ℂ => sin (π*z^2/2)) (cos (π*z^2/2)*(π*z)) z := by
    have h := (((hasDerivAt_id' z).pow 2).const_mul (π:ℂ)).div_const 2 |>.csin
    convert h using 1
    simp only [Pi.pow_apply]
    ring
  have hS2 : iteratedDeriv 2 fresnelSinInt = fun z => cos (π*z^2/2)*(π*z) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, hS1]
    exact funext fun z => (hd2 z).deriv
  have hd3 : HasDerivAt (fun z : ℂ => cos (π*z^2/2)*(π*z))
      (-sin (π*0^2/2)*(π*0)*(π*0)+cos (π*0^2/2)*π) 0 := by
    have h1 := (((hasDerivAt_id' (0:ℂ)).pow 2).const_mul (π:ℂ)).div_const 2 |>.ccos
    have h2 := ((hasDerivAt_id' (0:ℂ)).const_mul (π:ℂ))
    convert h1.mul h2 using 1
    simp
  refine ⟨primitive_zero _, ?_, primitive_zero _, ?_, ?_, ?_⟩
  · rw [(hasDerivAt_fresnelCosInt_complex 0).deriv]; simp
  · rw [hS1]; simp
  · rw [hS2]; simp
  · rw [iteratedDeriv_succ, hS2, hd3.deriv]; simp

/-- errorFunctionZero spec. -/
theorem errorFunctionZero_spec (complement : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if complement then erfc else erf; let S := if complement then {z : ℂ | π/2 < arg z ∧ arg z < 3*π/4} else {z : ℂ | 0 < z.re ∧ 0 < z.im}; errorFunctionZero complement k ∈ S ∧ f (errorFunctionZero complement k)=0 ∧ ({z : ℂ | z ∈ S ∧ f z=0 ∧ ‖z‖ < ‖errorFunctionZero complement k‖} : Set ℂ).ncard=k-1 := by
  sorry

/-- errorFunctionZero ordered. -/
theorem errorFunctionZero_ordered (complement : Bool) :
    StrictMonoOn (fun k => ‖errorFunctionZero complement k‖) (Ici 1) := by
  sorry

/-- erf zero classification. -/
theorem erf_zero_classification (z : ℂ) :
    erf z=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u := errorFunctionZero false k; z=u ∨ z = -u ∨ z=star u ∨ z = -star u := by
  sorry

/-- erfc zero classification. -/
theorem erfc_zero_classification (z : ℂ) :
    erfc z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧ (z=errorFunctionZero true k ∨ z=star (errorFunctionZero true k)) := by
  sorry

/-- faddeevaW zero classification. -/
theorem faddeevaW_zero_classification (z : ℂ) :
    faddeevaW z=0 ↔ ∃ k : ℕ, 1 ≤ k ∧ (z=I*errorFunctionZero true k ∨ z=I*star (errorFunctionZero true k)) := by
  sorry

/-- fresnelFunctionZero spec. -/
theorem fresnelFunctionZero_spec (sine : Bool) {k : ℕ} (hk : 1 ≤ k) :
    let f := if sine then fresnelSinInt else fresnelCosInt; 0 < arg (fresnelFunctionZero sine k) ∧ arg (fresnelFunctionZero sine k) < π/4 ∧ f (fresnelFunctionZero sine k)=0 ∧ ({z : ℂ | 0 < arg z ∧ arg z < π/4 ∧ f z=0 ∧ ‖z‖ < ‖fresnelFunctionZero sine k‖} : Set ℂ).ncard=k-1 := by
  sorry

/-- fresnelFunctionZero ordered. -/
theorem fresnelFunctionZero_ordered (sine : Bool) :
    StrictMonoOn (fun k => ‖fresnelFunctionZero sine k‖) (Ici 1) := by
  sorry

/-- fresnel zero classification. -/
theorem fresnel_zero_classification (sine : Bool) (z : ℂ) :
    (if sine then fresnelSinInt z else fresnelCosInt z)=0 ↔ z=0 ∨ ∃ k : ℕ, 1 ≤ k ∧ let u := fresnelFunctionZero sine k; z=u ∨ z = -u ∨ z=star u ∨ z = -star u ∨ z=I*u ∨ z = -I*u ∨ z=I*star u ∨ z = -I*star u := by
  sorry

/-- The complete Fresnel-tail zero correspondence in DLMF §7.13(iv). -/
theorem fresnelTail_zero_classification (z : ℂ) :
    fresnelTail z=0 ↔ erfc (Real.sqrt π/(1+I)*z)=0 := by
  have h := fresnel_signed_erf z (ε:=1) (Or.inl rfl)
  have hz : fresnelZetaComplex 1 z = Real.sqrt π/(1+I)*z := by
    have h1 : (1+I) ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
    unfold fresnelZetaComplex
    simp only [Complex.ofReal_one, one_mul]
    field_simp
    ring_nf
    rw [I_sq]
    ring
  have ht : fresnelTail z = (1+I)/2*erfc (Real.sqrt π/(1+I)*z) := by
    rw [fresnelTail, erfc, ← hz]
    simp only [Complex.ofReal_one, one_mul] at h
    linear_combination -h
  have hne : (1+I)/2 ≠ 0 := by
    intro h0; have := congrArg Complex.re h0; simp at this
  rw [ht, mul_eq_zero, or_iff_right hne]

/-- Large error-function zero variable λ. -/
@[dlmf 7.13.E2, dlmf 7.13.E4]
def errorZeroLambda (k : ℕ) : ℝ :=
  Real.sqrt (((k : ℝ)-1/8)*π)

/-- Logarithmic error-function zero variable μ. -/
@[dlmf 7.13.E2, dlmf 7.13.E4]
def errorZeroMu (complement : Bool) (k : ℕ) : ℝ :=
  Real.log ((if complement then 2 else 1)*errorZeroLambda k*Real.sqrt (2*π))

/-- All-order polynomial-logarithmic expansions of both coordinates. -/
@[dlmf 7.13.E1, dlmf 7.13.E3]
theorem errorFunctionZero_asymptotic (complement : Bool) :
    ∃ p q : ℕ → Polynomial ℝ, (∀ μ : ℝ, (p 0).eval μ=(if complement then -1 else 1) ∧ (q 0).eval μ=1 ∧ (p 1).eval μ=(if complement then 1 else -1)*μ/4 ∧ (q 1).eval μ=μ/4 ∧ (p 2).eval μ=(if complement then -1 else 1)*(1-μ+μ^2/2)/16 ∧ (q 2).eval μ=(1-μ+μ^2/2)/16) ∧ ∀ N : ℕ, (IsBigO atTop (fun k : ℕ => (errorFunctionZero complement (k+1)).re-∑ n ∈ Finset.range N, (p n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n)) (fun k : ℕ => errorZeroLambda (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) ∧ (IsBigO atTop (fun k : ℕ => (errorFunctionZero complement (k+1)).im-∑ n ∈ Finset.range N, (q n).eval (errorZeroMu complement (k+1))*errorZeroLambda (k+1)^((1 : ℤ)-2*n)) (fun k : ℕ => errorZeroLambda (k+1)^((1 : ℤ)-2*N)*(1+|errorZeroMu complement (k+1)|)^N)) := by
  sorry

/-- Fresnel zero variable λ. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroLambda (sine : Bool) (k : ℕ) : ℝ :=
  if sine then 2*Real.sqrt k else Real.sqrt (4*(k : ℝ)-1)

/-- Fresnel zero logarithmic variable α. -/
@[dlmf 7.13.E6, dlmf 7.13.E7]
def fresnelZeroAlpha (sine : Bool) (k : ℕ) : ℝ :=
  2/π*Real.log (π*fresnelZeroLambda sine k)

/-- All-order Fresnel zero expansions with logarithmic-polynomial coefficients. -/
@[dlmf 7.13.E5]
theorem fresnelFunctionZero_asymptotic (sine : Bool) :
    ∃ p q : ℕ → Polynomial ℝ, (∀ α : ℝ, (p 0).eval α=1 ∧ (p 1).eval α=α*(α*π-4)/(8*π) ∧ (q 0).eval α=α/2) ∧ ∀ N : ℕ, (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).re-∑ n ∈ Finset.range N, (p n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((1 : ℤ)-4*n)) (fun k : ℕ => fresnelZeroLambda sine (k+1)^((1 : ℤ)-4*N)*(1+|fresnelZeroAlpha sine (k+1)|)^(2*N))) ∧ (IsBigO atTop (fun k : ℕ => (fresnelFunctionZero sine (k+1)).im-∑ n ∈ Finset.range N, (q n).eval (fresnelZeroAlpha sine (k+1))*fresnelZeroLambda sine (k+1)^((-1 : ℤ)-4*n)) (fun k : ℕ => fresnelZeroLambda sine (k+1)^((-1 : ℤ)-4*N)*(1+|fresnelZeroAlpha sine (k+1)|)^(2*N+1))) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.1. -/
theorem zero_table_1_1  :
    |(errorFunctionZero false 1).re-(1.4506161632)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero false 1).im-(1.8809430002)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.1. -/
theorem zero_table_1_2  :
    |(errorFunctionZero false 2).re-(2.2446592738)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero false 2).im-(2.6165751407)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.1. -/
theorem zero_table_1_3  :
    |(errorFunctionZero false 3).re-(2.8397410469)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero false 3).im-(3.1756280996)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.1. -/
theorem zero_table_1_4  :
    |(errorFunctionZero false 4).re-(3.3354607354)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero false 4).im-(3.6461743764)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.1. -/
theorem zero_table_1_5  :
    |(errorFunctionZero false 5).re-(3.7690055670)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero false 5).im-(4.0606972339)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.2. -/
theorem zero_table_2_1  :
    |(errorFunctionZero true 1).re-(-1.3548101281)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero true 1).im-(1.9914668428)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.2. -/
theorem zero_table_2_2  :
    |(errorFunctionZero true 2).re-(-2.1770449061)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero true 2).im-(2.6911490243)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.2. -/
theorem zero_table_2_3  :
    |(errorFunctionZero true 3).re-(-2.7843876132)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero true 3).im-(3.2353308684)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.2. -/
theorem zero_table_2_4  :
    |(errorFunctionZero true 4).re-(-3.2874107894)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero true 4).im-(3.6973097025)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.2. -/
theorem zero_table_2_5  :
    |(errorFunctionZero true 5).re-(-3.7259487194)| ≤ 1/(2*10^10) ∧ |(errorFunctionZero true 5).im-(4.1061072847)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.3. -/
theorem zero_table_3_1  :
    |(fresnelFunctionZero false 1).re-(1.7436674862)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero false 1).im-(0.3057350636)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.3. -/
theorem zero_table_3_2  :
    |(fresnelFunctionZero false 2).re-(2.6514595973)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero false 2).im-(0.2529039555)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.3. -/
theorem zero_table_3_3  :
    |(fresnelFunctionZero false 3).re-(3.3203593363)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero false 3).im-(0.2239534581)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.3. -/
theorem zero_table_3_4  :
    |(fresnelFunctionZero false 4).re-(3.8757344884)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero false 4).im-(0.2047474706)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.3. -/
theorem zero_table_3_5  :
    |(fresnelFunctionZero false 5).re-(4.3610635170)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero false 5).im-(0.1906697324)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.4. -/
theorem zero_table_4_1  :
    |(fresnelFunctionZero true 1).re-(2.0092570118)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero true 1).im-(0.2885478973)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.4. -/
theorem zero_table_4_2  :
    |(fresnelFunctionZero true 2).re-(2.8334772325)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero true 2).im-(0.2442852408)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.4. -/
theorem zero_table_4_3  :
    |(fresnelFunctionZero true 3).re-(3.4675330835)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero true 3).im-(0.2184926805)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.4. -/
theorem zero_table_4_4  :
    |(fresnelFunctionZero true 4).re-(4.0025782433)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero true 4).im-(0.2008510251)| ≤ 1/(2*10^10) := by
  sorry

/-- Rational error bounds for DLMF Table 7.13.4. -/
theorem zero_table_4_5  :
    |(fresnelFunctionZero true 5).re-(4.4741892952)| ≤ 1/(2*10^10) ∧ |(fresnelFunctionZero true 5).im-(0.1876885891)| ≤ 1/(2*10^10) := by
  sorry

end AAR.Confluent
