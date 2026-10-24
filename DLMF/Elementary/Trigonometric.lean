/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import ToMathlib.NumberTheory.BernoulliTaylor
public import ToMathlib.NumberTheory.EulerNumbers
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ComplexDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Meromorphic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import TauCeti.Analysis.SpecialFunctions.Trigonometric.Orthogonality

/-!
# Trigonometric and inverse trigonometric functions (DLMF §§4.14–4.27)

Acquisition checked against NIST DLMF on 2026-10-24. Upstream results are recorded in
`MathlibCoverage`, without duplicate wrappers. This module supplies genuinely missing definitions
and statements. Admissions remain explicit. Complex inverse functions use principal logarithms
and square roots off their cuts; their two boundary values are represented separately. General
inverse values are sets, so identities between multivalued functions retain every branch.
Reciprocal functions are totalized at poles; all identities that need finite values state this.

The sine orthogonality API is imported from pinned TauCeti. The Bernoulli/Euler and partial-fraction
APIs are existing Mathlib-only `ToMathlib` developments. The general-solution and Gudermannian
statements record the necessary singular-solution and sign corrections to the displayed source.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Polynomial
open scoped Real Topology Nat
namespace DLMF.Elementary

private theorem trig_sqrt_inverse {x:ℝ} (hx:1<x) :
    Real.sqrt (1-x⁻¹^2)=Real.sqrt (x^2-1)/x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hs : 0<x^2-1 := by nlinarith
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hsi : 0≤1-x⁻¹^2 := by nlinarith
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (div_nonneg (Real.sqrt_nonneg _) hx0.le)).mp
  rw [Real.sq_sqrt hsi,div_pow,Real.sq_sqrt hs.le]
  field_simp


private theorem trig_norm_sq_sin (z : ℂ) : ‖Complex.sin z‖^2=(Real.sin z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm]
  conv_lhs => rw [← Complex.re_add_im z,Complex.sin_add_mul_I]
  simp [Complex.normSq,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  linear_combination (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re) + (Real.sin z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)

private theorem trig_norm_sq_cos (z : ℂ) : ‖Complex.cos z‖^2=(Real.cos z.re)^2+(Real.sinh z.im)^2 := by
  rw [Complex.sq_norm]
  conv_lhs => rw [← Complex.re_add_im z,Complex.cos_add_mul_I]
  simp [Complex.normSq,← Complex.ofReal_sin,← Complex.ofReal_cos,← Complex.ofReal_sinh,← Complex.ofReal_cosh]
  linear_combination (Real.sinh z.im)^2*(Real.sin_sq_add_cos_sq z.re) + (Real.cos z.re)^2*(Real.cosh_sq_sub_sinh_sq z.im)


/-- Real sign, including zero, used in the DLMF branch and table formulas. -/
def trigRealSign (x : ℝ) : ℝ := if 0<x then 1 else if x<0 then -1 else 0

/-- Complex cosecant, totalized to zero at its poles. -/
@[dlmf 4.14.E5]
def csc (z : ℂ) : ℂ := (Complex.sin z)⁻¹

/-- Complex secant, totalized to zero at its poles. -/
@[dlmf 4.14.E6]
def sec (z : ℂ) : ℂ := (Complex.cos z)⁻¹

/-- DLMF 4.14.E7: cot eq inv tan. -/
@[dlmf 4.14.E7]
theorem cot_eq_inv_tan (z : ℂ) : Complex.cot z = (Complex.tan z)⁻¹ := by
  simp [Complex.cot,Complex.tan]

/-- DLMF 4.15.E2: cot eq neg tan add half pi. -/
@[dlmf 4.15.E2]
theorem cot_eq_neg_tan_add_half_pi (z : ℂ) : Complex.cot z = -Complex.tan (z+π/2) := by
  simp [Complex.tan,Complex.cot,Complex.sin_add_pi_div_two,Complex.cos_add_pi_div_two,div_neg]

/-- DLMF 4.15.E3: sec eq csc add half pi. -/
@[dlmf 4.15.E3]
theorem sec_eq_csc_add_half_pi (z : ℂ) : sec z = csc (z+π/2) := by
  simp [sec,csc,Complex.sin_add_pi_div_two]

/-- DLMF 4.14: meromorphic reciprocal trig. -/
@[dlmf 4.14]
theorem meromorphic_reciprocal_trig : Meromorphic csc ∧ Meromorphic sec ∧ Meromorphic Complex.cot := by
  have hs : Meromorphic Complex.sin := fun z => (Complex.differentiable_sin.analyticAt z).meromorphicAt
  have hc : Meromorphic Complex.cos := fun z => (Complex.differentiable_cos.analyticAt z).meromorphicAt
  exact ⟨hs.inv,hc.inv,hc.div hs⟩

/-- DLMF 4.14: reciprocal trig poles. -/
@[dlmf 4.14]
theorem reciprocal_trig_poles (z : ℂ) :
    (Tendsto (fun w => ‖csc w‖) (𝓝[≠] z) atTop ↔ Complex.sin z=0) ∧
    (Tendsto (fun w => ‖sec w‖) (𝓝[≠] z) atTop ↔ Complex.cos z=0) ∧
    (Tendsto (fun w => ‖Complex.cot w‖) (𝓝[≠] z) atTop ↔ Complex.sin z=0) := by
  sorry

/-- DLMF 4.14: cot zeros. -/
@[dlmf 4.14]
theorem cot_zeros {z : ℂ} (hz : Complex.sin z ≠ 0) :
    Complex.cot z=0 ↔ ∃ k : ℤ,z=(2*k+1)*π/2 := by
  simp only [Complex.cot,div_eq_zero_iff,hz,or_false,Complex.cos_eq_zero_iff]

/-- DLMF 4.14: reciprocal trig nonzero. -/
@[dlmf 4.14]
theorem reciprocal_trig_nonzero {z : ℂ} (hs : Complex.sin z≠0) (hc : Complex.cos z≠0) : csc z≠0 ∧ sec z≠0 := by
  exact ⟨inv_ne_zero hs,inv_ne_zero hc⟩

/-- DLMF 4.18.E3: cos le sinc le one. -/
@[dlmf 4.18.E3]
theorem cos_le_sinc_le_one {x : ℝ} (hx : 0≤x) (hπ : x≤π) :
    Real.cos x ≤ Real.sinc x ∧ Real.sinc x≤1 := by
  refine ⟨?_,Real.sinc_le_one x⟩
  by_cases h : x<π/2
  · exact Real.cos_le_sinc (by rwa [abs_of_nonneg hx])
  · have hcos : Real.cos x≤0 := Real.cos_nonpos_of_pi_div_two_le_of_le (le_of_not_gt h) (by linarith [Real.pi_pos])
    have hsinc : 0≤Real.sinc x := by
      by_cases hx0 : x=0
      · simp [hx0]
      · rw [Real.sinc_of_ne_zero hx0]
        exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx hπ) hx
    exact hcos.trans hsinc


/-- DLMF 4.18.E4: sine parabolic bounds. -/
@[dlmf 4.18.E4]
theorem sine_parabolic_bounds {x : ℝ} (hx : 0<x) (h1 : x<1) :
    π < Real.sin (π*x)/(x*(1-x)) ∧ Real.sin (π*x)/(x*(1-x))≤4 := by
  sorry

/-- DLMF 4.18.E5: sinh im le norm sin le cosh im. -/
@[dlmf 4.18.E5]
theorem sinh_im_le_norm_sin_le_cosh_im (z : ℂ) :
    |Real.sinh z.im| ≤ ‖Complex.sin z‖ ∧ ‖Complex.sin z‖≤Real.cosh z.im := by
  have hn:=trig_norm_sq_sin z
  have hc:=Real.cosh_sq_sub_sinh_sq z.im
  have hs:=Real.sin_sq_add_cos_sq z.re
  have hp:=norm_nonneg (Complex.sin z)
  have hcp:=Real.cosh_pos z.im
  have ha:=abs_nonneg (Real.sinh z.im)
  have hasq:=sq_abs (Real.sinh z.im)
  constructor <;> nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.cos z.re)]


/-- DLMF 4.18.E6: sinh im le norm cos le cosh im. -/
@[dlmf 4.18.E6]
theorem sinh_im_le_norm_cos_le_cosh_im (z : ℂ) :
    |Real.sinh z.im| ≤ ‖Complex.cos z‖ ∧ ‖Complex.cos z‖≤Real.cosh z.im := by
  have hn:=trig_norm_sq_cos z
  have hc:=Real.cosh_sq_sub_sinh_sq z.im
  have hs:=Real.sin_sq_add_cos_sq z.re
  have hp:=norm_nonneg (Complex.cos z)
  have hcp:=Real.cosh_pos z.im
  have ha:=abs_nonneg (Real.sinh z.im)
  have hasq:=sq_abs (Real.sinh z.im)
  constructor <;> nlinarith [sq_nonneg (Real.sin z.re),sq_nonneg (Real.cos z.re)]


/-- DLMF 4.18.E7: norm csc le csch im. -/
@[dlmf 4.18.E7]
theorem norm_csc_le_csch_im {z : ℂ} (hz : z.im≠0) :
    ‖csc z‖ ≤ (Real.sinh |z.im|)⁻¹ := by
  rw [csc,norm_inv]
  have hpos : 0 < |Real.sinh z.im| := abs_pos.mpr (Real.sinh_ne_zero.mpr hz)
  have h := (sinh_im_le_norm_sin_le_cosh_im z).1
  have habs : Real.sinh |z.im|=|Real.sinh z.im| := by
    rcases le_or_gt 0 z.im with hp|hn
    · rw [abs_of_nonneg hp,abs_of_nonneg (Real.sinh_nonneg_iff.mpr hp)]
    · rw [abs_of_neg hn,Real.sinh_neg,abs_of_neg (Real.sinh_neg_iff.mpr hn)]
  rw [habs]
  exact inv_anti₀ hpos h


/-- DLMF 4.18.E8: norm cos le cosh norm. -/
@[dlmf 4.18.E8]
theorem norm_cos_le_cosh_norm (z : ℂ) : ‖Complex.cos z‖ ≤ Real.cosh ‖z‖ := by
  apply (Complex.hasSum_cos z).norm_le_of_bounded (Real.hasSum_cosh ‖z‖)
  intro n
  simp [norm_div,norm_mul,norm_pow]


/-- DLMF 4.18.E9: norm sin le sinh norm. -/
@[dlmf 4.18.E9]
theorem norm_sin_le_sinh_norm (z : ℂ) : ‖Complex.sin z‖ ≤ Real.sinh ‖z‖ := by
  apply (Complex.hasSum_sin z).norm_le_of_bounded (Real.hasSum_sinh ‖z‖)
  intro n
  simp [norm_div,norm_mul,norm_pow]


/-- DLMF 4.18.E10: trig unit disc bounds. -/
@[dlmf 4.18.E10]
theorem trig_unit_disc_bounds {z : ℂ} (hz : ‖z‖<1) :
    ‖Complex.cos z‖<2 ∧ ‖Complex.sin z‖≤(6/5:ℝ)*‖z‖ := by
  sorry

/-- DLMF 4.19.E5: hasSum sec euler. -/
@[dlmf 4.19.E5]
theorem hasSum_sec_euler {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (-1:ℂ)^n*(eulerNumber (2*n):ℂ)*z^(2*n)/(2*n)!) (sec z) := by
  sorry

/-- DLMF 4.19.E7: hasSum log sinc bernoulli. -/
@[dlmf 4.19.E7]
theorem hasSum_log_sinc_bernoulli {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (if z=0 then 1 else Complex.sin z/z)) := by
  sorry

/-- DLMF 4.19.E8: hasSum log cos bernoulli. -/
@[dlmf 4.19.E8]
theorem hasSum_log_cos_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^(n+1)*2^(2*(n+1)-1)*(2^(2*(n+1))-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (Complex.cos z)) := by
  sorry

/-- DLMF 4.19.E9: hasSum log tan div bernoulli. -/
@[dlmf 4.19.E9]
theorem hasSum_log_tan_div_bernoulli {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => ((-1:ℂ)^n*2^(2*(n+1))*(2^(2*(n+1)-1)-1)*(bernoulli (2*(n+1)):ℂ)/((n+1)*(2*(n+1))!))*z^(2*(n+1))) (Complex.log (if z=0 then 1 else Complex.tan z/z)) := by
  sorry

/-- DLMF 4.20.E4: hasDerivAt csc. -/
@[dlmf 4.20.E4]
theorem hasDerivAt_csc {z : ℂ} (hz : Complex.sin z≠0) :
    HasDerivAt csc (-csc z*Complex.cot z) z := by
  refine ((Complex.hasDerivAt_sin z).inv hz).congr_deriv ?_
  simp only [csc,Complex.cot,div_eq_mul_inv,inv_pow,pow_two]
  ring

/-- DLMF 4.20.E5: hasDerivAt sec. -/
@[dlmf 4.20.E5]
theorem hasDerivAt_sec {z : ℂ} (hz : Complex.cos z≠0) :
    HasDerivAt sec (sec z*Complex.tan z) z := by
  refine ((Complex.hasDerivAt_cos z).inv hz).congr_deriv ?_
  simp only [sec,Complex.tan,div_eq_mul_inv,inv_pow,pow_two]
  ring

/-- DLMF 4.20.E6: hasDerivAt cot. -/
@[dlmf 4.20.E6]
theorem hasDerivAt_cot {z : ℂ} (hz : Complex.sin z≠0) :
    HasDerivAt Complex.cot (-(csc z)^2) z := by
  have h := (Complex.hasDerivAt_cos z).div (Complex.hasDerivAt_sin z) hz
  refine h.congr_deriv ?_
  simp only [csc]
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.20.E12: trig linear ode general. -/
@[dlmf 4.20.E12]
theorem trig_linear_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,deriv (deriv w) z+a^2*w z=0) :
    ∃ A B : ℂ,∀ z∈U,w z=A*Complex.cos (a*z)+B*Complex.sin (a*z) := by
  sorry

/-- The energy equation has the displayed sine family and two singular constant solutions. -/
@[dlmf 4.20.E13]
theorem trig_energy_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,(deriv w z)^2+a^2*(w z)^2=1) :
    (∃ c : ℂ,∀ z∈U,w z=Complex.sin (a*z+c)/a) ∨
      (∀ z∈U,w z=a⁻¹) ∨ (∀ z∈U,w z= -a⁻¹) := by
  sorry

/-- The Riccati equation has the displayed tangent family and two omitted constant solutions. -/
@[dlmf 4.20.E14]
theorem trig_riccati_ode_general {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U) (hne : U.Nonempty)
    {a : ℂ} (ha : a≠0) {w : ℂ→ℂ} (hw : AnalyticOnNhd ℂ w U) (h : ∀ z∈U,deriv w z-a^2*(w z)^2=1) :
    (∃ c : ℂ,∀ z∈U,Complex.cos (a*z+c)≠0 ∧ w z=Complex.tan (a*z+c)/a) ∨
      (∀ z∈U,w z=I/a) ∨ (∀ z∈U,w z= -I/a) := by
  sorry

/-- The linear oscillator equation, with a nonzero complex frequency. -/
@[dlmf 4.20.E9]
def IsTrigLinearSolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,deriv (deriv w) z+a^2*w z=0

/-- The trigonometric energy equation. -/
@[dlmf 4.20.E10]
def IsTrigEnergySolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,(deriv w z)^2+a^2*(w z)^2=1

/-- The trigonometric Riccati equation, considered away from poles of solutions. -/
@[dlmf 4.20.E11]
def IsTrigRiccatiSolution (a : ℂ) (w : ℂ→ℂ) (U : Set ℂ) : Prop :=
  ∀ z∈U,deriv w z-a^2*(w z)^2=1

/-- DLMF 4.21.E1: sin add cos phase. -/
@[dlmf 4.21.E1]
theorem sin_add_cos_phase (u : ℂ) :
    Complex.sin u+Complex.cos u=(Real.sqrt 2:ℂ)*Complex.sin (u+π/4) ∧
    Complex.sin u-Complex.cos u=(Real.sqrt 2:ℂ)*Complex.sin (u-π/4) ∧
    Complex.sin u+Complex.cos u=(Real.sqrt 2:ℂ)*Complex.cos (u-π/4) ∧
    Complex.sin u-Complex.cos u= -(Real.sqrt 2:ℂ)*Complex.cos (u+π/4) := by
  have hs : Complex.sin ((Real.pi:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.sin_pi_div_four
  have hc : Complex.cos ((Real.pi:ℂ)/4)=(Real.sqrt 2:ℂ)/2 := by exact_mod_cast Real.cos_pi_div_four
  have hr : (Real.sqrt 2:ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
  rw [Complex.sin_add,Complex.sin_sub,Complex.cos_sub,Complex.cos_add,hs,hc]
  refine ⟨?_,?_,?_,?_⟩
  · linear_combination -((Complex.sin u+Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u-Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u+Complex.cos u)/2)*hr
  · linear_combination -((Complex.sin u-Complex.cos u)/2)*hr

/-- DLMF 4.21.E5: cot add sub. -/
@[dlmf 4.21.E5]
theorem cot_add_sub {u v : ℂ} (hu : Complex.sin u≠0) (hv : Complex.sin v≠0) :
    Complex.cot (u+v)=(Complex.cot u*Complex.cot v-1)/(Complex.cot u+Complex.cot v) ∧
    Complex.cot (u-v)=(-Complex.cot u*Complex.cot v-1)/(Complex.cot u-Complex.cot v) := by
  have hAdd (a b : ℂ) (ha : Complex.sin a≠0) (hb : Complex.sin b≠0) :
      Complex.cot (a+b)=(Complex.cot a*Complex.cot b-1)/(Complex.cot a+Complex.cot b) := by
    unfold Complex.cot
    rw [Complex.sin_add,Complex.cos_add]
    field_simp
    ring
  refine ⟨hAdd u v hu hv,?_⟩
  have hn : Complex.sin (-v)≠0 := by simpa only [Complex.sin_neg,neg_ne_zero] using hv
  simpa [Complex.cot,Complex.cos_neg,Complex.sin_neg,sub_eq_add_neg,div_neg] using hAdd u (-v) hu hn

/-- DLMF 4.21.E10: tan add sub values. -/
@[dlmf 4.21.E10]
theorem tan_add_sub_values {u v : ℂ} (hu : Complex.cos u≠0) (hv : Complex.cos v≠0) :
    Complex.tan u+Complex.tan v=Complex.sin (u+v)/(Complex.cos u*Complex.cos v) ∧
    Complex.tan u-Complex.tan v=Complex.sin (u-v)/(Complex.cos u*Complex.cos v) := by
  constructor
  · rw [Complex.tan_eq_sin_div_cos,Complex.tan_eq_sin_div_cos,Complex.sin_add]
    field_simp <;> ring
  · rw [Complex.tan_eq_sin_div_cos,Complex.tan_eq_sin_div_cos,Complex.sin_sub]
    field_simp <;> ring

/-- DLMF 4.21.E11: cot add sub values. -/
@[dlmf 4.21.E11]
theorem cot_add_sub_values {u v : ℂ} (hu : Complex.sin u≠0) (hv : Complex.sin v≠0) :
    Complex.cot u+Complex.cot v=Complex.sin (v+u)/(Complex.sin u*Complex.sin v) ∧
    Complex.cot u-Complex.cot v=Complex.sin (v-u)/(Complex.sin u*Complex.sin v) := by
  constructor
  · rw [Complex.cot,Complex.cot,Complex.sin_add]
    field_simp <;> ring
  · rw [Complex.cot,Complex.cot,Complex.sin_sub]
    field_simp <;> ring

/-- DLMF 4.21.E13: sec sq eq. -/
@[dlmf 4.21.E13]
theorem sec_sq_eq {z : ℂ} (hz : Complex.cos z≠0) : (sec z)^2=1+(Complex.tan z)^2 := by
  unfold sec Complex.tan
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E14: csc sq eq. -/
@[dlmf 4.21.E14]
theorem csc_sq_eq {z : ℂ} (hz : Complex.sin z≠0) : (csc z)^2=1+(Complex.cot z)^2 := by
  unfold csc Complex.cot
  field_simp
  linear_combination -(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E15: two sin mul sin. -/
@[dlmf 4.21.E15]
theorem two_sin_mul_sin (u v : ℂ) : 2*Complex.sin u*Complex.sin v=Complex.cos (u-v)-Complex.cos (u+v) := by
  rw [Complex.cos_sub,Complex.cos_add]
  ring

/-- DLMF 4.21.E16: two cos mul cos. -/
@[dlmf 4.21.E16]
theorem two_cos_mul_cos (u v : ℂ) : 2*Complex.cos u*Complex.cos v=Complex.cos (u-v)+Complex.cos (u+v) := by
  rw [Complex.cos_sub,Complex.cos_add]
  ring

/-- DLMF 4.21.E17: two sin mul cos. -/
@[dlmf 4.21.E17]
theorem two_sin_mul_cos (u v : ℂ) : 2*Complex.sin u*Complex.cos v=Complex.sin (u-v)+Complex.sin (u+v) := by
  rw [Complex.sin_sub,Complex.sin_add]
  ring

/-- DLMF 4.21.E18: sin sq sub sin sq. -/
@[dlmf 4.21.E18]
theorem sin_sq_sub_sin_sq (u v : ℂ) : (Complex.sin u)^2-(Complex.sin v)^2=Complex.sin (u+v)*Complex.sin (u-v) := by
  rw [Complex.sin_add,Complex.sin_sub]
  linear_combination -(Complex.sin u)^2*(Complex.sin_sq_add_cos_sq v)+
    (Complex.sin v)^2*(Complex.sin_sq_add_cos_sq u)

/-- DLMF 4.21.E19: cos sq sub cos sq. -/
@[dlmf 4.21.E19]
theorem cos_sq_sub_cos_sq (u v : ℂ) : (Complex.cos u)^2-(Complex.cos v)^2= -Complex.sin (u+v)*Complex.sin (u-v) := by
  rw [Complex.cos_sq',Complex.cos_sq']
  linear_combination -(sin_sq_sub_sin_sq u v)

/-- DLMF 4.21.E20: cos sq sub sin sq. -/
@[dlmf 4.21.E20]
theorem cos_sq_sub_sin_sq (u v : ℂ) : (Complex.cos u)^2-(Complex.sin v)^2=Complex.cos (u+v)*Complex.cos (u-v) := by
  rw [Complex.cos_add,Complex.cos_sub]
  linear_combination -(Complex.cos u)^2*(Complex.sin_sq_add_cos_sq v)+
    (Complex.sin v)^2*(Complex.sin_sq_add_cos_sq u)

/-- Squaring the principal complex square root returns its argument, including zero. -/
lemma trig_sqrt_sq (z : ℂ) : (Complex.sqrt z)^2=z := by
  rw [Complex.sqrt,← Complex.cpow_mul_nat]
  norm_num

/-- DLMF 4.21.E21: sin half roots. -/
@[dlmf 4.21.E21]
theorem sin_half_roots (z : ℂ) : Complex.sin (z/2)=Complex.sqrt ((1-Complex.cos z)/2) ∨
    Complex.sin (z/2)= -Complex.sqrt ((1-Complex.cos z)/2) := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq]
  have h := Complex.cos_two_mul_eq_one_sub (z/2)
  rw [show (2:ℂ)*(z/2)=z by ring] at h
  linear_combination h/2

/-- DLMF 4.21.E22: cos half roots. -/
@[dlmf 4.21.E22]
theorem cos_half_roots (z : ℂ) : Complex.cos (z/2)=Complex.sqrt ((1+Complex.cos z)/2) ∨
    Complex.cos (z/2)= -Complex.sqrt ((1+Complex.cos z)/2) := by
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq]
  have h := Complex.cos_two_mul (z/2)
  rw [show (2:ℂ)*(z/2)=z by ring] at h
  linear_combination -h/2

/-- DLMF 4.21.E23: tan half roots and ratios. -/
@[dlmf 4.21.E23]
theorem tan_half_roots_and_ratios {z : ℂ} (hs : Complex.sin z≠0) :
    (Complex.tan (z/2)=Complex.sqrt ((1-Complex.cos z)/(1+Complex.cos z)) ∨
      Complex.tan (z/2)= -Complex.sqrt ((1-Complex.cos z)/(1+Complex.cos z))) ∧
    Complex.tan (z/2)=(1-Complex.cos z)/Complex.sin z ∧
    Complex.tan (z/2)=Complex.sin z/(1+Complex.cos z) := by
  have hsin : Complex.sin z=2*Complex.sin (z/2)*Complex.cos (z/2) := by
    rw [← Complex.sin_two_mul,show (2:ℂ)*(z/2)=z by ring]
  have hcos : Complex.cos z=2*(Complex.cos (z/2))^2-1 := by
    rw [← Complex.cos_two_mul,show (2:ℂ)*(z/2)=z by ring]
  have hc : Complex.cos (z/2)≠0 := by intro h; apply hs; simp [hsin,h]
  have hp : 1+Complex.cos z≠0 := by
    rw [hcos]
    convert mul_ne_zero (two_ne_zero : (2:ℂ)≠0) (pow_ne_zero 2 hc) using 1 <;> ring
  have hcircle:=Complex.sin_sq_add_cos_sq (z/2)
  have hr1 : Complex.tan (z/2)=(1-Complex.cos z)/Complex.sin z := by
    rw [Complex.tan]
    field_simp [hc,hs]
    rw [hsin,hcos]
    linear_combination 2*Complex.cos (z/2)*hcircle
  have hr2 : Complex.tan (z/2)=Complex.sin z/(1+Complex.cos z) := by
    rw [Complex.tan]
    field_simp [hc,hp]
    rw [hsin,hcos]
    ring
  refine ⟨?_,hr1,hr2⟩
  apply (sq_eq_sq_iff_eq_or_eq_neg).mp
  rw [trig_sqrt_sq,Complex.tan]
  field_simp [hc,hp]
  rw [hcos]
  linear_combination 2*(Complex.cos (z/2))^2*hcircle


/-- DLMF 4.21.E27: sin double tan. -/
@[dlmf 4.21.E27]
theorem sin_double_tan {z : ℂ} (hc : Complex.cos z≠0) :
    Complex.sin (2*z)=2*Complex.tan z/(1+(Complex.tan z)^2) := by
  unfold Complex.tan
  rw [Complex.sin_two_mul]
  field_simp
  linear_combination (Complex.sin z)*(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E28: cos double tan. -/
@[dlmf 4.21.E28]
theorem cos_double_tan {z : ℂ} (hc : Complex.cos z≠0) :
    Complex.cos (2*z)=(1-(Complex.tan z)^2)/(1+(Complex.tan z)^2) := by
  unfold Complex.tan
  rw [Complex.cos_two_mul']
  field_simp
  linear_combination ((Complex.cos z)^2-(Complex.sin z)^2)*(Complex.sin_sq_add_cos_sq z)

/-- DLMF 4.21.E29: tan double cot. -/
@[dlmf 4.21.E29]
theorem tan_double_cot {z : ℂ} (hs : Complex.sin z≠0) (hc : Complex.cos z≠0) :
    Complex.tan (2*z)=2*Complex.cot z/((Complex.cot z)^2-1) ∧
    Complex.tan (2*z)=2/(Complex.cot z-Complex.tan z) := by
  have ht : Complex.tan z≠0 := div_ne_zero hs hc
  rw [Complex.tan_two_mul,cot_eq_inv_tan]
  constructor <;> field_simp [ht] <;> ring

/-- DLMF 4.21.E32: sin quadruple. -/
@[dlmf 4.21.E32]
theorem sin_quadruple (z : ℂ) :
    Complex.sin (4*z)=8*(Complex.cos z)^3*Complex.sin z-4*Complex.cos z*Complex.sin z := by
  rw [show (4:ℂ)*z=2*(2*z) by ring,Complex.sin_two_mul,Complex.sin_two_mul,Complex.cos_two_mul]
  ring

/-- DLMF 4.21.E33: cos quadruple. -/
@[dlmf 4.21.E33]
theorem cos_quadruple (z : ℂ) :
    Complex.cos (4*z)=8*(Complex.cos z)^4-8*(Complex.cos z)^2+1 := by
  rw [show (4:ℂ)*z=2*(2*z) by ring,Complex.cos_two_mul,Complex.cos_two_mul]
  ring

/-- DLMF 4.21.E34: de moivre int. -/
@[dlmf 4.21.E34]
theorem de_moivre_int (z : ℂ) (n : ℤ) :
    Complex.cos (n*z)+I*Complex.sin (n*z)=(Complex.cos z+I*Complex.sin z)^n := by
  rw [mul_comm I,← Complex.exp_mul_I,mul_assoc,Complex.exp_int_mul]
  rw [mul_comm I,← Complex.exp_mul_I]

/-- Complex De Moivre formula with the precise principal logarithm strip convention. -/
@[dlmf 4.21]
theorem de_moivre_complex {z : ℂ} (hlo : -π<z.re) (hhi : z.re≤π) (n : ℂ) :
    Complex.cos (n*z)+I*Complex.sin (n*z)=(Complex.cos z+I*Complex.sin z)^n := by
  rw [mul_comm I,← Complex.exp_mul_I,mul_comm I,← Complex.exp_mul_I]
  rw [Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),Complex.log_exp]
  · congr 1; ring
  · simpa using hlo
  · simpa using hhi

/-- DLMF 4.21.E35: sin multiple product. -/
@[dlmf 4.21.E35]
theorem sin_multiple_product (z : ℂ) {n : ℕ} (hn : 0<n) :
    Complex.sin (n*z)=2^(n-1)*∏ k∈Finset.range n,Complex.sin (z+k*π/n) := by
  sorry

/-- DLMF 4.21.E36: tan half substitution. -/
@[dlmf 4.21.E36]
theorem tan_half_substitution {z : ℂ} (hz : Complex.cos (z/2)≠0) :
    Complex.sin z=2*Complex.tan (z/2)/(1+(Complex.tan (z/2))^2) ∧
    Complex.cos z=(1-(Complex.tan (z/2))^2)/(1+(Complex.tan (z/2))^2) ∧
    HasDerivAt (fun w : ℂ => Complex.tan (w/2)) ((1+(Complex.tan (z/2))^2)/2) z := by
  have hsin := sin_double_tan hz
  have hcos := cos_double_tan hz
  rw [show (2:ℂ)*(z/2)=z by ring] at hsin hcos
  refine ⟨hsin,hcos,?_⟩
  have hd:=(Complex.hasDerivAt_tan hz).comp z ((hasDerivAt_id z).div_const 2)
  convert hd using 1
  · rfl
  · rw [Complex.tan]
    field_simp
    linear_combination (Complex.sin_sq_add_cos_sq (z/2))


/-- DLMF 4.21.E40: cot real imag. -/
@[dlmf 4.21.E40]
theorem cot_real_imag {z : ℂ} (hz : Complex.sin z≠0) :
    Complex.cot z=((Real.sin (2*z.re):ℂ)-I*Real.sinh (2*z.im))/
      ((Real.cosh (2*z.im):ℂ)-Real.cos (2*z.re)) := by
  sorry

/-- DLMF 4.21.E41: norm sin explicit. -/
@[dlmf 4.21.E41]
theorem norm_sin_explicit (z : ℂ) :
    ‖Complex.sin z‖=Real.sqrt ((Real.sin z.re)^2+(Real.sinh z.im)^2) ∧
    ‖Complex.sin z‖=Real.sqrt ((Real.cosh (2*z.im)-Real.cos (2*z.re))/2) := by
  have h : ‖Complex.sin z‖=Real.sqrt ((Real.sin z.re)^2+(Real.sinh z.im)^2) := by
    rw [← trig_norm_sq_sin,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨h,?_⟩
  rw [h]
  congr 1
  rw [Real.cosh_two_mul,Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq z.re,Real.cosh_sq_sub_sinh_sq z.im]


/-- DLMF 4.21.E42: norm cos explicit. -/
@[dlmf 4.21.E42]
theorem norm_cos_explicit (z : ℂ) :
    ‖Complex.cos z‖=Real.sqrt ((Real.cos z.re)^2+(Real.sinh z.im)^2) ∧
    ‖Complex.cos z‖=Real.sqrt ((Real.cosh (2*z.im)+Real.cos (2*z.re))/2) := by
  have h : ‖Complex.cos z‖=Real.sqrt ((Real.cos z.re)^2+(Real.sinh z.im)^2) := by
    rw [← trig_norm_sq_cos,Real.sqrt_sq (norm_nonneg _)]
  refine ⟨h,?_⟩
  rw [h]
  congr 1
  rw [Real.cosh_two_mul,Real.cos_two_mul]
  nlinarith [Real.cosh_sq_sub_sinh_sq z.im]


/-- DLMF 4.21.E43: norm tan explicit. -/
@[dlmf 4.21.E43]
theorem norm_tan_explicit {z : ℂ} (hz : Complex.cos z≠0) :
    ‖Complex.tan z‖=Real.sqrt ((Real.cosh (2*z.im)-Real.cos (2*z.re))/
      (Real.cosh (2*z.im)+Real.cos (2*z.re))) := by
  have hp : 0≤(Real.cosh (2*z.im)-Real.cos (2*z.re))/2 := by
    rw [Real.cosh_two_mul,Real.cos_two_mul]
    nlinarith [Real.cosh_sq_sub_sinh_sq z.im,Real.sin_sq_add_cos_sq z.re,
      sq_nonneg (Real.sin z.re),sq_nonneg (Real.sinh z.im)]
  rw [Complex.tan,norm_div,(norm_sin_explicit z).2,(norm_cos_explicit z).2,← Real.sqrt_div hp]
  congr 1
  exact div_div_div_cancel_right₀ (two_ne_zero : (2:ℝ)≠0) _ _


/-- DLMF 4.22.E2: cos infinite product. -/
@[dlmf 4.22.E2]
theorem cos_infinite_product (z : ℂ) :
    Tendsto (fun N : ℕ => ∏ n∈Finset.range N,
      (1-4*z^2/(((2*n+1:ℕ):ℂ)^2*(π:ℂ)^2))) atTop (𝓝 (Complex.cos z)) := by
  sorry

/-- DLMF 4.22.E4: hasSum csc sq partial fraction. -/
@[dlmf 4.22.E4]
theorem hasSum_csc_sq_partial_fraction {z : ℂ} (hz : Complex.sin z≠0) :
    HasSum (fun n : ℤ => 1/(z-n*π)^2) ((csc z)^2) := by
  sorry


/-! ## Principal and general inverse functions, including cut banks -/

/-- Principal complex arcsine off its cuts; its assigned cut values select one bank only. -/
@[dlmf 4.23.E19]
def arcsinPrincipal (z : ℂ) : ℂ := -I*Complex.log (Complex.sqrt (1-z^2)+I*z)

/-- Principal complex arccosine off its cuts. -/
@[dlmf 4.23.E16]
def arccosPrincipal (z : ℂ) : ℂ := π/2-arcsinPrincipal z

/-- Principal inverse cosecant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E7]
def arccscPrincipal (z : ℂ) : ℂ := arcsinPrincipal z⁻¹

/-- Principal inverse secant, used on its cut domain with z nonzero. -/
@[dlmf 4.23.E8]
def arcsecPrincipal (z : ℂ) : ℂ := arccosPrincipal z⁻¹

/-- Principal inverse cotangent off its central imaginary cut; its totalized value at zero is not a bank value. -/
@[dlmf 4.23.E9]
def arccotPrincipal (z : ℂ) : ℂ := Complex.arctan z⁻¹

/-- The open arcsine/arccosine cut plane, excluding the two branch points. -/
def arcsinCutPlane : Set ℂ := {z | z.im≠0 ∨ |z.re|<1}

/-- The open arctangent cut plane, excluding ±i. -/
def arctanCutPlane : Set ℂ := {z | z.re≠0 ∨ |z.im|<1}

/-- The reciprocal cut plane for inverse secant and cosecant. -/
def arccscCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arcsinCutPlane}

/-- The central imaginary cut is deleted for inverse cotangent. -/
def arccotCutPlane : Set ℂ := {z | z≠0 ∧ z⁻¹∈arctanCutPlane}

/-- The sign of the upper bank, or of the right bank for vertical cuts. -/
def trigBankSign (upper : Bool) : ℂ := if upper then 1 else -1

/-- General arcsine values, retaining every inverse image. -/
def arcsinGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w=z}

/-- General arccosine values, retaining every inverse image. -/
def arccosGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w=z}

/-- General arctangent values; totalized tangent poles are excluded. -/
def arctanGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ Complex.tan w=z}

/-- General inverse cosecant values, excluding poles of cosecant. -/
def arccscGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ csc w=z}

/-- General inverse secant values, excluding poles of secant. -/
def arcsecGeneral (z : ℂ) : Set ℂ := {w | Complex.cos w≠0 ∧ sec w=z}

/-- General inverse cotangent values, excluding poles of cotangent. -/
def arccotGeneral (z : ℂ) : Set ℂ := {w | Complex.sin w≠0 ∧ Complex.cot w=z}

/-- A path together with a continuously continued square root starting at +1. -/
def ArcsinLift (γ r : ℝ→ℂ) (z : ℂ) : Prop :=
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
    ∀ t∈Icc 0 1,r t≠0 ∧ (r t)^2=1-(γ t)^2

/-- DLMF 4.23.E1: arcsin general integral. -/
@[dlmf 4.23.E1]
theorem arcsin_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arcsinGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      (∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- The integral from z to 1, normalized by the principal segment from zero to one. -/
@[dlmf 4.23.E2]
theorem arccos_general_integral {z w : ℂ} (hzp : z≠1) (hzm : z≠ -1) :
    w∈arccosGeneral z ↔ ∃ γ r : ℝ→ℂ,ArcsinLift γ r z ∧
      π/2-(∫ t in (0:ℝ)..1,deriv γ t/r t)=w := by
  sorry

/-- DLMF 4.23.E3: arctan general integral. -/
@[dlmf 4.23.E3]
theorem arctan_general_integral {z w : ℂ} (hzp : z≠I) (hzm : z≠ -I) :
    w∈arctanGeneral z ↔ ∃ γ : ℝ→ℂ,
      ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
      (∀ t∈Icc 0 1,γ t≠I ∧ γ t≠ -I) ∧
      (∫ t in (0:ℝ)..1,deriv γ t/(1+(γ t)^2))=w := by
  sorry

private theorem trig_arctan_quotient_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    (1+z*I)/(1-z*I)∈Complex.slitPlane := by
  have hre : ((1+z*I)/(1-z*I)).re=(1-z.im^2-z.re^2)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_re,Complex.normSq]
    ring
  have him : ((1+z*I)/(1-z*I)).im=(2*z.re)/((1+z.im)^2+z.re^2) := by
    simp [Complex.div_im,Complex.normSq]
    ring
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re≠0
  · right
    rw [him]
    have hD:0<(1+z.im)^2+z.re^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hr)
    exact div_ne_zero (mul_ne_zero two_ne_zero hr) hD.ne'
  · left
    have hr0:z.re=0 := not_ne_iff.mp hr
    have hi:|z.im|<1 := hz.resolve_left hr
    rw [hre,hr0]
    have hip:0<1+z.im := by linarith [(abs_lt.mp hi).1]
    apply div_pos
    · nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
    · positivity

private theorem trig_arctan_linear_ne {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z*I≠0 ∧ 1-z*I≠0 := by
  have hgood: ¬(z.re=0 ∧ (z.im=1 ∨ z.im= -1)) := by
    rintro ⟨hr,hi⟩
    have h:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    rcases hi with hi|hi <;> simp [hi] at h
  constructor
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inl (by linarith)⟩
  · intro h
    have hr:=congrArg Complex.re h
    have hi:=congrArg Complex.im h
    simp at hr hi
    exact hgood ⟨by linarith,Or.inr (by linarith)⟩

private theorem trig_hasDerivAt_arctan {z:ℂ} (hz:z∈arctanCutPlane) :
    HasDerivAt Complex.arctan ((1+z^2)⁻¹) z := by
  obtain ⟨hp,hm⟩:=trig_arctan_linear_ne hz
  have hd0 := (((hasDerivAt_id z).mul_const I).const_add 1).div
    (((hasDerivAt_id z).mul_const I).const_sub 1) hm
  have hd1 := (Complex.hasDerivAt_log (trig_arctan_quotient_slit hz)).comp z hd0
  have hd:=hd1.const_mul (-I/2)
  convert hd using 1
  · rfl
  · dsimp only [id]
    have hfac:(1+z*I)*(1-z*I)=1+z^2 := by
      linear_combination -z^2*Complex.I_sq
    rw [← hfac]
    field_simp [hp,hm]
    linear_combination 2*Complex.I_sq


private theorem trig_one_add_sq_slit {z:ℂ} (hz:z∈arctanCutPlane) :
    1+z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hr:z.re=0
  · left
    have hi:|z.im|<1 := hz.resolve_left (not_ne_iff.mpr hr)
    simp [Complex.add_re,pow_two,Complex.mul_re,hr]
    nlinarith [(abs_lt.mp hi).1,(abs_lt.mp hi).2]
  · by_cases hi:z.im=0
    · left
      simp [Complex.add_re,pow_two,Complex.mul_re,hi]
      nlinarith [sq_nonneg z.re]
    · right
      simp [Complex.add_im,pow_two,Complex.mul_im]
      convert mul_ne_zero (mul_ne_zero two_ne_zero hr) hi using 1 <;> ring

/-- DLMF 4.23.E4: arccsc general reciprocal. -/
@[dlmf 4.23.E4]
theorem arccsc_general_reciprocal {z : ℂ} (hz : z≠0) : arccscGeneral z=arcsinGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ (Complex.sin w)⁻¹=z) ↔ Complex.sin w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩


/-- DLMF 4.23.E5: arcsec general reciprocal. -/
@[dlmf 4.23.E5]
theorem arcsec_general_reciprocal {z : ℂ} (hz : z≠0) : arcsecGeneral z=arccosGeneral z⁻¹ := by
  ext w
  change (Complex.cos w≠0 ∧ (Complex.cos w)⁻¹=z) ↔ Complex.cos w=z⁻¹
  constructor
  · intro h
    have := congrArg Inv.inv h.2
    simpa using this
  · intro h
    exact ⟨by simpa [h] using inv_ne_zero hz,by simp [h]⟩


/-- DLMF 4.23.E6: arccot general reciprocal. -/
@[dlmf 4.23.E6]
theorem arccot_general_reciprocal {z : ℂ} (hz : z≠0) : arccotGeneral z=arctanGeneral z⁻¹ := by
  ext w
  change (Complex.sin w≠0 ∧ Complex.cot w=z) ↔ Complex.cos w≠0 ∧ Complex.tan w=z⁻¹
  rw [cot_eq_inv_tan]
  constructor
  · rintro ⟨hs,ht⟩
    have ht0 : Complex.tan w≠0 := by
      intro h
      apply hz
      simpa [h] using ht.symm
    refine ⟨?_,?_⟩
    · intro h; exact ht0 (by simp [Complex.tan,h])
    · simpa using congrArg Inv.inv ht
  · rintro ⟨hc,ht⟩
    refine ⟨?_,by simp [ht]⟩
    intro h
    have : (z⁻¹:ℂ)=0 := by simpa [Complex.tan,h] using ht.symm
    exact inv_ne_zero hz this


private theorem trig_arcsin_product (z:ℂ) :
    (Complex.sqrt (1-z^2)+I*z)*(Complex.sqrt (1-z^2)-I*z)=1 := by
  linear_combination trig_sqrt_sq (1-z^2) - z^2*Complex.I_sq

private theorem trig_arcsin_log_arg_ne (z:ℂ) : Complex.sqrt (1-z^2)+I*z≠0 := by
  intro h
  have hp:=trig_arcsin_product z
  rw [h,zero_mul] at hp
  exact zero_ne_one hp

private theorem trig_arcsin_log_slit (z:ℂ) : Complex.sqrt (1-z^2)+I*z∈Complex.slitPlane := by
  let r:=Complex.sqrt (1-z^2)
  change r+I*z∈Complex.slitPlane
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:(r+I*z).im≠0
  · exact Or.inr hi
  · left
    have hi0:(r+I*z).im=0 := not_ne_iff.mp hi
    have hr:0≤r.re := by
      dsimp [r]
      rw [Complex.sqrt,Complex.cpow_inv_two_re]
      positivity
    have him:r.im= -z.re := by
      simp only [Complex.add_im,Complex.I_mul_im] at hi0
      linarith
    have hp:=congrArg Complex.re (trig_arcsin_product z)
    change ((r+I*z)*(r-I*z)).re=1 at hp
    simp only [Complex.mul_re,Complex.add_re,Complex.sub_re,Complex.add_im,Complex.sub_im,
      Complex.I_mul_re,Complex.I_mul_im,him] at hp
    norm_num only [Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hp
    simp only [Complex.add_re,Complex.I_mul_re]
    nlinarith

private theorem trig_one_sub_sq_slit {z:ℂ} (hz:z∈arcsinCutPlane) : 1-z^2∈Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  by_cases hi:z.im=0
  · left
    have hr:|z.re|<1 := hz.resolve_left (not_ne_iff.mpr hi)
    simp [pow_two,Complex.mul_re,hi]
    nlinarith [(abs_lt.mp hr).1,(abs_lt.mp hr).2]
  · by_cases hr:z.re=0
    · left
      simp [pow_two,Complex.mul_re,hr]
      nlinarith [sq_nonneg z.im]
    · right
      simp [pow_two,Complex.mul_im]
      convert neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero two_ne_zero hr) hi) using 1 <;> ring

private theorem trig_hasDerivAt_sqrt {q:ℂ} (hq:q∈Complex.slitPlane) :
    HasDerivAt Complex.sqrt ((Complex.sqrt q)⁻¹/2) q := by
  simpa only [Complex.sqrt,show (-1/2:ℂ)= -(2⁻¹:ℂ) by norm_num,Complex.cpow_neg] using
    Complex.hasDerivAt_sqrt hq

private theorem trig_hasDerivAt_arcsin {z:ℂ} (hz:z∈arcsinCutPlane) :
    HasDerivAt arcsinPrincipal (Complex.sqrt (1-z^2))⁻¹ z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hd0:=(trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1)
  have hd1:=hd0.add ((hasDerivAt_id z).const_mul I)
  have hd2:=(Complex.hasDerivAt_log (trig_arcsin_log_slit z)).comp z hd1
  have hd:=hd2.const_mul (-I)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.pow_apply,Pi.add_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
    generalize heq : Complex.sqrt (1-z^2)=r at hr ⊢
    have hw:r+I*z≠0 := by rw [← heq]; exact trig_arcsin_log_arg_ne z
    field_simp [hr,hw]
    linear_combination r*Complex.I_sq

/-- DLMF 4.23.ii: analytic arcsin principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsin_principal : AnalyticOnNhd ℂ arcsinPrincipal arcsinCutPlane := by
  have hU:IsOpen arcsinCutPlane := by
    change IsOpen ({z:ℂ | z.im≠0}∪{z:ℂ | |z.re|<1})
    exact (isOpen_ne.preimage Complex.continuous_im).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_re) continuous_const)
  exact (show DifferentiableOn ℂ arcsinPrincipal arcsinCutPlane from fun z hz=>
    (trig_hasDerivAt_arcsin hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- DLMF 4.23.ii: analytic arccos principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccos_principal : AnalyticOnNhd ℂ arccosPrincipal arcsinCutPlane := by
  intro z hz
  change AnalyticAt ℂ (fun w=>(π:ℂ)/2-arcsinPrincipal w) z
  exact analyticAt_const.sub (analytic_arcsin_principal z hz)


/-- DLMF 4.23.ii: analytic arctan principal. -/
@[dlmf 4.23.ii]
theorem analytic_arctan_principal : AnalyticOnNhd ℂ Complex.arctan arctanCutPlane := by
  have hU:IsOpen arctanCutPlane := by
    change IsOpen ({z:ℂ|z.re≠0}∪{z:ℂ | |z.im|<1})
    exact (isOpen_ne.preimage Complex.continuous_re).union
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  exact (show DifferentiableOn ℂ Complex.arctan arctanCutPlane from fun z hz=>
    (trig_hasDerivAt_arctan hz).differentiableAt.differentiableWithinAt).analyticOnNhd hU


/-- DLMF 4.23.ii: analytic arccsc principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccsc_principal : AnalyticOnNhd ℂ arccscPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arcsin_principal _ hz.2).comp (analyticAt_id.inv hz.1)


/-- DLMF 4.23.ii: analytic arcsec principal. -/
@[dlmf 4.23.ii]
theorem analytic_arcsec_principal : AnalyticOnNhd ℂ arcsecPrincipal arccscCutPlane := by
  intro z hz
  exact (analytic_arccos_principal _ hz.2).comp (analyticAt_id.inv hz.1)


/-- DLMF 4.23.ii: analytic arccot principal. -/
@[dlmf 4.23.ii]
theorem analytic_arccot_principal : AnalyticOnNhd ℂ arccotPrincipal arccotCutPlane := by
  intro z hz
  exact (analytic_arctan_principal _ hz.2).comp (analyticAt_id.inv hz.1)


/-- DLMF 4.23.ii: inverse principal real. -/
@[dlmf 4.23.ii]
theorem inverse_principal_real {x : ℝ} (hx : x∈Icc (-1) 1) :
    arcsinPrincipal x=(Real.arcsin x:ℂ) ∧ arccosPrincipal x=(Real.arccos x:ℂ) := by
  sorry

/-- DLMF 4.23.E10: arcsin principal neg. -/
@[dlmf 4.23.E10]
theorem arcsin_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arcsinPrincipal (-z)= -arcsinPrincipal z := by
  have hn:Complex.sqrt (1-(-z)^2)+I*(-z)=(Complex.sqrt (1-z^2)+I*z)⁻¹ := by
    apply (mul_left_cancel₀ (trig_arcsin_log_arg_ne z))
    rw [mul_inv_cancel₀ (trig_arcsin_log_arg_ne z)]
    convert trig_arcsin_product z using 1 <;> ring
  unfold arcsinPrincipal
  rw [hn,Complex.log_inv _ (Complex.mem_slitPlane_iff_arg.mp (trig_arcsin_log_slit z)).1]
  ring


/-- DLMF 4.23.E11: arccos principal neg. -/
@[dlmf 4.23.E11]
theorem arccos_principal_neg {z : ℂ} (hz : z∈arcsinCutPlane) : arccosPrincipal (-z)=π-arccosPrincipal z := by
  unfold arccosPrincipal
  rw [arcsin_principal_neg hz]
  ring


/-- DLMF 4.23.E12: arctan principal neg. -/
@[dlmf 4.23.E12]
theorem arctan_principal_neg {z : ℂ} (hz : z∈arctanCutPlane) : Complex.arctan (-z)= -Complex.arctan z := by
  have hq: (1+(-z)*I)/(1-(-z)*I)=((1+z*I)/(1-z*I))⁻¹ := by
    simp only [neg_mul,sub_neg_eq_add,sub_eq_add_neg,inv_div,neg_neg]
  rw [Complex.arctan,Complex.arctan,hq,Complex.log_inv _
    (Complex.mem_slitPlane_iff_arg.mp (trig_arctan_quotient_slit hz)).1]
  ring


/-- DLMF 4.23.E13: arccsc principal neg. -/
@[dlmf 4.23.E13]
theorem arccsc_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arccscPrincipal (-z)= -arccscPrincipal z := by
  unfold arccscPrincipal
  rw [inv_neg]
  exact arcsin_principal_neg hz.2


/-- DLMF 4.23.E14: arcsec principal neg. -/
@[dlmf 4.23.E14]
theorem arcsec_principal_neg {z : ℂ} (hz : z∈arccscCutPlane) : arcsecPrincipal (-z)=π-arcsecPrincipal z := by
  unfold arcsecPrincipal
  rw [inv_neg]
  exact arccos_principal_neg hz.2


/-- DLMF 4.23.E15: arccot principal neg. -/
@[dlmf 4.23.E15]
theorem arccot_principal_neg {z : ℂ} (hz : z∈arccotCutPlane) : arccotPrincipal (-z)= -arccotPrincipal z := by
  unfold arccotPrincipal
  rw [inv_neg]
  exact arctan_principal_neg hz.2


/-- DLMF 4.23.E17: arcsec principal complement. -/
@[dlmf 4.23.E17]
theorem arcsec_principal_complement (z : ℂ) : arcsecPrincipal z=π/2-arccscPrincipal z := by
  rfl

/-- DLMF 4.23.E18: arccot principal complement. -/
@[dlmf 4.23.E18]
theorem arccot_principal_complement {z : ℂ} (hz : z.re≠0) :
    arccotPrincipal z=(if 0<z.re then π/2 else -π/2)-Complex.arctan z := by
  sorry

/-- Arcsine on either bank of the positive real cut. -/
@[dlmf 4.23.E20]
def arcsinRightBank (upper : Bool) (x : ℝ) : ℂ :=
  π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)+x):ℂ)

/-- Arcsine on either bank of the negative real cut. -/
@[dlmf 4.23.E21]
def arcsinLeftBank (upper : Bool) (x : ℝ) : ℂ :=
  -π/2+trigBankSign upper*I*(Real.log (Real.sqrt (x^2-1)-x):ℂ)

/-- DLMF 4.23.E20: arcsin right cut limit. -/
@[dlmf 4.23.E20]
theorem arcsin_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinRightBank upper x)) := by
  sorry

/-- DLMF 4.23.E21: arcsin left cut limit. -/
@[dlmf 4.23.E21]
theorem arcsin_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arcsinPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (arcsinLeftBank upper x)) := by
  sorry

/-- DLMF 4.23.E22: arccos principal log. -/
@[dlmf 4.23.E22]
theorem arccos_principal_log (z : ℂ) :
    arccosPrincipal z=π/2+I*Complex.log (Complex.sqrt (1-z^2)+I*z) := by
  unfold arccosPrincipal arcsinPrincipal; ring

/-- DLMF 4.23.E23: arccos principal log half. -/
@[dlmf 4.23.E23]
theorem arccos_principal_log_half {z : ℂ} (hz : z∈arcsinCutPlane) :
    arccosPrincipal z= -2*I*Complex.log (Complex.sqrt ((1+z)/2)+I*Complex.sqrt ((1-z)/2)) := by
  sorry

/-- DLMF 4.23.E24: arccos right cut limit. -/
@[dlmf 4.23.E24]
theorem arccos_right_cut_limit {x : ℝ} (hx : 1≤x) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinRightBank upper x)) := by
  sorry

/-- DLMF 4.23.E25: arccos left cut limit. -/
@[dlmf 4.23.E25]
theorem arccos_left_cut_limit {x : ℝ} (hx : x≤ -1) (upper : Bool) :
    Tendsto arccosPrincipal (𝓝[{z : ℂ | if upper then 0<z.im else z.im<0}] (x:ℂ))
      (𝓝 (π/2-arcsinLeftBank upper x)) := by
  sorry

/-- DLMF 4.23.E26: arctan principal log. -/
@[dlmf 4.23.E26]
theorem arctan_principal_log {z : ℂ} (hz : z∈arctanCutPlane) :
    Complex.arctan z=I/2*Complex.log ((I+z)/(I-z)) := by
  sorry

/-- Arctangent bank values on the two exterior imaginary cuts. -/
@[dlmf 4.23.E27]
def arctanCutBank (right : Bool) (y : ℝ) : ℂ :=
  trigBankSign right*π/2+I/2*(Real.log ((y+1)/(y-1)):ℂ)

/-- DLMF 4.23.E27: arctan cut limit. -/
@[dlmf 4.23.E27]
theorem arctan_cut_limit {y : ℝ} (hy : 1< |y|) (right : Bool) :
    Tendsto Complex.arctan (𝓝[{z : ℂ | if right then 0<z.re else z.re<0}] ((y:ℂ)*I))
      (𝓝 (arctanCutBank right y)) := by
  sorry

/-- DLMF 4.23.iv: reciprocal reverses real cut bank. -/
@[dlmf 4.23.iv]
theorem reciprocal_reverses_real_cut_bank {x : ℝ} (hx : x≠0) :
    Tendsto (fun y : ℝ => ((x:ℂ)+I*y)⁻¹) (𝓝[>] 0) (𝓝 ((x:ℂ)⁻¹)) ∧
    ∀ y : ℝ,0<y→(((x:ℂ)+I*y)⁻¹).im<0 := by
  sorry

/-- DLMF 4.23.E28: sin arcsin principal. -/
@[dlmf 4.23.E28]
theorem sin_arcsin_principal (z : ℂ) : Complex.sin (arcsinPrincipal z)=z := by
  let w:=Complex.sqrt (1-z^2)+I*z
  have hw:w≠0 := trig_arcsin_log_arg_ne z
  have hp:w*(Complex.sqrt (1-z^2)-I*z)=1 := trig_arcsin_product z
  have hi:w⁻¹=Complex.sqrt (1-z^2)-I*z := by
    apply (mul_left_cancel₀ hw)
    rw [mul_inv_cancel₀ hw,hp]
  have he:Complex.exp (arcsinPrincipal z*I)=w := by
    rw [arcsinPrincipal,show -I*Complex.log w*I=Complex.log w by linear_combination -Complex.log w*Complex.I_sq]
    exact Complex.exp_log hw
  have hn:Complex.exp (-(arcsinPrincipal z)*I)=w⁻¹ := by
    rw [neg_mul,Complex.exp_neg,he]
  rw [Complex.sin,he,hn,hi]
  dsimp [w]
  linear_combination -z*Complex.I_sq


/-- DLMF 4.23.E29: cos arccos principal. -/
@[dlmf 4.23.E29]
theorem cos_arccos_principal (z : ℂ) : Complex.cos (arccosPrincipal z)=z := by
  rw [arccosPrincipal,Complex.cos_pi_div_two_sub,sin_arcsin_principal]


/-- DLMF 4.23.E31: arcsin general values. -/
@[dlmf 4.23.E31]
theorem arcsin_general_values (z w : ℂ) :
    w∈arcsinGeneral z ↔ ∃ k : ℤ,w=(-1:ℂ)^k*arcsinPrincipal z+k*π := by
  sorry

/-- DLMF 4.23.E32: arccos general values. -/
@[dlmf 4.23.E32]
theorem arccos_general_values (z w : ℂ) :
    w∈arccosGeneral z ↔ ∃ k : ℤ,w=arccosPrincipal z+2*k*π ∨ w= -arccosPrincipal z+2*k*π := by
  sorry

/-- DLMF 4.23.E33: arctan general values. -/
@[dlmf 4.23.E33]
theorem arctan_general_values {z : ℂ} (hp : z≠I) (hm : z≠ -I) (w : ℂ) :
    w∈arctanGeneral z ↔ ∃ k : ℤ,w=Complex.arctan z+k*π := by
  sorry

/-- The half-sum of distances to the inverse sine branch points. -/
@[dlmf 4.23.E37]
def inverseTrigAlpha (z : ℂ) : ℝ := (‖z+1‖+‖z-1‖)/2

/-- The half-difference of distances to the inverse sine branch points. -/
@[dlmf 4.23.E38]
def inverseTrigBeta (z : ℂ) : ℝ := (‖z+1‖-‖z-1‖)/2

/-- DLMF 4.23.E34: arcsin real imag. -/
@[dlmf 4.23.E34]
theorem arcsin_real_imag {z : ℂ} (hz : z.im≠0 ∨ |z.re|≤1) :
    arcsinPrincipal z=(Real.arcsin (inverseTrigBeta z):ℂ)+
      I*(trigRealSign z.im:ℂ)*Real.log (inverseTrigAlpha z+Real.sqrt ((inverseTrigAlpha z)^2-1)) := by
  sorry

/-- DLMF 4.23.E35: arccos real imag. -/
@[dlmf 4.23.E35]
theorem arccos_real_imag {z : ℂ} (hz : z.im≠0 ∨ |z.re|≤1) :
    arccosPrincipal z=(Real.arccos (inverseTrigBeta z):ℂ)-
      I*(trigRealSign z.im:ℂ)*Real.log (inverseTrigAlpha z+Real.sqrt ((inverseTrigAlpha z)^2-1)) := by
  sorry

/-- DLMF 4.23.E36: arctan real imag. -/
@[dlmf 4.23.E36]
theorem arctan_real_imag {z : ℂ} (hz : ‖z‖<1) :
    Complex.arctan z=(Real.arctan (2*z.re/(1-z.re^2-z.im^2)):ℂ)/2+
      I/4*Real.log ((z.re^2+(z.im+1)^2)/(z.re^2+(z.im-1)^2)) := by
  sorry

/-- The Gudermannian, real and odd on the full real line. -/
@[dlmf 4.23.E39]
def gudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cosh t)⁻¹

/-- The inverse Gudermannian on the open strip (-pi/2,pi/2). -/
@[dlmf 4.23.E41]
def inverseGudermannian (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x,(Real.cos t)⁻¹


private theorem trig_gd_integral {f:ℝ→ℝ}
    (hf:∀x,HasDerivAt f (Real.cosh x)⁻¹ x) (h0:f 0=0) (x:ℝ) : gudermannian x=f x := by
  have hc:Continuous (fun t:ℝ=>(Real.cosh t)⁻¹) := Real.continuous_cosh.inv₀ (fun t=>(Real.cosh_pos t).ne')
  rw [gudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _=>hf t) (hc.intervalIntegrable 0 x),h0,sub_zero]

private theorem trig_sqrt_one_sub_tanh (x:ℝ) :
    Real.sqrt (1-(Real.tanh x)^2)=(Real.cosh x)⁻¹ := by
  have hc:0<Real.cosh x := Real.cosh_pos x
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (inv_nonneg.mpr hc.le)).mp
  rw [Real.sq_sqrt (by linarith [Real.tanh_sq_lt_one x]),Real.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination Real.cosh_sq_sub_sinh_sq x

private theorem trig_sqrt_one_add_tan {x:ℝ} (hx:|x|<π/2) :
    Real.sqrt (1+(Real.tan x)^2)=(Real.cos x)⁻¹ := by
  simpa only [inv_inv] using congrArg Inv.inv
    (Real.inv_sqrt_one_add_tan_sq (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)))

private theorem trig_inverse_gd_integral {f:ℝ→ℝ}
    (hf:∀t,|t|<π/2→HasDerivAt f (Real.cos t)⁻¹ t) (h0:f 0=0)
    {x:ℝ} (hx:|x|<π/2) : inverseGudermannian x=f x := by
  have hmem:∀t∈uIcc (0:ℝ) x,|t|<π/2 := by
    intro t ht
    apply abs_lt.mpr
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcos:∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := fun t ht=>
    (Real.cos_pos_of_mem_Ioo (abs_lt.mp (hmem t ht))).ne'
  have hc:ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) := Real.continuous_cos.continuousOn.inv₀ hcos
  rw [inverseGudermannian,intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht=>hf t (hmem t ht)) hc.intervalIntegrable,h0,sub_zero]

private theorem trig_inverse_gd_arsinh {x:ℝ} (hx:|x|<π/2) :
    inverseGudermannian x=Real.arsinh (Real.tan x) := by
  refine trig_inverse_gd_integral (f:=fun t=>Real.arsinh (Real.tan t)) ?_ ?_ hx
  · intro t ht
    have hc:Real.cos t≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp ht)).ne'
    have hd:=(Real.hasDerivAt_tan hc).arsinh
    convert hd using 1
    rw [smul_eq_mul,trig_sqrt_one_add_tan ht]
    field_simp
  · simp

/-- DLMF 4.23.E40: gudermannian elementary. -/
@[dlmf 4.23.E40]
theorem gudermannian_elementary (x : ℝ) :
    gudermannian x=2*Real.arctan (Real.exp x)-π/2 ∧
    gudermannian x=Real.arcsin (Real.tanh x) ∧
    gudermannian x=Real.arctan (Real.sinh x) := by
  have he: gudermannian x=2*Real.arctan (Real.exp x)-π/2 := by
    apply trig_gd_integral
    · intro t
      have hd:=((Real.hasDerivAt_exp t).arctan.const_mul 2).sub_const (π/2)
      convert hd using 1
      rw [Real.cosh_eq,Real.exp_neg]
      field_simp
      ring
    · norm_num
      ring
  have hs: gudermannian x=Real.arctan (Real.sinh x) := by
    apply trig_gd_integral
    · intro t
      have hd:=(Real.hasDerivAt_sinh t).arctan
      convert hd using 1
      have hc:Real.cosh t≠0 := (Real.cosh_pos t).ne'
      have hp:1+(Real.sinh t)^2≠0 := by positivity
      field_simp
      linear_combination -Real.cosh_sq_sub_sinh_sq t
    · simp
  refine ⟨he,?_,hs⟩
  rw [Real.arcsin_eq_arctan ⟨Real.neg_one_lt_tanh x,Real.tanh_lt_one x⟩,trig_sqrt_one_sub_tanh]
  convert hs using 2
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp


/-- DLMF 4.23.E40: gudermannian reciprocal. -/
@[dlmf 4.23.E40]
theorem gudermannian_reciprocal {x : ℝ} (hx : x≠0) :
    gudermannian x=Real.arcsin ((Real.cosh x/Real.sinh x)⁻¹) ∧
    gudermannian x=Real.arctan (((Real.sinh x)⁻¹)⁻¹) := by
  constructor
  · simpa only [inv_div,Real.tanh_eq_sinh_div_cosh] using (gudermannian_elementary x).2.1
  · simpa only [inv_inv] using (gudermannian_elementary x).2.2


/-- The principal arccosine/secant forms require x nonnegative. -/
@[dlmf 4.23.E40]
theorem gudermannian_nonneg_cosine {x : ℝ} (hx : 0≤x) :
    gudermannian x=Real.arccos ((Real.cosh x)⁻¹) := by
  have hcos:Real.cos (Real.arctan (Real.sinh x))=(Real.cosh x)⁻¹ := by
    rw [Real.cos_arctan,← Real.cosh_sq',Real.sqrt_sq (Real.cosh_pos x).le,one_div]
  rw [← hcos,Real.arccos_cos]
  · exact (gudermannian_elementary x).2.2
  · exact Real.arctan_nonneg.mpr (Real.sinh_nonneg_iff.mpr hx)
  · exact (Real.arctan_lt_pi_div_two _).le.trans (by linarith [Real.pi_pos])


/-- DLMF 4.23.E42: inverse gudermannian elementary. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_elementary {x : ℝ} (hx : |x|<π/2) :
    inverseGudermannian x=Real.log (Real.tan (x/2+π/4)) ∧
    inverseGudermannian x=Real.log ((Real.cos x)⁻¹+Real.tan x) ∧
    inverseGudermannian x=Real.arsinh (Real.tan x) ∧
    inverseGudermannian x=Real.artanh (Real.sin x) := by
  have ha:=trig_inverse_gd_arsinh hx
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)
  have hinv:gudermannian (inverseGudermannian x)=x := by
    rw [(gudermannian_elementary _).2.2,ha,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  have he:Real.exp (inverseGudermannian x)=Real.tan (x/2+π/4) := by
    rw [← Real.tan_arctan (Real.exp (inverseGudermannian x))]
    congr 1
    linarith [(gudermannian_elementary (inverseGudermannian x)).1]
  refine ⟨?_,?_,ha,?_⟩
  · rw [← he,Real.log_exp]
  · rw [ha,Real.arsinh,trig_sqrt_one_add_tan hx]
    congr 1
    ring
  · have hs:Real.sin x∈Ioo (-1:ℝ) 1 := by
      have hcircle:=Real.sin_sq_add_cos_sq x
      have hp:=sq_pos_of_pos hc
      constructor <;> nlinarith
    have hsqrt:Real.sqrt (1-(Real.sin x)^2)=Real.cos x := by
      rw [show 1-(Real.sin x)^2=(Real.cos x)^2 by nlinarith [Real.sin_sq_add_cos_sq x],Real.sqrt_sq hc.le]
    rw [ha]
    apply Real.sinh_injective
    rw [Real.sinh_arsinh,Real.sinh_artanh hs,hsqrt,Real.tan_eq_sin_div_cos]


/-- DLMF 4.23.E42: inverse gudermannian reciprocal. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_reciprocal {x : ℝ} (hx : |x|<π/2) (hx0 : x≠0) :
    inverseGudermannian x=Real.arsinh (Real.cot x)⁻¹ ∧
    inverseGudermannian x=Real.artanh (((Real.sin x)⁻¹)⁻¹) := by
  refine ⟨?_,?_⟩
  · simpa only [Real.cot_eq_cos_div_sin,inv_div,Real.tan_eq_sin_div_cos] using
      (inverse_gudermannian_elementary hx).2.2.1
  · simpa only [inv_inv] using (inverse_gudermannian_elementary hx).2.2.2


/-- The principal arccosh/arcsech forms require x nonnegative. -/
@[dlmf 4.23.E42]
theorem inverse_gudermannian_nonneg_cosh {x : ℝ} (hx : 0≤x) (hπ : x<π/2) :
    inverseGudermannian x=Real.arcosh ((Real.cos x)⁻¹) := by
  have hbound:|x|<π/2 := by rwa [abs_of_nonneg hx]
  have hc:0<Real.cos x := Real.cos_pos_of_mem_Ioo (abs_lt.mp hbound)
  have ht:0≤Real.tan x := by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hx (by linarith [Real.pi_pos])) hc.le
  have hcosh:Real.cosh (Real.arsinh (Real.tan x))=(Real.cos x)⁻¹ := by
    rw [Real.cosh_arsinh,trig_sqrt_one_add_tan hbound]
  rw [← hcosh,Real.arcosh_cosh (Real.arsinh_nonneg_iff.mpr ht)]
  exact (inverse_gudermannian_elementary hbound).2.2.1


/-- DLMF 4.23.viii: gudermannian inverse. -/
@[dlmf 4.23.viii]
theorem gudermannian_inverse {x : ℝ} (hx : |x|<π/2) (y : ℝ) :
    gudermannian (inverseGudermannian x)=x ∧ inverseGudermannian (gudermannian y)=y := by
  constructor
  · rw [(gudermannian_elementary _).2.2,(inverse_gudermannian_elementary hx).2.2.1,Real.sinh_arsinh]
    exact Real.arctan_tan (abs_lt.mp hx).1 (abs_lt.mp hx).2
  · have hy:|gudermannian y|<π/2 := by
      rw [(gudermannian_elementary y).2.2]
      exact abs_lt.mpr ⟨Real.neg_pi_div_two_lt_arctan _,Real.arctan_lt_pi_div_two _⟩
    rw [(inverse_gudermannian_elementary hy).2.2.1,(gudermannian_elementary y).2.2,
      Real.tan_arctan,Real.arsinh_sinh]


/-- DLMF 4.24.E1: hasSum arcsin principal. -/
@[dlmf 4.24.E1]
theorem hasSum_arcsin_principal {z : ℂ} (hz : ‖z‖≤1) :
    HasSum (fun n : ℕ => ((2*n).choose n:ℂ)*z^(2*n+1)/(4^n*(2*n+1))) (arcsinPrincipal z) := by
  sorry

/-- Arccosine series after factoring its square root, with the removable center handled separately. -/
@[dlmf 4.24.E2]
theorem hasSum_arccos_principal {z : ℂ} (hz : ‖1-z‖≤2) :
    HasSum (fun n : ℕ => Complex.sqrt (2*(1-z))*((2*n).choose n:ℂ)*(1-z)^n/(8^n*(2*n+1)))
      (arccosPrincipal z) := by
  sorry

/-- DLMF 4.24.E2: arccos series center. -/
@[dlmf 4.24.E2]
theorem arccos_series_center : arccosPrincipal 1=0 := by
  norm_num [arccosPrincipal,arcsinPrincipal,Complex.sqrt_zero]
  rw [Complex.log_I]
  norm_num [div_eq_mul_inv]
  linear_combination Complex.I_sq* (Real.pi:ℂ)/2


/-- Ordered partial sums retain conditional convergence on the unit circle. -/
@[dlmf 4.24.E3]
theorem hasSum_arctan_closed_disc {z : ℂ} (hz : ‖z‖≤1) (hp : z≠I) (hm : z≠ -I) :
    Tendsto (fun N : ℕ => ∑ n∈Finset.range N,(-1:ℂ)^n*z^(2*n+1)/(2*n+1)) atTop
      (𝓝 (Complex.arctan z)) := by
  sorry

/-- DLMF 4.24.E4: arctan exterior series. -/
@[dlmf 4.24.E4]
theorem arctan_exterior_series {z : ℂ} (hz : 1≤‖z‖) (hr : z.re≠0) :
    Tendsto (fun N : ℕ => (if 0<z.re then (π:ℂ)/2 else -π/2)-
      ∑ n∈Finset.range N,(-1:ℂ)^n/(z^(2*n+1)*(2*n+1))) atTop (𝓝 (Complex.arctan z)) := by
  sorry

/-- Euler transformed arctangent series, with its removable zero excluded. -/
@[dlmf 4.24.E5]
theorem hasSum_arctan_euler {z : ℂ} (hz : -(1/2:ℝ)<(z^2).re) :
    HasSum (fun n : ℕ => z/(1+z^2)*(4:ℂ)^n*(n.factorial:ℂ)^2/(2*n+1)!*(z^2/(1+z^2))^n)
      (Complex.arctan z) := by
  sorry

/-- DLMF 4.24.E6: arctan euler domain. -/
@[dlmf 4.24.E6]
theorem arctan_euler_domain (z : ℂ) : -(1/2:ℝ)<(z^2).re ↔ -(1/2:ℝ)<z.re^2-z.im^2 := by
  simp [Complex.mul_re,pow_two]

/-- DLMF 4.24.E7: hasDerivAt arcsin principal. -/
@[dlmf 4.24.E7]
theorem hasDerivAt_arcsin_principal {z : ℂ} (hz : z∈arcsinCutPlane) : HasDerivAt arcsinPrincipal ((Complex.sqrt (1-z^2))⁻¹) z := by
  exact trig_hasDerivAt_arcsin hz


/-- DLMF 4.24.E8: hasDerivAt arccos principal. -/
@[dlmf 4.24.E8]
theorem hasDerivAt_arccos_principal {z : ℂ} (hz : z∈arcsinCutPlane) : HasDerivAt arccosPrincipal (-(Complex.sqrt (1-z^2))⁻¹) z := by
  exact (trig_hasDerivAt_arcsin hz).const_sub ((π:ℂ)/2)


/-- DLMF 4.24.E9: hasDerivAt arctan principal. -/
@[dlmf 4.24.E9]
theorem hasDerivAt_arctan_principal {z : ℂ} (hz : z∈arctanCutPlane) : HasDerivAt Complex.arctan ((1+z^2)⁻¹) z := by
  exact trig_hasDerivAt_arctan hz


/-- DLMF 4.24.E10: hasDerivAt arccsc principal. -/
@[dlmf 4.24.E10]
theorem hasDerivAt_arccsc_principal {z : ℂ} (hz : z∈arccscCutPlane) (hr : z.re≠0) : HasDerivAt arccscPrincipal (-(if 0<z.re then 1 else -1)/(z*Complex.sqrt (z^2-1))) z := by
  sorry

/-- DLMF 4.24.E11: hasDerivAt arcsec principal. -/
@[dlmf 4.24.E11]
theorem hasDerivAt_arcsec_principal {z : ℂ} (hz : z∈arccscCutPlane) (hr : z.re≠0) : HasDerivAt arcsecPrincipal ((if 0<z.re then 1 else -1)/(z*Complex.sqrt (z^2-1))) z := by
  sorry

/-- DLMF 4.24.E12: hasDerivAt arccot principal. -/
@[dlmf 4.24.E12]
theorem hasDerivAt_arccot_principal {z : ℂ} (hz : z∈arccotCutPlane) : HasDerivAt arccotPrincipal (-(1+z^2)⁻¹) z := by
  have hd:=(trig_hasDerivAt_arctan hz.2).comp z ((hasDerivAt_id z).inv hz.1)
  convert hd using 1
  · rfl
  · dsimp only [id]
    field_simp [hz.1]
    ring


/-- Minkowski addition with an independently chosen sign. -/
def inverseTrigSum (A B : Set ℂ) (σ : ℂ) : Set ℂ := {w | ∃ a∈A,∃ b∈B,w=a+σ*b}

/-- Arcsine addition with root signs correlated to the chosen inverse values. -/
@[dlmf 4.24.E13]
theorem arcsin_general_add (u v a b σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (ha : a∈arcsinGeneral u) (hb : b∈arcsinGeneral v) :
    (Complex.cos a)^2=1-u^2 ∧ (Complex.cos b)^2=1-v^2 ∧
    a+σ*b∈arcsinGeneral (u*Complex.cos b+σ*v*Complex.cos a) := by
  simp only [arcsinGeneral,mem_setOf_eq] at ha hb ⊢
  rcases hσ with rfl | rfl <;>
    simp_all [Complex.cos_sq',Complex.sin_add,Complex.sin_neg,Complex.cos_neg,mul_comm,mul_left_comm,mul_assoc]

/-- DLMF 4.24.E14: arccos general add. -/
@[dlmf 4.24.E14]
theorem arccos_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1) :
    inverseTrigSum (arccosGeneral u) (arccosGeneral v) σ=
      {w | ∃ r : ℂ,r^2=(1-u^2)*(1-v^2) ∧ w∈arccosGeneral (u*v-σ*r)} := by
  sorry

/-- DLMF 4.24.E15: arctan general add. -/
@[dlmf 4.24.E15]
theorem arctan_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hu : u≠I ∧ u≠ -I) (hv : v≠I ∧ v≠ -I) (hd : 1-σ*u*v≠0) :
    inverseTrigSum (arctanGeneral u) (arctanGeneral v) σ=arctanGeneral ((u+σ*v)/(1-σ*u*v)) := by
  sorry

/-- Mixed addition with consistent inverse and square-root branches. -/
@[dlmf 4.24.E16]
theorem arcsin_arccos_general_add (u v a b σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (ha : a∈arcsinGeneral u) (hb : b∈arccosGeneral v) :
    (Complex.cos a)^2=1-u^2 ∧ (Complex.sin b)^2=1-v^2 ∧
    a+σ*b∈arcsinGeneral (u*v+σ*Complex.cos a*Complex.sin b) ∧
    a+σ*b∈arccosGeneral (v*Complex.cos a-σ*u*Complex.sin b) := by
  simp only [arcsinGeneral,arccosGeneral,mem_setOf_eq] at ha hb ⊢
  rcases hσ with rfl | rfl <;>
    simp_all [Complex.cos_sq',Complex.sin_sq,Complex.sin_add,Complex.cos_add,
      Complex.sin_neg,Complex.cos_neg,mul_comm,mul_left_comm,mul_assoc]

/-- DLMF 4.24.E17: arctan arccot general add. -/
@[dlmf 4.24.E17]
theorem arctan_arccot_general_add (u v σ : ℂ) (hσ : σ=1 ∨ σ= -1)
    (hu : u≠I ∧ u≠ -I) (hv : v≠I ∧ v≠ -I)
    (h1 : v-σ*u≠0) (h2 : u*v+σ≠0) :
    inverseTrigSum (arctanGeneral u) (arccotGeneral v) σ=arctanGeneral ((u*v+σ)/(v-σ*u)) ∧
    inverseTrigSum (arctanGeneral u) (arccotGeneral v) σ=arccotGeneral ((v-σ*u)/(u*v+σ)) := by
  sorry

/-- DLMF 4.25.E1: tan continued fraction. -/
@[dlmf 4.25.E1]
theorem tan_continued_fraction {z : ℂ} (hz : Complex.cos z≠0) :
    DLMF.HasContinuedFraction (fun k => if k=0 then z else -z^2)
      (fun k => 2*k+1) (Complex.tan z) := by
  sorry

/-- DLMF 4.25.E2: tan scaled continued fraction. -/
@[dlmf 4.25.E2]
theorem tan_scaled_continued_fraction (a : ℂ) {z : ℂ} (hz : |z.re|<π/2) (ha : Complex.cos (a*z)≠0) :
    DLMF.HasContinuedFraction
      (fun k => if k=0 then a*Complex.tan z else ((k:ℂ)^2-a^2)*(Complex.tan z)^2)
      (fun k => 2*k+1) (Complex.tan (a*z)) := by
  sorry

/-- DLMF 4.25.E3: arcsin continued fraction. -/
@[dlmf 4.25.E3]
theorem arcsin_continued_fraction {z : ℂ} (hz : z∈arcsinCutPlane) :
    DLMF.HasContinuedFraction
      (fun k => if k=0 then z else -(((2*((k+1)/2)-1)*(2*((k+1)/2)):ℕ):ℂ)*z^2)
      (fun k => 2*k+1) (arcsinPrincipal z/Complex.sqrt (1-z^2)) := by
  sorry

/-- DLMF 4.25.E4: arctan continued fraction. -/
@[dlmf 4.25.E4]
theorem arctan_continued_fraction {z : ℂ} (hz : z∈arctanCutPlane) :
    DLMF.HasContinuedFraction (fun k => if k=0 then z else (k:ℂ)^2*z^2)
      (fun k => 2*k+1) (Complex.arctan z) := by
  sorry

/-- DLMF 4.25.E5: exp arccot continued fraction. -/
@[dlmf 4.25.E5]
theorem exp_arccot_continued_fraction (a : ℂ) {z : ℂ} (hz : z∈arccotCutPlane) :
    DLMF.HasContinuedFraction (fun k => if k=0 then 2*a else a^2+(k:ℂ)^2)
      (fun k => if k=0 then z-a else (2*k+1)*z) (Complex.exp (2*a*arccotPrincipal z)-1) := by
  sorry


/-! ## Exact trigonometric tables -/

/-- The six real trigonometric functions in the order used by the exact-value tables. -/
def trigRealVector (θ : ℝ) : Fin 6→ℝ :=
  ![Real.sin θ,Real.cos θ,Real.tan θ,(Real.sin θ)⁻¹,(Real.cos θ)⁻¹,Real.cot θ]

/-- Signs of the six functions in quadrants I, II, III and IV. -/
def trigQuadrantSigns : Fin 4→Fin 6→ℝ :=
  ![![1,1,1,1,1,1],![1,-1,-1,1,-1,-1],![-1,-1,1,-1,-1,1],![-1,1,-1,-1,1,-1]]

/-- DLMF 4.16.T1: trig quadrant signs. -/
@[dlmf 4.16.T1]
theorem trig_quadrant_signs (q : Fin 4) {θ : ℝ}
    (hθ : θ∈Ioo ((q:ℝ)*π/2) (((q:ℝ)+1)*π/2)) (j : Fin 6) :
    trigRealSign (trigRealVector θ j)=trigQuadrantSigns q j := by
  sorry

/-- All quarter-period identities; reflection and the full period supply both signs in Table 4.16.2. -/
@[dlmf 4.16.T2]
theorem trig_quarter_period_table (θ : ℝ) (q : Fin 4) :
    trigRealVector (θ+(q:ℝ)*π/2)=
    (![trigRealVector θ,
      ![Real.cos θ,-Real.sin θ,-Real.cot θ,(Real.cos θ)⁻¹,-(Real.sin θ)⁻¹,-Real.tan θ],
      ![-Real.sin θ,-Real.cos θ,Real.tan θ,-(Real.sin θ)⁻¹,-(Real.cos θ)⁻¹,Real.cot θ],
      ![-Real.cos θ,Real.sin θ,-Real.cot θ,-(Real.cos θ)⁻¹,(Real.sin θ)⁻¹,-Real.tan θ]] : Fin 4→Fin 6→ℝ) q := by
  have hs3 : Real.sin (3*Real.pi/2)= -1 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.sin_add]
    norm_num
  have hc3 : Real.cos (3*Real.pi/2)=0 := by
    rw [show (3:ℝ)*Real.pi/2=Real.pi+Real.pi/2 by ring,Real.cos_add]
    norm_num
  fin_cases q <;> ext j <;> fin_cases j <;>
    norm_num [trigRealVector,Real.tan_eq_sin_div_cos,Real.cot_eq_cos_div_sin,
      Real.sin_add,Real.cos_add,hs3,hc3,neg_div,div_neg]

/-- Algebraic interrelations; rows are output functions, columns are the known function. -/
def trigInterrelationTable (a : ℝ) : Fin 6→Fin 6→ℝ :=
  ![![a,Real.sqrt (1-a^2),a/Real.sqrt (1+a^2),a⁻¹,Real.sqrt (a^2-1)/a,(Real.sqrt (1+a^2))⁻¹],
    ![Real.sqrt (1-a^2),a,(Real.sqrt (1+a^2))⁻¹,Real.sqrt (a^2-1)/a,a⁻¹,a/Real.sqrt (1+a^2)],
    ![a/Real.sqrt (1-a^2),Real.sqrt (1-a^2)/a,a,(Real.sqrt (a^2-1))⁻¹,Real.sqrt (a^2-1),a⁻¹],
    ![a⁻¹,(Real.sqrt (1-a^2))⁻¹,Real.sqrt (1+a^2)/a,a,a/Real.sqrt (a^2-1),Real.sqrt (1+a^2)],
    ![(Real.sqrt (1-a^2))⁻¹,a⁻¹,Real.sqrt (1+a^2),a/Real.sqrt (a^2-1),a,Real.sqrt (1+a^2)/a],
    ![Real.sqrt (1-a^2)/a,a/Real.sqrt (1-a^2),a⁻¹,Real.sqrt (a^2-1),(Real.sqrt (a^2-1))⁻¹,a]]

/-- Every cell of the interrelation table, with its nonnegative finite principal-root convention. -/
@[dlmf 4.16.T3]
theorem trig_interrelation_table {θ : ℝ} (hs : 0<Real.sin θ) (hc : 0<Real.cos θ) (i j : Fin 6) :
    trigRealVector θ i=trigInterrelationTable (trigRealVector θ j) i j := by
  sorry

/-- Exact values at all multiples of pi/12 from zero to pi; pole cells contain placeholders. -/
def trigTwelfthTable : Fin 13→Fin 6→ℝ :=
  let r := Real.sqrt 2
  let t := Real.sqrt 3
  ![![0,1,0,0,1,0],
    ![r*(t-1)/4,r*(t+1)/4,2-t,r*(t+1),r*(t-1),2+t],
    ![1/2,t/2,t/3,2,2*t/3,t],
    ![r/2,r/2,1,r,r,1],
    ![t/2,1/2,t,2*t/3,2,t/3],
    ![r*(t+1)/4,r*(t-1)/4,2+t,r*(t-1),r*(t+1),2-t],
    ![1,0,0,1,0,0],
    ![r*(t+1)/4,-r*(t-1)/4,-(2+t),r*(t-1),-r*(t+1),-(2-t)],
    ![t/2,-1/2,-t,2*t/3,-2,-t/3],
    ![r/2,-r/2,-1,r,-r,-1],
    ![1/2,-t/2,-t/3,2,-2*t/3,-t],
    ![r*(t-1)/4,-r*(t+1)/4,-(2-t),r*(t+1),-r*(t-1),-(2+t)],
    ![0,-1,0,0,-1,0]]

/-- Pole cells of the exact trigonometric value table; they are not finite values. -/
def trigTwelfthPole (q : Fin 13) (j : Fin 6) : Prop :=
  ((q=0 ∨ q=12) ∧ (j=3 ∨ j=5)) ∨ (q=6 ∧ (j=2 ∨ j=4))

/-- DLMF 4.17.T1: trig twelfth exact values. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_exact_values (q : Fin 13) (j : Fin 6) (h : ¬trigTwelfthPole q j) :
    trigRealVector ((q:ℝ)*π/12) j=trigTwelfthTable q j := by
  sorry

/-- DLMF 4.17.T1: trig twelfth poles. -/
@[dlmf 4.17.T1]
theorem trig_twelfth_poles (q : Fin 13) (j : Fin 6) (h : trigTwelfthPole q j) :
    Tendsto (fun θ : ℝ => |trigRealVector θ j|) (𝓝[≠] ((q:ℝ)*π/12)) atTop := by
  sorry

/-- Real inverse functions where the table specifies finite real values. -/
def inverseTrigRealVector (x : ℝ) : Fin 6→ℝ :=
  ![Real.arcsin x,Real.arccos x,Real.arctan x,Real.arcsin x⁻¹,Real.arccos x⁻¹,Real.arctan x⁻¹]

/-- DLMF 4.23.T1: inverse trig exact table. -/
@[dlmf 4.23.T1]
theorem inverse_trig_exact_table (q : Fin 3) (j : Fin 6) (h : q≠1 ∨ (j:ℕ)<3) :
    inverseTrigRealVector ((q:ℝ)-1) j=
      (![![-π/2,π,-π/4,-π/2,π,-π/4],![0,π/2,0,0,0,0],![π/2,0,π/4,π/2,0,π/4]] : Fin 3→Fin 6→ℝ) q j := by
  fin_cases q <;> fin_cases j <;>
    norm_num [inverseTrigRealVector,Real.arcsin_neg,Real.arccos_neg,Real.arctan_neg,neg_div] at *

/-- DLMF 4.23.T1: inverse reciprocal limits. -/
@[dlmf 4.23.T1]
theorem inverse_reciprocal_limits (positive : Bool) :
    Tendsto (fun x : ℝ => Real.arcsin x⁻¹) (if positive then atTop else atBot) (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.arccos x⁻¹) (if positive then atTop else atBot) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
  have hi : Tendsto (fun x : ℝ => x⁻¹) (if positive then atTop else atBot) (𝓝 0) := by
    cases positive
    · exact tendsto_inv_atBot_zero
    · exact tendsto_inv_atTop_zero
  exact ⟨by simpa [Function.comp_def] using (Real.continuous_arcsin.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arccos.tendsto 0).comp hi,
    by simpa [Function.comp_def] using (Real.continuous_arctan.tendsto 0).comp hi⟩

/-- DLMF 4.23.T1: arccot zero bank limits. -/
@[dlmf 4.23.T1]
theorem arccot_zero_bank_limits :
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[>] 0) (𝓝 (π/2)) ∧
    Tendsto (fun x : ℝ => Real.arctan x⁻¹) (𝓝[<] 0) (𝓝 (-π/2)) := by
  constructor
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[>] 0]
        (fun x => Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      exact Real.arctan_inv_of_pos hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm
  · have h := (Real.continuous_arctan.continuousAt (x:=0)).const_sub (-Real.pi/2)
    have heq : (fun x : ℝ => Real.arctan x⁻¹)=ᶠ[𝓝[<] 0]
        (fun x => -Real.pi/2-Real.arctan x) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simpa only [neg_div] using Real.arctan_inv_of_neg hx
    simpa using (h.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- The prose inverse secant/cotangent interrelation, with positive real finite principal roots. -/
@[dlmf 4.23.vii]
theorem arcsec_arccot_interrelation {a : ℝ} (ha : 1<a) :
    Real.arccos a⁻¹=Real.arctan (Real.sqrt (a^2-1)) := by
  rw [Real.arccos_eq_arctan (inv_pos.mpr (lt_trans zero_lt_one ha)),trig_sqrt_inverse ha]
  congr 1
  field_simp



/-! ## Antiderivatives and conditionally convergent improper integrals -/

/-- DLMF 4.26.E3: hasDerivAt neg log cos. -/
@[dlmf 4.26.E3]
theorem hasDerivAt_neg_log_cos {x : ℝ} (hx : |x|<π/2) : HasDerivAt (fun x : ℝ => -Real.log (Real.cos x)) (Real.tan x) x := by
  have hc : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  convert ((Real.hasDerivAt_cos x).log hc).neg using 1
  simp only [Real.tan_eq_sin_div_cos]
  ring

/-- DLMF 4.26.E4: hasDerivAt log tan half. -/
@[dlmf 4.26.E4]
theorem hasDerivAt_log_tan_half {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.tan (x/2))) ((Real.sin x)⁻¹) x := by
  have hhalf : x/2∈Ioo (-(π/2)) (π/2) := ⟨by linarith [Real.pi_pos,hx.1],by linarith [hx.2]⟩
  have hc : Real.cos (x/2)≠0 := (Real.cos_pos_of_mem_Ioo hhalf).ne'
  have hs : Real.sin (x/2)≠0 := (Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2,Real.pi_pos])).ne'
  have ht : Real.tan (x/2)≠0 := by simpa only [Real.tan_eq_sin_div_cos] using div_ne_zero hs hc
  have hd0 : HasDerivAt (fun t:ℝ=>Real.tan (t/2)) (1/Real.cos (x/2)^2*(1/2)) x := by
    exact (Real.hasDerivAt_tan (x:=x/2) hc).comp x ((hasDerivAt_id x).div_const (2:ℝ))
  have hd:=hd0.log ht
  convert hd using 1
  rw [Real.tan_eq_sin_div_cos]
  have hsin : Real.sin x=2*Real.sin (x/2)*Real.cos (x/2) := by
    rw [← Real.sin_two_mul,show (2:ℝ)*(x/2)=x by ring]
  rw [hsin]
  field_simp


/-- DLMF 4.26.E5: hasDerivAt inverse gudermannian. -/
@[dlmf 4.26.E5]
theorem hasDerivAt_inverse_gudermannian {x : ℝ} (hx : |x|<π/2) : HasDerivAt (inverseGudermannian) ((Real.cos x)⁻¹) x := by
  have hcos : ∀t∈uIcc (0:ℝ) x,Real.cos t≠0 := by
    intro t ht
    apply (Real.cos_pos_of_mem_Ioo _).ne'
    rcases le_total 0 x with h|h
    · rw [uIcc_of_le h] at ht
      exact ⟨by linarith [ht.1,Real.pi_pos],by linarith [ht.2,(abs_lt.mp hx).2]⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨by linarith [ht.1,(abs_lt.mp hx).1],by linarith [ht.2,Real.pi_pos]⟩
  have hcont : ContinuousOn (fun t:ℝ=>(Real.cos t)⁻¹) (uIcc 0 x) := Real.continuous_cos.continuousOn.inv₀ hcos
  have hxcos : Real.cos x≠0 := (Real.cos_pos_of_mem_Ioo (abs_lt.mp hx)).ne'
  apply intervalIntegral.integral_hasDerivAt_right hcont.intervalIntegrable
  · exact Real.continuous_cos.measurable.inv.aestronglyMeasurable.stronglyMeasurableAtFilter
  · exact Real.continuous_cos.continuousAt.inv₀ hxcos


/-- DLMF 4.26.E6: hasDerivAt log sin. -/
@[dlmf 4.26.E6]
theorem hasDerivAt_log_sin {x : ℝ} (hx : x∈Ioo 0 π) : HasDerivAt (fun x : ℝ => Real.log (Real.sin x)) (Real.cot x) x := by
  have hs : Real.sin x≠0 := (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'
  simpa only [Real.cot_eq_cos_div_sin] using (Real.hasDerivAt_sin x).log hs

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E7]
theorem hasDerivAt_exp_sin_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.sin (b*z)-b*Complex.cos (b*z)))
      (Complex.exp (a*z)*Complex.sin (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).csin.const_mul a).sub
      (((hasDerivAt_id z).const_mul b).ccos.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- The exponential-trigonometric primitive, valid for complex parameters when its denominator is nonzero. -/
@[dlmf 4.26.E8]
theorem hasDerivAt_exp_cos_antiderivative {a b : ℂ} (h : a^2+b^2≠0) (z : ℂ) :
    HasDerivAt (fun z : ℂ => Complex.exp (a*z)/(a^2+b^2)*(a*Complex.cos (b*z)+b*Complex.sin (b*z)))
      (Complex.exp (a*z)*Complex.cos (b*z)) z := by
  have hd := ((((hasDerivAt_id z).const_mul a).cexp.div_const (a^2+b^2)).mul
    ((((hasDerivAt_id z).const_mul b).ccos.const_mul a).add
      (((hasDerivAt_id z).const_mul b).csin.const_mul b)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- Integer sine orthogonality requires both m not equal n and m not equal -n. -/
@[dlmf 4.26.E9]
theorem integral_sin_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.sin ((m:ℝ)*t)*Real.sin ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)-Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_sub (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- Integer cosine orthogonality with the missing opposite-frequency exclusion. -/
@[dlmf 4.26.E10]
theorem integral_cos_integer_orthogonal (m n : ℤ) (hne : m≠n) (hneg : m≠ -n) :
    (∫ t in (0:ℝ)..π,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t))=0 := by
  have hp : m+n≠0 := by omega
  have hm : m-n≠0 := by omega
  have hc (k : ℤ) : IntervalIntegrable (fun t : ℝ => Real.cos ((k:ℝ)*t)) volume 0 Real.pi :=
    (by fun_prop : Continuous (fun t : ℝ => Real.cos ((k:ℝ)*t))).intervalIntegrable _ _
  have he : ∀ t : ℝ,Real.cos ((m:ℝ)*t)*Real.cos ((n:ℝ)*t)=
      (Real.cos (((m-n:ℤ):ℝ)*t)+Real.cos (((m+n:ℤ):ℝ)*t))/2 := by
    intro t
    push_cast
    rw [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_div,intervalIntegral.integral_add (hc _) (hc _),
    TauCeti.integral_cos_int_mul,TauCeti.integral_cos_int_mul,if_neg hm,if_neg hp]
  norm_num

/-- DLMF 4.26.E11: integral trig integer squares. -/
@[dlmf 4.26.E11]
theorem integral_trig_integer_squares {n : ℤ} (hn : n≠0) :
    (∫ t in (0:ℝ)..π,(Real.sin ((n:ℝ)*t))^2)=π/2 ∧
    (∫ t in (0:ℝ)..π,(Real.cos ((n:ℝ)*t))^2)=π/2 := by
  have hn' : (n:ℝ)≠0 := Int.cast_ne_zero.mpr hn
  constructor
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.sin x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_sin_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring
  · have h := intervalIntegral.mul_integral_comp_mul_left
      (f:=fun x : ℝ => Real.cos x^2) (a:=(0:ℝ)) (b:=Real.pi) (n:ℝ)
    rw [integral_cos_sq,mul_zero,Real.sin_zero,Real.sin_int_mul_pi] at h
    apply mul_left_cancel₀ hn'
    convert h using 1 <;> ring

/-- Dirichlet integral as an ordered improper limit, stronger real frequency version. -/
@[dlmf 4.26.E12]
theorem dirichlet_integral_scaled (m : ℝ) :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (m*t)/t) atTop
      (𝓝 (trigRealSign m*π/2)) := by
  sorry

/-- DLMF 4.26.E13: fresnel integrals elementary. -/
@[dlmf 4.26.E13]
theorem fresnel_integrals_elementary :
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.sin (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) ∧
    Tendsto (fun R : ℝ => ∫ t in (0:ℝ)..R,Real.cos (t^2)) atTop (𝓝 (Real.sqrt (π/2)/2)) := by
  sorry

/-- DLMF 4.26.E14: hasDerivAt arcsin antiderivative. -/
@[dlmf 4.26.E14]
theorem hasDerivAt_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arcsin x+Real.sqrt (1-x^2)) (Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arcsin hxm hx1)).add
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E15: hasDerivAt arccos antiderivative. -/
@[dlmf 4.26.E15]
theorem hasDerivAt_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => x*Real.arccos x-Real.sqrt (1-x^2)) (Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arccos hxm hx1)).sub
    ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E16: hasDerivAt arctan antiderivative. -/
@[dlmf 4.26.E16]
theorem hasDerivAt_arctan_antiderivative {x : ℝ} : HasDerivAt (fun x : ℝ => x*Real.arctan x-Real.log (1+x^2)/2) (Real.arctan x) x := by
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul (Real.hasDerivAt_arctan x)).sub
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring

/-- DLMF 4.26.E17: hasDerivAt arccsc antiderivative. -/
@[dlmf 4.26.E17]
theorem hasDerivAt_arccsc_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arcsin x⁻¹+Real.log (x+Real.sqrt (x^2-1))) (Real.arcsin x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arcsin t⁻¹) ((Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arcsin hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).add (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring


/-- DLMF 4.26.E18: hasDerivAt arcsec antiderivative. -/
@[dlmf 4.26.E18]
theorem hasDerivAt_arcsec_antiderivative {x : ℝ} (hx : 1<x) : HasDerivAt (fun x : ℝ => x*Real.arccos x⁻¹-Real.log (x+Real.sqrt (x^2-1))) (Real.arccos x⁻¹) x := by
  have hx0 : 0<x := lt_trans zero_lt_one hx
  have hi : x⁻¹<1 := inv_lt_one_of_one_lt₀ hx
  have hip : 0<x⁻¹ := inv_pos.mpr hx0
  have hxm : x⁻¹≠ -1 := by linarith
  have hs : 0<x^2-1 := by nlinarith
  have hs0 : Real.sqrt (x^2-1)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hinv : HasDerivAt (fun t:ℝ=>Real.arccos t⁻¹) (-(Real.sqrt (1-x⁻¹^2))⁻¹ * (-1/x^2)) x := by
    simpa only [one_div,id_eq,Function.comp_def] using (Real.hasDerivAt_arccos hxm hi.ne).comp x ((hasDerivAt_id x).inv hx0.ne')
  have hd := ((hasDerivAt_id x).mul hinv).sub (Real.hasDerivAt_arcosh hx)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
    rw [trig_sqrt_inverse hx]
    field_simp
    ring


/-- DLMF 4.26.E19: hasDerivAt arccot antiderivative. -/
@[dlmf 4.26.E19]
theorem hasDerivAt_arccot_antiderivative {x : ℝ} (hx : 0<x) : HasDerivAt (fun x : ℝ => x*Real.arctan x⁻¹+Real.log (1+x^2)/2) (Real.arctan x⁻¹) x := by
  have hx0 : x≠0 := hx.ne'
  have hlog : (1+x^2:ℝ)≠0 := by positivity
  have hd := ((hasDerivAt_id x).mul ((hasDerivAt_id x).inv hx0 |>.arctan)).add
    ((((hasDerivAt_id x).pow 2).const_add 1).log hlog |>.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.inv_apply,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring


/-- DLMF 4.26.E20: hasDerivAt mul arcsin antiderivative. -/
@[dlmf 4.26.E20]
theorem hasDerivAt_mul_arcsin_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arcsin x+x/4*Real.sqrt (1-x^2)) (x*Real.arcsin x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arcsin hxm hx1)).add
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- DLMF 4.26.E21: hasDerivAt mul arccos antiderivative. -/
@[dlmf 4.26.E21]
theorem hasDerivAt_mul_arccos_antiderivative {x : ℝ} (hx : |x|<1) : HasDerivAt (fun x : ℝ => (x^2/2-1/4)*Real.arccos x-x/4*Real.sqrt (1-x^2)) (x*Real.arccos x) x := by
  have hx1 : x≠1 := ne_of_lt (abs_lt.mp hx).2
  have hxm : x≠ -1 := ne_of_gt (abs_lt.mp hx).1
  have hs : 0<1-x^2 := by nlinarith [(abs_lt.mp hx).1,(abs_lt.mp hx).2]
  have hroot := Real.sq_sqrt hs.le
  have hroot0 : Real.sqrt (1-x^2)≠0 := (Real.sqrt_pos.mpr hs).ne'
  have hd := ((((hasDerivAt_id x).pow 2).div_const 2 |>.sub_const (1/4)).mul
    (Real.hasDerivAt_arccos hxm hx1)).sub
    (((hasDerivAt_id x).div_const 4).mul
      ((((hasDerivAt_id x).pow 2).const_sub 1).sqrt (ne_of_gt hs)))
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
    norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul] <;> field_simp <;> nlinarith

/-- Complex antiderivatives use local continuous logarithm branches and exclude reciprocal poles. -/
@[dlmf 4.26.i]
theorem complex_trig_log_primitives {U : Set ℂ} (hU : IsOpen U) {L : ℂ→ℂ}
    (hL : AnalyticOnNhd ℂ L U) {z : ℂ} (hz : z∈U) :
    ((∀ w∈U,Complex.exp (L w)=Complex.cos w) → HasDerivAt (fun w => -L w) (Complex.tan z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=Complex.sin w) → HasDerivAt L (Complex.cot z) z) ∧
    ((∀ w∈U,Complex.exp (L w)=sec w+Complex.tan w) →
      Complex.cos z≠0 → HasDerivAt L (sec z) z) := by
  have hdL:HasDerivAt L (deriv L z) z := (hL z hz).differentiableAt.hasDerivAt
  have hlog {f:ℂ→ℂ} {d:ℂ} (hf:HasDerivAt f d z)
      (he:∀w∈U,Complex.exp (L w)=f w) : HasDerivAt L (d/f z) z := by
    have heq:(fun w=>Complex.exp (L w))=ᶠ[𝓝 z] f := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact he w hw
    have hdexp:=hdL.cexp
    have hdeq:=hdexp.unique (hf.congr_of_eventuallyEq heq)
    have hf0:f z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    convert hdL using 1
    rw [← hdeq,he z hz]
    field_simp
  refine ⟨?_,?_,?_⟩
  · intro he
    have hd:=(hlog (Complex.hasDerivAt_cos z) he).neg
    convert hd using 1
    simp [Complex.tan,neg_div]
  · intro he
    simpa only [Complex.cot] using hlog (Complex.hasDerivAt_sin z) he
  · intro he hc
    have hd:=hlog ((hasDerivAt_sec hc).add (Complex.hasDerivAt_tan hc)) he
    have hdEq:sec z*Complex.tan z+1/(Complex.cos z)^2=(sec z+Complex.tan z)*sec z := by
      rw [sec]
      ring
    rw [hdEq] at hd
    have he0:sec z+Complex.tan z≠0 := by rw [← he z hz]; exact Complex.exp_ne_zero _
    simpa only [Pi.add_apply,mul_div_cancel_left₀ (sec z) he0] using hd



/-- Real phase-amplitude reduction with its argument convention made explicit. -/
@[dlmf 4.21.E1_5]
theorem trig_phase_amplitude (A B : ℝ) (u : ℂ) :
    (A:ℂ)*Complex.cos u+B*Complex.sin u=(Real.sqrt (A^2+B^2):ℂ)*
      Complex.cos (u-(Complex.arg ((A:ℂ)+B*I):ℂ)) := by
  let z:ℂ:=(A:ℂ)+B*I
  have hn:Real.sqrt (A^2+B^2)=‖z‖ := by
    rw [Complex.norm_def]
    congr 1
    simp [z,Complex.normSq]
    ring
  have hc:(‖z‖:ℂ)*Complex.cos (Complex.arg z:ℂ)=(A:ℂ) := by
    rw [← Complex.ofReal_cos,← Complex.ofReal_mul,Complex.norm_mul_cos_arg]
    simp [z]
  have hs:(‖z‖:ℂ)*Complex.sin (Complex.arg z:ℂ)=(B:ℂ) := by
    rw [← Complex.ofReal_sin,← Complex.ofReal_mul,Complex.norm_mul_sin_arg]
    simp [z]
  rw [hn,Complex.cos_sub]
  linear_combination -Complex.cos u*hc -Complex.sin u*hs


/-- The two rectangular hyperbolas bounding Euler's transformed arctangent domain. -/
@[dlmf 4.24.E6]
theorem arctan_euler_boundary (z : ℂ) :
    (z^2).re= -(1/2:ℝ) ↔ z.re^2-z.im^2= -(1/2:ℝ) := by
  simp [Complex.mul_re,pow_two]

/-- No analytic inverse branch of sine or cosine crosses either finite branch point. -/
@[dlmf 4.23.i]
theorem inverse_sin_cos_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)=z) ∨ (∀ z∈U,Complex.cos (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  rcases hInv with hs|hc
  · have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hs a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_sin (f a)).comp a hdf
    rw [hzero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.sin∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hc a haU]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(Complex.hasDerivAt_cos (f a)).comp a hdf
    rw [hzero,neg_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] Complex.cos∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra


/-- The logarithmic tangent branch points have no finite nonpolar inverse images. -/
@[dlmf 4.23.i]
theorem inverse_tan_cot_branch_points (a : ℂ) (ha : a=I ∨ a= -I) :
    arctanGeneral a=∅ ∧ arccotGeneral a=∅ := by
  have ha2:a^2= -1 := by rcases ha with rfl|rfl <;> simp
  constructor
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hc,ht⟩
    have hs:Complex.sin w=a*Complex.cos w := (div_eq_iff hc).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hs,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp
  · apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hs,ht⟩
    have hc:Complex.cos w=a*Complex.sin w := (div_eq_iff hs).mp ht
    have hp:=Complex.sin_sq_add_cos_sq w
    rw [hc,mul_pow,ha2] at hp
    ring_nf at hp
    norm_num at hp


/-- Reciprocal inverse sine/cosine branches have the same endpoint obstructions. -/
@[dlmf 4.23.i]
theorem inverse_reciprocal_branch_points (a : ℂ) (ha : a=1 ∨ a= -1) :
    ¬∃ U : Set ℂ,IsOpen U ∧ a∈U ∧ ∃ f : ℂ→ℂ,AnalyticOnNhd ℂ f U ∧
      ((∀ z∈U,Complex.sin (f z)≠0 ∧ csc (f z)=z) ∨
       (∀ z∈U,Complex.cos (f z)≠0 ∧ sec (f z)=z)) := by
  rintro ⟨U,hU,haU,f,hf,hInv⟩
  have hdf:=(hf a haU).differentiableAt.hasDerivAt
  have hai:a⁻¹=a := by rcases ha with rfl|rfl <;> norm_num
  rcases hInv with hs|hc
  · have hsval:Complex.sin (f a)=a := by
      simpa only [csc,inv_inv,hai] using congrArg Inv.inv (hs a haU).2
    have hzero:Complex.cos (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.cos_sq',hsval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_csc (hs a haU).1).comp a hdf
    have hcot:Complex.cot (f a)=0 := by simp [Complex.cot,hzero]
    rw [hcot,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] csc∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hs z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra
  · have hcval:Complex.cos (f a)=a := by
      simpa only [sec,inv_inv,hai] using congrArg Inv.inv (hc a haU).2
    have hzero:Complex.sin (f a)=0 := by
      apply sq_eq_zero_iff.mp
      rw [Complex.sin_sq,hcval]
      rcases ha with rfl|rfl <;> norm_num
    have hd:=(hasDerivAt_sec (hc a haU).1).comp a hdf
    have htan:Complex.tan (f a)=0 := by simp [Complex.tan,hzero]
    rw [htan,mul_zero,zero_mul] at hd
    have heq:id=ᶠ[𝓝 a] sec∘f := by
      filter_upwards [hU.mem_nhds haU] with z hz
      exact (hc z hz).2.symm
    have hcontra:=(hd.congr_of_eventuallyEq heq).unique (hasDerivAt_id a)
    norm_num at hcontra


/-- Principal complex inverse-sine and cosine primitives on their common cut plane. -/
@[dlmf 4.26.i]
theorem complex_inverse_sin_cos_primitives {z : ℂ} (hz : z∈arcsinCutPlane) :
    HasDerivAt (fun w : ℂ => w*arcsinPrincipal w+Complex.sqrt (1-w^2)) (arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arccosPrincipal w-Complex.sqrt (1-w^2)) (arccosPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arcsinPrincipal w+w/4*Complex.sqrt (1-w^2))
      (z*arcsinPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => (w^2/2-1/4)*arccosPrincipal w-w/4*Complex.sqrt (1-w^2))
      (z*arccosPrincipal z) z := by
  have hq:=trig_one_sub_sq_slit hz
  have hr:Complex.sqrt (1-z^2)≠0 := by
    intro h
    have hs:=trig_sqrt_sq (1-z^2)
    rw [h,zero_pow two_ne_zero] at hs
    exact (Complex.mem_slitPlane_iff_arg.mp hq).2 hs.symm
  have hS:HasDerivAt (fun w:ℂ=>Complex.sqrt (1-w^2)) (-z/Complex.sqrt (1-z^2)) z := by
    convert (trig_hasDerivAt_sqrt hq).comp z (((hasDerivAt_id z).pow 2).const_sub 1) using 1 <;>
      simp only [id_eq,Function.comp_def,Pi.pow_apply,Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one] <;> ring
  have hA:=trig_hasDerivAt_arcsin hz
  have hC:=hasDerivAt_arccos_principal hz
  have hroot:=trig_sqrt_sq (1-z^2)
  refine ⟨?_,?_,?_,?_⟩
  · have hd:=((hasDerivAt_id z).mul hA).add hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.add_apply]
      field_simp
      ring
  · have hd:=((hasDerivAt_id z).mul hC).sub hS
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply]
      field_simp
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hA |>.add
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring
  · have hd:=((((hasDerivAt_id z).pow 2).div_const 2).sub_const (1/4)).mul hC |>.sub
      (((hasDerivAt_id z).div_const 4).mul hS)
    convert hd using 1
    · rfl
    · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.add_apply,Pi.pow_apply]
      norm_num only [Nat.cast_ofNat,Nat.reduceSub,pow_one,mul_one,one_mul]
      field_simp
      rw [hroot]
      ring


/-- The complex arctangent primitive on its principal cut plane. -/
@[dlmf 4.26.i]
theorem complex_arctan_primitive {z : ℂ} (hz : z∈arctanCutPlane) :
    HasDerivAt (fun w : ℂ => w*Complex.arctan w-Complex.log (1+w^2)/2) (Complex.arctan z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit hz)).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (trig_hasDerivAt_arctan hz)).sub (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.sub_apply,Pi.pow_apply]
    field_simp
    ring


/-- Reciprocal inverse primitives on the right component, using principal square roots and logs. -/
@[dlmf 4.26.i]
theorem complex_reciprocal_inverse_primitives {z : ℂ} (hz : z∈arccscCutPlane) (hr : 0<z.re) :
    HasDerivAt (fun w : ℂ => w*arccscPrincipal w+Complex.log (w+Complex.sqrt (w^2-1)))
      (arccscPrincipal z) z ∧
    HasDerivAt (fun w : ℂ => w*arcsecPrincipal w-Complex.log (w+Complex.sqrt (w^2-1)))
      (arcsecPrincipal z) z := by
  sorry

/-- The inverse cotangent primitive away from the imaginary logarithm cuts. -/
@[dlmf 4.26.i]
theorem complex_arccot_primitive {z : ℂ} (hz : z∈arccotCutPlane) (hr : z.re≠0) :
    HasDerivAt (fun w : ℂ => w*arccotPrincipal w+Complex.log (1+w^2)/2) (arccotPrincipal z) z := by
  have hlog := (Complex.hasDerivAt_log (trig_one_add_sq_slit (Or.inl hr))).comp z
    (((hasDerivAt_id z).pow 2).const_add 1)
  have hd := ((hasDerivAt_id z).mul (hasDerivAt_arccot_principal hz)).add (hlog.div_const 2)
  convert hd using 1
  · rfl
  · dsimp only [id,Pi.mul_apply,Pi.add_apply,Pi.pow_apply]
    field_simp
    ring


end DLMF.Elementary
