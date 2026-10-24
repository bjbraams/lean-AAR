/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.Core.Framework
public import DLMF.Core.Upstream
public import Mathlib.Analysis.Complex.SqrtDeriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import ToMathlib.NumberTheory.EulerNumbers

/-!
# Hyperbolic and inverse hyperbolic functions (DLMF §§4.28–4.41)

This acquisition retains complex arguments, principal branches, the two sides of cuts,
convergence of series/products/continued fractions, exact algebraic tables, and prose results.
Upstream coverage is recorded separately in `DLMF.Elementary.MathlibCoverage`.

Reciprocals have Lean's totalized values at poles; every meromorphic identity requiring a
finite value has its pole exclusions stated. The inverse functions below choose one value on
each cut; the other cut value is represented by a one-sided limit. Multivalued inverses are
sets of solutions, with poles excluded from the inverse equations.

The Mathlib real inverse functions `Real.arsinh`, `Real.arcosh`, `Real.artanh` are reused for
real antiderivatives. TauCeti's real tanh/artanh additions and derivative declarations are
credited in the separate upstream coverage fragment; no upstream proofs are copied here.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory
open scoped Real Topology
namespace DLMF.Elementary

/-- The hyperbolic cosecant, totalized at its poles. -/
@[dlmf 4.28.E5]
def csch (z : ℂ) : ℂ := (Complex.sinh z)⁻¹
/-- The hyperbolic secant, totalized at its poles. -/
@[dlmf 4.28.E6]
def sech (z : ℂ) : ℂ := (Complex.cosh z)⁻¹
/-- The hyperbolic cotangent, totalized at its poles. -/
@[dlmf 4.28.E7]
def coth (z : ℂ) : ℂ := Complex.cosh z/Complex.sinh z
/-- The open principal domain of arcsinh (the imaginary rays beyond ±i are cut). -/
def arcsinhDomain : Set ℂ := {z | z.re ≠ 0 ∨ |z.im| < 1}
/-- The open principal domain of arccosh, with the real ray up to 1 removed. -/
def arccoshDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < z.re}
/-- The open principal domain of arctanh (the real rays beyond ±1 are cut). -/
def arctanhDomain : Set ℂ := {z | z.im ≠ 0 ∨ |z.re| < 1}
/-- The open principal domain of arccsch, obtained by inversion of the arcsinh domain. -/
def arccschDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arcsinhDomain}
/-- The open principal domain of arcsech, obtained by inversion of the arccosh domain. -/
def arcsechDomain : Set ℂ := {z | z ≠ 0 ∧ z⁻¹ ∈ arccoshDomain}
/-- The open principal domain of arccoth, with the segment [-1,1] removed. -/
def arccothDomain : Set ℂ := {z | z.im ≠ 0 ∨ 1 < |z.re|}
/-- Principal inverse sinh; cut-side statements below remove the tie at the square-root cut. -/
@[dlmf 4.37.E16]
def arcsinh (z : ℂ) : ℂ := Complex.log (Complex.sqrt (z^2+1)+z)
/-- Principal inverse cosh, with the square roots factored to preserve the negative half-plane. -/
def arccosh (z : ℂ) : ℂ := Complex.log (z+Complex.sqrt (z-1)*Complex.sqrt (z+1))
/-- Principal inverse tanh off its poles, with the principal logarithm's cut convention. -/
@[dlmf 4.37.E24]
def arctanh (z : ℂ) : ℂ := Complex.log ((1+z)/(1-z))/2
/-- Principal inverse hyperbolic cosecant. -/
@[dlmf 4.37.E7]
def arccsch (z : ℂ) : ℂ := arcsinh z⁻¹
/-- Principal inverse hyperbolic secant. -/
@[dlmf 4.37.E8]
def arcsech (z : ℂ) : ℂ := arccosh z⁻¹
/-- Principal inverse hyperbolic cotangent; the value at zero is a cut-side value. -/
def arccoth (z : ℂ) : ℂ := if z=0 then π*I/2 else arctanh z⁻¹
/-- All finite inverse-sinh values. -/
def arcsinhValues (z : ℂ) : Set ℂ := {w | Complex.sinh w=z}
/-- All finite inverse-cosh values. -/
def arccoshValues (z : ℂ) : Set ℂ := {w | Complex.cosh w=z}
/-- All finite inverse-tanh values; totalized pole values are excluded. -/
def arctanhValues (z : ℂ) : Set ℂ := {w | Complex.cosh w ≠ 0 ∧ Complex.tanh w=z}
/-- All finite inverse-csch values. -/
def arccschValues (z : ℂ) : Set ℂ := {w | Complex.sinh w ≠ 0 ∧ csch w=z}
/-- All finite inverse-sech values. -/
def arcsechValues (z : ℂ) : Set ℂ := {w | Complex.cosh w ≠ 0 ∧ sech w=z}
/-- All finite inverse-coth values. -/
def arccothValues (z : ℂ) : Set ℂ := {w | Complex.sinh w ≠ 0 ∧ coth w=z}
/-- Analytic logarithm normalized at the origin, used when the principal logarithm can wrap. -/
def HyperbolicNormalizedLog (U : Set ℂ) (f L : ℂ → ℂ) : Prop :=
  AnalyticOnNhd ℂ L U ∧ L 0=0 ∧ ∀ z ∈ U, Complex.exp (L z)=f z
/-- The removable sinh quotient at the origin. -/
def sinhc (z : ℂ) : ℂ := if z=0 then 1 else Complex.sinh z/z
/-- The removable tanh quotient at the origin. -/
def tanhc (z : ℂ) : ℂ := if z=0 then 1 else Complex.tanh z/z
/-- Real nonnegative finite values, fixing the square-root convention in Table4.30.1. -/
def HyperbolicPositive (z : ℂ) : Prop :=
  Complex.sinh z ≠ 0 ∧ Complex.cosh z ≠ 0 ∧
  0 ≤ (Complex.sinh z).re ∧ (Complex.sinh z).im=0 ∧
  0 ≤ (Complex.cosh z).re ∧ (Complex.cosh z).im=0
/-- The six hyperbolic functions in the row order of Table4.30.1. -/
def hyperbolicSix (z : ℂ) : Fin 6 → ℂ := ![Complex.sinh z,Complex.cosh z,Complex.tanh z,csch z,sech z,coth z]
/-- coth eq inv tanh. -/
@[dlmf 4.28.E7]
theorem coth_eq_inv_tanh (z : ℂ) : coth z=(Complex.tanh z)⁻¹ := by
  simp [coth, Complex.tanh_eq_sinh_div_cosh, inv_div]

/-- csc mul I. -/
@[dlmf 4.28.E11]
theorem csc_mul_I (z : ℂ) : (Complex.sin (I*z))⁻¹= -I*csch z := by
  simp [mul_comm I z, Complex.sin_mul_I, csch, mul_inv_rev, Complex.inv_I, mul_comm]

/-- sec mul I. -/
@[dlmf 4.28.E12]
theorem sec_mul_I (z : ℂ) : (Complex.cos (I*z))⁻¹=sech z := by
  rw [mul_comm I z, Complex.cos_mul_I]; rfl

/-- cot mul I. -/
@[dlmf 4.28.E13]
theorem cot_mul_I (z : ℂ) : (Complex.tan (I*z))⁻¹= -I*coth z := by
  simp [mul_comm I z, Complex.tan_mul_I, coth_eq_inv_tanh, mul_inv_rev, Complex.inv_I, mul_comm]

/-- sinh zeros. -/
theorem sinh_zeros (z : ℂ) : Complex.sinh z=0 ↔ ∃ k : ℤ, z=(k:ℂ)*π*I := by
  sorry

/-- cosh zeros. -/
theorem cosh_zeros (z : ℂ) : Complex.cosh z=0 ↔ ∃ k : ℤ, z=((k:ℂ)+1/2)*π*I := by
  sorry

/-- Table4.30.1, column1: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_0 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 0=a) :
    hyperbolicSix z = ![a,Complex.sqrt (1+a^2),a/Complex.sqrt (1+a^2),a⁻¹,1/Complex.sqrt (1+a^2),Complex.sqrt (1+a^2)/a] := by
  sorry

/-- Table4.30.1, column2: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_1 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 1=a) :
    hyperbolicSix z = ![Complex.sqrt (a^2-1),a,Complex.sqrt (a^2-1)/a,1/Complex.sqrt (a^2-1),a⁻¹,a/Complex.sqrt (a^2-1)] := by
  sorry

/-- Table4.30.1, column3: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_2 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 2=a) :
    hyperbolicSix z = ![a/Complex.sqrt (1-a^2),1/Complex.sqrt (1-a^2),a,Complex.sqrt (1-a^2)/a,Complex.sqrt (1-a^2),a⁻¹] := by
  sorry

/-- Table4.30.1, column4: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_3 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 3=a) :
    hyperbolicSix z = ![a⁻¹,Complex.sqrt (1+a^2)/a,1/Complex.sqrt (1+a^2),a,a/Complex.sqrt (1+a^2),Complex.sqrt (1+a^2)] := by
  sorry

/-- Table4.30.1, column5: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_4 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 4=a) :
    hyperbolicSix z = ![Complex.sqrt (1-a^2)/a,a⁻¹,Complex.sqrt (1-a^2),a/Complex.sqrt (1-a^2),a,1/Complex.sqrt (1-a^2)] := by
  sorry

/-- Table4.30.1, column6: all six entries with the stated real nonnegative branch. -/
@[dlmf 4.30.T1]
theorem hyperbolic_interrelations_5 {z a : ℂ} (hz : HyperbolicPositive z) (ha : hyperbolicSix z 5=a) :
    hyperbolicSix z = ![1/Complex.sqrt (a^2-1),a/Complex.sqrt (a^2-1),a⁻¹,Complex.sqrt (a^2-1),Complex.sqrt (a^2-1)/a,a] := by
  sorry

/-- sinh div limit. -/
@[dlmf 4.31.E1]
theorem sinh_div_limit  : Tendsto (fun z : ℂ => Complex.sinh z/z) (𝓝[≠] 0) (𝓝 1) := by
  simpa [slope_fun_def_field] using (Complex.hasDerivAt_sinh (0:ℂ)).tendsto_slope

/-- tanh div limit. -/
@[dlmf 4.31.E2]
theorem tanh_div_limit  : Tendsto (fun z : ℂ => Complex.tanh z/z) (𝓝[≠] 0) (𝓝 1) := by
  sorry

/-- cosh sub one div sq limit. -/
@[dlmf 4.31.E3]
theorem cosh_sub_one_div_sq_limit  : Tendsto (fun z : ℂ => (Complex.cosh z-1)/z^2) (𝓝[≠] 0) (𝓝 (1/2)) := by
  sorry

/-- Every finite entry of Table4.31.1; zeros at excluded pole entries are Lean totalizations, whose meromorphic poles are asserted separately below. -/
@[dlmf 4.31.T1]
theorem hyperbolic_special_values  :
    hyperbolicSix 0 = ![0,1,0,0,1,0] ∧
    hyperbolicSix (π*I/2) = ![I,0,0,-I,0,0] ∧
    hyperbolicSix (π*I) = ![0,-1,0,0,-1,0] ∧
    hyperbolicSix (3*π*I/2) = ![-I,0,0,I,0,0] := by
  sorry

/-- hyperbolic real infinity. -/
@[dlmf 4.31.T1]
theorem hyperbolic_real_infinity  :
    Tendsto Real.sinh atTop atTop ∧ Tendsto Real.cosh atTop atTop ∧
    Tendsto Real.tanh atTop (𝓝 1) ∧
    Tendsto (fun x : ℝ => (Real.sinh x)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => (Real.cosh x)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun x : ℝ => Real.cosh x/Real.sinh x) atTop (𝓝 1) := by
  sorry

/-- hyperbolic table sinh poles. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_sinh_poles (k : ℤ) :
    Tendsto (fun z : ℂ => ‖csch z‖) (𝓝[≠] ((k:ℂ)*π*I)) atTop ∧
    Tendsto (fun z : ℂ => ‖coth z‖) (𝓝[≠] ((k:ℂ)*π*I)) atTop := by
  sorry

/-- hyperbolic table cosh poles. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_cosh_poles (k : ℤ) :
    Tendsto (fun z : ℂ => ‖Complex.tanh z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I)) atTop ∧
    Tendsto (fun z : ℂ => ‖sech z‖) (𝓝[≠] (((k:ℂ)+1/2)*π*I)) atTop := by
  sorry

/-- cosh le sinhc cube. -/
@[dlmf 4.32.E1]
theorem cosh_le_sinhc_cube (x : ℝ) : Real.cosh x ≤ (if x=0 then 1 else Real.sinh x/x)^3 := by
  sorry

/-- sin cos lt tanh lt. -/
@[dlmf 4.32.E2]
theorem sin_cos_lt_tanh_lt {x : ℝ} (hx : 0<x) : Real.sin x*Real.cos x < Real.tanh x ∧ Real.tanh x<x := by
  sorry

/-- cosh sub lower. -/
@[dlmf 4.32.E3]
theorem cosh_sub_lower {x y : ℝ} (hx : 0<x) (hy : 0<y) :
    |Real.cosh x-Real.cosh y| ≥ |x-y| *Real.sqrt (Real.sinh x*Real.sinh y) := by
  sorry

/-- arctan le tanh. -/
@[dlmf 4.32.E4]
theorem arctan_le_tanh {x : ℝ} (hx : 0≤x) : Real.arctan x ≤ π/2*Real.tanh x := by
  sorry

/-- hasSum tanh. -/
@[dlmf 4.33.E3]
theorem hasSum_tanh {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*(n+1))*((2:ℂ)^(2*(n+1))-1)*
      (bernoulli (2*(n+1)):ℂ)/((2*(n+1)).factorial:ℂ)*z^(2*n+1)) (Complex.tanh z) := by
  sorry

/-- hasSum csch. -/
theorem hasSum_csch {z : ℂ} (hz0 : z≠0) (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => 2*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)*z^(2*n+1)) (csch z-z⁻¹) := by
  sorry

/-- hasSum sech. -/
theorem hasSum_sech {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (eulerNumber (2*n):ℂ)/((2*n).factorial:ℂ)*z^(2*n)) (sech z) := by
  sorry

/-- hasSum coth. -/
theorem hasSum_coth {z : ℂ} (hz0 : z≠0) (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+2)*(bernoulli (2*n+2):ℂ)/
      ((2*n+2).factorial:ℂ)*z^(2*n+1)) (coth z-z⁻¹) := by
  sorry

/-- hasSum log sinhc. -/
theorem hasSum_log_sinhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L)
    {z : ℂ} (hz : ‖z‖<π) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasSum log cosh. -/
theorem hasSum_log_cosh {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+1)*((2:ℂ)^(2*n+2)-1)*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasSum log tanhc. -/
theorem hasSum_log_tanhc {L : ℂ → ℂ} (hL : HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L)
    {z : ℂ} (hz : ‖z‖<π/2) :
    HasSum (fun n : ℕ => (2:ℂ)^(2*n+2)*(1-(2:ℂ)^(2*n+1))*(bernoulli (2*n+2):ℂ)/
      ((n+1:ℂ)*((2*n+2).factorial:ℂ))*z^(2*n+2)) (L z) := by
  sorry

/-- hasDerivAt tanh. -/
@[dlmf 4.34.E3]
theorem hasDerivAt_tanh {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt Complex.tanh (sech z^2) z := by
  convert (Complex.hasDerivAt_sinh z).div (Complex.hasDerivAt_cosh z) hz using 1
  · ext w; exact Complex.tanh_eq_sinh_div_cosh w
  · simp only [sech]
    field_simp
    linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- hasDerivAt csch. -/
@[dlmf 4.34.E4]
theorem hasDerivAt_csch {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt csch (-csch z*coth z) z := by
  convert (Complex.hasDerivAt_sinh z).inv hz using 1
  · rfl
  · simp only [csch, coth]
    field_simp <;> ring

/-- hasDerivAt sech. -/
@[dlmf 4.34.E5]
theorem hasDerivAt_sech {z : ℂ} (hz : Complex.cosh z≠0) : HasDerivAt sech (-sech z*Complex.tanh z) z := by
  convert (Complex.hasDerivAt_cosh z).inv hz using 1
  · rfl
  · simp only [sech, Complex.tanh_eq_sinh_div_cosh]
    field_simp <;> ring

/-- hasDerivAt coth. -/
@[dlmf 4.34.E6]
theorem hasDerivAt_coth {z : ℂ} (hz : Complex.sinh z≠0) : HasDerivAt coth (-csch z^2) z := by
  convert (Complex.hasDerivAt_cosh z).div (Complex.hasDerivAt_sinh z) hz using 1
  · rfl
  · simp only [coth, csch]
    field_simp
    linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- hyperbolic linear ode. -/
@[dlmf 4.34.E7, dlmf 4.34.E11]
theorem hyperbolic_linear_ode {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (hf' : DifferentiableOn ℂ (deriv f) U) :
    (∀ z ∈ U, deriv (deriv f) z-a^2*f z=0) ↔
      ∃ A B : ℂ, ∀ z ∈ U, f z=A*Complex.cosh (a*z)+B*Complex.sinh (a*z) := by
  sorry

/-- General squared first-order equation, including the equilibrium solutions omitted in the source shorthand. -/
@[dlmf 4.34.E8, dlmf 4.34.E12]
theorem hyperbolic_squared_ode_plus {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, (deriv f z)^2-a^2*(f z)^2=1) ↔
      (∃ c : ℂ, ∀ z ∈ U, f z=a⁻¹*Complex.sinh (a*z+c)) ∨
      (∃ w : ℂ, -a^2*w^2=1 ∧ ∀ z ∈ U, f z=w) := by
  sorry

/-- General squared first-order equation, including the equilibrium solutions omitted in the source shorthand. -/
@[dlmf 4.34.E9, dlmf 4.34.E13]
theorem hyperbolic_squared_ode_minus {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, (deriv f z)^2-a^2*(f z)^2=-1) ↔
      (∃ c : ℂ, ∀ z ∈ U, f z=a⁻¹*Complex.cosh (a*z+c)) ∨
      (∃ w : ℂ, -a^2*w^2=-1 ∧ ∀ z ∈ U, f z=w) := by
  sorry

/-- The Riccati general solution, with both constant equilibria and all pole exclusions. -/
@[dlmf 4.34.E10, dlmf 4.34.E14]
theorem hyperbolic_riccati_ode {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {a : ℂ} (ha : a≠0)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) :
    (∀ z ∈ U, deriv f z+a^2*(f z)^2=1) ↔
      (∃ c : ℂ, (∀ z ∈ U, Complex.sinh (a*z+c)≠0) ∧ ∀ z ∈ U, f z=a⁻¹*coth (a*z+c)) ∨
      (∀ z ∈ U, f z=a⁻¹) ∨ (∀ z ∈ U, f z= -a⁻¹) := by
  sorry

/-- tanh add. -/
@[dlmf 4.35.E3]
theorem tanh_add {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u+v)=(Complex.tanh u+Complex.tanh v)/(1+Complex.tanh u*Complex.tanh v) := by
  sorry

/-- tanh sub. -/
@[dlmf 4.35.E3]
theorem tanh_sub {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh (u-v)=(Complex.tanh u-Complex.tanh v)/(1-Complex.tanh u*Complex.tanh v) := by
  sorry

/-- coth add. -/
@[dlmf 4.35.E4]
theorem coth_add {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u+v)=(coth u*coth v+1)/(coth u+coth v) := by
  sorry

/-- coth sub. -/
@[dlmf 4.35.E4]
theorem coth_sub {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth (u-v)=(-coth u*coth v+1)/(coth u-coth v) := by
  sorry

/-- sinh add sinh. -/
@[dlmf 4.35.E5]
theorem sinh_add_sinh (u v : ℂ) : Complex.sinh u+Complex.sinh v=2*Complex.sinh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- sinh sub sinh. -/
@[dlmf 4.35.E6]
theorem sinh_sub_sinh (u v : ℂ) : Complex.sinh u-Complex.sinh v=2*Complex.cosh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.sinh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.sinh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- cosh add cosh. -/
@[dlmf 4.35.E7]
theorem cosh_add_cosh (u v : ℂ) : Complex.cosh u+Complex.cosh v=2*Complex.cosh ((u+v)/2)*Complex.cosh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1+h2

/-- cosh sub cosh. -/
@[dlmf 4.35.E8]
theorem cosh_sub_cosh (u v : ℂ) : Complex.cosh u-Complex.cosh v=2*Complex.sinh ((u+v)/2)*Complex.sinh ((u-v)/2) := by
  have h1 := Complex.cosh_add ((u+v)/2) ((u-v)/2)
  have h2 := Complex.cosh_sub ((u+v)/2) ((u-v)/2)
  rw [show (u+v)/2+(u-v)/2=u by ring] at h1
  rw [show (u+v)/2-(u-v)/2=v by ring] at h2
  linear_combination h1-h2

/-- tanh add tanh. -/
@[dlmf 4.35.E9]
theorem tanh_add_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u+Complex.tanh v=Complex.sinh (u+v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_add]
  field_simp <;> ring

/-- tanh sub tanh. -/
@[dlmf 4.35.E9]
theorem tanh_sub_tanh {u v : ℂ} (hu : Complex.cosh u≠0) (hv : Complex.cosh v≠0) : Complex.tanh u-Complex.tanh v=Complex.sinh (u-v)/(Complex.cosh u*Complex.cosh v) := by
  simp only [Complex.tanh_eq_sinh_div_cosh, Complex.sinh_sub]
  field_simp <;> ring

/-- coth add coth. -/
@[dlmf 4.35.E10]
theorem coth_add_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u+coth v=Complex.sinh (v+u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_add]
  field_simp <;> ring

/-- coth sub coth. -/
@[dlmf 4.35.E10]
theorem coth_sub_coth {u v : ℂ} (hu : Complex.sinh u≠0) (hv : Complex.sinh v≠0) : coth u-coth v=Complex.sinh (v-u)/(Complex.sinh u*Complex.sinh v) := by
  simp only [coth, Complex.sinh_sub]
  field_simp <;> ring

/-- sech sq. -/
@[dlmf 4.35.E12]
theorem sech_sq {z : ℂ} (hz : Complex.cosh z≠0) : sech z^2=1-Complex.tanh z^2 := by
  simp only [sech, Complex.tanh_eq_sinh_div_cosh]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- csch sq. -/
@[dlmf 4.35.E13]
theorem csch_sq {z : ℂ} (hz : Complex.sinh z≠0) : csch z^2=coth z^2-1 := by
  simp only [csch, coth]
  field_simp
  linear_combination -(Complex.cosh_sq_sub_sinh_sq z)

/-- two sinh mul sinh. -/
@[dlmf 4.35.E14]
theorem two_sinh_mul_sinh (u v : ℂ) : 2*Complex.sinh u*Complex.sinh v=Complex.cosh (u+v)-Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- two cosh mul cosh. -/
@[dlmf 4.35.E15]
theorem two_cosh_mul_cosh (u v : ℂ) : 2*Complex.cosh u*Complex.cosh v=Complex.cosh (u+v)+Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  ring

/-- two sinh mul cosh. -/
@[dlmf 4.35.E16]
theorem two_sinh_mul_cosh (u v : ℂ) : 2*Complex.sinh u*Complex.cosh v=Complex.sinh (u+v)+Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  ring

/-- sinh sq sub sinh sq. -/
@[dlmf 4.35.E17]
theorem sinh_sq_sub_sinh_sq (u v : ℂ) : Complex.sinh u^2-Complex.sinh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  rw [Complex.sinh_add, Complex.sinh_sub]
  linear_combination -(Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v) +
    (Complex.sinh v)^2*(Complex.cosh_sq_sub_sinh_sq u)

/-- cosh sq sub cosh sq. -/
@[dlmf 4.35.E18]
theorem cosh_sq_sub_cosh_sq (u v : ℂ) : Complex.cosh u^2-Complex.cosh v^2=Complex.sinh (u+v)*Complex.sinh (u-v) := by
  linear_combination (Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.cosh_sq_sub_sinh_sq v) + (sinh_sq_sub_sinh_sq u v)

/-- sinh sq add cosh sq. -/
@[dlmf 4.35.E19]
theorem sinh_sq_add_cosh_sq (u v : ℂ) : Complex.sinh u^2+Complex.cosh v^2=Complex.cosh (u+v)*Complex.cosh (u-v) := by
  rw [Complex.cosh_add, Complex.cosh_sub]
  linear_combination -(Complex.cosh v)^2*(Complex.cosh_sq_sub_sinh_sq u) -
    (Complex.sinh u)^2*(Complex.cosh_sq_sub_sinh_sq v)

/-- sinh half sq. -/
@[dlmf 4.35.E20]
theorem sinh_half_sq (z : ℂ) : Complex.sinh (z/2)^2=(Complex.cosh z-1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2-(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- cosh half sq. -/
@[dlmf 4.35.E21]
theorem cosh_half_sq (z : ℂ) : Complex.cosh (z/2)^2=(Complex.cosh z+1)/2 := by
  have h := Complex.cosh_two_mul (z/2)
  rw [show 2*(z/2)=z by ring] at h
  linear_combination -h/2+(Complex.cosh_sq_sub_sinh_sq (z/2))/2

/-- tanh half sq. -/
@[dlmf 4.35.E22]
theorem tanh_half_sq {z : ℂ} (hz : Complex.cosh (z/2)≠0) : Complex.tanh (z/2)^2=(Complex.cosh z-1)/(Complex.cosh z+1) := by
  sorry

/-- tanh half ratios. -/
@[dlmf 4.35.E22]
theorem tanh_half_ratios {z : ℂ} (hz : Complex.sinh z≠0) : Complex.tanh (z/2)=(Complex.cosh z-1)/Complex.sinh z ∧ Complex.tanh (z/2)=Complex.sinh z/(Complex.cosh z+1) := by
  sorry

/-- sinh two mul tanh. -/
@[dlmf 4.35.E26]
theorem sinh_two_mul_tanh {z : ℂ} (hz : Complex.cosh z≠0) : Complex.sinh (2*z)=2*Complex.tanh z/(1-Complex.tanh z^2) := by
  sorry

/-- cosh two mul forms. -/
@[dlmf 4.35.E27]
theorem cosh_two_mul_forms (z : ℂ) : Complex.cosh (2*z)=2*Complex.cosh z^2-1 ∧ Complex.cosh (2*z)=2*Complex.sinh z^2+1 := by
  rw [Complex.cosh_two_mul]
  constructor
  · linear_combination -(Complex.cosh_sq_sub_sinh_sq z)
  · linear_combination (Complex.cosh_sq_sub_sinh_sq z)

/-- tanh two mul. -/
@[dlmf 4.35.E28]
theorem tanh_two_mul {z : ℂ} (hz : Complex.cosh z≠0) : Complex.tanh (2*z)=2*Complex.tanh z/(1+Complex.tanh z^2) := by
  sorry

/-- sinh four mul. -/
@[dlmf 4.35.E31]
theorem sinh_four_mul (z : ℂ) : Complex.sinh (4*z)=4*Complex.sinh z^3*Complex.cosh z+4*Complex.cosh z^3*Complex.sinh z := by
  rw [show 4*z=2*(2*z) by ring, Complex.sinh_two_mul,
    Complex.sinh_two_mul, Complex.cosh_two_mul]
  ring

/-- cosh four mul. -/
@[dlmf 4.35.E32]
theorem cosh_four_mul (z : ℂ) : Complex.cosh (4*z)=Complex.cosh z^4+6*Complex.sinh z^2*Complex.cosh z^2+Complex.sinh z^4 := by
  rw [show 4*z=2*(2*z) by ring, Complex.cosh_two_mul,
    Complex.cosh_two_mul, Complex.sinh_two_mul]
  ring

/-- cosh add sinh int mul. -/
@[dlmf 4.35.E33]
theorem cosh_add_sinh_int_mul (n : ℤ) (z : ℂ) : Complex.cosh ((n:ℂ)*z)+Complex.sinh ((n:ℂ)*z)=(Complex.cosh z+Complex.sinh z)^n ∧ Complex.cosh ((n:ℂ)*z)-Complex.sinh ((n:ℂ)*z)=(Complex.cosh z-Complex.sinh z)^n := by
  constructor
  · rw [Complex.cosh_add_sinh, Complex.cosh_add_sinh, Complex.exp_int_mul]
  · rw [Complex.cosh_sub_sinh, Complex.cosh_sub_sinh, show -((n:ℂ)*z)=(n:ℂ)*(-z) by ring, Complex.exp_int_mul]

/-- sinh cartesian. -/
@[dlmf 4.35.E34]
theorem sinh_cartesian (z : ℂ) : Complex.sinh z=Real.sinh z.re*Real.cos z.im+I*(Real.cosh z.re*Real.sin z.im) := by
  sorry

/-- cosh cartesian. -/
@[dlmf 4.35.E35]
theorem cosh_cartesian (z : ℂ) : Complex.cosh z=Real.cosh z.re*Real.cos z.im+I*(Real.sinh z.re*Real.sin z.im) := by
  sorry

/-- tanh cartesian. -/
@[dlmf 4.35.E36]
theorem tanh_cartesian (z : ℂ) : Complex.tanh z=((Real.sinh (2*z.re):ℂ)+I*Real.sin (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im)) := by
  sorry

/-- coth cartesian. -/
@[dlmf 4.35.E37]
theorem coth_cartesian (z : ℂ) : coth z=((Real.sinh (2*z.re):ℂ)-I*Real.sin (2*z.im))/(Real.cosh (2*z.re)-Real.cos (2*z.im)) := by
  sorry

/-- norm sinh cartesian. -/
@[dlmf 4.35.E38]
theorem norm_sinh_cartesian (z : ℂ) : ‖Complex.sinh z‖=Real.sqrt (Real.sinh z.re^2+Real.sin z.im^2) ∧ ‖Complex.sinh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/2) := by
  sorry

/-- norm cosh cartesian. -/
@[dlmf 4.35.E39]
theorem norm_cosh_cartesian (z : ℂ) : ‖Complex.cosh z‖=Real.sqrt (Real.sinh z.re^2+Real.cos z.im^2) ∧ ‖Complex.cosh z‖=Real.sqrt ((Real.cosh (2*z.re)+Real.cos (2*z.im))/2) := by
  sorry

/-- norm tanh cartesian. -/
@[dlmf 4.35.E40]
theorem norm_tanh_cartesian (z : ℂ) : ‖Complex.tanh z‖=Real.sqrt ((Real.cosh (2*z.re)-Real.cos (2*z.im))/(Real.cosh (2*z.re)+Real.cos (2*z.im))) := by
  sorry

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E20]
theorem sinh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.sinh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.sinh (z/2) := by
  sorry

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E21]
theorem cosh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z+1)/2)
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.cosh ((x:ℂ)/2))
     :
    ∀ z ∈ U, r z=Complex.cosh (z/2) := by
  sorry

/-- The half-angle square root selected on the positive real axis and continued analytically. -/
@[dlmf 4.35.E22]
theorem tanh_half_continued_root {U : Set ℂ} (hU : IsOpen U) (hc : IsConnected U) {r : ℂ → ℂ}
    (hr : AnalyticOnNhd ℂ r U) (hsq : ∀ z ∈ U, r z^2=(Complex.cosh z-1)/(Complex.cosh z+1))
    {x : ℝ} (hx : 0<x) (hxU : (x:ℂ) ∈ U) (hanchor : r x=Complex.tanh ((x:ℂ)/2))
    (hpole : ∀ z ∈ U, Complex.cosh (z/2)≠0) :
    ∀ z ∈ U, r z=Complex.tanh (z/2) := by
  sorry

/-- hasProd sinh. -/
@[dlmf 4.36.E1]
theorem hasProd_sinh (z : ℂ) : HasProd (fun n : ℕ => 1+z^2/(((n+1:ℂ)^2)*π^2)) (sinhc z) := by
  sorry

/-- hasProd cosh. -/
@[dlmf 4.36.E2]
theorem hasProd_cosh (z : ℂ) : HasProd (fun n : ℕ => 1+4*z^2/(((2*n+1:ℂ)^2)*π^2)) (Complex.cosh z) := by
  sorry

/-- hasSum coth. -/
@[dlmf 4.36.E3]
theorem hasSum_coth_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => 1/(z^2+(n+1:ℂ)^2*π^2)) ((coth z-z⁻¹)/(2*z)) := by
  sorry

/-- hasSum csch sq. -/
@[dlmf 4.36.E4]
theorem hasSum_csch_sq {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℤ => 1/(z-(n:ℂ)*π*I)^2) (csch z^2) := by
  sorry

/-- hasSum csch. -/
@[dlmf 4.36.E5]
theorem hasSum_csch_partialFractions {z : ℂ} (hz : ∀ n : ℤ, z≠(n:ℂ)*π*I) : HasSum (fun n : ℕ => (-1:ℂ)^(n+1)/(z^2+(n+1:ℂ)^2*π^2)) ((csch z-z⁻¹)/(2*z)) := by
  sorry

/-- A path integral with the square root continued from its value 1 at the origin. -/
def IsArcsinhPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=1 ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠I ∧ γ s≠ -I ∧ r s^2=1+γ s^2) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- A path integral with the square root selected on an initial positive-real segment. -/
def IsArccoshPathValue (z w : ℂ) : Prop := ∃ γ r : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=1 ∧ γ 1=z ∧ ContinuousOn r (Icc 0 1) ∧ r 0=0 ∧
  (∀ s ∈ Ioc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1 ∧ r s^2=γ s^2-1) ∧
  (∃ ε ∈ Ioc (0:ℝ) 1, ∀ s ∈ Ioo (0:ℝ) ε,
    (γ s).im=0 ∧ 1<(γ s).re ∧ r s=Complex.sqrt (γ s^2-1)) ∧
  IntervalIntegrable (fun s => deriv γ s/r s) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/r s)=w
/-- The inverse-tanh path integral, avoiding the two logarithmic branch points. -/
def IsArctanhPathValue (z w : ℂ) : Prop := ∃ γ : ℝ → ℂ,
  ContDiffOn ℝ 1 γ (Icc 0 1) ∧ γ 0=0 ∧ γ 1=z ∧
  (∀ s ∈ Icc (0:ℝ) 1, γ s≠1 ∧ γ s≠ -1) ∧
  IntervalIntegrable (fun s => deriv γ s/(1-γ s^2)) volume 0 1 ∧
  (∫ s : ℝ in 0..1, deriv γ s/(1-γ s^2))=w
/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E1]
theorem arcsinh_path_values {z : ℂ} (hz : z≠I ∧ z≠ -I) : {w | IsArcsinhPathValue z w}=arcsinhValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E2]
theorem arccosh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArccoshPathValue z w}=arccoshValues z := by
  sorry

/-- The multivalued inverse defined by all admissible continued-branch path integrals. -/
@[dlmf 4.37.E3]
theorem arctanh_path_values {z : ℂ} (hz : z≠1 ∧ z≠ -1) : {w | IsArctanhPathValue z w}=arctanhValues z := by
  sorry

/-- arccsch values inv. -/
@[dlmf 4.37.E4]
theorem arccsch_values_inv {z : ℂ} (hz : z≠0) : arccschValues z=arcsinhValues z⁻¹ := by
  sorry

/-- arcsech values inv. -/
@[dlmf 4.37.E5]
theorem arcsech_values_inv {z : ℂ} (hz : z≠0) : arcsechValues z=arccoshValues z⁻¹ := by
  sorry

/-- arccoth values inv. -/
@[dlmf 4.37.E6]
theorem arccoth_values_inv {z : ℂ} (hz : z≠0) : arccothValues z=arctanhValues z⁻¹ := by
  sorry

/-- arccoth eq inv. -/
@[dlmf 4.37.E9]
theorem arccoth_eq_inv {z : ℂ} (hz : z≠0) : arccoth z=arctanh z⁻¹ := by
  simp [arccoth,hz]

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsinh_analytic  : AnalyticOnNhd ℂ arcsinh arcsinhDomain := by
  sorry

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccosh_analytic  : AnalyticOnNhd ℂ arccosh arccoshDomain := by
  sorry

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arctanh_analytic  : AnalyticOnNhd ℂ arctanh arctanhDomain := by
  sorry

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccsch_analytic  : AnalyticOnNhd ℂ arccsch arccschDomain := by
  sorry

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arcsech_analytic  : AnalyticOnNhd ℂ arcsech arcsechDomain := by
  sorry

/-- Analyticity of the principal inverse on precisely its open cut domain. -/
theorem arccoth_analytic  : AnalyticOnNhd ℂ arccoth arccothDomain := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsinh_branch_points  : ¬AnalyticAt ℂ arcsinh I ∧ ¬AnalyticAt ℂ arcsinh (-I) := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arccosh_branch_points  : ¬AnalyticAt ℂ arccosh (1:ℂ) ∧ ¬AnalyticAt ℂ arccosh (-(1:ℂ)) := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arctanh_branch_points  : ¬AnalyticAt ℂ arctanh (1:ℂ) ∧ ¬AnalyticAt ℂ arctanh (-(1:ℂ)) := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arccsch_branch_points  : ¬AnalyticAt ℂ arccsch I ∧ ¬AnalyticAt ℂ arccsch (-I) := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arcsech_branch_points  : ¬AnalyticAt ℂ arcsech (1:ℂ) ∧ ¬AnalyticAt ℂ arcsech (-(1:ℂ)) := by
  sorry

/-- The two inverse branch points stated in the definition prose. -/
theorem arccoth_branch_points  : ¬AnalyticAt ℂ arccoth (1:ℂ) ∧ ¬AnalyticAt ℂ arccoth (-(1:ℂ)) := by
  sorry

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arcsinh_ofReal (x : ℝ)  : arcsinh x=(Real.arsinh x:ℂ) := by
  sorry

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arccosh_ofReal (x : ℝ) (hx : 1≤x) : arccosh x=(Real.arcosh x:ℂ) := by
  sorry

/-- Reality and agreement with the existing real inverse on the uncut real interval. -/
theorem arctanh_ofReal (x : ℝ) (hx : |x|<1) : arctanh x=(Real.artanh x:ℂ) := by
  sorry

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E10]
theorem arcsinh_neg (z : ℂ) : arcsinh (-z)= -arcsinh z := by
  sorry

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E12]
theorem arctanh_neg {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh (-z)= -arctanh z := by
  sorry

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E13]
theorem arccsch_neg (z : ℂ) : arccsch (-z)= -arccsch z := by
  sorry

/-- Oddness on the open cut plane; cut-side values are given separately. -/
@[dlmf 4.37.E15]
theorem arccoth_neg {z : ℂ} (hz : z ∈ arccothDomain) : arccoth (-z)= -arccoth z := by
  sorry

/-- Corrected principal-branch sign: E20 at z=±i contradicts the printed E11 sign pairing. -/
@[dlmf 4.37.E11]
theorem arccosh_neg {z : ℂ} (hz : z.im≠0) :
    arccosh (-z)=arccosh z-(if 0<z.im then 1 else -1)*π*I := by
  sorry

/-- The reciprocal version of the corrected principal arccosh sign relation. -/
@[dlmf 4.37.E14]
theorem arcsech_neg {z : ℂ} (hz : z.im≠0) :
    arcsech (-z)=arcsech z+(if 0<z.im then 1 else -1)*π*I := by
  sorry

/-- arcsinh log. -/
@[dlmf 4.37.E16]
theorem arcsinh_log {z : ℂ} (hz : z ∈ arcsinhDomain) : arcsinh z=Complex.log (Complex.sqrt (z^2+1)+z) := by
  rfl

/-- arcsinh upper cut. -/
@[dlmf 4.37.E17]
theorem arcsinh_upper_cut {y : ℝ} (hy : 1≤y) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log (Real.sqrt (y^2-1)+y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (π*I/2-(Real.log (Real.sqrt (y^2-1)+y):ℂ))) := by
  sorry

/-- arcsinh lower cut. -/
@[dlmf 4.37.E18]
theorem arcsinh_lower_cut {y : ℝ} (hy : y≤ -1) :
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[>] 0)
      (𝓝 (-π*I/2+(Real.log (Real.sqrt (y^2-1)-y):ℂ))) ∧
    Tendsto (fun ε : ℝ => arcsinh ((ε:ℂ)+I*y)) (𝓝[<] 0)
      (𝓝 (-π*I/2-(Real.log (Real.sqrt (y^2-1)-y):ℂ))) := by
  sorry

/-- arccosh log. -/
@[dlmf 4.37.E19]
theorem arccosh_log {z : ℂ} (hz : z ∈ arccoshDomain) (hre : z.re≠0) :
    arccosh z=Complex.log ((if 0<z.re then 1 else -1)*Complex.sqrt (z^2-1)+z) := by
  sorry

/-- arccosh imaginary. -/
@[dlmf 4.37.E20]
theorem arccosh_imaginary {y : ℝ} (hy : y≠0) :
    arccosh (I*y)=(if 0<y then 1 else -1)*π*I/2+
      (Real.log (Real.sqrt (y^2+1)+(if 0<y then y else -y)):ℂ) := by
  sorry

/-- arccosh log half. -/
@[dlmf 4.37.E21]
theorem arccosh_log_half {z : ℂ} (hz : z ∈ arccoshDomain) :
    arccosh z=2*Complex.log (Complex.sqrt ((z+1)/2)+Complex.sqrt ((z-1)/2)) := by
  sorry

/-- arccosh inner cut. -/
@[dlmf 4.37.E22]
theorem arccosh_inner_cut {x : ℝ} (hx : -1<x ∧ x≤1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (Complex.log (I*Real.sqrt (1-x^2)+x))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-Complex.log (I*Real.sqrt (1-x^2)+x))) := by
  sorry

/-- arccosh outer cut. -/
@[dlmf 4.37.E23]
theorem arccosh_outer_cut {x : ℝ} (hx : x≤ -1) :
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) ∧
    Tendsto (fun ε : ℝ => arccosh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I+(Real.log (Real.sqrt (x^2-1)-x):ℂ))) := by
  sorry

/-- arctanh log. -/
@[dlmf 4.37.E24]
theorem arctanh_log {z : ℂ} (hz : z ∈ arctanhDomain) : arctanh z=Complex.log ((1+z)/(1-z))/2 := by
  rfl

/-- arctanh cut. -/
@[dlmf 4.37.E25]
theorem arctanh_cut {x : ℝ} (hx : 1< |x|) :
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[>] 0)
      (𝓝 (π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) ∧
    Tendsto (fun ε : ℝ => arctanh ((x:ℂ)+I*ε)) (𝓝[<] 0)
      (𝓝 (-π*I/2+(Real.log ((x+1)/(x-1)):ℂ)/2)) := by
  sorry

/-- sinh inverse family. -/
@[dlmf 4.37.E26, dlmf 4.37.E29]
theorem sinh_inverse_family (z w : ℂ) :
    Complex.sinh w=z ↔ ∃ k : ℤ, w=(-1:ℂ)^k*arcsinh z+(k:ℂ)*π*I := by
  sorry

/-- cosh inverse family. -/
@[dlmf 4.37.E27, dlmf 4.37.E30]
theorem cosh_inverse_family (z w : ℂ) :
    Complex.cosh w=z ↔ ∃ k : ℤ, w=arccosh z+2*(k:ℂ)*π*I ∨ w= -arccosh z+2*(k:ℂ)*π*I := by
  sorry

/-- tanh inverse family. -/
@[dlmf 4.37.E28, dlmf 4.37.E31]
theorem tanh_inverse_family {z w : ℂ} (hz : z≠1 ∧ z≠ -1) :
    w ∈ arctanhValues z ↔ ∃ k : ℤ, w=arctanh z+(k:ℂ)*π*I := by
  sorry

/-- The interrelation example in §4.37(vi), with compatible principal branches. -/
theorem arcsech_arccoth_interrelation {a : ℂ} (hre : 0<a.re) (ha : a∈arcsechDomain)
    (hr : (Complex.sqrt (1-a^2))⁻¹∈arccothDomain) :
    arcsech a=arccoth ((Complex.sqrt (1-a^2))⁻¹) := by
  sorry

/-- Central-binomial coefficient divided by 4^n, used in the inverse expansions. -/
def hyperbolicCentral (n : ℕ) : ℂ := (Nat.choose (2*n) n:ℂ)/(4:ℂ)^n
/-- hasSum arcsinh. -/
@[dlmf 4.38.E1]
theorem hasSum_arcsinh {z : ℂ} (hz : ‖z‖<1) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/(2*n+1:ℂ)*z^(2*n+1)) (arcsinh z) := by
  sorry

/-- hasSum arcsinh large. -/
@[dlmf 4.38.E2]
theorem hasSum_arcsinh_large {z : ℂ} (hz : 0<z.re) (hn : 1<‖z‖) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (arcsinh z-Complex.log (2*z)) := by
  sorry

/-- hasSum arccosh large. -/
@[dlmf 4.38.E3]
theorem hasSum_arccosh_large {z : ℂ} (hn : 1<‖z‖) : HasSum (fun n : ℕ => hyperbolicCentral (n+1)/((2*n+2:ℂ)*z^(2*n+2))) (Complex.log (2*z)-arccosh z) := by
  sorry

/-- hasSum arccosh near one. -/
@[dlmf 4.38.E4]
theorem hasSum_arccosh_near_one {z : ℂ} (hz : 0<z.re) (hn : ‖z-1‖≤2) : HasSum (fun n : ℕ => (-1:ℂ)^n*hyperbolicCentral n/((2:ℂ)^n*(2*n+1:ℂ))*(z-1)^n) (if z=1 then 1 else arccosh z/Complex.sqrt (2*(z-1))) := by
  sorry

/-- hasSum arctanh. -/
@[dlmf 4.38.E5]
theorem hasSum_arctanh {z : ℂ} (hn : ‖z‖≤1) (hz : z≠1 ∧ z≠ -1) : HasSum (fun n : ℕ => z^(2*n+1)/(2*n+1:ℂ)) (arctanh z) := by
  sorry

/-- hasSum arctanh large. -/
@[dlmf 4.38.E6]
theorem hasSum_arctanh_large {z : ℂ} (hn : 1≤‖z‖) (hz : z.im≠0) : HasSum (fun n : ℕ => 1/((2*n+1:ℂ)*z^(2*n+1))) (arctanh z-(if 0<z.im then 1 else -1)*I*π/2) := by
  sorry

/-- hasSum arctanh transformed. -/
@[dlmf 4.38.E7]
theorem hasSum_arctanh_transformed {z : ℂ} (hz : (z^2).re<1/2) : HasSum (fun n : ℕ => (4:ℂ)^n*(n.factorial:ℂ)^2/((2*n+1).factorial:ℂ)*(z^2/(z^2-1))^n) (if z=0 then 1 else (1-z^2)/z*arctanh z) := by
  sorry

/-- arctanh transformed region. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_region (z : ℂ) : (z^2).re<1/2 ↔ z.re^2-z.im^2<1/2 := by
  sorry

/-- hasDerivAt arcsinh. -/
@[dlmf 4.38.E9]
theorem hasDerivAt_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) : HasDerivAt arcsinh ((Complex.sqrt (1+z^2))⁻¹) z := by
  sorry

/-- hasDerivAt arccosh. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh {z : ℂ} (hz : z∈arccoshDomain) : HasDerivAt arccosh ((Complex.sqrt (z-1)*Complex.sqrt (z+1))⁻¹) z := by
  sorry

/-- hasDerivAt arccosh signed. -/
@[dlmf 4.38.E10]
theorem hasDerivAt_arccosh_signed {z : ℂ} (hz : z∈arccoshDomain) (hre : z.re≠0) : HasDerivAt arccosh ((if 0<z.re then 1 else -1)*(Complex.sqrt (z^2-1))⁻¹) z := by
  sorry

/-- hasDerivAt arctanh. -/
@[dlmf 4.38.E11]
theorem hasDerivAt_arctanh {z : ℂ} (hz : z∈arctanhDomain) : HasDerivAt arctanh (1/(1-z^2)) z := by
  sorry

/-- hasDerivAt arccsch. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch {z : ℂ} (hz : z∈arccschDomain) : HasDerivAt arccsch (-1/(z^2*Complex.sqrt (1+z⁻¹^2))) z := by
  sorry

/-- hasDerivAt arccsch signed. -/
@[dlmf 4.38.E12]
theorem hasDerivAt_arccsch_signed {z : ℂ} (hz : z∈arccschDomain) (hre : z.re≠0) : HasDerivAt arccsch (-(if 0<z.re then 1 else -1)/(z*Complex.sqrt (1+z^2))) z := by
  sorry

/-- hasDerivAt arcsech. -/
@[dlmf 4.38.E13]
theorem hasDerivAt_arcsech {z : ℂ} (hz : z∈arcsechDomain) : HasDerivAt arcsech (-1/(z*Complex.sqrt (1-z^2))) z := by
  sorry

/-- hasDerivAt arccoth. -/
@[dlmf 4.38.E14]
theorem hasDerivAt_arccoth {z : ℂ} (hz : z∈arccothDomain) : HasDerivAt arccoth (1/(1-z^2)) z := by
  sorry

/-- arcsinh values add. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ, r^2=1+v^2 ∧ s^2=1+u^2 ∧ w ∈ arcsinhValues (u*r+v*s)} := by
  sorry

/-- arccosh values add. -/
@[dlmf 4.38.E16]
theorem arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v+r)} := by
  sorry

/-- arctanh values add. -/
@[dlmf 4.38.E17]
theorem arctanh_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1+u*v≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u+v)/(1+u*v)) := by
  sorry

/-- arcsinh arccosh values add. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_add (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a+b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(1+u^2)*(v^2-1) ∧ w ∈ arcsinhValues (u*v+r)} ∧
    Set.image2 (fun a b : ℂ => a+b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ, r^2=1+u^2 ∧ s^2=v^2-1 ∧ w ∈ arccoshValues (v*r+u*s)} := by
  sorry

/-- arctanh arccoth values add. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_add {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v+u≠0) (hq : u*v+1≠0) :
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v+1)/(v+u)) ∧
    Set.image2 (fun a b : ℂ => a+b) (arctanhValues u) (arccothValues v)=arccothValues ((v+u)/(u*v+1)) := by
  sorry

/-- arcsinh values sub. -/
@[dlmf 4.38.E15]
theorem arcsinh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arcsinhValues u) (arcsinhValues v)=
      {w | ∃ r s : ℂ, r^2=1+v^2 ∧ s^2=1+u^2 ∧ w ∈ arcsinhValues (u*r-v*s)} := by
  sorry

/-- arccosh values sub. -/
@[dlmf 4.38.E16]
theorem arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arccoshValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(u^2-1)*(v^2-1) ∧ w ∈ arccoshValues (u*v-r)} := by
  sorry

/-- arctanh values sub. -/
@[dlmf 4.38.E17]
theorem arctanh_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1) (hp : 1-u*v≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arctanhValues v)=arctanhValues ((u-v)/(1-u*v)) := by
  sorry

/-- arcsinh arccosh values sub. -/
@[dlmf 4.38.E18]
theorem arcsinh_arccosh_values_sub (u v : ℂ) :
    Set.image2 (fun a b : ℂ => a-b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r : ℂ, r^2=(1+u^2)*(v^2-1) ∧ w ∈ arcsinhValues (u*v-r)} ∧
    Set.image2 (fun a b : ℂ => a-b) (arcsinhValues u) (arccoshValues v)=
      {w | ∃ r s : ℂ, r^2=1+u^2 ∧ s^2=v^2-1 ∧ w ∈ arccoshValues (v*r-u*s)} := by
  sorry

/-- arctanh arccoth values sub. -/
@[dlmf 4.38.E19]
theorem arctanh_arccoth_values_sub {u v : ℂ} (hu : u≠1 ∧ u≠ -1) (hv : v≠1 ∧ v≠ -1)
    (hp : v-u≠0) (hq : u*v-1≠0) :
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arctanhValues ((u*v-1)/(v-u)) ∧
    Set.image2 (fun a b : ℂ => a-b) (arctanhValues u) (arccothValues v)=arccothValues ((v-u)/(u*v-1)) := by
  sorry

/-- tanh continued fraction. -/
@[dlmf 4.39.E1]
theorem tanh_continued_fraction {z : ℂ} (hz : Complex.cosh z≠0) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else z^2) (fun n => (2*n+1:ℂ)) (Complex.tanh z) := by
  sorry

/-- arcsinh continued fraction. -/
@[dlmf 4.39.E2]
theorem arcsinh_continued_fraction {z : ℂ} (hz : z∈arcsinhDomain) :
    DLMF.HasContinuedFraction
      (fun n => if n=0 then z else ((2*((n+1)/2)-1:ℕ):ℂ)*(2*((n+1)/2):ℂ)*z^2)
      (fun n => (2*n+1:ℂ)) (arcsinh z/Complex.sqrt (1+z^2)) := by
  sorry

/-- arctanh continued fraction. -/
@[dlmf 4.39.E3]
theorem arctanh_continued_fraction {z : ℂ} (hz : z∈arctanhDomain) :
    DLMF.HasContinuedFraction (fun n => if n=0 then z else -(n:ℂ)^2*z^2)
      (fun n => (2*n+1:ℂ)) (arctanh z) := by
  sorry

/-- antiderivative tanh. -/
@[dlmf 4.40.E3]
theorem antiderivative_tanh (x : ℝ) : HasDerivAt (fun t : ℝ => Real.log (Real.cosh t)) (Real.tanh x) x := by
  sorry

/-- antiderivative csch. -/
@[dlmf 4.40.E4]
theorem antiderivative_csch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.tanh (t/2))) (Real.sinh x)⁻¹ x := by
  sorry

/-- antiderivative sech. -/
@[dlmf 4.40.E5]
theorem antiderivative_sech (x : ℝ) : HasDerivAt (fun t : ℝ => 2*Real.arctan (Real.exp t)-π/2) (Real.cosh x)⁻¹ x := by
  sorry

/-- antiderivative coth. -/
@[dlmf 4.40.E6]
theorem antiderivative_coth {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => Real.log (Real.sinh t)) (Real.cosh x/Real.sinh x) x := by
  sorry

/-- integral exp sin div sinh. -/
@[dlmf 4.40.E7]
theorem integral_exp_sin_div_sinh {a : ℝ} (ha : a≠0) : IntegrableOn (fun x : ℝ => Real.exp (-x)*Real.sin (a*x)/Real.sinh x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.exp (-x)*Real.sin (a*x)/Real.sinh x)=π/2*(Real.cosh (π*a/2)/Real.sinh (π*a/2))-1/a := by
  sorry

/-- integral sinh div sinh. -/
@[dlmf 4.40.E8]
theorem integral_sinh_div_sinh {a : ℝ} (ha : -π<a ∧ a<π) : IntegrableOn (fun x : ℝ => Real.sinh (a*x)/Real.sinh (π*x)) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, Real.sinh (a*x)/Real.sinh (π*x))=Real.tan (a/2)/2 := by
  sorry

/-- integral exp div cosh sq. -/
@[dlmf 4.40.E9]
theorem integral_exp_div_cosh_sq {a : ℝ} (ha : -1<a ∧ a<1) : Integrable (fun x : ℝ => Real.exp (a*x)/(Real.cosh (x/2))^2) ∧ (∫ x : ℝ, Real.exp (a*x)/(Real.cosh (x/2))^2)=(if a=0 then 4 else 4*π*a/Real.sin (π*a)) := by
  sorry

/-- integral tanh difference. -/
@[dlmf 4.40.E10]
theorem integral_tanh_difference {a b : ℝ} (ha : 0<a) (hb : 0<b) : IntegrableOn (fun x : ℝ => (Real.tanh (a*x)-Real.tanh (b*x))/x) (Ioi 0) ∧ (∫ x : ℝ in Ioi 0, (Real.tanh (a*x)-Real.tanh (b*x))/x)=Real.log (a/b) := by
  sorry

/-- antiderivative arcsinh. -/
@[dlmf 4.40.E11]
theorem antiderivative_arcsinh (x : ℝ) : HasDerivAt (fun t : ℝ => t*Real.arsinh t-Real.sqrt (1+t^2)) (Real.arsinh x) x := by
  sorry

/-- antiderivative arccosh. -/
@[dlmf 4.40.E12]
theorem antiderivative_arccosh {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.arcosh t-Real.sqrt (t^2-1)) (Real.arcosh x) x := by
  sorry

/-- antiderivative arctanh. -/
@[dlmf 4.40.E13]
theorem antiderivative_arctanh {x : ℝ} (hx : |x|<1) : HasDerivAt (fun t : ℝ => t*Real.artanh t+Real.log (1-t^2)/2) (Real.artanh x) x := by
  sorry

/-- antiderivative arccsch. -/
@[dlmf 4.40.E14]
theorem antiderivative_arccsch {x : ℝ} (hx : 0<x) : HasDerivAt (fun t : ℝ => t*Real.arsinh t⁻¹+Real.arsinh t) (Real.arsinh x⁻¹) x := by
  sorry

/-- antiderivative arcsech. -/
@[dlmf 4.40.E15]
theorem antiderivative_arcsech {x : ℝ} (hx : 0<x ∧ x<1) : HasDerivAt (fun t : ℝ => t*Real.arcosh t⁻¹+Real.arcsin t) (Real.arcosh x⁻¹) x := by
  sorry

/-- antiderivative arccoth. -/
@[dlmf 4.40.E16]
theorem antiderivative_arccoth {x : ℝ} (hx : 1<x) : HasDerivAt (fun t : ℝ => t*Real.artanh t⁻¹+Real.log (t^2-1)/2) (Real.artanh x⁻¹) x := by
  sorry

/-- Local logarithmic branches give complex primitives without imposing principal-log cuts. -/
theorem complex_antiderivatives_hyperbolic {U : Set ℂ} (hU : IsOpen U)
    {z : ℂ} (hz : z∈U) (hc : Complex.cosh z≠0) (hs : Complex.sinh z≠0)
    {Lcosh Lsinh Ltanh : ℂ → ℂ}
    (hLc : AnalyticOnNhd ℂ Lcosh U) (hLs : AnalyticOnNhd ℂ Lsinh U)
    (hLt : AnalyticOnNhd ℂ Ltanh U)
    (hEc : ∀ w∈U, Complex.exp (Lcosh w)=Complex.cosh w)
    (hEs : ∀ w∈U, Complex.exp (Lsinh w)=Complex.sinh w)
    (hEt : ∀ w∈U, Complex.exp (Ltanh w)=Complex.tanh (w/2)) :
    HasDerivAt Lcosh (Complex.tanh z) z ∧ HasDerivAt Lsinh (coth z) z ∧
      HasDerivAt Ltanh (csch z) z := by
  sorry

/-- The principal complex arcsinh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arcsinh {z : ℂ} (hz : z∈arcsinhDomain) :
    HasDerivAt (fun w => w*arcsinh w-Complex.sqrt (1+w^2)) (arcsinh z) z := by
  sorry

/-- The principal complex arccosh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arccosh {z : ℂ} (hz : z∈arccoshDomain) :
    HasDerivAt (fun w => w*arccosh w-Complex.sqrt (w-1)*Complex.sqrt (w+1)) (arccosh z) z := by
  sorry

/-- The principal complex arctanh primitive on its complete open cut domain. -/
theorem complex_antiderivative_arctanh {z : ℂ} (hz : z∈arctanhDomain) :
    HasDerivAt (fun w => w*arctanh w+Complex.log (1-w^2)/2) (arctanh z) z := by
  sorry

/-- The remaining inverse functions are real on their uncut real intervals. -/
theorem reciprocal_inverses_ofReal {x : ℝ} :
    (x≠0 → arccsch x=(Real.arsinh x⁻¹:ℂ)) ∧
    (0<x ∧ x≤1 → arcsech x=(Real.arcosh x⁻¹:ℂ)) ∧
    (1< |x| → arccoth x=(Real.artanh x⁻¹:ℂ)) := by
  sorry

/-- Existence of the three normalized analytic logarithms used in the prose series. -/
theorem exists_hyperbolic_logarithms :
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 π) sinhc L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) Complex.cosh L) ∧
    (∃ L, HyperbolicNormalizedLog (Metric.ball 0 (π/2)) tanhc L) := by
  sorry

/-- The complex extension of the reciprocal-inverse antiderivatives on compatible branches. -/
theorem complex_antiderivatives_reciprocal_inverse {z : ℂ}
    (hre : 0<z.re) (hs : z∈arccschDomain) (hc : z∈arcsechDomain)
    (ha : z.im≠0 ∨ |z.re|<1) :
    HasDerivAt (fun w => w*arccsch w+arcsinh w) (arccsch z) z ∧
    HasDerivAt (fun w => w*arcsech w-I*Complex.log (Complex.sqrt (1-w^2)+I*w))
      (arcsech z) z := by
  sorry

/-- The complex inverse-cotangent primitive with a locally consistent logarithm. -/
theorem complex_antiderivative_arccoth {z : ℂ} (hz : z∈arccothDomain)
    (hlog : z^2-1∈slitPlane) :
    HasDerivAt (fun w => w*arccoth w+Complex.log (w^2-1)/2) (arccoth z) z := by
  sorry

/-- One-sided imaginary pole directions in the exact-value table, without an assigned infinite complex value. -/
@[dlmf 4.31.T1]
theorem hyperbolic_table_imaginary_pole_sides :
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (Complex.tanh (I*y)).im) (𝓝[>] (3*π/2)) atBot ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[<] (π/2)) atTop ∧
    Tendsto (fun y : ℝ => (sech (I*y)).re) (𝓝[>] (3*π/2)) atTop := by
  sorry

/-- A local continued Gudermannian, extending the sech antiderivative to the complex plane. -/
theorem complex_antiderivative_sech {z : ℂ} (hz : Complex.cosh z≠0) :
    ∃ U : Set ℂ, IsOpen U ∧ z∈U ∧ ∃ G : ℂ → ℂ,
      AnalyticOnNhd ℂ G U ∧
      (∀ w∈U, HasDerivAt G (sech w) w) ∧
      (∀ w∈U, Complex.tan (G w/2+π/4)=Complex.exp w) := by
  sorry

/-- Oddness of all inverse-tanh branches includes the two values on each cut. -/
@[dlmf 4.37.E12]
theorem arctanh_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arctanhValues z=arctanhValues (-z) := by
  sorry

/-- Oddness of all inverse-coth branches includes the two cut values at zero. -/
@[dlmf 4.37.E15]
theorem arccoth_values_neg (z : ℂ) :
    (fun w : ℂ => -w) '' arccothValues z=arccothValues (-z) := by
  sorry

/-- The rectangular-hyperbola equation delimiting the transformed inverse-tanh series. -/
@[dlmf 4.38.E8]
theorem arctanh_transformed_boundary (z : ℂ) :
    (z^2).re=1/2 ↔ z.re^2-z.im^2=1/2 := by
  simp only [pow_two, Complex.mul_re]

/-- The regular endpoint of the principal inverse cosh is included in its logarithmic formulas. -/
@[dlmf 4.37.E19, dlmf 4.37.E21]
theorem arccosh_one : arccosh 1=0 := by
  simp [arccosh]

/-- At zero inverse coth has the finite half-period family; reciprocal zero is not totalized inside the inverse. -/
@[dlmf 4.37.E6, dlmf 4.37.E9]
theorem arccoth_zero_values :
    arccothValues 0=Set.range (fun k : ℤ => ((k:ℂ)+1/2)*π*I) := by
  sorry

/-- Continued inverse-sinh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arcsinh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.sinh (A w)=w) (hcrit : z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w-Complex.cosh (A w)) (A z) z := by
  sorry

/-- Continued inverse-cosh branches have the corresponding continued primitive. -/
theorem continued_antiderivative_arccosh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U)
    (hinv : ∀ w∈U, Complex.cosh (A w)=w) (hcrit : z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w-Complex.sinh (A w)) (A z) z := by
  sorry

/-- Continued inverse-tanh and logarithm branches have the corresponding primitive. -/
theorem continued_antiderivative_arctanh {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, Complex.tanh (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (L w)=Complex.cosh (A w)) :
    HasDerivAt (fun w => w*A w-L w) (A z) z := by
  sorry

/-- Continued inverse-csch branches use a matching inverse-sinh square-root branch. -/
theorem continued_antiderivative_arccsch {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, csch (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sinh (B w)=w)
    (hbranch : ∀ w∈U, Complex.cosh (B w)=w*Complex.cosh (A w))
    (hcrit : z≠0 ∧ z≠I ∧ z≠ -I) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  sorry

/-- Continued inverse-sech branches use a matching inverse-sine square-root branch. -/
theorem continued_antiderivative_arcsech {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A B : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hB : AnalyticOnNhd ℂ B U)
    (hinv : ∀ w∈U, sech (A w)=w) (hpole : ∀ w∈U, Complex.cosh (A w)≠0)
    (hbinv : ∀ w∈U, Complex.sin (B w)=w)
    (hbranch : ∀ w∈U, Complex.cos (B w)=w*Complex.sinh (A w))
    (hcrit : z≠0 ∧ z≠1 ∧ z≠ -1) :
    HasDerivAt (fun w => w*A w+B w) (A z) z := by
  sorry

/-- Continued inverse-coth branches and a continued logarithm give the full complex primitive. -/
theorem continued_antiderivative_arccoth {U : Set ℂ} (hU : IsOpen U) {z : ℂ} (hz : z∈U)
    {A L : ℂ → ℂ} (hA : AnalyticOnNhd ℂ A U) (hL : AnalyticOnNhd ℂ L U)
    (hinv : ∀ w∈U, coth (A w)=w) (hpole : ∀ w∈U, Complex.sinh (A w)≠0)
    (hlog : ∀ w∈U, Complex.exp (2*L w)=w^2-1) :
    HasDerivAt (fun w => w*A w+L w) (A z) z := by
  sorry

end DLMF.Elementary
