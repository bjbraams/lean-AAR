/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.QHypergeometric.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# q-calculus adapters and Gaussian coefficients (DLMF §17.2)

The shifted factorials, Gaussian polynomial, Jackson integral and q-derivative reuse
`DLMF.QSeries`. The derivative adapter supplies the removable value at0 required by DLMF,
while the existing q-derivative remains the operator at every nonzero argument.
Finite-interval and bilateral integrals are the standard adapters around that Jackson API.
Natural partial-sum predicates retain the distinction between conditional convergence and
Lean's totalized, unordered `tsum`.
-/

@[expose] public noncomputable section
open Complex Filter Finset Set MeasureTheory
open scoped Real Topology
namespace DLMF.QHypergeometric

/-- Jackson's q-derivative with the derivative value at the origin specified in DLMF. -/
@[dlmf 17.2.E41]
def qDerivExtended (q : ℂ) (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z=0 then deriv f 0 else DLMF.QSeries.qDeriv q f z
/-- The n-fold q-derivative, including its DLMF value at the origin. -/
def qDerivIterate (n : ℕ) (q : ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  (fun g : ℂ → ℂ => qDerivExtended q g)^[n] f
/-- A finite two-endpoint Jackson integral, reusing the existing integral from zero. -/
def jacksonBetween (q a b : ℂ) (f : ℂ → ℂ) : ℂ :=
  DLMF.QSeries.jacksonIntegral q b f-DLMF.QSeries.jacksonIntegral q a f
/-- The bilateral Jackson integral, used only together with convergence hypotheses. -/
@[dlmf 17.2.E48]
def jacksonBilateral (q : ℂ) (f : ℂ → ℂ) : ℂ :=
  (1-q)*∑' n : ℤ, q^n*f (q^n)
/-- Natural-order convergence of the finite-interval Jackson series, permitting conditional sums. -/
def HasNaturalJacksonIntegral (q a : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  Tendsto (fun N : ℕ => a*(1-q)*∑ j∈range N, f (a*q^j)*q^j) atTop (𝓝 v)
/-- Bilateral natural convergence means convergence of both tails separately. -/
def HasNaturalJacksonBilateral (q : ℂ) (f : ℂ → ℂ) (v : ℂ) : Prop :=
  ∃ vp vm : ℂ,
    Tendsto (fun N : ℕ => ∑ j∈range N, q^j*f (q^j)) atTop (𝓝 vp) ∧
    Tendsto (fun N : ℕ => ∑ j∈range N, q^(-(j:ℤ)-1)*f (q^(-(j:ℤ)-1))) atTop (𝓝 vm) ∧
    v=(1-q)*(vp+vm)

/-- Away from the origin the existing q-derivative is reused exactly. -/
theorem qDerivExtended_of_ne_zero {z : ℂ} (hz : z≠0) (q : ℂ) (f : ℂ → ℂ) :
    qDerivExtended q f z=DLMF.QSeries.qDeriv q f z := by simp [qDerivExtended,hz]
/-- The value at the origin is the ordinary derivative, rather than division by zero. -/
theorem qDerivExtended_zero (q : ℂ) (f : ℂ → ℂ) : qDerivExtended q f 0=deriv f 0 := by
  simp [qDerivExtended]

open DLMF.QSeries

/-- Integer-upper Gaussian coefficient, extending the existing natural-upper polynomial. -/
def qBinomialInt (q : ℂ) (n : ℤ) (m : ℕ) : ℂ :=
  qPochhammer (q^(n-(m:ℤ)+1)) q m/qPochhammer q q m
/-- qPochhammer negative modular. -/
@[dlmf 17.2.E6_2]
theorem qPochhammer_negative_modular {t : ℝ} (ht : 0<t) :
    qPochhammerInf (-Complex.exp (-(t:ℂ))) (Complex.exp (-(t:ℂ)))=
      (Real.sqrt 2:ℂ)⁻¹*Complex.exp ((π:ℂ)^2/(12*t)+t/24)*
        qPochhammerInf (Complex.exp (-2*(π:ℂ)^2/t)) (Complex.exp (-4*(π:ℂ)^2/t)) := by
  sorry

/-- qBinom ratio. -/
@[dlmf 17.2.E27]
theorem qBinom_ratio {q : ℂ} (hq : ‖q‖<1) {m n : ℕ} (hm : m≤n) :
    qBinom q n m=qPochhammer q q n/(qPochhammer q q m*qPochhammer q q (n-m)) := by
  have h := qBinom_mul_qPochhammer q m (n-m)
  rw [Nat.add_sub_of_le hm] at h
  apply (eq_div_iff (mul_ne_zero (qPochhammer_self_ne_zero hq m)
    (qPochhammer_self_ne_zero hq (n-m)))).2
  simpa [mul_assoc] using h

/-- qBinom terminating ratio. -/
@[dlmf 17.2.E27]
theorem qBinom_terminating_ratio {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) {m n : ℕ} (hm : m≤n) :
    qBinom q n m=qPochhammer (q^(-(n:ℤ))) q m*(-1:ℂ)^m*
      q^((n:ℤ)*m-(m.choose 2:ℤ))/qPochhammer q q m := by
  sorry

/-- qBinomialInt nat. -/
theorem qBinomialInt_nat {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) (n m : ℕ) :
    qBinomialInt q n m=qBinom q n m := by
  unfold qBinomialInt
  by_cases hm : m≤n
  · rw [show (n:ℤ)-(m:ℤ)+1=((n-m+1:ℕ):ℤ) by omega,zpow_natCast]
    simpa [Nat.add_sub_of_le hm,pow_succ,mul_comm] using (qBinom_eq hq m (n-m)).symm
  · have hmn : n<m := by omega
    rw [qBinom_eq_zero_of_lt q hmn]
    rw [show (n:ℤ)-(m:ℤ)+1= -((m-n-1:ℕ):ℤ) by omega]
    rw [zpow_neg,zpow_natCast,qPochhammer_recip_pow_eq_zero hq0 (by omega : m-n-1<m),zero_div]

/-- qBinomialInt negative. -/
@[dlmf 17.2.E30]
theorem qBinomialInt_negative {q : ℂ} (hq0 : q≠0) (hq : ‖q‖<1) {n : ℕ} (hn : 0<n) (m : ℕ) :
    qBinomialInt q (-(n:ℤ)) m=qBinom q (m+n-1) m*(-1:ℂ)^m*
      q^(-(m:ℤ)*n-(m.choose 2:ℤ)) := by
  sorry

/-- qBinom pascal second. -/
@[dlmf 17.2.E32]
theorem qBinom_pascal_second (q : ℂ) (n m : ℕ) :
    qBinom q (n+m+1) (m+1)=qBinom q (n+m) (m+1)+q^n*qBinom q (n+m) m := by
  simpa using DLMF.QSeries.qBinom_succ_succ' q (n+m) m

/-- qBinom fixed lower limit. -/
@[dlmf 17.2.E33]
theorem qBinom_fixed_lower_limit {q : ℂ} (hq : ‖q‖<1) (m : ℕ) :
    Tendsto (fun n : ℕ => qBinom q n m) atTop (𝓝 (qPochhammer q q m)⁻¹) := by
  apply (tendsto_add_atTop_iff_nat m).1
  have hp := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul q
  have hc := (continuous_qPochhammer q m).continuousAt.tendsto.comp hp
  have h := hc.div_const (qPochhammer q q m)
  simp only [mul_zero,qPochhammer_zero_param,one_div] at h
  refine h.congr' (Eventually.of_forall fun n => ?_)
  simpa only [Function.comp_apply,Nat.add_comm n m] using (qBinom_eq hq m n).symm

/-- Both Gaussian indices tend to infinity; s>0 is necessary (s=0 gives a different fixed-index limit). -/
@[dlmf 17.2.E34]
theorem qBinom_two_growing_indices {q : ℂ} (hq : ‖q‖<1) {r s : ℕ} (hs : 0<s) (hrs : s<r)
    (u t : ℕ) : Tendsto (fun n : ℕ => qBinom q (r*n+u) (s*n+t)) atTop
      (𝓝 (qPochhammerInf q q)⁻¹) := by
  have hP := qPochhammerInf_ne_zero_of_norm_lt_one hq hq
  have htop : Tendsto (fun n : ℕ => r*n+u) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
  have hbot : Tendsto (fun n : ℕ => s*n+t) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
  have hdiff : Tendsto (fun n : ℕ => (r*n+u)-(s*n+t)) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b+t, fun n hn => by
      have : b+(s*n+t)≤r*n+u := by nlinarith
      omega⟩
  have hlim := ((tendsto_qPochhammer (w := q) hq).comp htop).div
    (((tendsto_qPochhammer (w := q) hq).comp hbot).mul ((tendsto_qPochhammer (w := q) hq).comp hdiff))
    (mul_ne_zero hP hP)
  have hval : qPochhammerInf q q/(qPochhammerInf q q*qPochhammerInf q q)=
      (qPochhammerInf q q)⁻¹ := by field_simp
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop t] with n hn
  exact (qBinom_ratio hq (by nlinarith : s*n+t≤r*n+u)).symm

-- DLMF 17.2.E36 is Mathlib `add_pow` specialized to -z and 1; see MathlibCoverage.

/-- q binomial series. -/
@[dlmf 17.2.E38]
theorem q_binomial_series {q z : ℂ} (hq : ‖q‖<1) (hz : ‖z‖<1) (m : ℕ) :
    HasSum (fun n : ℕ => qBinom q (n+m) n*z^n) (qPochhammer z q (m+1))⁻¹ := by
  have hs := (summable_q_binomial_series (a := q*q^m) hq hz).hasSum
  rw [← q_binomial_theorem hq hz] at hs
  have hshift := qPochhammerInf_mul_qPochhammer (a := z) hq (m+1)
  have hi := qPochhammerInf_ne_zero_of_norm_lt_one hz hq
  have htail := qPochhammerInf_shift_ne_zero hq
    (fun j => one_sub_mul_pow_ne_zero_of_norm hz hq j) (m+1)
  have hprod := qPochhammer_ne_zero_of_factors hq
    (fun j => one_sub_mul_pow_ne_zero_of_norm hz hq j) (m+1)
  have hv : qPochhammerInf ((q*q^m)*z) q/qPochhammerInf z q=
      (qPochhammer z q (m+1))⁻¹ := by
    rw [show (q*q^m)*z=z*q^(m+1) by rw [pow_succ]; ring]
    rw [hshift]
    field_simp
  rw [hv] at hs
  simpa [qBinom_eq hq] using hs

/-- q binomial base square. -/
@[dlmf 17.2.E39]
theorem q_binomial_base_square (q : ℂ) (n : ℕ) :
    ∑ j∈range (n+1), qBinom (q^2) n j*q^j=qPochhammer (-q) q n := by
  sorry

/-- q binomial alternating even. -/
@[dlmf 17.2.E40]
theorem q_binomial_alternating_even (q : ℂ) (n : ℕ) :
    ∑ j∈range (2*n+1), (-1:ℂ)^j*qBinom q (2*n) j=qPochhammer q (q^2) n := by
  sorry

/-- qDeriv iterate finite difference. -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_finite_difference {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q f z=z^(-(n:ℤ))*(1-q)^(-(n:ℤ))*
      ∑ j∈range (n+1), q^(-(n:ℤ)*j+((j+1).choose 2:ℤ))*(-1:ℂ)^j*qBinom q n j*f (z*q^j) := by
  sorry

/-- qDeriv iterate origin. -/
@[dlmf 17.2.E42]
theorem qDeriv_iterate_origin {q : ℂ} (hq1 : q≠1) {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0) (n : ℕ) :
    qDerivIterate n q f 0=iteratedDeriv n f 0*qPochhammer q q n/
      ((n.factorial:ℂ)*(1-q)^n) := by
  sorry

/-- qDeriv product extended. -/
@[dlmf 17.2.E43]
theorem qDeriv_product_extended (q z : ℂ) (f g : ℂ → ℂ)
    (hf : z=0 → DifferentiableAt ℂ f 0) (hg : z=0 → DifferentiableAt ℂ g 0) :
    qDerivExtended q (fun w => f w*g w) z=
      g z*qDerivExtended q f z+f (z*q)*qDerivExtended q g z := by
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended,mul_comm] using deriv_fun_mul (hf rfl) (hg rfl)
  · simpa [qDerivExtended,hz,mul_comm] using qDeriv_mul q f g z

/-- qDeriv leibniz. -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz {q z : ℂ} (hq0 : q≠0) (hq1 : q≠1) (hz : z≠0)
    (f g : ℂ → ℂ) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) z=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f (z*q^j)*qDerivIterate j q g z := by
  sorry

/-- qDeriv leibniz origin. -/
@[dlmf 17.2.E44]
theorem qDeriv_leibniz_origin {q : ℂ} (hq1 : q≠1) {f g : ℂ → ℂ}
    (hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (n : ℕ) :
    qDerivIterate n q (fun w => f w*g w) 0=
      ∑ j∈range (n+1), qBinom q n j*qDerivIterate (n-j) q f 0*qDerivIterate j q g 0 := by
  sorry

/-- qDeriv limit. -/
theorem qDeriv_limit {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) :
    Tendsto (fun q : ℂ => qDerivExtended q f z) (𝓝[≠] 1) (𝓝 (deriv f z)) := by
  by_cases hz : z=0
  · subst z
    simpa [qDerivExtended] using (tendsto_const_nhds :
      Tendsto (fun _ : ℂ => deriv f 0) (𝓝[≠] 1) (𝓝 (deriv f 0)))
  · simpa [qDerivExtended,hz] using DLMF.QSeries.tendsto_qDeriv hf.hasDerivAt hz

/-- qDeriv iterate limit. -/
theorem qDeriv_iterate_limit {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (n : ℕ) :
    Tendsto (fun q : ℂ => qDerivIterate n q f z) (𝓝[≠] 1) (𝓝 (iteratedDeriv n f z)) := by
  sorry

/-- jackson series hasSum. -/
@[dlmf 17.2.E45, dlmf 17.2.E46]
theorem jackson_series_hasSum {q a : ℂ} (hq : ‖q‖<1) {f : ℂ → ℂ} (hf : ContinuousAt f 0) :
    HasSum (fun j : ℕ => a*(1-q)*f (a*q^j)*q^j) (jacksonIntegral q a f) := by
  have hpow := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hq).const_mul a
  simp only [mul_zero] at hpow
  have hcont : Tendsto (fun j : ℕ => f (a*q^j)) atTop (𝓝 (f 0)) := by
    simpa only [Function.comp_def] using hf.tendsto.comp hpow
  obtain ⟨B,hB⟩ := hcont.norm.bddAbove_range
  have hs : Summable (fun j : ℕ => f (a*q^j)*q^j) :=
    Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left B)
      (fun j => by simpa [norm_mul,norm_pow] using
        mul_le_mul_of_nonneg_right (hB ⟨j,rfl⟩) (pow_nonneg (norm_nonneg q) j))
  simpa only [jacksonIntegral,mul_assoc] using hs.hasSum.mul_left (a*(1-q))

/-- jacksonBetween additivity. -/
theorem jacksonBetween_additivity (q a b c : ℂ) (f : ℂ → ℂ) :
    jacksonBetween q a c f=jacksonBetween q a b f+jacksonBetween q b c f := by
  simp only [jacksonBetween]; ring

/-- jackson classical limit. -/
@[dlmf 17.2.E47]
theorem jackson_classical_limit {f : ℝ → ℂ} {a : ℝ} (hf : ContinuousOn f (uIcc 0 a)) :
    Tendsto (fun q : ℝ => jacksonIntegral (q:ℂ) (a:ℂ) (fun z => f z.re))
      (𝓝[<] 1) (𝓝 (∫ x : ℝ in 0..a, f x)) := by
  sorry

/-- jackson bilateral limit. -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {f : ℂ → ℂ}
    (hf : Summable (fun j : ℤ => (q:ℂ)^j*f ((q:ℂ)^j))) :
    Tendsto (fun n : ℕ => jacksonIntegral (q:ℂ) ((q:ℂ)^(-(n:ℤ))) f) atTop
      (𝓝 (jacksonBilateral q f)) := by
  sorry

/-- The same improper-integral identity for two naturally convergent tails, without assuming absolute summability. -/
@[dlmf 17.2.E48]
theorem jackson_bilateral_natural_limit {q : ℝ} (hq0 : 0<q) (hq1 : q<1) {f : ℂ → ℂ} {v : ℂ}
    (hf : HasNaturalJacksonBilateral q f v) :
    ∃ J : ℕ → ℂ,
      (∀ n : ℕ, HasNaturalJacksonIntegral q ((q:ℂ)^(-(n:ℤ))) f (J n)) ∧
      Tendsto J atTop (𝓝 v) := by
  sorry

/-- The complete two-index Gaussian limit, including the fixed-index boundary s=0. -/
@[dlmf 17.2.E34]
theorem qBinom_two_index_limit {q : ℂ} (hq : ‖q‖<1) {r s : ℕ} (hrs : s<r)
    (u t : ℕ) : Tendsto (fun n : ℕ => qBinom q (r*n+u) (s*n+t)) atTop
      (𝓝 (if s=0 then (qPochhammer q q t)⁻¹ else (qPochhammerInf q q)⁻¹)) := by
  by_cases hs : s=0
  · subst s
    simp only [Nat.zero_mul,zero_add,ite_true]
    have hr : 0<r := hrs
    have ht : Tendsto (fun n : ℕ => r*n+u) atTop atTop :=
      tendsto_atTop_atTop.mpr fun b => ⟨b, fun n hn => by nlinarith⟩
    exact (qBinom_fixed_lower_limit hq t).comp ht
  · simpa [hs] using qBinom_two_growing_indices hq (Nat.pos_of_ne_zero hs) hrs u t

end DLMF.QHypergeometric
