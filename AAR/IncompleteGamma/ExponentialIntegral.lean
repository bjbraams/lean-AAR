/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues

/-!
# Generalized exponential integral, DLMF §8.19

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- Generalized exponential integral on the logarithmic plane. -/
def genExpIntEOnLog (p w : ℂ) : ℂ :=
  exp ((p-1)*w)*upperIncGammaOnLog (1-p) w

/-- Extension at zero in Re p>1; the old plain function keeps its totalized value. -/
def genExpIntEExtended (p z : ℂ) : ℂ :=
  if z=0 then 1/(p-1) else genExpIntE p z

/-- genExpIntE horizontal integral. -/
@[dlmf 8.19.E2]
theorem genExpIntE_horizontal_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => (z+t)^(-p)*exp (-(z+t))) 0 (z^(1-p)*genExpIntE p z) := by
  sorry

/-- genExpIntE laplace complex. -/
@[dlmf 8.19.E3]
theorem genExpIntE_laplace_complex (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    genExpIntE p z=∫ t : ℝ in Ioi 1, exp (-z*t)*(t : ℂ)^(-p) := by
  sorry

/-- genExpIntE stieltjes. -/
@[dlmf 8.19.E4]
theorem genExpIntE_stieltjes {p z : ℂ} (hp : 0 < p.re) (hz : 0 < z.re) :
    genExpIntE p z=z^(p-1)*exp (-z)/Gamma p*(∫ t : ℝ in Ioi 0, (t : ℂ)^(p-1)*exp (-z*t)/(1+t)) := by
  sorry

/-- genExpIntEExtended zero. -/
@[dlmf 8.19.E6]
theorem genExpIntEExtended_zero {p : ℂ} (hp : 1 < p.re) :
    genExpIntEExtended p 0=1/(p-1) ∧ ContinuousAt (genExpIntEExtended p) 0 := by
  sorry

/-- genExpIntE nat finite. -/
@[dlmf 8.19.E7]
theorem genExpIntE_nat_finite {n : ℕ} (hn : 2 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-z)^(n-1)/(n-1).factorial*genExpIntE 1 z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), ((n-k-2).factorial : ℂ)*(-z)^k) := by
  sorry

/-- genExpIntE nat hasSum. -/
@[dlmf 8.19.E8]
theorem genExpIntE_nat_hasSum {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => if k=n-1 then 0 else (-z)^k/((k.factorial : ℂ)*(1-(n : ℂ)+k))) ((-z)^(n-1)/(n-1).factorial*(digamma n-log z)-genExpIntE n z) := by
  sorry

/-- genExpIntE nat digamma series. -/
@[dlmf 8.19.E9]
theorem genExpIntE_nat_digamma_series {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    genExpIntE n z=(-1 : ℂ)^n*z^(n-1)/(n-1).factorial*log z+exp (-z)/(n-1).factorial*(∑ k ∈ Finset.range (n-1), (-z)^k*Gamma (n-(k+1)))+exp (-z)*(-z)^(n-1)/(n-1).factorial*(∑' k : ℕ, z^k/(k.factorial : ℂ)*digamma (k+1)) := by
  sorry

/-- genExpIntE hasSum noninteger. -/
@[dlmf 8.19.E10]
theorem genExpIntE_hasSum_noninteger {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => (-z)^k/((k.factorial : ℂ)*(1-p+k))) (z^(p-1)*Gamma (1-p)-genExpIntE p z) := by
  sorry

/-- genExpIntE hasSum exponential. -/
@[dlmf 8.19.E11]
theorem genExpIntE_hasSum_exponential {p : ℂ} (hp : ∀ n : ℕ, p ≠ n+1) {z : ℂ} (hz : z ≠ 0) :
    HasSum (fun k : ℕ => exp (-z)*z^k/Gamma (2-p+k)) (z^(p-1)-genExpIntE p z/Gamma (1-p)) := by
  sorry

/-- The required limiting interpretation at positive integral p. -/
@[dlmf 8.19.E10, dlmf 8.19.E11]
theorem genExpIntE_series_integer_limits {n : ℕ} (hn : 1 ≤ n) {z : ℂ} (hz : z ≠ 0) :
    Tendsto (fun p : ℂ => z^(p-1)*Gamma (1-p)-∑' k : ℕ, (-z)^k/((k.factorial : ℂ)*(1-p+k))) (𝓝[≠] (n : ℂ)) (𝓝 (genExpIntE n z)) := by
  sorry

/-- genExpIntE scaled derivative. -/
@[dlmf 8.19.E14]
theorem genExpIntE_scaled_derivative (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun t => exp t*genExpIntE p t) (exp z*genExpIntE p z*(1+(p-1)/z)-1/z) z := by
  sorry

/-- genExpIntE parameter derivatives. -/
@[dlmf 8.19.E15]
theorem genExpIntE_parameter_derivatives (j : ℕ) (p : ℂ) {z : ℂ} (hz : 0 < z.re) :
    iteratedDeriv j (fun q => genExpIntE q z) p=(-1 : ℂ)^j*(∫ t : ℝ in Ioi 1, (Real.log t : ℂ)^j*(t : ℂ)^(-p)*exp (-z*t)) := by
  sorry

/-- genExpIntE continuedFraction. -/
@[dlmf 8.19.E17]
theorem genExpIntE_continuedFraction (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasContinuedFraction (fun k => if k=0 then exp (-z) else if Odd k then p+((k-1)/2 : ℕ) else ((k/2 : ℕ) : ℂ)) (fun k => if Even k then z else 1) (genExpIntE p z) := by
  sorry

/-- genExpIntEOnLog monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_monodromy {p : ℂ} (hp : ∀ n : ℤ, p ≠ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog p (w+2*m*π*I)=2*π*I*exp (m*p*π*I)/Gamma p*sin (m*p*π)/sin (p*π)*exp ((p-1)*w)+genExpIntEOnLog p w := by
  sorry

/-- genExpIntEOnLog nat monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nat_monodromy {n : ℕ} (hn : 1 ≤ n) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog n (w+2*m*π*I)=genExpIntEOnLog n w+2*π*I*m*(-1 : ℂ)^n/(n-1).factorial*exp (((n : ℂ)-1)*w) := by
  sorry

/-- genExpIntEOnLog nonpos nat monodromy. -/
@[dlmf 8.19.E18]
theorem genExpIntEOnLog_nonpos_nat_monodromy (n : ℕ) (w : ℂ) (m : ℤ) :
    genExpIntEOnLog (-n) (w+2*m*π*I)=genExpIntEOnLog (-n) w := by
  sorry

/-- Each nonzero-argument branch is entire in p. -/
theorem genExpIntEOnLog_parameter_entire (w : ℂ) :
    Differentiable ℂ (fun p => genExpIntEOnLog p w) := by
  sorry

/-- Nontrivial monodromy except at nonpositive integral order. -/
theorem genExpIntEOnLog_branch_point {p : ℂ} (hp : ∀ n : ℕ, p ≠ -n) (w : ℂ) :
    genExpIntEOnLog p (w+2*π*I) ≠ genExpIntEOnLog p w := by
  sorry

/-- genExpIntE nat order bounds. -/
@[dlmf 8.19.E19]
theorem genExpIntE_nat_order_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    ((n : ℝ)-1)/n*(genExpIntE n x).re < (genExpIntE (n+1) x).re ∧ (genExpIntE (n+1) x).re < (genExpIntE n x).re := by
  sorry

/-- genExpIntE nat logconvex. -/
@[dlmf 8.19.E20]
theorem genExpIntE_nat_logconvex {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (genExpIntE n x).re^2 < (genExpIntE (n-1 : ℕ) x).re*(genExpIntE (n+1) x).re := by
  sorry

/-- genExpIntE nat rational bounds. -/
@[dlmf 8.19.E21]
theorem genExpIntE_nat_rational_bounds {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    1/(x+n) < Real.exp x*(genExpIntE n x).re ∧ Real.exp x*(genExpIntE n x).re ≤ 1/(x+n-1) := by
  sorry

/-- genExpIntE nat ratio derivative. -/
@[dlmf 8.19.E22]
theorem genExpIntE_nat_ratio_derivative {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    0 < deriv (fun y : ℝ => (genExpIntE n y).re/(genExpIntE (n-1 : ℕ) y).re) x := by
  sorry

/-- genExpIntE tail integral. -/
@[dlmf 8.19.E23]
theorem genExpIntE_tail_integral (p : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasIntegralAtTop (fun t : ℝ => genExpIntE (p-1) (z+t)) 0 (genExpIntE p z) := by
  sorry

/-- genExpIntE nat laplace. -/
@[dlmf 8.19.E24]
theorem genExpIntE_nat_laplace {n : ℕ} (hn : 1 ≤ n) {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE n t)=if a=0 then 1/(n : ℂ) else (-1 : ℂ)^(n-1)/a^n*(log (1+a)+∑ k ∈ Finset.range (n-1), (-1 : ℂ)^(k+1)*a^(k+1)/(k+1)) := by
  sorry

/-- The displayed formula also needs Re b>0 for convergence at zero. -/
@[dlmf 8.19.E25]
theorem genExpIntE_mellin_laplace {a b p : ℂ} (ha : -1 < a.re) (hb : 0 < b.re) (hpb : 1 < (p+b).re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*(t : ℂ)^(b-1)*genExpIntE p t)=Gamma b*(1+a)^(-b)/(p+b-1)*Gamma (p+b)*AAR.Hypergeometric.regularizedGaussHG 1 b (p+b) (a/(1+a)) := by
  sorry

/-- The auxiliary integral L(p) for positive p. -/
@[dlmf 8.19.E27]
def genExpIntL (p : ℝ) : ℂ :=
  ∫ t : ℝ in Ioi 0, exp (-t : ℂ)*genExpIntE p t

/-- genExpIntL hypergeometric. -/
@[dlmf 8.19.E27]
theorem genExpIntL_hypergeometric {p : ℝ} (hp : 0 < p) :
    genExpIntL p=Gamma (1+(p : ℂ))/(2*p)*AAR.Hypergeometric.regularizedGaussHG 1 1 (1+p) (1/2) := by
  sorry

/-- genExpIntE product integral. -/
@[dlmf 8.19.E26]
theorem genExpIntE_product_integral {p q : ℝ} (hp : 0 < p) (hq : 0 < q) (hpq : 1 < p+q) :
    (∫ t : ℝ in Ioi 0, genExpIntE p t*genExpIntE q t)=(genExpIntL p+genExpIntL q)/(p+q-1) := by
  sorry

/-- The error-to-exponential-integral relation with its square-argument continuation. -/
@[dlmf 7.11.E3]
theorem erfc_genExpIntEOnLog_square {z : ℂ} (hz : z ≠ 0) :
    erfc z=z/Real.sqrt π*genExpIntEOnLog (1/2) (2*log z) := by
  sorry

end AAR.Confluent
