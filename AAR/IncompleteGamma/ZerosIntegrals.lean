/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues
public import Mathlib.NumberTheory.LSeries.HurwitzZeta
public import Mathlib.NumberTheory.Bernoulli

/-!
# Zeros, transforms and sums, DLMF §§8.13–8.15

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- The negative x-zero when it exists. -/
def Real.scIncGammaNegativeZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => x < 0 ∧ scIncGamma a x=0)

/-- The positive x-zero when it exists. -/
def Real.scIncGammaPositiveZero (a : ℝ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ scIncGamma a x=0)

/-- scIncGamma nonnegative parameter no real zeros. -/
theorem scIncGamma_nonnegative_parameter_no_real_zeros {a : ℝ} (ha : 0 ≤ a) (x : ℝ) :
    scIncGamma a x ≠ 0 := by
  sorry

/-- scIncGamma one negative zero. -/
theorem scIncGamma_one_negative_zero {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : 1-2*(n : ℝ) < a) (ha1 : a < 2-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a := by
  sorry

/-- scIncGamma two real zeros. -/
theorem scIncGamma_two_real_zeros {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha0 : -2*(n : ℝ) < a) (ha1 : a < 1-2*(n : ℝ)) :
    Real.scIncGammaNegativeZero a < 0 ∧ 0 < Real.scIncGammaPositiveZero a ∧ ∀ x : ℝ, scIncGamma a x=0 ↔ x=Real.scIncGammaNegativeZero a ∨ x=Real.scIncGammaPositiveZero a := by
  sorry

/-- Real.scIncGammaNegativeZero strictAnti. -/
theorem Real.scIncGammaNegativeZero_strictAnti  :
    StrictAntiOn Real.scIncGammaNegativeZero (Ioo (-1) 0) := by
  sorry

/-- Real.scIncGammaNegativeZero bounds. -/
@[dlmf 8.13.E1]
theorem Real.scIncGammaNegativeZero_bounds {a : ℝ} (ha0 : -1 < a) (ha1 : a < 0) :
    1+1/a < Real.scIncGammaNegativeZero a ∧ Real.scIncGammaNegativeZero a < Real.log |a| := by
  sorry

/-- The double parameter-zero pair (a_n*,x_n*). -/
def scIncGammaDoubleZero (n : ℕ) : ℝ × ℝ :=
  Classical.epsilon (fun p : ℝ × ℝ => -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0)

/-- scIncGamma two parameter zeros negative x. -/
theorem scIncGamma_two_parameter_zeros_negative_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : x < 0) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 2-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- scIncGamma two parameter zeros positive x. -/
theorem scIncGamma_two_parameter_zeros_positive_x {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) (hx1 : x < (scIncGammaDoubleZero n).2) :
    ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a x=0} : Set ℝ).ncard=2 := by
  sorry

/-- At coalescence the two zeros are counted with multiplicity, not as distinct points. -/
theorem scIncGamma_double_parameter_zero {n : ℕ} (hn : 1 ≤ n) :
    let p := scIncGammaDoubleZero n; -2*(n : ℝ) < p.1 ∧ p.1 < 1-2*(n : ℝ) ∧ 0 < p.2 ∧ scIncGamma p.1 p.2=0 ∧ deriv (fun a : ℂ => scIncGamma a p.2) p.1=0 ∧ iteratedDeriv 2 (fun a : ℂ => scIncGamma a p.2) p.1 ≠ 0 ∧ ({a : ℝ | -2*(n : ℝ) < a ∧ a < 1-2*(n : ℝ) ∧ scIncGamma a p.2=0} : Set ℝ).ncard=1 := by
  sorry

/-- scIncGamma parameter zeros at x zero. -/
theorem scIncGamma_parameter_zeros_at_x_zero (a : ℝ) :
    scIncGamma a 0=0 ↔ ∃ n : ℕ, 1 ≤ n ∧ a = -(n : ℝ) := by
  sorry

/-- scIncGamma conjugate zero trajectories. -/
theorem scIncGamma_conjugate_zero_trajectories {n : ℕ} (hn : 1 ≤ n) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ f : ℝ → ℂ, ContinuousOn f (Icc (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ)) ∧ f (scIncGammaDoubleZero n).2=(scIncGammaDoubleZero n).1 ∧ ∀ x ∈ Ioo (scIncGammaDoubleZero n).2 ((scIncGammaDoubleZero n).2+δ), 0 < (f x).im ∧ scIncGamma (f x) x=0 ∧ scIncGamma (star (f x)) x=0 := by
  sorry

/-- normIncGammaP laplace. -/
@[dlmf 8.14.E1]
theorem normIncGammaP_laplace {a b : ℂ} (ha : 0 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*normIncGammaPContinued b x)=(1+a)^(-b)/a := by
  sorry

/-- upperIncGamma laplace. -/
@[dlmf 8.14.E2]
theorem upperIncGamma_laplace {a b : ℂ} (ha : -1 < a.re) (hb : -1 < b.re) :
    (∫ x : ℝ in Ioi 0, exp (-a*x)*upperIncGamma b x)=if a=0 then Gamma (b+1) else if b=0 then log (1+a)/a else Gamma b*(1-(1+a)^(-b))/a := by
  sorry

/-- lowerIncGamma mellin. -/
@[dlmf 8.14.E3]
theorem lowerIncGamma_mellin {a b : ℂ} (ha : a.re < 0) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*lowerIncGamma b x) = -Gamma (a+b)/a := by
  sorry

/-- upperIncGamma mellin. -/
@[dlmf 8.14.E4]
theorem upperIncGamma_mellin {a b : ℂ} (ha : 0 < a.re) (hab : 0 < (a+b).re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*upperIncGamma b x)=Gamma (a+b)/a := by
  sorry

/-- lowerIncGamma mellin laplace. -/
@[dlmf 8.14.E5]
theorem lowerIncGamma_mellin_laplace {a b s : ℂ} (hs : 0 < s.re) (hab : 0 < (a+b).re) (hb : ∀ n : ℕ, b ≠ -n) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*lowerIncGamma b x)=Gamma (a+b)/(b*(1+s)^(a+b))*Gamma (1+b)*AAR.Hypergeometric.regularizedGaussHG 1 (a+b) (1+b) (1/(1+s)) := by
  sorry

/-- upperIncGamma mellin laplace. -/
@[dlmf 8.14.E6]
theorem upperIncGamma_mellin_laplace {a b s : ℂ} (hs : -1 < s.re) (hab : 0 < (a+b).re) (ha : 0 < a.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ)^(a-1)*exp (-s*x)*upperIncGamma b x)=Gamma (a+b)/(a*(1+s)^(a+b))*Gamma (1+a)*AAR.Hypergeometric.regularizedGaussHG 1 (a+b) (1+a) (s/(1+s)) := by
  sorry

/-- lowerIncGamma multiplication hasSum. -/
@[dlmf 8.15.E1]
theorem lowerIncGamma_multiplication_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (u v : ℂ) :
    HasSum (fun k : ℕ => exp (a*v)*lowerIncGammaOnLog (a+k) u*(1-exp v)^k/(k.factorial : ℂ)) (lowerIncGammaOnLog a (u+v)) := by
  sorry

/-- Complex-argument Hurwitz zeta by Euler–Maclaurin continuation; used only for 8.15.2. -/
def hurwitzZetaComplex (s z : ℂ) : ℂ :=
  let M := ⌈(1-s.re)/2⌉₊+1; limUnder atTop (fun N : ℕ => (∑ n ∈ Finset.range N, (z+n)^(-s))+(z+N)^(1-s)/(s-1)+(z+N)^(-s)/2+∑ k ∈ Finset.range M, (bernoulli (2*k+2) : ℂ)/(2*k+2).factorial*poch s (2*k+1)*(z+N)^(-s-(2*k+1)))

/-- Bridge to Mathlib; its existing Hurwitz zeta is periodic in a real second argument. -/
theorem hurwitzZetaComplex_mathlib {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) {s : ℂ} (hs : s ≠ 1) :
    hurwitzZetaComplex s x=HurwitzZeta.hurwitzZeta (x : UnitAddCircle) s := by
  sorry

/-- Inherited logarithms and a right-half-plane convergence domain are explicit. -/
@[dlmf 8.15.E2]
theorem incompleteGamma_hurwitz_fourier_sum {a z : ℂ} (ha : a ≠ -1) (hz : 0 < z.re) {h : ℝ} (hh0 : 0 ≤ h) (hh1 : h ≤ 1) :
    HasSum (fun k : ℕ => let j : ℂ := k+1; a*(exp (2*π*I*j*(z+h))/(2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)+π*I/2)+exp (-2*π*I*j*(z+h))/(-2*π*I*j)^(a+1)*upperIncGammaOnLog a (log z+log (2*π*j)-π*I/2))) (hurwitzZetaComplex (-a) (z+h)+z^(a+1)/(a+1)+(h-1/2)*z^a) := by
  sorry

/-- The function F(p,x) approximated in DLMF §8.27(i). -/
def Real.gammaDiDonatoF (p x : ℝ) : ℝ :=
  x^(-p)*Real.exp (x^2/2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2/2)*t^p)

/-- The explicit approximation denominator in DLMF §8.27(i). -/
def Real.gammaDiDonatoH (p x : ℝ) : ℝ :=
  3*(x^2-p)+Real.sqrt ((x^2-p)^2+8*(x^2+p))

/-- The change of variable mentioned in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_gamma (p : ℝ) {x : ℝ} (hx : 0 < x) :
    (Real.gammaDiDonatoF p x : ℂ)=(x : ℂ)^(-(p : ℂ))*Real.exp (x^2/2)*(2 : ℂ)^(((p : ℂ)-1)/2)*upperIncGamma ((p+1)/2) (x^2/2) := by
  sorry

/-- The explicit O(x^-7) approximation theorem in DLMF §8.27(i). -/
theorem Real.gammaDiDonato_approximation (p : ℝ) :
    IsBigO atTop (fun x : ℝ => Real.gammaDiDonatoF p x-4*x/Real.gammaDiDonatoH p x) (fun x => x^(-7 : ℤ)) := by
  sorry

end AAR.Confluent
