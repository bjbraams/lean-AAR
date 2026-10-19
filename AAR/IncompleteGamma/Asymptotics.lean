/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.IncompleteGamma.SpecialValues

/-!
# Large argument and large parameter expansions, DLMF §8.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Statistical

/-- Falling-factorial incomplete-Gamma coefficients. -/
@[dlmf 8.11.E1]
def incGammaAsymptoticCoeff (a : ℂ) (k : ℕ) : ℂ :=
  (-1 : ℂ)^k*poch (1-a) k

/-- Normalized finite upper-Gamma remainder on the logarithmic plane. -/
@[dlmf 8.11.E2]
def incGammaAsymptoticRemainder (a : ℂ) (N : ℕ) (w : ℂ) : ℂ :=
  exp ((1-a)*w+exp w)*upperIncGammaOnLog a w-∑ k ∈ Finset.range N, incGammaAsymptoticCoeff a k*exp (-(k : ℂ)*w)

/-- upperIncGamma log asymptotic. -/
@[dlmf 8.11.E3]
theorem upperIncGamma_log_asymptotic (a : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp ((a-1-k)*w-exp w)) (incGammaAsymptoticCoeff a) (fun w => upperIncGammaOnLog a w) := by
  sorry

/-- The signed next-term real bound in DLMF §8.11(i). -/
theorem incGammaAsymptoticRemainder_real_bound {a x : ℝ} (hx : 0 < x) {N : ℕ} (hN : a-1 ≤ N) :
    ‖incGammaAsymptoticRemainder a N (Real.log x)‖ ≤ ‖incGammaAsymptoticCoeff a N/(x : ℂ)^N‖ ∧ 0 ≤ (incGammaAsymptoticRemainder a N (Real.log x)).re*(incGammaAsymptoticCoeff a N/(x : ℂ)^N).re := by
  sorry

/-- lowerIncGamma large parameter hasSum. -/
@[dlmf 8.11.E4]
theorem lowerIncGamma_large_parameter_hasSum {a : ℂ} (ha : ∀ n : ℕ, a ≠ -n) (z : ℂ) :
    HasSum (fun k : ℕ => z^a*exp (-z)*z^k/poch a (k+1)) (lowerIncGamma a z) := by
  sorry

/-- lowerIncGamma large parameter asymptotic. -/
@[dlmf 8.11.E4]
theorem lowerIncGamma_large_parameter_asymptotic {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) (N : ℕ) :
    IsBigO (sector (π-δ)) (fun a => lowerIncGamma a z-z^a*exp (-z)*∑ k ∈ Finset.range N, z^k/poch a (k+1)) (fun a => z^a*exp (-z)*z^N/poch a (N+1)) := by
  sorry

/-- normIncGammaP large parameter equivalent. -/
@[dlmf 8.11.E5]
theorem normIncGammaP_large_parameter_equivalent {z : ℂ} (hz : z ≠ 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    IsEquivalent (logSector (π-δ)) (fun w => normIncGammaPContinued (exp w) z) (fun w => z^(exp w)*exp (-z)/Gamma (1+exp w)) ∧ IsEquivalent (logSector (π-δ)) (fun w => normIncGammaPContinued (exp w) z) (fun w => exp (exp w-z+exp w*(log z-w)-w/2)/Real.sqrt (2*π)) := by
  sorry

/-- Polynomials b_k(lam), defined by the differential recurrence 8.11.9. -/
@[dlmf 8.11.E9]
def incGammaLambdaPolynomial : ℕ → Polynomial ℂ
  | 0 => 1
  | k+1 => Polynomial.X*(1-Polynomial.X)*(incGammaLambdaPolynomial k).derivative+
      Polynomial.C (2*(k : ℂ)+1)*Polynomial.X*incGammaLambdaPolynomial k

/-- incGammaLambdaPolynomial initial. -/
@[dlmf 8.11.E8]
theorem incGammaLambdaPolynomial_initial  :
    incGammaLambdaPolynomial 0=1 ∧ incGammaLambdaPolynomial 1=Polynomial.X ∧ incGammaLambdaPolynomial 2=Polynomial.X*(2*Polynomial.X+1) := by
  norm_num [incGammaLambdaPolynomial, Polynomial.derivative_mul, Polynomial.derivative_X, Polynomial.C_ofNat]
  ring

/-- lowerIncGamma fixed ratio asymptotic. -/
@[dlmf 8.11.E6]
theorem lowerIncGamma_fixed_ratio_asymptotic {lam : ℝ} (hlam : 0 < lam) (hlam1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (logSector (π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) (fun k => -(-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => lowerIncGammaOnLog (exp w) (w+Real.log lam)) := by
  sorry

/-- upperIncGamma fixed ratio asymptotic. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_fixed_ratio_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun k w => exp (exp w*(w+Real.log lam)-lam*exp w-(k+1 : ℂ)*w)/(lam-1 : ℂ)^(2*k+1)) (fun k => (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (exp w) (w+Real.log lam)) := by
  sorry

/-- The negative-parameter continuation stated after DLMF 8.11.9. -/
@[dlmf 8.11.E7]
theorem upperIncGamma_negative_parameter_ratio_asymptotic {lam : ℝ} (hlam : lam < 0) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)) :
    HasAsymptoticExpansion (logSector (3*π/2-arg ((-lam+Real.log (-lam) : ℝ)+π*I)-δ)) (fun k w => exp (-exp w*(w+Real.log (-lam))+lam*exp w-(k+1 : ℂ)*w)/(1-lam : ℂ)^(2*k+1)) (fun k => (incGammaLambdaPolynomial k).eval (lam : ℂ)) (fun w => upperIncGammaOnLog (-exp w) (w+Real.log (-lam))) := by
  sorry

/-- Uniform large positive parameter with bounded real central variable. -/
def gammaCentralFilter (B : ℝ) : Filter (ℝ × ℝ) :=
  comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℝ | 0 < p.1 ∧ |p.2| ≤ B}

/-- normIncGammaP central expansion. -/
@[dlmf 8.11.E10]
theorem normIncGammaP_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => normIncGammaPContinued (p.1+1) (p.1+Real.sqrt (2*p.1)*p.2)-erfc (-p.2)/2+((Real.sqrt (2/(π*p.1))/3*(1+p.2^2)*Real.exp (-p.2^2) : ℝ) : ℂ)) (fun p => p.1⁻¹) := by
  sorry

/-- scIncGamma central expansion. -/
@[dlmf 8.11.E11]
theorem scIncGamma_central_expansion {B : ℝ} (hB : 0 < B) :
    IsBigO (gammaCentralFilter B) (fun p : ℝ × ℝ => let x := p.1+Real.sqrt (2*p.1)*p.2; (x : ℂ)^(1-(p.1 : ℂ))*scIncGamma (1-p.1) (-x)+Real.cos (π*p.1)-Real.sin (π*p.1)/π*(2*Real.sqrt π*dawsonF p.2+(2/3*Real.sqrt (2*π/p.1)*(1-p.2^2) : ℝ))*Real.exp (p.2^2)) (fun p => p.1⁻¹) := by
  sorry

/-- upperIncGamma diagonal asymptotic. -/
@[dlmf 8.11.E12]
theorem upperIncGamma_diagonal_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 6, c n=([Real.sqrt (π/2),-1/3,Real.sqrt (2*π)/24,-4/135,Real.sqrt (2*π)/576,8/2835] : List ℂ)[n]!) ∧ ∀ δ : ℝ, 0 < δ → δ < 2*π → HasAsymptoticExpansion (logSector (2*π-δ)) (fun n w => exp ((exp w-1)*w-exp w+(1-(n : ℂ))*w/2)) c (fun w => upperIncGammaOnLog (exp w) w) := by
  sorry

/-- expPartialSum poisson limit. -/
@[dlmf 8.11.E13]
theorem expPartialSum_poisson_limit {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun n : ℕ => expPartialSum n (n*x)/exp (n*x : ℂ)) atTop (𝓝 (if 1 < x then 0 else if x=1 then 1/2 else 1)) := by
  sorry

/-- The exponential partial-sum remainder S_n. -/
@[dlmf 8.11.E15]
def expPartialSumRemainderS (n : ℕ) (x : ℝ) : ℂ :=
  lowerIncGamma (n+1) (n*x)/((n*x : ℂ)^n*exp (-n*x : ℂ))

/-- expPartialSumRemainderS identity. -/
@[dlmf 8.11.E14]
theorem expPartialSumRemainderS_identity (n : ℕ) (x : ℝ) :
    exp (n*x : ℂ)=expPartialSum n (n*x)+(n*x : ℂ)^n/n.factorial*expPartialSumRemainderS n x := by
  sorry

/-- expPartialSumRemainderS one asymptotic. -/
@[dlmf 8.11.E16]
theorem expPartialSumRemainderS_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 4, c n=([-2/3,4/135,-8/2835,-16/8505] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) 1-(n+1).factorial*exp (n+1 : ℂ)/(2*(n+1 : ℂ)^(n+1))) := by
  sorry

/-- expPartialSumRemainderS neg one asymptotic. -/
@[dlmf 8.11.E17]
theorem expPartialSumRemainderS_neg_one_asymptotic  :
    ∃ c : ℕ → ℂ, (∀ n < 5, c n=([-1/2,1/8,1/32,-1/128,-13/512] : List ℂ)[n]!) ∧ HasAsymptoticExpansion atTop (fun j (n : ℕ) => (n+1 : ℂ)^(-(j : ℤ))) c (fun n => expPartialSumRemainderS (n+1) (-1)) := by
  sorry

/-- The coefficients d_k(x). -/
@[dlmf 8.11.E19]
def expPartialSumRemainderCoeff (k : ℕ) (x : ℝ) : ℂ :=
  if k=0 then x/(1-x) else (-1 : ℂ)^k*(incGammaLambdaPolynomial k).eval (x : ℂ)/(1-x : ℂ)^(2*k+1)

/-- expPartialSumRemainderS uniform asymptotic. -/
@[dlmf 8.11.E18]
theorem expPartialSumRemainderS_uniform_asymptotic {δ : ℝ} (hδ : 0 < δ) (N : ℕ) :
    IsBigO (comap (fun p : ℕ × ℝ => p.1) atTop ⊓ 𝓟 {p : ℕ × ℝ | p.2 ≤ 1-δ}) (fun p => expPartialSumRemainderS (p.1+1) p.2-∑ k ∈ Finset.range N, expPartialSumRemainderCoeff k p.2/(p.1+1 : ℂ)^k) (fun p => (p.1+1 : ℝ)^(-(N : ℤ))) := by
  sorry

end AAR.Confluent
