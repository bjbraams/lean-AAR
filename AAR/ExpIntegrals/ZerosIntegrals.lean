/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ExpIntegrals.Asymptotics

/-!
# Zeros, transforms, sums and computational recurrences, DLMF §§6.13–6.18

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- The unique real zero of Ei. -/
@[dlmf 6.13.E1]
def Real.expIntEiZero  : ℝ :=
  Classical.epsilon (fun x : ℝ => x ≠ 0 ∧ Real.expIntEi x=0)

/-- Positive Ci zeros, indexed from zero. -/
def Real.cosIntZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.cosInt x=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.cosInt y=0} : Set ℝ).ncard=k)

/-- Positive si zeros, indexed from zero. -/
def Real.sinIntTailZero (k : ℕ) : ℝ :=
  Classical.epsilon (fun x : ℝ => 0 < x ∧ Real.sinInt x-π/2=0 ∧ ({y : ℝ | 0 < y ∧ y < x ∧ Real.sinInt y-π/2=0} : Set ℝ).ncard=k)

/-- Real.expIntEi unique zero. -/
theorem Real.expIntEi_unique_zero  :
    Real.expIntEiZero ≠ 0 ∧ Real.expIntEi Real.expIntEiZero=0 ∧ ∀ x : ℝ, x ≠ 0 → Real.expIntEi x=0 → x=Real.expIntEiZero := by
  sorry

/-- Real.expIntEiZero decimal. -/
@[dlmf 6.13.E1]
theorem Real.expIntEiZero_decimal  :
    372507410781366634461991866580/10^30 ≤ Real.expIntEiZero ∧ Real.expIntEiZero < 372507410781366634461991866581/10^30 := by
  sorry

/-- Real.cosIntZero spec. -/
theorem Real.cosIntZero_spec (k : ℕ) :
    0 < Real.cosIntZero k ∧ (Real.cosInt) (Real.cosIntZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.cosIntZero k ∧ (Real.cosInt) y=0} : Set ℝ).ncard=k := by
  sorry

/-- Real.cosIntZero enumeration. -/
theorem Real.cosIntZero_enumeration  :
    StrictMono Real.cosIntZero ∧ ∀ x : ℝ, 0 < x → ((Real.cosInt) x=0 ↔ ∃ k, Real.cosIntZero k=x) := by
  sorry

/-- Real.sinIntTailZero spec. -/
theorem Real.sinIntTailZero_spec (k : ℕ) :
    0 < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) (Real.sinIntTailZero k)=0 ∧ ({y : ℝ | 0 < y ∧ y < Real.sinIntTailZero k ∧ (fun x => Real.sinInt x-π/2) y=0} : Set ℝ).ncard=k := by
  sorry

/-- Real.sinIntTailZero enumeration. -/
theorem Real.sinIntTailZero_enumeration  :
    StrictMono Real.sinIntTailZero ∧ ∀ x : ℝ, 0 < x → ((fun x => Real.sinInt x-π/2) x=0 ↔ ∃ k, Real.sinIntTailZero k=x) := by
  sorry

/-- Shared all-order zero expansions and signed next-term bounds. -/
@[dlmf 6.13.E2]
theorem Real.trigonometric_integral_zero_asymptotics  :
    ∃ c : ℕ → ℝ, (∀ n < 5, c n=([1,1,-16/3,1673/15,-507746/105] : List ℝ)[n]!) ∧ (∀ aux : Bool, let α := fun k : ℕ => ((k : ℝ)+(if aux then 1/2 else 0))*π; let zero := if aux then Real.sinIntTailZero else Real.cosIntZero; HasAsymptoticExpansion atTop (fun n k => (α k)^(-(2*n : ℤ)+1)) c zero ∧ ∀ k N : ℕ, 1 ≤ k → 1 ≤ N → |zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1)| ≤ |c N*(α k)^(-(2*N : ℤ)+1)| ∧ 0 ≤ (zero k-∑ n ∈ Finset.range N, c n*(α k)^(-(2*n : ℤ)+1))*(c N*(α k)^(-(2*N : ℤ)+1))) := by
  sorry

/-- expIntE1 laplace. -/
@[dlmf 6.14.E1]
theorem expIntE1_laplace {a : ℂ} (ha : -1 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*genExpIntE 1 t) = if a=0 then 1 else log (1+a)/a := by
  sorry

/-- cosInt laplace. -/
@[dlmf 6.14.E2]
theorem cosInt_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*cosInt t) = -log (1+a^2)/(2*a) := by
  sorry

/-- sinIntTail laplace. -/
@[dlmf 6.14.E3]
theorem sinIntTail_laplace {a : ℂ} (ha : 0 < a.re) :
    (∫ t : ℝ in Ioi 0, exp (-a*t)*sinIntTail t) = -arctan a/a := by
  sorry

/-- expIntE1 squared integral. -/
@[dlmf 6.14.E4]
theorem expIntE1_squared_integral  :
    (∫ t : ℝ in Ioi 0, genExpIntE 1 t^2) = 2*Real.log 2 := by
  sorry

/-- cosInt fourier integral. -/
@[dlmf 6.14.E5]
theorem cosInt_fourier_integral  :
    HasIntegralAtTop (fun t : ℝ => cos t*cosInt t) 0 (-π/4) ∧ HasIntegralAtTop (fun t : ℝ => sin t*sinIntTail t) 0 (-π/4) := by
  sorry

/-- trigIntegral squared integrals. -/
@[dlmf 6.14.E6]
theorem trigIntegral_squared_integrals  :
    (∫ t : ℝ in Ioi 0, cosInt t^2) = π/2 ∧ (∫ t : ℝ in Ioi 0, sinIntTail t^2) = π/2 := by
  sorry

/-- trigIntegral product integral. -/
@[dlmf 6.14.E7]
theorem trigIntegral_product_integral  :
    (∫ t : ℝ in Ioi 0, cosInt t*sinIntTail t) = Real.log 2 := by
  sorry

/-- trigIntegral hasSum 1. -/
@[dlmf 6.15.E1]
theorem trigIntegral_hasSum_1  :
    HasSum (fun n : ℕ => cosInt (π*(n+1 : ℂ))) ((Real.log 2-Real.eulerMascheroniConstant)/2) := by
  sorry

/-- trigIntegral hasSum 2. -/
@[dlmf 6.15.E2]
theorem trigIntegral_hasSum_2  :
    HasSum (fun n : ℕ => sinIntTail (π*(n+1 : ℂ))/(n+1 : ℂ)) (π/2*(Real.log π-1)) := by
  sorry

/-- trigIntegral hasSum 3. -/
@[dlmf 6.15.E3]
theorem trigIntegral_hasSum_3  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*cosInt (2*π*(n+1 : ℂ))) (1-Real.log 2-Real.eulerMascheroniConstant/2) := by
  sorry

/-- trigIntegral hasSum 4. -/
@[dlmf 6.15.E4]
theorem trigIntegral_hasSum_4  :
    HasSum (fun n : ℕ => (-1 : ℂ)^(n+1)*sinIntTail (2*π*(n+1 : ℂ))/(n+1 : ℂ)) (π*(3/2*Real.log 2-1)) := by
  sorry

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonA (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^1*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonB (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/((t : ℂ)^2+1) * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Acton auxiliary integral. -/
@[dlmf 6.18.E1]
def expIntActonC (n : ℕ) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, (t : ℂ)^0*exp (-z*t)/1 * ((t : ℂ)^2/(1+(t : ℂ)^2))^n

/-- Initial normalization in DLMF §6.18(ii). -/
theorem expIntActon_initial {z : ℂ} (hz : 0 < z.re) :
    expIntActonB 0 z=expIntAuxF z ∧ expIntActonA 0 z=expIntAuxG z ∧ expIntActonC 0 z=1/z := by
  sorry

/-- expIntActon recurrence. -/
@[dlmf 6.18.E2]
theorem expIntActon_recurrence {z : ℂ} (hz : 0 < z.re) {n : ℕ} (hn : 1 ≤ n) :
    expIntActonA (n-1) z=expIntActonA n z+z/(2*n)*expIntActonC n z ∧ expIntActonB (n-1) z=(2*n*expIntActonB n z+z*expIntActonA (n-1) z)/(2*n-1) ∧ expIntActonC (n-1) z=expIntActonC n z+expIntActonB (n-1) z := by
  sorry

end AAR.Confluent
