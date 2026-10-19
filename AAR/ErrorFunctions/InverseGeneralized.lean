/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.BoundsAsymptotics

/-!
# Generalized and inverse error functions, DLMF §§7.16–7.17

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Generalized error integral of DLMF §7.16. -/
def Real.generalizedErrorIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-t^p)

/-- Generalized unscaled Dawson integral of DLMF §7.16. -/
def Real.generalizedDawsonIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (t^p)

/-- Change of variable to incomplete Gamma in DLMF §7.16. -/
theorem Real.generalizedErrorIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedErrorIntegral p x : ℂ)=lowerIncGamma (1/p) ((x^p : ℝ) : ℂ)/p := by
  sorry

/-- The negative-argument Gamma formula retains the compensating branch factor. -/
theorem Real.generalizedDawsonIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedDawsonIntegral p x : ℂ)=exp (-π*I/p)/p*lowerIncGamma (1/p) (-(x^p : ℝ)) := by
  sorry

/-- Inverse erf on (-1,1), reusing TauCeti; zero outside that interval. -/
@[dlmf 7.17.E1]
def Real.invErf (x : ℝ) : ℝ :=
  _root_.Real.erfInv x

/-- Inverse erfc on (0,2), with totalization inherited from invErf. -/
@[dlmf 7.17.E1]
def Real.invErfc (x : ℝ) : ℝ :=
  Real.invErf (1-x)

/-- Inverse identity; `Real.erf_erfInv` from TauCeti supplies the real theorem. -/
theorem Real.invErf_spec {x : ℝ} (hx : |x| < 1) :
    (erf (Real.invErf x)).re=x := by
  rw [erf_ofReal]
  simpa [Real.invErf] using _root_.Real.erf_erfInv (abs_lt.mp hx)

/-- Inverse complementary error function identity. -/
theorem Real.invErfc_spec {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    (erfc (Real.invErfc x)).re=x := by
  have h : |1-x| < 1 := abs_lt.mpr (by constructor <;> linarith)
  have he := Real.invErf_spec h
  change (erfc (Real.invErf (1-x))).re=x
  change (1-erf (Real.invErf (1-x))).re=x
  simp only [Complex.sub_re, Complex.one_re, he]
  ring

/-- Coefficients of the inverse-erf series from the unnumbered recurrence after 7.17.2. -/
def invErfSeriesCoeff : ℕ → ℝ
  | 0 => 1
  | m+1 => (∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*
      invErfSeriesCoeff (m-n)*invErfSeriesCoeff (m-(m-n)))/(2*m+3)
termination_by m => m

/-- invErfSeriesCoeff initial. -/
@[dlmf 7.17.E2]
theorem invErfSeriesCoeff_initial  :
    ∀ n < 4, invErfSeriesCoeff n=([1,1/3,7/30,127/630] : List ℝ)[n]! := by
  intro n hn
  interval_cases n <;> norm_num [invErfSeriesCoeff, Finset.sum_range_succ]

/-- hasSum invErf. -/
@[dlmf 7.17.E2]
theorem hasSum_invErf {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => invErfSeriesCoeff m*(Real.sqrt π*x/2)^(2*m+1)) (Real.invErf x) := by
  sorry

/-- The unnumbered inverse-erf coefficient recurrence. -/
theorem invErfSeriesCoeff_recurrence (m : ℕ) :
    invErfSeriesCoeff (m+1)=(∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*invErfSeriesCoeff n*invErfSeriesCoeff (m-n))/(2*m+3) := by
  sorry

/-- Small-argument inverse-erfc variable u. -/
@[dlmf 7.17.E5]
def invErfcAsymptoticU (x : ℝ) : ℝ :=
  -2/Real.log (π*x^2*Real.log (1/x))

/-- Small-argument inverse-erfc logarithmic variable v. -/
@[dlmf 7.17.E6]
def invErfcAsymptoticV (x : ℝ) : ℝ :=
  Real.log (Real.log (1/x))-2+Real.log π

/-- All-order expansion with polynomial logarithmic coefficients. -/
@[dlmf 7.17.E3, dlmf 7.17.E4]
theorem invErfc_asymptotic  :
    ∃ c : ℕ → Polynomial ℝ, (∀ v : ℝ, (c 0).eval v=1 ∧ (c 1).eval v=0 ∧ (c 2).eval v=v/8 ∧ (c 3).eval v = -(v^2+6*v-6)/32 ∧ (c 4).eval v=(4*v^3+27*v^2+108*v-300)/384) ∧ ∀ N : ℕ, IsBigO (𝓝[>] (0 : ℝ)) (fun x => Real.invErfc x-∑ n ∈ Finset.range N, (c n).eval (invErfcAsymptoticV x)*(invErfcAsymptoticU x)^((n : ℝ)-1/2)) (fun x => (invErfcAsymptoticU x)^((N : ℝ)-1/2)*(1+|invErfcAsymptoticV x|)^N) := by
  sorry

end AAR.Confluent
