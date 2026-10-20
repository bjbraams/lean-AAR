/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.AngerWeber
public import AAR.Airy.Scorer

/-!
# Struve and Anger–Weber asymptotics

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel AAR.Airy

/-- struveAsymptoticTerm. -/
def struveAsymptoticTerm (ν z : ℂ) (k : ℕ) : ℂ :=
  Gamma (k+1/2)/Gamma (ν+1/2-k)*(z/2)^(ν-2*k-1)/π

/-- struveK asymptotic. -/
@[dlmf 11.6.E1]
theorem struveK_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => struveK ν z-∑ k ∈ Finset.range N, struveAsymptoticTerm ν z k) =O[sector (π-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  sorry

/-- struveM asymptotic. -/
@[dlmf 11.6.E2]
theorem struveM_asymptotic (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => struveM ν z-∑ k ∈ Finset.range N, (-1)^(k+1)*struveAsymptoticTerm ν z k) =O[sector (π/2-δ)] (fun z : ℂ => z^(ν-2*N-1)) := by
  sorry

/-- struveK primitive asymptotic. -/
@[dlmf 11.6.E3]
theorem struveK_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveK 0) z - 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; (-1)^(k+1)*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

/-- struveM primitive asymptotic. -/
@[dlmf 11.6.E4]
theorem struveM_primitive_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun z : ℂ => AAR.DLMF.primitive (struveM 0) z + 2/π*(log (2*z)+Real.eulerMascheroniConstant)-2/π*∑ j ∈ Finset.range N, let k:=j+1; 1*((2*k).factorial:ℂ)*(2*k-1).factorial/((k.factorial:ℂ)^2*(2*z)^(2*k))) =O[sector (π/2-δ)] (fun z : ℂ => z^(-(2*(N+1):ℤ))) := by
  sorry

/-- struveH large order. -/
@[dlmf 11.6.E5]
theorem struveH_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveH ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  sorry

/-- struveL large order. -/
@[dlmf 11.6.E5]
theorem struveL_large_order {z : ℂ} (hz : z ∈ slitPlane) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => struveL ν z) ~[sector (π-δ)] (fun ν => z/(π*ν*Real.sqrt 2)*exp (ν*(1+log z-log 2-log ν))) := by
  sorry

/-- Finite polynomial formula for the saddle-endpoint coefficients. -/
def struveScaledCoeff (lam : ℂ) (k : ℕ) : ℂ :=
  (∑ j ∈ Finset.range (k+1), if k ≤ 2*j then
    ((2*j).factorial:ℂ)/(j.factorial:ℂ) *
      (∏ r ∈ Finset.range j, (Polynomial.X-Polynomial.C (1/2+r:ℂ))).coeff (2*j-k) /
      lam^(2*j) else 0) / (k.factorial:ℂ)

/-- struveK scaled asymptotic. -/
@[dlmf 11.6.E6]
theorem struveK_scaled_asymptotic {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveK ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveM scaled asymptotic. -/
@[dlmf 11.6.E7]
theorem struveM_scaled_asymptotic {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => -Real.sqrt π*Gamma (ν+1/2)*exp ((1-ν)*(log (lam*ν)-log 2))*struveM ν (lam*ν)-∑ k ∈ Finset.range N, (k.factorial:ℂ)*struveScaledCoeff (I*lam) k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- struveScaledCoeff initial. -/
@[dlmf 11.6.E8]
theorem struveScaledCoeff_initial (lam : ℂ) (hlam : lam ≠ 0) :
    struveScaledCoeff lam 0=1 ∧ struveScaledCoeff lam 1=2/(lam:ℂ)^2 ∧ struveScaledCoeff lam 2=6/(lam:ℂ)^4-1/(2*(lam:ℂ)^2) ∧ struveScaledCoeff lam 3=20/(lam:ℂ)^6-4/(lam:ℂ)^4 ∧ struveScaledCoeff lam 4=70/(lam:ℂ)^8-45/(2*(lam:ℂ)^6)+3/(8*(lam:ℂ)^4) := by
  simp only [struveScaledCoeff, Finset.sum_range_succ, Finset.prod_range_succ,
    Finset.sum_range_zero, Finset.prod_range_zero, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [Nat.factorial, Polynomial.coeff_mul_X_sub_C, Polynomial.coeff_one,
      Polynomial.mul_coeff_zero, Polynomial.coeff_X] <;>
    field_simp <;> ring

/-- struveL scaled equiv. -/
@[dlmf 11.6.E9]
theorem struveL_scaled_equiv {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => struveL ν (lam*ν)) ~[sector (π/2-δ)] (fun ν => besselI ν (lam*ν)) := by
  sorry

/-- First omitted term bounds the real positive-argument remainder. -/
theorem struveK_remainder_sign {ν x : ℝ} (hx : 0 < x) (m : ℕ) (hm : ν ≤ m+1/2) :
    let R := struveK ν x-∑ k ∈ Finset.range m, struveAsymptoticTerm ν x k; R.im=0 ∧ R.re*(struveAsymptoticTerm ν x m).re ≥ 0 ∧ ‖R‖ ≤ ‖struveAsymptoticTerm ν x m‖ := by
  sorry

/-- angerF. -/
@[dlmf 11.11.E1]
def angerF (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+1)^2)

/-- angerG. -/
@[dlmf 11.11.E1]
def angerG (ν : ℂ) (k : ℕ) : ℂ :=
  ∏ j ∈ Finset.range k, (ν^2-(2*j+2)^2)

/-- angerFG poch. -/
@[dlmf 11.11.E1]
theorem angerFG_poch (ν : ℂ) (k : ℕ) :
    angerF ν k = (-4)^k*poch (1/2-ν/2) k*poch (1/2+ν/2) k ∧ angerG ν k = (-4)^k*poch (1-ν/2) k*poch (1+ν/2) k := by
  induction k with
  | zero => simp [angerF, angerG, poch_zero]
  | succ k ih =>
    rcases ih with ⟨ihF, ihG⟩
    have hF : angerF ν (k+1)=angerF ν k*(ν^2-(2*k+1)^2) := by
      simp [angerF, Finset.prod_range_succ]
    have hG : angerG ν (k+1)=angerG ν k*(ν^2-(2*k+2)^2) := by
      simp [angerG, Finset.prod_range_succ]
    rw [hF,hG,ihF,ihG,poch_succ,poch_succ,poch_succ,poch_succ,pow_succ]
    push_cast
    constructor <;> ring

/-- angerJ large argument. -/
@[dlmf 11.11.E2]
theorem angerJ_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerJ ν z-besselJ ν z-(∑ k ∈ Finset.range N, sin (π*ν)/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- weberE large argument. -/
@[dlmf 11.11.E3]
theorem weberE_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => weberE ν z+besselY ν z-(∑ k ∈ Finset.range N, -(1+cos (π*ν))/π*angerF ν k/z^(2*k+1)-ν*(1-cos (π*ν))/π*angerG ν k/z^(2*k+2))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA large argument. -/
@[dlmf 11.11.E4]
theorem angerA_large_argument (ν : ℂ) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun z : ℂ => angerA ν z-(∑ k ∈ Finset.range N, 1/π*(angerF ν k/z^(2*k+1)-ν*angerG ν k/z^(2*k+2)))) =O[sector (π-δ)] (fun z : ℂ => z^(-(2*N+1:ℤ))) := by
  sorry

/-- Large orders separated from all integers. -/
def nonintegerOrderSector (ε : ℝ) : Filter ℂ :=
  sector π ⊓ 𝓟 {ν : ℂ | ∀ n : ℤ, ε ≤ ‖ν-n‖}

/-- angerJ large order. -/
@[dlmf 11.11.E5]
theorem angerJ_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/sin (π*ν)*angerJ ν z-1+ν*z/(ν^2-1)) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- weberE large order. -/
@[dlmf 11.11.E6]
theorem weberE_large_order (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (fun ν : ℂ => π*ν/2*weberE ν z-(sin (π*ν/2))^2-ν*z/(ν^2-1)*(cos (π*ν/2))^2) =O[nonintegerOrderSector ε] (fun ν : ℂ => ν^(-2:ℤ)) := by
  sorry

/-- One integration by parts against `e^{ωθ}` on `[0, π]`. -/
theorem integral_exp_mul_ibp {ω : ℂ} (hω : ω ≠ 0) {H H' : ℝ → ℂ}
    (hd : ∀ θ, HasDerivAt H (H' θ) θ) (hc : Continuous H') :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) =
      (exp (ω*π) * H π - H 0)/ω - (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
  have hv : ∀ θ ∈ uIcc (0:ℝ) π, HasDerivAt (fun θ : ℝ => exp (ω*θ)/ω) (exp (ω*θ)) θ := by
    intro θ _
    have := (((hasDerivAt_id (θ:ℝ)).ofReal_comp.const_mul ω).cexp).div_const ω
    refine this.congr_deriv ?_
    simp only [id, ofReal_one, mul_one]; field_simp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (fun θ _ => hd θ) hv
    (hc.intervalIntegrable _ _) ((by fun_prop : Continuous fun θ : ℝ => exp (ω*θ)).intervalIntegrable _ _)
  have e1 : (∫ θ : ℝ in 0..π, exp (ω*θ) * H θ) = ∫ θ : ℝ in 0..π, H θ * exp (ω*θ) :=
    intervalIntegral.integral_congr fun θ _ => by ring
  have e2 : (∫ θ : ℝ in 0..π, H' θ * (exp (ω*θ)/ω)) =
      (1/ω) * ∫ θ : ℝ in 0..π, exp (ω*θ) * H' θ := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [e1, hibp, e2]
  simp only [ofReal_zero, mul_zero, Complex.exp_zero]
  ring

/-- `|∫₀^π e^{itθ} k| ≤ ∫₀^π |k|`. -/
theorem norm_integral_exp_I_mul_le (t : ℝ) (k : ℝ → ℂ) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ ∫ θ : ℝ in 0..π, ‖k θ‖ := by
  refine (intervalIntegral.norm_integral_le_integral_norm Real.pi_pos.le).trans ?_
  refine le_of_eq (intervalIntegral.integral_congr fun θ _ => ?_)
  simp only [norm_mul]
  rw [show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Derivatives of `θ ↦ exp (a sin θ)`. -/
theorem hasDerivAt_exp_mul_sin (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => exp (a*Real.sin θ)) (a*Real.cos θ*exp (a*Real.sin θ)) θ := by
  have := ((Real.hasDerivAt_sin θ).ofReal_comp.const_mul a).cexp
  convert this using 1; ring

theorem hasDerivAt_exp_mul_sin_one (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => a*Real.cos θ*exp (a*Real.sin θ))
      ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) θ := by
  have h1 := ((Real.hasDerivAt_cos θ).ofReal_comp.const_mul a).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1; push_cast; ring

theorem hasDerivAt_exp_mul_sin_two (a : ℂ) (θ : ℝ) :
    HasDerivAt (fun θ : ℝ => (a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ))
      ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)) θ := by
  have hc := (Real.hasDerivAt_cos θ).ofReal_comp
  have hs := (Real.hasDerivAt_sin θ).ofReal_comp
  have h1 := (((hc.pow 2).const_mul (a^2)).sub (hs.const_mul a)).mul (hasDerivAt_exp_mul_sin a θ)
  convert h1 using 1
  simp only [Pi.sub_apply, Pi.pow_apply]; push_cast; ring

theorem integral_exp_mul_exp_sin_odd {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = -1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = -2/ω + (1/ω^2) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

theorem integral_exp_mul_exp_sin_even {ω : ℂ} (hω : ω ≠ 0) (he : exp (ω*π) = 1) (a : ℂ) :
    (∫ θ : ℝ in 0..π, exp (ω*θ) * exp (a*Real.sin θ)) = 2*a/ω^2 - (1/ω^3) *
      ∫ θ : ℝ in 0..π, exp (ω*θ) * ((a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ -
        a*Real.cos θ)*exp (a*Real.sin θ)) := by
  rw [integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_one a) (by fun_prop),
    integral_exp_mul_ibp hω (hasDerivAt_exp_mul_sin_two a) (by fun_prop), he]
  simp only [Real.sin_pi, Real.cos_pi, Real.sin_zero, Real.cos_zero, ofReal_zero, ofReal_one,
    ofReal_neg, mul_zero, Complex.exp_zero, mul_one]
  field_simp
  ring

/-- The Weber function as a combination of two exponential integrals. -/
theorem weberE_eq_exp_integrals (ν z : ℂ) :
    weberE ν z = 1/π * (I/2 * ((∫ θ : ℝ in 0..π, exp ((-I*ν)*θ) * exp ((I*z)*Real.sin θ)) -
      ∫ θ : ℝ in 0..π, exp ((I*ν)*θ) * exp ((-I*z)*Real.sin θ))) := by
  unfold weberE
  congr 1
  rw [← intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [Complex.sin, ← Complex.exp_add, ← Complex.exp_add]
  ring_nf

/-- A uniform bound for an integral against `e^{itθ}`. -/
theorem norm_integral_exp_I_mul_le_const (t : ℝ) {k : ℝ → ℂ} {C : ℝ}
    (hk : ∀ θ, ‖k θ‖ ≤ C) :
    ‖∫ θ : ℝ in 0..π, exp ((I*t)*θ) * k θ‖ ≤ C * π := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := π)
    (f := fun θ : ℝ => exp ((I*t)*θ) * k θ) (C := C) (fun θ _ => by
      rw [norm_mul, show (I*t)*(θ:ℂ) = ((t*θ:ℝ):ℂ)*I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, one_mul]; exact hk θ)
  rwa [sub_zero, abs_of_pos Real.pi_pos] at this

theorem exp_I_mul_odd_mul_pi (n : ℤ) : exp ((I*(2*n+1:ℂ))*π) = -1 := by
  rw [show (I*(2*n+1:ℂ))*π = n*(2*π*I) + π*I by ring, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, Complex.exp_pi_mul_I, one_mul]

theorem exp_I_mul_even_mul_pi (n : ℤ) : exp ((I*(2*n:ℂ))*π) = 1 := by
  rw [show (I*(2*n:ℂ))*π = n*(2*π*I) by ring, Complex.exp_int_mul_two_pi_mul_I]

theorem exp_neg_I_mul_odd_mul_pi (n : ℤ) : exp ((-I*(2*n+1:ℂ))*π) = -1 := by
  have := exp_I_mul_odd_mul_pi (-n-1)
  rw [← this]; congr 1; push_cast; ring

theorem exp_neg_I_mul_even_mul_pi (n : ℤ) : exp ((-I*(2*n:ℂ))*π) = 1 := by
  have := exp_I_mul_even_mul_pi (-n)
  rw [← this]; congr 1; push_cast; ring

/-- `E_{2n+1}(z) = 2/((2n+1)π) + O((2n+1)^{-2})`, uniformly in `n`. -/
theorem weberE_odd_bound (z : ℂ) : ∃ M : ℝ, ∀ n : ℤ,
    ‖weberE (2*n+1) z - 2/((2*n+1:ℂ)*π)‖ ≤ M / ((2*n+1:ℝ))^2 := by
  set K : ℝ := (‖z‖^2 + ‖z‖) * Real.exp ‖z‖
  have hH2 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^2*(Real.cos θ)^2 - a*Real.sin θ)*exp (a*Real.sin θ)‖ ≤ K := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have h1 : ‖a^2*(Real.cos θ:ℂ)^2 - a*Real.sin θ‖ ≤ ‖z‖^2 + ‖z‖ := by
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha]
      have : |Real.cos θ|^2 ≤ 1 := by nlinarith [abs_nonneg (Real.cos θ)]
      have hz := norm_nonneg z
      nlinarith [abs_nonneg (Real.sin θ)]
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
  refine ⟨K * π / π, fun n => ?_⟩
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n+1:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_odd hω1 (exp_neg_I_mul_odd_mul_pi n),
    integral_exp_mul_exp_sin_odd hω2 (exp_I_mul_odd_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n+1:ℂ))*θ) *
    (((I*z)^2*(Real.cos θ)^2 - (I*z)*Real.sin θ)*exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n+1:ℂ))*θ) *
    (((-I*z)^2*(Real.cos θ)^2 - (-I*z)*Real.sin θ)*exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH2 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ K * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH2 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((-2/(-I*(2*n+1:ℂ)) + 1/(-I*(2*n+1:ℂ))^2 * R1) -
      (-2/(I*(2*n+1:ℂ)) + 1/(I*(2*n+1:ℂ))^2 * R2))) - 2/((2*n+1:ℂ)*π) =
      (I/(2*π)) * (R2 - R1) / (t:ℂ)^2 := by
    rw [ht]
    field_simp
    ring_nf
    rw [I_sq]
    ring_nf
  rw [key, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hI : ‖I/(2*(π:ℂ))‖ = 1/(2*π) := by
    rw [norm_div, Complex.norm_I, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
  rw [hI]
  have hsum : ‖R2 - R1‖ ≤ 2*(K*π) := (norm_sub_le _ _).trans (by linarith)
  have ht2 : 0 < t^2 := by positivity
  rw [div_le_div_iff_of_pos_right ht2]
  calc 1/(2*π) * ‖R2 - R1‖ ≤ 1/(2*π) * (2*(K*π)) := by gcongr
    _ = K * π / π := by field_simp

/-- `|2n+1| ≥ |n|` and `|2n| ≥ |n|` in real form. -/
theorem abs_two_mul_add_ge (n : ℤ) (e : ℝ) (he : e = 0 ∨ e = 1) :
    (|n| : ℝ) ≤ |2*(n:ℝ)+e| ∨ n = 0 := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inr h
  left
  have h1 : (1:ℝ) ≤ |(n:ℝ)| := by
    have : (1:ℤ) ≤ |n| := Int.one_le_abs h
    exact_mod_cast this
  rcases he with rfl | rfl
  · rw [add_zero, abs_mul]; norm_num; linarith [abs_nonneg (n:ℝ)]
  · have := abs_sub_abs_le_abs_sub (2*(n:ℝ)) (-1)
    rw [abs_mul, abs_two, abs_neg, abs_one, sub_neg_eq_add] at this
    linarith

theorem norm_sub_sub_le_add_add (A B C : ℂ) : ‖A - B - C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ :=
  (norm_sub_le _ _).trans (by linarith [norm_sub_le A B])

/-- `E_{2n}(z) = 2z/(π(2n)²) + O(|z| (2n)^{-3})`, uniformly in `n ≠ 0`. -/
theorem weberE_even_bound (z : ℂ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℤ, n ≠ 0 →
    ‖weberE (2*n) z - 2*z/(π*(2*n:ℂ)^2)‖ ≤ ‖z‖ * K / |(2*n:ℝ)|^3 := by
  set K0 : ℝ := (‖z‖^2 + 3*‖z‖ + 1) * Real.exp ‖z‖
  have hK0 : 0 ≤ K0 := by positivity
  have hH3 : ∀ a : ℂ, ‖a‖ = ‖z‖ → ∀ θ : ℝ,
      ‖(a^3*(Real.cos θ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ)*exp (a*Real.sin θ)‖ ≤
        ‖z‖ * K0 := by
    intro a ha θ
    rw [norm_mul, Complex.norm_exp]
    have hc := Real.abs_cos_le_one θ
    have hs := Real.abs_sin_le_one θ
    have hz := norm_nonneg z
    have h1 : ‖a^3*(Real.cos θ:ℂ)^3 - 3*a^2*Real.sin θ*Real.cos θ - a*Real.cos θ‖ ≤
        ‖z‖^3 + 3*‖z‖^2 + ‖z‖ := by
      refine (norm_sub_sub_le_add_add _ _ _).trans ?_
      simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ha, Complex.norm_ofNat]
      have hc3 : |Real.cos θ|^3 ≤ 1 := pow_le_one₀ (abs_nonneg _) hc
      have hsc : |Real.sin θ| * |Real.cos θ| ≤ 1 := by
        nlinarith [abs_nonneg (Real.sin θ), abs_nonneg (Real.cos θ)]
      have e1 : ‖z‖^3 * |Real.cos θ|^3 ≤ ‖z‖^3 := by
        calc _ ≤ ‖z‖^3 * 1 := by gcongr
          _ = _ := mul_one _
      have e2 : 3 * ‖z‖^2 * |Real.sin θ| * |Real.cos θ| ≤ 3*‖z‖^2 := by
        calc _ = 3 * ‖z‖^2 * (|Real.sin θ| * |Real.cos θ|) := by ring
          _ ≤ 3 * ‖z‖^2 * 1 := by gcongr
          _ = _ := mul_one _
      have e3 : ‖z‖ * |Real.cos θ| ≤ ‖z‖ := by
        calc _ ≤ ‖z‖ * 1 := by gcongr
          _ = _ := mul_one _
      linarith
    have h2 : Real.exp (a*Real.sin θ).re ≤ Real.exp ‖z‖ := by
      apply Real.exp_le_exp.2
      calc (a*Real.sin θ).re ≤ ‖a*Real.sin θ‖ := re_le_norm _
        _ = ‖a‖ * |Real.sin θ| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖z‖ := by rw [ha]; nlinarith [norm_nonneg z, abs_nonneg (Real.sin θ)]
    calc _ ≤ (‖z‖^3 + 3*‖z‖^2 + ‖z‖) * Real.exp ‖z‖ :=
          mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
      _ = ‖z‖ * K0 := by simp only [K0]; ring
  refine ⟨K0, hK0, fun n hn => ?_⟩
  set t : ℝ := 2*n
  have ht : (2*n:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 ht0
  have hω1 : -I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  have hω2 : I*(2*n:ℂ) ≠ 0 := by rw [ht]; simp [htc]
  rw [weberE_eq_exp_integrals,
    integral_exp_mul_exp_sin_even hω1 (exp_neg_I_mul_even_mul_pi n),
    integral_exp_mul_exp_sin_even hω2 (exp_I_mul_even_mul_pi n)]
  set R1 := ∫ θ : ℝ in 0..π, exp ((-I*(2*n:ℂ))*θ) *
    (((I*z)^3*(Real.cos θ)^3 - 3*(I*z)^2*Real.sin θ*Real.cos θ - (I*z)*Real.cos θ)*
      exp ((I*z)*Real.sin θ))
  set R2 := ∫ θ : ℝ in 0..π, exp ((I*(2*n:ℂ))*θ) *
    (((-I*z)^3*(Real.cos θ)^3 - 3*(-I*z)^2*Real.sin θ*Real.cos θ - (-I*z)*Real.cos θ)*
      exp ((-I*z)*Real.sin θ))
  have hR1 : ‖R1‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const (-t) (hH3 (I*z) (by simp))
    simp only [R1]; convert h using 4; push_cast [ht]; ring_nf
  have hR2 : ‖R2‖ ≤ ‖z‖ * K0 * π := by
    have h := norm_integral_exp_I_mul_le_const t (hH3 (-I*z) (by simp))
    simp only [R2]; convert h using 4; push_cast [ht]; ring_nf
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have key : 1/π * (I/2 * ((2*(I*z)/(-I*(2*n:ℂ))^2 - 1/(-I*(2*n:ℂ))^3 * R1) -
      (2*(-I*z)/(I*(2*n:ℂ))^2 - 1/(I*(2*n:ℂ))^3 * R2))) - 2*z/(π*(2*n:ℂ)^2) =
      -(R1 + R2) / (2*π*(t:ℂ)^3) := by
    rw [ht]
    have e1 : (-I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e2 : (I*(t:ℂ))^2 = -(t:ℂ)^2 := by linear_combination (t:ℂ)^2 * I_sq
    have e3 : (-I*(t:ℂ))^3 = I*(t:ℂ)^3 := by linear_combination (-I*(t:ℂ)^3) * I_sq
    have e4 : (I*(t:ℂ))^3 = -(I*(t:ℂ)^3) := by linear_combination (I*(t:ℂ)^3) * I_sq
    rw [e1, e2, e3, e4]
    field_simp
    ring_nf
    simp only [I_sq]
    ring_nf
  rw [key]
  simp only [norm_div, norm_neg, norm_mul, norm_pow, Complex.norm_real, Complex.norm_ofNat,
    Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsum : ‖R1 + R2‖ ≤ 2*(‖z‖ * K0 * π) := (norm_add_le _ _).trans (by linarith)
  have ht3 : 0 < |t|^3 := by positivity
  rw [div_le_div_iff₀ (by positivity) ht3]
  nlinarith [Real.pi_pos]

/-- weberE large integer 0. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_0 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+0) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2*z/((4*(n:ℂ)^2-1)*π)) := by
  obtain ⟨K, hK, hb⟩ := weberE_even_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (2/c + K*π/c + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  have h2c : 0 ≤ 2/c := by positivity
  have hKc : 0 ≤ K*π/c := by positivity
  have hn1 : (1:ℝ) ≤ |(n:ℝ)| := by linarith
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn1; linarith
  set t : ℝ := 2*n
  set x : ℝ := |t|
  have hx : x = 2*|(n:ℝ)| := by simp only [x, t, abs_mul, abs_two]
  have hx2 : 2 ≤ x := by linarith
  have hxN : (N:ℝ) ≤ x := by linarith
  have hxc : 2/c ≤ x := by linarith
  have hxK : K*π/c ≤ x := by linarith
  have ht : (2*n:ℂ) = t := by simp [t]
  have htx : t^2 = x^2 := (sq_abs t).symm
  have hx0 : 0 < x := by linarith
  have hx21 : 0 < x^2 - 1 := by nlinarith
  rw [Pi.sub_apply, add_zero]
  set u := weberE (2*n) z
  set w : ℂ := 2*z/(π*(2*n:ℂ)^2)
  set v : ℂ := 2*z/((4*(n:ℂ)^2-1)*π)
  have hπ : (π:ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have htc : (t:ℂ) ≠ 0 := ofReal_ne_zero.2 fun h => by
    have : x = 0 := by simp only [x, h, abs_zero]
    linarith
  have hn4 : (4*(n:ℂ)^2-1) = ((x^2-1:ℝ):ℂ) := by
    rw [← htx]; push_cast [t]; ring
  have hn4ne : (4*(n:ℂ)^2-1) ≠ 0 := by rw [hn4]; exact ofReal_ne_zero.2 hx21.ne'
  have hwv : w - v = -(2*z) / (π*(t:ℂ)^2*((x^2-1:ℝ):ℂ)) := by
    simp only [w, v]
    rw [ht, hn4]
    have : ((x^2-1:ℝ):ℂ) = (t:ℂ)^2 - 1 := by push_cast [← htx]; ring
    have h1 : ((x^2-1:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.2 hx21.ne'
    rw [this] at h1 ⊢
    field_simp
    ring
  have hnv : ‖v‖ = 2*‖z‖/((x^2-1)*π) := by
    simp only [v]
    rw [hn4, norm_div, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le]
  have hnwv : ‖w - v‖ = 2*‖z‖/(π*x^2*(x^2-1)) := by
    rw [hwv, norm_div, norm_neg, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat,
      Complex.norm_real, Complex.norm_real, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg hx21.le, Real.norm_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  have huw : ‖u - w‖ ≤ ‖z‖ * K / x^3 := hb n hn0
  have htri : ‖u - v‖ ≤ ‖u - w‖ + ‖w - v‖ := by
    have := norm_add_le (u - w) (w - v); rwa [sub_add_sub_cancel] at this
  rw [hnv]
  refine htri.trans ?_
  rw [hnwv]
  have hzn := norm_nonneg z
  have e1 : K / x^3 ≤ c/((x^2-1)*π) := by
    have ha : K / x^3 ≤ c/(x^2*π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : K*π ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxK
      nlinarith [sq_nonneg x]
    refine ha.trans (div_le_div_of_nonneg_left hc.le (by positivity) ?_)
    nlinarith [Real.pi_pos]
  have e2 : 2/(π*x^2*(x^2-1)) ≤ c/((x^2-1)*π) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : 2 ≤ c*x := by rwa [div_le_iff₀ hc, mul_comm x] at hxc
    have : 2 ≤ c*x^2 := by nlinarith
    have hp : 0 < (x^2-1)*π := by positivity
    nlinarith
  refine (add_le_add huw le_rfl).trans ?_
  calc ‖z‖ * K / x^3 + 2*‖z‖/(π*x^2*(x^2-1)) = ‖z‖ * (K/x^3 + 2/(π*x^2*(x^2-1))) := by ring
    _ ≤ ‖z‖ * (c/((x^2-1)*π) + c/((x^2-1)*π)) := by gcongr
    _ = c * (2*‖z‖/((x^2-1)*π)) := by ring

/-- weberE large integer 1. -/
@[dlmf 11.11.E7]
theorem weberE_large_integer_1 (z : ℂ) :
    (fun n : ℤ => weberE (2*n+1) z) ~[comap (fun n : ℤ => |n|) atTop] (fun n => 2/((2*n+1:ℂ)*π)) := by
  obtain ⟨M, hM⟩ := weberE_odd_bound z
  unfold IsEquivalent
  rw [isLittleO_iff]
  intro c hc
  obtain ⟨N, hN⟩ := exists_nat_ge (M * π / (2*c) + 1)
  have hev : ∀ᶠ n : ℤ in comap (fun n : ℤ => |n|) atTop, (N:ℤ) ≤ |n| :=
    tendsto_comap.eventually (eventually_ge_atTop (N:ℤ))
  filter_upwards [hev] with n hn
  have hnR : (N:ℝ) ≤ |(n:ℝ)| := by
    have : ((N:ℤ):ℝ) ≤ ((|n|:ℤ):ℝ) := by exact_mod_cast hn
    simpa [Int.cast_abs] using this
  set t : ℝ := 2*n+1
  have ht : (2*n+1:ℂ) = t := by simp [t]
  have ht0 : t ≠ 0 := by
    intro h
    have h' : ((2*n+1 : ℤ) : ℝ) = 0 := by push_cast; exact h
    have : (2*n+1 : ℤ) = 0 := by exact_mod_cast h'
    omega
  have htabs : M * π / (2*c) ≤ |t| := by
    rcases abs_two_mul_add_ge n 1 (Or.inr rfl) with h | h
    · linarith
    · subst h
      simp only [Int.cast_zero, abs_zero, mul_zero, zero_add, abs_one, t] at hnR ⊢
      have : (N:ℝ) ≤ 0 := hnR
      linarith
  have htpos : 0 < |t| := abs_pos.2 ht0
  have hv : ‖(2:ℂ)/((2*n+1:ℂ)*π)‖ = 2/(|t| * π) := by
    rw [ht, norm_div, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, Real.norm_of_nonneg Real.pi_pos.le]
  rw [hv, Pi.sub_apply]
  refine (hM n).trans ?_
  have hMle : M * π ≤ 2*c*|t| := by
    have := (div_le_iff₀ (by positivity : (0:ℝ) < 2*c)).1 htabs
    linarith
  rw [← sq_abs t, div_le_iff₀ (by positivity)]
  have : c * (2 / (|t| * π)) * |t|^2 = 2*c*|t|/π := by field_simp
  rw [this, le_div_iff₀ Real.pi_pos]
  linarith

/-- Coefficients in the scaled Anger–Weber expansion. -/
def angerScaledA : ℕ → ℂ → ℂ
  | 0 => fun lam => 1/(1+lam)
  | k+1 => fun lam => limUnder (𝓝[≠] lam) (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))

/-- Derivative of a quadratic divided by a power of `1 + l`. -/
theorem hasDerivAt_quadratic_div_pow (a b c : ℂ) (n : ℕ) {l : ℂ} (hl : 1+l ≠ 0) :
    HasDerivAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1))
      (((2*a*l+b)*(1+l)-(n+1)*(a*l^2+b*l+c))/(1+l)^(n+2)) l := by
  have hp : HasDerivAt (fun l : ℂ => a*l^2+b*l+c) (2*a*l+b) l := by
    convert (((hasDerivAt_pow 2 l).const_mul a).add ((hasDerivAt_id' l).const_mul b)).add_const c
      using 1
    simp; ring
  have hq : HasDerivAt (fun l : ℂ => (1+l)^(n+1)) ((n+1)*(1+l)^n) l := by
    convert ((hasDerivAt_id' l).const_add 1).pow (n+1) using 1
    simp
  convert hp.div hq (pow_ne_zero _ hl) using 1
  field_simp
  ring

/-- One step of the recursion for `angerScaledA`: if the `k`-th coefficient agrees with `g`
off `l = -1`, with derivatives `d`, `e`, then the removable limit defining the next
coefficient is the continuous closed form `G`. -/
theorem angerScaledA_succ_eq (k : ℕ) {g d e G : ℂ → ℂ}
    (hA : ∀ l, 1+l ≠ 0 → angerScaledA k l = g l)
    (hd : ∀ l, 1+l ≠ 0 → HasDerivAt g (d l) l)
    (he : ∀ l, 1+l ≠ 0 → HasDerivAt d (e l) l)
    (halg : ∀ l, 1+l ≠ 0 → l ≠ 1 → l/(1-l^2)*(l*e l+d l)/((2*k+1:ℂ)*(2*k+2)) = G l)
    (hG : ∀ l, 1+l ≠ 0 → ContinuousAt G l) {lam : ℂ} (hlam : 1+lam ≠ 0) :
    angerScaledA (k+1) lam = G lam := by
  have hU : IsOpen {l : ℂ | 1+l ≠ 0} := isOpen_ne_fun (by fun_prop) continuous_const
  have hAd : ∀ l, 1+l ≠ 0 → HasDerivAt (angerScaledA k) (d l) l := fun l hl =>
    (hd l hl).congr_of_eventuallyEq (by
      filter_upwards [hU.mem_nhds hl] with x hx using hA x hx)
  have hAe : ∀ l, 1+l ≠ 0 → iteratedDeriv 2 (angerScaledA k) l = e l := by
    intro l hl
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    refine ((he l hl).congr_of_eventuallyEq ?_).deriv
    filter_upwards [hU.mem_nhds hl] with x hx using (hAd x hx).deriv
  have hev : ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0 ∧ l ≠ 1 := by
    refine Filter.Eventually.and (nhdsWithin_le_nhds (hU.mem_nhds hlam) :
      ∀ᶠ l in 𝓝[≠] lam, 1+l ≠ 0) ?_
    by_cases h1 : lam = 1
    · subst h1; exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds h1)
  show limUnder _ _ = _
  refine (((hG lam hlam).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_).limUnder_eq
  filter_upwards [hev] with l hl
  rw [hAe l hl.1, (hAd l hl.1).deriv, halg l hl.1 hl.2]

/-- angerScaledA initial. -/
@[dlmf 11.11.E9]
theorem angerScaledA_initial (lam : ℂ) (h : lam ≠ -1) :
    angerScaledA 1 lam = -lam/(2*(1+lam)^4) ∧ angerScaledA 2 lam = (9*lam^2-lam)/(24*(1+lam)^7) ∧ angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
  have hlam : 1+lam ≠ 0 := fun h0 => h (by linear_combination h0)
  have hc : ∀ (a b c : ℂ) (n : ℕ) l, 1+l ≠ 0 → ContinuousAt (fun l => (a*l^2+b*l+c)/(1+l)^(n+1)) l :=
    fun a b c n l hl => (hasDerivAt_quadratic_div_pow a b c n hl).continuousAt
  have h1m : ∀ l : ℂ, 1+l ≠ 0 → l ≠ 1 → 1-l^2 ≠ 0 := fun l hl h1 => by
    have : 1-l ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
    rw [show 1-l^2 = (1-l)*(1+l) by ring]; exact mul_ne_zero this hl
  have s1 : ∀ l, 1+l ≠ 0 → angerScaledA 1 l = (0*l^2+(-1/2)*l+0)/(1+l)^(3+1) := by
    intro l hl
    refine angerScaledA_succ_eq 0 (g := fun l => (0*l^2+0*l+1)/(1+l)^(0+1))
      (d := fun l => (0*l^2+0*l+(-1))/(1+l)^(1+1)) (e := fun l => (0*l^2+0*l+2)/(1+l)^(2+1))
      (fun l hl => by simp [angerScaledA]) (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 0 1 0 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 0 (-1) 1 hl using 1; field_simp; ring
    · have := h1m l hl h1; field_simp; ring
  have s2 : ∀ l, 1+l ≠ 0 → angerScaledA 2 l = ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1) := by
    intro l hl
    refine angerScaledA_succ_eq 1 (g := fun l => (0*l^2+(-1/2)*l+0)/(1+l)^(3+1))
      (d := fun l => (0*l^2+(3/2)*l+(-1/2))/(1+l)^(4+1))
      (e := fun l => (0*l^2+(-6)*l+4)/(1+l)^(5+1))
      s1 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => hc _ _ _ _ l hl) hl
    · convert hasDerivAt_quadratic_div_pow 0 (-1/2) 0 3 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow 0 (3/2) (-1/2) 4 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
  have s3 : angerScaledA 3 lam = -(225*lam^3-54*lam^2+lam)/(720*(1+lam)^10) := by
    refine angerScaledA_succ_eq 2 (g := fun l => ((9/24)*l^2+(-1/24)*l+0)/(1+l)^(6+1))
      (d := fun l => ((-45/24)*l^2+1*l+(-1/24))/(1+l)^(7+1))
      (e := fun l => ((270/24)*l^2+(-258/24)*l+(32/24))/(1+l)^(8+1))
      (G := fun l => -(225*l^3-54*l^2+l)/(720*(1+l)^10))
      s2 (fun l hl => ?_) (fun l hl => ?_) (fun l hl h1 => ?_)
      (fun l hl => ?_) hlam
    · convert hasDerivAt_quadratic_div_pow (9/24) (-1/24) 0 6 hl using 1; field_simp; ring
    · convert hasDerivAt_quadratic_div_pow (-45/24) 1 (-1/24) 7 hl using 1; field_simp; ring
    · have := h1m l hl h1; push_cast; field_simp; ring
    · exact ((by fun_prop : Continuous fun l : ℂ => -(225*l^3-54*l^2+l)).continuousAt).div
        (by fun_prop) (mul_ne_zero (by norm_num) (pow_ne_zero _ hl))
  refine ⟨?_, ?_, s3⟩
  · rw [s1 lam hlam]; field_simp; ring
  · rw [s2 lam hlam]; field_simp; ring

/-- angerA scaled 8. -/
@[dlmf 11.11.E8]
theorem angerA_scaled_8 {lam : ℝ} (hlam : 0 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (1*ν) (lam*ν)-(1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerA scaled 10. -/
@[dlmf 11.11.E10]
theorem angerA_scaled_10 {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => angerA (-1*ν) (lam*ν)-(-1:ℂ)/π*∑ k ∈ Finset.range N, ((2*k).factorial:ℂ)*angerScaledA k (-1*lam)/ν^(2*k+1)) =O[sector (π-δ)] (fun ν : ℂ => ν^(-(2*N+1:ℤ))) := by
  sorry

/-- angerMu. -/
@[dlmf 11.11.E12]
def angerMu (lam : ℂ) : ℂ :=
  (1-lam^2)^(1/2:ℂ)-log ((1+(1-lam^2)^(1/2:ℂ))/lam)

/-- Coefficients of the saddle expansion, with existence provided by the expansion theorem. -/
def angerScaledB (lam : ℝ) (k : ℕ) : ℂ :=
  asymptoticCoeff (fun v : ℝ => ((π*v/2:ℂ)^(1/2:ℂ))*exp (v*angerMu lam)*angerA (-v) (lam*v)) k / poch (1/2) k

/-- angerA scaled saddle. -/
@[dlmf 11.11.E11]
theorem angerA_scaled_saddle {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) (N : ℕ) :
    (fun ν : ℂ => (π*ν/2)^(1/2:ℂ)*exp (ν*angerMu lam)*angerA (-ν) (lam*ν)-∑ k ∈ Finset.range N, poch (1/2) k*angerScaledB lam k/ν^k) =O[sector (π/2-δ)] (fun ν : ℂ => ν^(-(N:ℤ))) := by
  sorry

/-- angerScaledB initial. -/
@[dlmf 11.11.E13]
theorem angerScaledB_initial {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) :
    angerScaledB lam 0 = (1-lam^2:ℂ)^(-1/4:ℂ) ∧ angerScaledB lam 1 = (2+3*lam^2:ℂ)/(12*(1-lam^2:ℂ)^(7/4:ℂ)) ∧ angerScaledB lam 2 = (4+300*lam^2+81*lam^4:ℂ)/(864*(1-lam^2:ℂ)^(13/4:ℂ)) := by
  sorry

/-- angerA scaled outer equiv. -/
@[dlmf 11.11.E14]
theorem angerA_scaled_outer_equiv {lam : ℝ} (hlam : 1 < lam) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π-δ)] (fun ν => 1/(π*ν*(lam-1))) := by
  sorry

/-- angerA scaled inner equiv. -/
@[dlmf 11.11.E15]
theorem angerA_scaled_inner_equiv {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π/2) :
    (fun ν : ℂ => angerA (-ν) (lam*ν)) ~[sector (π/2-δ)] (fun ν => (2/(π*ν))^(1/2:ℂ)*exp (-ν*angerMu lam)/(1-lam^2:ℂ)^(1/4:ℂ)) := by
  sorry

/-- angerA turning equiv. -/
@[dlmf 11.11.E16]
theorem angerA_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerA (-ν) ν) ~[sector (π-δ)] (fun ν => 2^(4/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- angerJ turning equiv. -/
@[dlmf 11.11.E18]
theorem angerJ_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => angerJ ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(2/3:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- weberE turning equiv. -/
@[dlmf 11.11.E19]
theorem weberE_turning_equiv {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) :
    (fun ν : ℂ => weberE ν ν) ~[sector (π-δ)] (fun ν => 2^(1/3:ℂ)/(3^(7/6:ℂ)*Gamma (2/3)*ν^(1/3:ℂ))) := by
  sorry

/-- Turning-point approximation uniform on bounded complex transition parameters; positive real order. -/
@[dlmf 11.11.E17]
theorem angerA_turning_uniform (M : ℝ) (hM : 0 < M) :
    (fun p : ℝ × ℂ => angerA (-p.1) (p.1+p.2*(p.1:ℂ)^(1/3:ℂ))-2^(1/3:ℂ)*(p.1:ℂ)^(-1/3:ℂ)*scorerHi (-2^(1/3:ℂ)*p.2)) =O[comap Prod.fst atTop ⊓ 𝓟 {p : ℝ × ℂ | ‖p.2‖ ≤ M}] (fun p : ℝ × ℂ => (p.1:ℂ)^(-1:ℤ)) := by
  sorry

/-- The recurrence in DLMF 11.11(iii) has a removable singularity at lambda=1. -/
theorem angerScaledA_removable (k : ℕ) {lam : ℂ} (hlam : lam ≠ -1) :
    Tendsto (fun l : ℂ => l/(1-l^2)*(l*iteratedDeriv 2 (angerScaledA k) l+deriv (angerScaledA k) l)/((2*k+1:ℂ)*(2*k+2)))
      (𝓝[≠] lam) (𝓝 (angerScaledA (k+1) lam)) := by
  sorry

/-- The convergent defining H series is also a generalized large-order expansion, DLMF 11.6(ii). -/
theorem struveH_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveH ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (-1)^n*(z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  sorry

/-- The corresponding generalized L expansion in DLMF 11.6(ii). -/
theorem struveL_large_order_expansion {z : ℂ} (hz : z ∈ slitPlane)
    {δ : ℝ} (hδ : 0 < δ) (hδπ : δ < π) (N : ℕ) :
    (fun ν : ℂ => struveL ν z-(z/2)^(ν+1)*∑ n ∈ Finset.range N,
      (z/2)^(2*n)*struveCoeff ν n) =O[sector (π-δ)]
      (fun ν : ℂ => (z/2)^(ν+1)/Gamma (ν+N+3/2)) := by
  sorry

end AAR.Struve
