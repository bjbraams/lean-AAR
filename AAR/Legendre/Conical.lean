/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Toroidal
public import AAR.Legendre.Singularities

/-!
# Conical functions, Mehler–Fock transforms and special identities

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- Real conical Ferrers function. -/
def conicalP (τ μ x : ℝ) : ℂ :=
  ferrersP (-1/2+I*τ) (-μ) x

/-- Dunster’s conical companion; the order is minus the parameter μ. -/
@[dlmf 14.20.E2]
def conicalQHat (τ μ x : ℝ) : ℂ :=
  ((exp (μ*π*I)*ferrersQ (-1/2+I*τ) (-μ) x).re:ℂ)-π/2*Real.sin (μ*π)*conicalP τ μ x

/-- conical ode. -/
@[dlmf 14.20.E1]
theorem conical_ode (τ μ : ℝ) (hμ : 0 ≤ μ) (hτ : 0 ≤ τ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    (1-x^2:ℂ)*iteratedDeriv 2 (conicalP τ μ) x-2*x*deriv (conicalP τ μ) x-(τ^2+1/4+μ^2/(1-x^2):ℂ)*conicalP τ μ x=0 := by
  have h := ferrersP_ode (-1/2+I*τ) (-(μ:ℂ)) hx
  have e : conicalP τ μ = ferrersP (-1/2+I*τ) (-(μ:ℂ)) := rfl
  rw [e]
  linear_combination h + (-(τ:ℂ)^2 * ferrersP (-1/2+I*τ) (-(μ:ℂ)) x) * I_sq

/-- conicalQHat connection. -/
@[dlmf 14.20.E3]
theorem conicalQHat_connection {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conicalQHat τ μ x=π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ x+π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ (-x) := by
  sorry

/-- conical wronskian. -/
@[dlmf 14.20.E4]
theorem conical_wronskian (τ μ : ℝ) (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (conicalP τ μ) (fun x => conicalP τ μ (-x)) x=2/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*(1-x^2)) := by
  show ferrersWronskian (fun x => ferrersP (-1/2+I*τ) (-(μ:ℂ)) x)
    (fun x => ferrersP (-1/2+I*τ) (-(μ:ℂ)) (-x)) x = _
  rw [ferrers_wronskian_3 _ _ hx]
  congr 2
  rw [show (μ:ℂ)-(-1/2+I*τ) = (starRingEnd ℂ) ((μ:ℂ)+1/2+I*τ) by simp [map_ofNat]; ring,
    show -1/2+I*(τ:ℂ)+μ+1 = (μ:ℂ)+1/2+I*τ by ring, Gamma_conj, mul_comm, mul_conj,
    normSq_eq_norm_sq]
  push_cast; ring

/-- conicalQHat wronskian. -/
@[dlmf 14.20.E5]
theorem conicalQHat_wronskian {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersWronskian (conicalP τ μ) (conicalQHat τ μ) x=π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(1-x^2)) := by
  sorry

/-- conical associated connection. -/
@[dlmf 14.20.E6]
theorem conical_associated_connection {τ μ : ℝ} (hτ : 0 < τ) (hμ : 0 ≤ μ) {x : ℝ} (hx : 1 < x) :
    associatedP (-1/2+I*τ) (-μ) x=I*exp (-μ*π*I)/(Real.sinh (τ*π)*(‖Gamma (μ+1/2+I*τ)‖^2:ℂ))*(associatedQ (-1/2+I*τ) μ x-associatedQ (-1/2-I*τ) μ x) := by
  have hz : (x:ℂ)-1 ∈ slitPlane := by
    rw [show (x:ℂ)-1 = ((x-1:ℝ):ℂ) by push_cast; ring]; exact Or.inl (by simp; linarith)
  have h12 := associated_connection_12 (-1/2+I*τ) μ hz
  rw [show -(-1/2+I*(τ:ℂ))-1 = -1/2-I*τ by ring, show (μ:ℂ)-(-1/2+I*τ) = μ+1/2-I*τ by ring,
    show -1/2+I*(τ:ℂ)+μ+1 = μ+1/2+I*τ by ring] at h12
  have hr1 : LegendreQRegular (-1/2+I*τ) μ := legendreQRegular_of_im_ne_zero (by simp; exact hτ.ne')
  have hr2 : LegendreQRegular (-1/2-I*τ) μ := legendreQRegular_of_im_ne_zero (by simp; exact hτ.ne')
  rw [olverQ_normalization hr1, olverQ_normalization hr2] at h12
  rw [show -1/2+I*(τ:ℂ)+μ+1 = μ+1/2+I*τ by ring, show -1/2-I*(τ:ℂ)+μ+1 = μ+1/2-I*τ by ring] at h12
  have hc : (μ:ℂ)+1/2-I*τ = (starRingEnd ℂ) ((μ:ℂ)+1/2+I*τ) := by simp [map_ofNat]; ring
  have hn : ((‖Gamma (μ+1/2+I*τ)‖^2 : ℝ) : ℂ) = Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ) := by
    rw [hc, Gamma_conj, mul_conj, normSq_eq_norm_sq]
  have hcos : cos ((-1/2+I*τ)*π) = I*Real.sinh (τ*π) := by
    rw [show (-1/2+I*(τ:ℂ))*π = (τ*π)*I - π/2 by ring, cos_sub_pi_div_two, sin_mul_I]
    push_cast; ring
  have hG1 : Gamma (μ+1/2+I*τ) ≠ 0 := Gamma_ne_zero (fun n hn => by
    have := congrArg Complex.im hn; simp at this; exact hτ.ne' this)
  have hG2 : Gamma (μ+1/2-I*τ) ≠ 0 := Gamma_ne_zero (fun n hn => by
    have := congrArg Complex.im hn; simp at this; exact hτ.ne' this)
  have hsh : (Real.sinh (τ*π):ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sinh_pos_iff.mpr (by positivity)).ne'
  rw [hcos] at h12
  have hn' : (‖Gamma (μ+1/2+I*τ)‖^2:ℂ) = Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ) := by
    rw [← hn]; push_cast; ring
  rw [hn', div_mul_eq_mul_div, eq_div_iff (mul_ne_zero hsh (mul_ne_zero hG1 hG2))]
  have h12' : I*(Real.sinh (τ*π):ℂ)*associatedP (-1/2+I*τ) (-μ) x*(Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ)) =
      exp (-μ*π*I)*(associatedQ (-1/2-I*τ) μ x-associatedQ (-1/2+I*τ) μ x) := by
    rw [h12]
    generalize Gamma (μ+1/2+I*τ) = G1 at hG1 ⊢
    generalize Gamma (μ+1/2-I*τ) = G2 at hG2 ⊢
    field_simp
    ring
  linear_combination (-I)*h12' + ((Real.sinh (τ*π):ℂ)*associatedP (-1/2+I*τ) (-μ) x*
    (Gamma (μ+1/2+I*τ)*Gamma (μ+1/2-I*τ)))*I_sq

/-- conical singular 7. -/
@[dlmf 14.20.E7]
theorem conical_singular_7 {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 < μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => conicalQHat τ (-1*μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => Gamma (μ:ℂ)/2*(2/(1-x):ℂ)^((μ:ℂ)/2)) := by
  sorry

/-- conical singular 8. -/
@[dlmf 14.20.E8]
theorem conical_singular_8 {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 < μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) :
    (fun x : ℝ => conicalQHat τ (1*μ) x) ~[𝓝[<] (1:ℝ)] (fun x : ℝ => π*Gamma (μ:ℂ)*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(‖Gamma (μ+1/2+I*τ)‖^2:ℂ))*(2/(1-x):ℂ)^((μ:ℂ)/2)) := by
  sorry

/-- conical mehler integral. -/
@[dlmf 14.20.E9]
theorem conical_mehler_integral (τ : ℝ) {θ : ℝ} (h0 : 0 < θ) (hπ : θ < π) :
    conicalP τ 0 (Real.cos θ)=2/π*∫ t : ℝ in 0..θ, (Real.cosh (τ*t)/Real.sqrt (2*(Real.cos t-Real.cos θ)):ℂ) := by
  sorry

/-- The conical Pochhammer product `(1/2+iτ)ₖ(1/2-iτ)ₖ = ∏ (4τ²+(2j+1)²)/4ᵏ`. -/
lemma poch_conical (τ : ℝ) (k : ℕ) :
    poch (1/2+I*τ) k * poch (1/2-I*τ) k = (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/4^k := by
  induction k with
  | zero => simp [poch_zero]
  | succ k ih =>
    rw [poch_succ, poch_succ, Finset.prod_range_succ, pow_succ,
      show poch (1/2+I*τ) k * (1/2+I*τ+k) * (poch (1/2-I*τ) k * (1/2-I*τ+k)) =
        (poch (1/2+I*τ) k * poch (1/2-I*τ) k) * ((1/2+I*τ+k)*(1/2-I*τ+k)) by ring, ih]
    have : (1/2+I*τ+k)*(1/2-I*τ+k) = (4*τ^2+(2*k+1)^2:ℂ)/4 := by
      linear_combination (-(τ:ℂ)^2) * I_sq
    rw [this]; field_simp; ring

/-- The singular endpoint θ=π is excluded from a finite-valued convergence assertion. -/
@[dlmf 14.20.E10]
theorem conical_power_series (τ : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    HasSum (fun k : ℕ => (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*(Real.sin (θ/2):ℂ)^(2*k)) (conicalP τ 0 (Real.cos θ)) := by
  have hs : (1-(Real.cos θ:ℂ))/2 = (Real.sin (θ/2):ℂ)^2 := by
    have h1 := Real.cos_two_mul (θ/2)
    have h2 := Real.sin_sq_add_cos_sq (θ/2)
    rw [show 2*(θ/2) = θ by ring] at h1
    have h3 : (Real.cos θ:ℂ) = 1 - 2*(Real.sin (θ/2):ℂ)^2 := by
      exact_mod_cast (by linear_combination h1 + 2*h2 : Real.cos θ = 1 - 2*Real.sin (θ/2)^2)
    rw [h3]; ring
  have hw : ‖(Real.sin (θ/2):ℂ)^2‖ < 1 := by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have h1 : Real.sin (θ/2) < 1 := by
      rw [← Real.sin_pi_div_two]
      exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (by linarith) (by linarith)
    have h2 : 0 ≤ Real.sin (θ/2) := Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    nlinarith
  have h := hasSum_regularizedGaussHGFun_coeff (1/2+I*τ) (1/2-I*τ) 1 hw
  have e : conicalP τ 0 (Real.cos θ) = regularizedGaussHGFun (1/2+I*τ) (1/2-I*τ) 1 ((Real.sin (θ/2):ℂ)^2) := by
    unfold conicalP ferrersP
    rw [hs, regularizedGaussHG_eq_regularizedGaussHGFun _ _ _ hw]
    simp only [ofReal_zero, neg_zero, zero_div, cpow_zero, one_mul, sub_zero]
    congr 1 <;> ring
  rw [e]
  refine h.congr_fun fun k => ?_
  rw [poch_conical, add_comm (1:ℂ), Gamma_nat_eq_factorial, ← pow_mul]
  field_simp

/-- Positivity stated in DLMF 14.20(v). -/
theorem conical_positive (τ : ℝ) {θ : ℝ} (h0 : 0 ≤ θ) (hπ : θ < π) :
    0 < (conicalP τ 0 (Real.cos θ)).re := by
  have h := Complex.reCLM.hasSum (conical_power_series τ h0 hπ)
  set g : ℕ → ℝ := fun k => (∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2))/(4^k*(k.factorial:ℝ)^2)*
    (Real.sin (θ/2))^(2*k) with hg
  have he : ∀ k : ℕ, Complex.reCLM ((∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*
      (Real.sin (θ/2):ℂ)^(2*k)) = g k := by
    intro k
    have : ((∏ j ∈ Finset.range k, (4*τ^2+(2*j+1)^2:ℂ))/(4^k*(k.factorial:ℂ)^2)*
      (Real.sin (θ/2):ℂ)^(2*k)) = ((g k : ℝ) : ℂ) := by simp only [hg]; push_cast; rfl
    rw [this]; simp
  simp only [he] at h
  have hnn : ∀ k, 0 ≤ g k := fun k => by
    simp only [hg]
    refine mul_nonneg (div_nonneg (Finset.prod_nonneg fun j _ => by positivity) (by positivity)) ?_
    rw [pow_mul]; positivity
  have h1 := le_hasSum h 0 (fun j _ => hnn j)
  simp [hg] at h1
  simpa using lt_of_lt_of_le one_pos h1

/-- mehlerFockTransform. -/
@[dlmf 14.20.E11]
def mehlerFockTransform (μ : ℝ) (g : ℝ → ℂ) (τ : ℝ) : ℂ :=
  τ/π*Real.sinh (τ*π)*Gamma (1/2-μ+I*τ)*Gamma (1/2-μ-I*τ)*improperAtTop (fun x : ℝ => associatedP (-1/2+I*τ) μ x*g x) 1

/-- mehlerFockInverse. -/
@[dlmf 14.20.E12]
def mehlerFockInverse (μ : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  improperAtTop (fun τ : ℝ => associatedP (-1/2+I*τ) μ x*f τ) 0

/-- conical stieltjes integral. -/
@[dlmf 14.20.E13]
theorem conical_stieltjes_integral (τ : ℝ) {x : ℝ} (hx : 1 < x) :
    HasIntegralAtTop (fun t : ℝ => Real.cosh (τ*π)/π*associatedP (-1/2+I*τ) 0 t/(x+t)) 1 (associatedP (-1/2+I*τ) 0 x) := by
  sorry

/-- conical product transform. -/
@[dlmf 14.20.E14]
theorem conical_product_transform {x y : ℝ} (hx : 1 < x) (hy : 1 < y) :
    HasIntegralAtTop (fun τ : ℝ => π*τ*Real.tanh (τ*π)/Real.cosh (τ*π)*associatedP (-1/2+I*τ) 0 x*associatedP (-1/2+I*τ) 0 y) 0 (1/(y+x:ℂ)) := by
  sorry

end AAR.Legendre
