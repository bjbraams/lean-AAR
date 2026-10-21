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

/-- The conical Ferrers function is real-valued on `(-1,1)`. -/
lemma conicalP_ofReal_re (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ((conicalP τ μ x).re : ℂ) = conicalP τ μ x := by
  rw [Complex.conj_eq_iff_re.mp]
  show (starRingEnd ℂ) (ferrersP (-1/2+I*τ) (-(μ:ℂ)) x) = ferrersP (-1/2+I*τ) (-(μ:ℂ)) x
  rw [ferrersP_conj _ _ hx]
  have e1 : (starRingEnd ℂ) (-1/2+I*(τ:ℂ)) = -(-1/2+I*τ)-1 := by
    apply Complex.ext
    · simp [map_ofNat]; norm_num
    · simp [map_ofNat]
  have e2 : (starRingEnd ℂ) (-(μ:ℂ)) = -(μ:ℂ) := by simp
  rw [e1, e2, ferrers_connection_5 _ _ hx]

/-- Differentiability of the conical function on `(-1,1)`. -/
lemma conicalP_differentiableAt (τ μ : ℝ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    DifferentiableAt ℝ (conicalP τ μ) x :=
  (((hasDerivAt_ferrersEven _ _ hx).const_mul _).add ((hasDerivAt_ferrersOdd _ _ hx).const_mul _)
    ).differentiableAt.congr_of_eventuallyEq
    ((ferrersP_eqOn_even_odd _ _).eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx))

/-- conicalQHat connection. -/
@[dlmf 14.20.E3]
theorem conicalQHat_connection {τ μ : ℝ} (hτ : 0 ≤ τ) (hμ : 0 ≤ μ) (hex : τ ≠ 0 ∨ ∀ n : ℕ, μ ≠ n+1/2) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    conicalQHat τ μ x=π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ x+π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))*conicalP τ μ (-x) := by
  have hxm : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  set ν : ℂ := -1/2+I*τ with hν
  have hreg1 : LegendreQRegular ν (μ:ℂ) := by
    intro n hn
    have := congrArg Complex.re hn
    simp [hν] at this
    linarith
  have hreg2 : LegendreQRegular ν (-(μ:ℂ)) := by
    intro n hn
    have hr := congrArg Complex.re hn
    have hi := congrArg Complex.im hn
    simp [hν] at hr hi
    rcases hex with h | h
    · exact h hi
    · exact h n (by linarith)
  have h10 := ferrers_connection_10 ν (μ:ℂ) hreg1 hreg2 hx
  have hw : (ν-μ)*π = ((-(μ*π) - π/2 : ℝ):ℂ) + ((τ*π:ℝ):ℂ)*I := by rw [hν]; push_cast; ring
  have hsw : sin ((ν-μ)*π) = ((-(Real.cos (μ*π)*Real.cosh (τ*π))):ℝ) + (-(Real.sin (μ*π)*Real.sinh (τ*π)):ℝ)*I := by
    rw [hw, Complex.sin_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh,
      Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two, Real.cos_neg, Real.sin_neg]
    simp only [ofReal_neg, ofReal_mul]; ring
  have hcw : cos ((ν-μ)*π) = (-(Real.sin (μ*π)*Real.cosh (τ*π)):ℝ) + (Real.cos (μ*π)*Real.sinh (τ*π):ℝ)*I := by
    rw [hw, Complex.cos_add_mul_I, ← ofReal_sin, ← ofReal_cos, ← ofReal_sinh, ← ofReal_cosh,
      Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two, Real.cos_neg, Real.sin_neg]
    simp only [ofReal_neg, ofReal_mul]; ring
  have he : exp (μ*π*I) = (Real.cos (μ*π):ℂ) + (Real.sin (μ*π):ℂ)*I := by
    rw [show (μ:ℂ)*π*I = ((μ*π:ℝ):ℂ)*I by push_cast; ring, exp_mul_I, ← ofReal_sin, ← ofReal_cos]
  have hexp : Real.exp (-τ*π) = Real.cosh (τ*π) - Real.sinh (τ*π) := by
    rw [show -τ*π = -(τ*π) by ring, Real.cosh_eq, Real.sinh_eq]; ring
  have hc0 : τ = 0 → Real.cos (μ*π) ≠ 0 := by
    intro h0 hc0
    obtain ⟨k, hk⟩ := Real.cos_eq_zero_iff.mp hc0
    have hk' : μ = k + 1/2 := by
      have := Real.pi_pos
      field_simp at hk; linarith
    rcases hex with h | h
    · exact h h0
    · have hk0 : (0:ℤ) ≤ k := by
        have : (-1:ℝ) < k := by linarith
        exact_mod_cast (show (-1:ℤ) < k by exact_mod_cast this)
      apply h k.toNat
      rw [hk']; congr 1; exact_mod_cast (Int.toNat_of_nonneg hk0).symm
  have hS0 : τ ≠ 0 → Real.sinh (τ*π) ≠ 0 := by
    intro h; rw [Ne, Real.sinh_eq_zero]; exact mul_ne_zero h Real.pi_ne_zero
  unfold conicalQHat
  rw [← conicalP_ofReal_re τ μ hx, ← conicalP_ofReal_re τ μ hxm]
  have hp : ferrersP ν (-(μ:ℂ)) x = (conicalP τ μ x).re := (conicalP_ofReal_re τ μ hx).symm
  have hq : ferrersP ν (-(μ:ℂ)) (-x) = (conicalP τ μ (-x)).re := (conicalP_ofReal_re τ μ hxm).symm
  rw [hp, hq, hsw, hcw] at h10
  rw [he, hexp]
  generalize (conicalP τ μ x).re = p at h10 ⊢
  generalize (conicalP τ μ (-x)).re = q at h10 ⊢
  generalize ferrersQ ν (-(μ:ℂ)) x = Q at h10 ⊢
  have pyth : Real.sin (μ*π)^2+Real.cos (μ*π)^2 = 1 := Real.sin_sq_add_cos_sq _
  have hyp : Real.cosh (τ*π)^2 - Real.sinh (τ*π)^2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hC : 1 ≤ Real.cosh (τ*π) := Real.one_le_cosh _
  generalize Real.cos (μ*π) = c at *
  generalize Real.sin (μ*π) = s at *
  generalize Real.cosh (τ*π) = C at *
  generalize Real.sinh (τ*π) = S at *
  have hD : 0 < C^2 - s^2 := by
    by_cases h0 : τ = 0
    · nlinarith [sq_pos_of_ne_zero (hc0 h0), sq_nonneg S]
    · nlinarith [sq_pos_of_ne_zero (hS0 h0), sq_nonneg c]
  have hPi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have key : (((-(c*C)):ℝ) + (-(s*S):ℝ)*I) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I) = ((C^2-s^2:ℝ):ℂ) := by
    have e : ((c*C)^2 + (s*S)^2 : ℝ) = C^2-s^2 := by linear_combination C^2*pyth - s^2*hyp
    rw [← e]; apply Complex.ext <;> simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im] <;> ring
  have h2 : (2/π*(C^2-s^2:ℝ):ℂ) * Q = (((-(s*C):ℝ) + (c*S:ℝ)*I) * p - q) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I) := by
    linear_combination ((-(c*C):ℝ) - (-(s*S):ℝ)*I) * h10 - (2/π*Q) * key
  have hQ : Q = ((π/2/(C^2-s^2) : ℝ):ℂ) * ((((-(s*C):ℝ) + (c*S:ℝ)*I) * p - q) * ((-(c*C):ℝ) - (-(s*S):ℝ)*I)) := by
    rw [← h2]
    have : ((C^2-s^2:ℝ):ℂ) ≠ 0 := ofReal_ne_zero.mpr hD.ne'
    push_cast at this ⊢
    field_simp
  have hre : (((c:ℂ) + (s:ℂ)*I) * Q).re = π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) := by
    rw [hQ]; simp only [mul_re, mul_im, add_re, add_im, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im]; ring
  rw [hre]
  have hfin : π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) - π/2*s*p
      - (π*(C-S)*s*S/(2*(C^2-s^2))*p + π*((C-S)*c^2+S)/(2*(C^2-s^2))*q)
      = π/(2*(C^2-s^2)) * (p*((s*S*C+s)*(s^2+c^2-1) + s*(c^2-1)*(C^2-S^2-1)) + q*(S*(s^2+c^2-1))) := by
    field_simp; ring
  rw [show s^2+c^2-1 = 0 by linarith, show C^2-S^2-1 = 0 by linarith] at hfin
  have : π/2/(C^2-s^2) * ((-(c^2*C+s^2*S))*(-(s*C*p)-q) - c*s*(S-C)*(c*S*p)) - π/2*s*p
      = π*(C-S)*s*S/(2*(C^2-s^2))*p + π*((C-S)*c^2+S)/(2*(C^2-s^2))*q := by linarith [hfin]
  rw [← sub_eq_zero]
  have h3 := congrArg (fun r : ℝ => (r:ℂ)) this
  push_cast at h3 ⊢
  linear_combination h3

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
  set A : ℂ := π*Real.exp (-τ*π)*Real.sin (μ*π)*Real.sinh (τ*π)/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  set B : ℂ := π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/(2*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2))
  have hev : conicalQHat τ μ =ᶠ[nhds x] fun y => A*conicalP τ μ y+B*conicalP τ μ (-y) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    exact conicalQHat_connection hτ hμ hex hy
  have hxm : -x ∈ Ioo (-1:ℝ) 1 := ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hd1 : DifferentiableAt ℝ (conicalP τ μ) x := conicalP_differentiableAt τ μ hx
  have hd2 : DifferentiableAt ℝ (fun y => conicalP τ μ (-y)) x :=
    (conicalP_differentiableAt τ μ hxm).comp x differentiableAt_id.neg
  have hW := conical_wronskian τ μ hτ hμ hx
  unfold ferrersWronskian at hW ⊢
  have hder : deriv (fun y => A*conicalP τ μ y+B*conicalP τ μ (-y)) x =
      A*deriv (conicalP τ μ) x + B*deriv (fun y => conicalP τ μ (-y)) x :=
    ((hd1.hasDerivAt.const_mul A).add (hd2.hasDerivAt.const_mul B)).deriv
  rw [hev.deriv_eq, hev.eq_of_nhds, hder]
  have hW' : conicalP τ μ x * deriv (fun x => conicalP τ μ (-x)) x - conicalP τ μ (-x) * deriv (conicalP τ μ) x =
      2 / (↑‖Gamma (↑μ + 1 / 2 + I * ↑τ)‖ ^ 2 * (1 - ↑x ^ 2)) := hW
  have hfin : B * (2 / (↑‖Gamma (↑μ + 1 / 2 + I * ↑τ)‖ ^ 2 * (1 - ↑x ^ 2))) =
      π*(Real.exp (-τ*π)*(Real.cos (μ*π))^2+Real.sinh (τ*π))/((‖Gamma (μ+1/2+I*τ)‖^2:ℂ)*((Real.cosh (τ*π))^2-(Real.sin (μ*π))^2)*(1-x^2)) := by
    simp only [B]
    generalize ((Real.cosh (τ*π):ℂ)^2-(Real.sin (μ*π):ℂ)^2) = D
    generalize ((‖Gamma (μ+1/2+I*τ)‖:ℂ)^2) = G
    generalize (1-(x:ℂ)^2) = X
    ring
  rw [← hfin]
  linear_combination B * hW'

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
