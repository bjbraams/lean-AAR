/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Airy.Scorer

/-!
# Airy indefinite integrals and transforms, DLMF §9.10

Statements acquired from the NIST DLMF, checked 2026-10-19.
New statements are initially admitted; existing proved Airy results are retained.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.Confluent
open scoped Real Topology
namespace AAR.Airy

/-- `Gi' = Bi'(1/3 - ∫Ai) + Ai' ∫Bi`, the derivative of 9.12.4. -/
lemma scorerGiDeriv_variation (z : ℂ) :
    scorerGiDeriv z = airyBiDeriv z * (1 / 3 - primitive airyAi z) +
      airyAiDeriv z * primitive airyBi z := by
  have hfun : scorerGi = fun z => airyBi z * (1 / 3 - primitive airyAi z) +
      airyAi z * primitive airyBi z := funext scorerGi_variation
  have pA := hasDerivAt_primitive differentiable_airyAi z
  have pB := hasDerivAt_primitive differentiable_airyBi z
  have hd := (((hasDerivAt_airyBi z).mul ((hasDerivAt_const z (1 / 3 : ℂ)).sub pA)).add
      ((hasDerivAt_airyAi z).mul pB))
  rw [scorerGiDeriv, hfun]
  refine hd.deriv.trans ?_
  simp only [Pi.sub_apply]; ring

/-- `Hi' = Bi'(2/3 + ∫Ai) - Ai' ∫Bi`, the derivative of 9.12.5. -/
lemma scorerHiDeriv_variation (z : ℂ) :
    scorerHiDeriv z = airyBiDeriv z * (2 / 3 + primitive airyAi z) -
      airyAiDeriv z * primitive airyBi z := by
  have h := scorerGiDeriv_eq z
  rw [scorerGiDeriv_variation] at h
  linear_combination h

/-- airyAi integral scorerGi (DLMF 9.10.1). -/
@[dlmf 9.10.E1]
theorem airyAi_integral_scorerGi (z : ℂ) :
    1 / 3 - primitive airyAi z = π * (airyAi z * scorerGiDeriv z - airyAiDeriv z * scorerGi z) := by
  rw [scorerGiDeriv_variation, scorerGi_variation]
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi z * (airyBiDeriv z * (1 / 3 - primitive airyAi z) +
      airyAiDeriv z * primitive airyBi z) - airyAiDeriv z * (airyBi z * (1 / 3 - primitive airyAi z) +
      airyAi z * primitive airyBi z) = (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) *
      (1 / 3 - primitive airyAi z) by ring, hW]
  field_simp

/-- airyAi integral scorerHi (DLMF 9.10.2). -/
@[dlmf 9.10.E2]
theorem airyAi_integral_scorerHi (z : ℂ) :
    2 / 3 + primitive airyAi z = π * (airyAi z * scorerHiDeriv z - airyAiDeriv z * scorerHi z) := by
  rw [scorerHiDeriv_variation, scorerHi_variation]
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [show airyAi z * (airyBiDeriv z * (2 / 3 + primitive airyAi z) -
      airyAiDeriv z * primitive airyBi z) - airyAiDeriv z * (airyBi z * (2 / 3 + primitive airyAi z) -
      airyAi z * primitive airyBi z) = (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) *
      (2 / 3 + primitive airyAi z) by ring, hW]
  field_simp

/-- airyBi integral scorer (DLMF 9.10.3). -/
@[dlmf 9.10.E3]
theorem airyBi_integral_scorer (z : ℂ) :
    primitive airyBi z = π * (airyBiDeriv z * scorerGi z - airyBi z * scorerGiDeriv z) ∧
      primitive airyBi z = π * (airyBi z * scorerHiDeriv z - airyBiDeriv z * scorerHi z) := by
  have hW := wronskian_airyAi_airyBi z
  have hp : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  constructor
  · rw [scorerGiDeriv_variation, scorerGi_variation]
    rw [show airyBiDeriv z * (airyBi z * (1 / 3 - primitive airyAi z) + airyAi z * primitive airyBi z) -
        airyBi z * (airyBiDeriv z * (1 / 3 - primitive airyAi z) + airyAiDeriv z * primitive airyBi z) =
        (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) * primitive airyBi z by ring, hW]
    field_simp
  · rw [scorerHiDeriv_variation, scorerHi_variation]
    rw [show airyBi z * (airyBiDeriv z * (2 / 3 + primitive airyAi z) - airyAiDeriv z * primitive airyBi z) -
        airyBiDeriv z * (airyBi z * (2 / 3 + primitive airyAi z) - airyAi z * primitive airyBi z) =
        (airyAi z * airyBiDeriv z - airyAiDeriv z * airyBi z) * primitive airyBi z by ring, hW]
    field_simp

/-- airyAi lower integral scorerHi (DLMF 9.10.2). -/
@[dlmf 9.10.E2]
theorem airyAi_lower_integral_scorerHi (x : ℝ) :
    HasIntegralAtBot (fun t => airyAi t) x (2 / 3 + primitive airyAi x) := by
  sorry

/-- airyBi lower integral scorer (DLMF 9.10.3). -/
@[dlmf 9.10.E3]
theorem airyBi_lower_integral_scorer (x : ℝ) :
    HasIntegralAtBot (fun t => airyBi t) x (primitive airyBi x) := by
  sorry

/-- airyAi tail integral asymptotic (DLMF 9.10.4). -/
@[dlmf 9.10.E4]
theorem airyAi_tail_integral_asymptotic  :
    (fun x : ℝ => improperAtTop (fun t => airyAi t) x) ~[atTop]
      (fun x : ℝ => ((Real.exp (-airyZeta x) / (2 * Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)) := by
  sorry

/-- airyBi integral asymptotic (DLMF 9.10.5). -/
@[dlmf 9.10.E5]
theorem airyBi_integral_asymptotic  :
    (fun x : ℝ => primitive airyBi x) ~[atTop]
      (fun x : ℝ => ((Real.exp (airyZeta x) / (Real.sqrt π * x ^ (3 / 4 : ℝ)) : ℝ) : ℂ)) := by
  sorry

/-- airyAi negative integral asymptotic (DLMF 9.10.6). -/
@[dlmf 9.10.E6]
theorem airyAi_negative_integral_asymptotic  :
    IsBigO atBot (fun x : ℝ => improperAtBot (fun t => airyAi t) x -
      ((Real.cos (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) /
        (Real.sqrt π * (-x) ^ (3 / 4 : ℝ)) : ℝ) : ℂ))
      (fun x : ℝ => |x| ^ (-9 / 4 : ℝ)) := by
  sorry

/-- airyBi negative integral asymptotic (DLMF 9.10.7). -/
@[dlmf 9.10.E7]
theorem airyBi_negative_integral_asymptotic  :
    IsBigO atBot (fun x : ℝ => improperAtBot (fun t => airyBi t) x -
      ((Real.sin (2 / 3 * (-x) ^ (3 / 2 : ℝ) + π / 4) /
        (Real.sqrt π * (-x) ^ (3 / 4 : ℝ)) : ℝ) : ℂ))
      (fun x : ℝ => |x| ^ (-9 / 4 : ℝ)) := by
  sorry

/-- airy linear antiderivative (DLMF 9.10.8). -/
@[dlmf 9.10.E8]
theorem airy_linear_antiderivative {w w' : ℂ → ℂ} (hw : IsAirySol w w') (z : ℂ) :
    HasDerivAt w' (z * w z) z := by
  exact (hw z).2

/-- airy quadratic antiderivative (DLMF 9.10.9). -/
@[dlmf 9.10.E9]
theorem airy_quadratic_antiderivative {w w' : ℂ → ℂ} (hw : IsAirySol w w') (z : ℂ) :
    HasDerivAt (fun t => t * w' t - w t) (z ^ 2 * w z) z := by
  have h := ((hasDerivAt_id z).mul (hw z).2).sub (hw z).1
  exact h.congr_deriv (by simp only [id]; ring)

/-- airy moment antiderivative recurrence (DLMF 9.10.10). -/
@[dlmf 9.10.E10]
theorem airy_moment_antiderivative_recurrence {w w' : ℂ → ℂ} (hw : IsAirySol w w') (n : ℕ) (z : ℂ) :
    HasDerivAt (fun t => t ^ (n + 2) * w' t - (n + 2 : ℂ) * t ^ (n + 1) * w t)
      (z ^ (n + 3) * w z - (n + 1 : ℂ) * (n + 2 : ℂ) * z ^ n * w z) z := by
  have h := ((hasDerivAt_pow (n + 2) z).mul (hw z).2).sub
    (((hasDerivAt_pow (n + 1) z).mul (hw z).1).const_mul (n + 2 : ℂ))
  convert h using 1
  · funext t
    change t ^ (n + 2) * w' t - (n + 2 : ℂ) * t ^ (n + 1) * w t =
      t ^ (n + 2) * w' t - (n + 2 : ℂ) * (t ^ (n + 1) * w t)
    ring
  · simp only [Pi.mul_apply, show n + 2 - 1 = n + 1 by omega, show n + 1 - 1 = n by omega,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, pow_succ]
    ring

/-- airyAi positive integral (DLMF 9.10.11). -/
@[dlmf 9.10.E11]
theorem airyAi_positive_integral  :
    HasIntegralAtTop (fun t => airyAi t) 0 (1 / 3) := by
  sorry

/-- airyAi negative integral (DLMF 9.10.11). -/
@[dlmf 9.10.E11]
theorem airyAi_negative_integral  :
    HasIntegralAtBot (fun t => airyAi t) 0 (2 / 3) := by
  sorry

/-- airyBi negative integral (DLMF 9.10.12). -/
@[dlmf 9.10.E12]
theorem airyBi_negative_integral  :
    HasIntegralAtBot (fun t => airyBi t) 0 0 := by
  sorry

/-- airyAi bilateral laplace (DLMF 9.10.13). -/
@[dlmf 9.10.E13]
theorem airyAi_bilateral_laplace {p : ℂ} (hp : 0 < p.re) :
    Integrable (fun t : ℝ => exp (p * t) * airyAi t) ∧
      (∫ t : ℝ, exp (p * t) * airyAi t) = exp (p ^ 3 / 3) := by
  sorry

/-- airyAi laplace (DLMF 9.10.14). -/
@[dlmf 9.10.E14]
theorem airyAi_laplace (p : ℂ) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi t) = exp (-p ^ 3 / 3) *
        (1 / 3 - p * kummerM (1 / 3) (4 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (4 / 3 : ℂ) * Gamma (4 / 3)) +
          p ^ 2 * kummerM (2 / 3) (5 / 3) (p ^ 3 / 3) /
          ((3 : ℂ) ^ (5 / 3 : ℂ) * Gamma (5 / 3))) := by
  sorry

/-- airyAi negative laplace (DLMF 9.10.15). -/
@[dlmf 9.10.E15]
theorem airyAi_negative_laplace {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyAi (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyAi (-t)) = exp (p ^ 3 / 3) / 3 * (airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3) + airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3)) := by
  sorry

/-- airyBi negative laplace (DLMF 9.10.16). -/
@[dlmf 9.10.E16]
theorem airyBi_negative_laplace {p : ℂ} (hp : 0 < p.re) :
    IntegrableOn (fun t : ℝ => exp (-p * t) * airyBi (-t)) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, exp (-p * t) * airyBi (-t)) = exp (p ^ 3 / 3) / Real.sqrt 3 * (airyUpperGammaOnLog (2 / 3) (3 * log p - log 3) / Gamma (2 / 3) - airyUpperGammaOnLog (1 / 3) (3 * log p - log 3) / Gamma (1 / 3)) := by
  sorry

/-- airyAi mellin (DLMF 9.10.17). -/
@[dlmf 9.10.E17]
theorem airyAi_mellin {α : ℂ} (hα : 0 < α.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (α - 1) * airyAi t) (Ioi 0) ∧
      (∫ t : ℝ in Ioi 0, (t : ℂ) ^ (α - 1) * airyAi t) =
        Gamma α / ((3 : ℂ) ^ ((α + 2) / 3) * Gamma (α / 3 + 2 / 3)) := by
  sorry

/-- airyAi stieltjes (DLMF 9.10.18). -/
@[dlmf 9.10.E18]
theorem airyAi_stieltjes {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < 2 * π / 3) :
    airyAi z = 3 * z ^ (5 / 4 : ℂ) * exp (-airyZetaComplex z) / (4 * π) *
      ∫ t : ℝ in Ioi 0, (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / (z ^ (3 / 2 : ℂ) + (t : ℂ) ^ (3 / 2 : ℂ)) := by
  sorry

/-- airyBi stieltjes principalValue (DLMF 9.10.19). -/
@[dlmf 9.10.E19]
theorem airyBi_stieltjes_principalValue {x : ℝ} (hx : 0 < x) :
    airyBi x = 3 * (x : ℂ) ^ (5 / 4 : ℂ) * exp (airyZeta x) / (2 * π) *
      principalValueIoi (fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
        airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))) x := by
  sorry

/-- For a solution `w` of Airy's equation on the real line,
`∫₀ˣ ∫₀ᵛ w = x ∫₀ˣ w - w'(x) + w'(0)`. -/
lemma airySol_double_integral {w w' : ℂ → ℂ} (hw : IsAirySol w w') (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, w t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, w t) - w' x + w' 0 := by
  have hc : Continuous fun t : ℝ => w t :=
    (continuous_iff_continuousAt.mpr fun z => (hw z).1.continuousAt).comp continuous_ofReal
  have hP : ∀ v : ℝ, HasDerivAt (fun v : ℝ => ∫ t : ℝ in 0..v, w t) (w v) v := fun v =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
      (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have hPc : Continuous fun v : ℝ => ∫ t : ℝ in 0..v, w t :=
    continuous_iff_continuousAt.mpr fun v => (hP v).continuousAt
  have hH : ∀ v : ℝ, HasDerivAt (fun v : ℝ => (v : ℂ) * (∫ t : ℝ in 0..v, w t) - w' v)
      (∫ t : ℝ in 0..v, w t) v := by
    intro v
    have h1 := (hasDerivAt_id (v : ℂ)).comp_ofReal.mul (hP v)
    have h2 := (hw v).2.comp_ofReal
    exact (h1.sub h2).congr_deriv (by simp)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := x)
    (fun v _ => hH v) (hPc.intervalIntegrable _ _)
  rw [h]
  simp

/-- airyAi double integral (DLMF 9.10.20). -/
@[dlmf 9.10.E20]
theorem airyAi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyAi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyAi t) - airyAiDeriv x + airyAiDeriv 0 := by
  exact airySol_double_integral isAirySol_airyAi x

/-- airyBi double integral (DLMF 9.10.21). -/
@[dlmf 9.10.E21]
theorem airyBi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyBi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyBi t) - airyBiDeriv x + airyBiDeriv 0 := by
  exact airySol_double_integral isAirySol_airyBi x

/-- Repeated upper ordinary improper integrals, including the unintegrated base function. -/
def airyRepeatedTail : ℕ → ℝ → ℂ
  | 0 => fun t => airyAi (-t)
  | n + 1 => fun t => improperAtTop (airyRepeatedTail n) t

/-- airyAi repeated integrals (DLMF 9.10.22). -/
@[dlmf 9.10.E22]
theorem airyAi_repeated_integrals {n : ℕ} (hn : 1 ≤ n) :
    HasIntegralAtTop (airyRepeatedTail (n - 1)) 0
      (2 * cos (((n : ℂ) - 1) * π / 3) /
        ((3 : ℂ) ^ (((n : ℂ) + 2) / 3) * Gamma ((n : ℂ) / 3 + 2 / 3))) := by
  sorry

/-- Convergence of the symmetric principal value in DLMF 9.10.19. -/
@[dlmf 9.10.E19]
theorem airyBi_stieltjes_principalValue_converges {x : ℝ} (hx : 0 < x) :
    let f := fun t : ℝ => (t : ℂ) ^ (-3 / 4 : ℂ) * exp (-(airyZeta t : ℂ)) *
      airyAi t / ((x : ℂ) ^ (3 / 2 : ℂ) - (t : ℂ) ^ (3 / 2 : ℂ))
    HasPrincipalValueIoi f x (principalValueIoi f x) := by
  sorry

end AAR.Airy
