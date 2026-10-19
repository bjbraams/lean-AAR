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

/-- airyAi integral scorerGi (DLMF 9.10.1). -/
@[dlmf 9.10.E1]
theorem airyAi_integral_scorerGi (z : ℂ) :
    1 / 3 - primitive airyAi z = π * (airyAi z * scorerGiDeriv z - airyAiDeriv z * scorerGi z) := by
  sorry

/-- airyAi integral scorerHi (DLMF 9.10.2). -/
@[dlmf 9.10.E2]
theorem airyAi_integral_scorerHi (z : ℂ) :
    2 / 3 + primitive airyAi z = π * (airyAi z * scorerHiDeriv z - airyAiDeriv z * scorerHi z) := by
  sorry

/-- airyBi integral scorer (DLMF 9.10.3). -/
@[dlmf 9.10.E3]
theorem airyBi_integral_scorer (z : ℂ) :
    primitive airyBi z = π * (airyBiDeriv z * scorerGi z - airyBi z * scorerGiDeriv z) ∧
      primitive airyBi z = π * (airyBi z * scorerHiDeriv z - airyBiDeriv z * scorerHi z) := by
  sorry

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

/-- airyAi double integral (DLMF 9.10.20). -/
@[dlmf 9.10.E20]
theorem airyAi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyAi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyAi t) - airyAiDeriv x + airyAiDeriv 0 := by
  sorry

/-- airyBi double integral (DLMF 9.10.21). -/
@[dlmf 9.10.E21]
theorem airyBi_double_integral (x : ℝ) :
    (∫ v : ℝ in 0..x, ∫ t : ℝ in 0..v, airyBi t) =
      (x : ℂ) * (∫ t : ℝ in 0..x, airyBi t) - airyBiDeriv x + airyBiDeriv 0 := by
  sorry

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
