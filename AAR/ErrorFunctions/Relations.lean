/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Basic

/-!
# Symmetries, differential identities and interrelations, DLMF §§7.4–7.5 and 7.10–7.11

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- erf negative. -/
@[dlmf 7.4.E1]
theorem erf_negative (z : ℂ) :
    erf (-z)=-erf z := by
  simp [erf]

/-- erfc negative. -/
@[dlmf 7.4.E2]
theorem erfc_negative (z : ℂ) :
    erfc (-z)=2-erfc z := by
  simp [erfc, erf_negative]
  ring

/-- faddeevaW negative. -/
@[dlmf 7.4.E3]
theorem faddeevaW_negative (z : ℂ) :
    faddeevaW (-z)=2*exp (-z^2)-faddeevaW z := by
  simp only [faddeevaW, neg_sq, mul_neg, erfc_negative]
  ring

/-- dawsonF negative. -/
@[dlmf 7.4.E4]
theorem dawsonF_negative (z : ℂ) :
    dawsonF (-z)=-dawsonF z := by
  sorry

/-- fresnel negative. -/
@[dlmf 7.4.E5]
theorem fresnel_negative (z : ℂ) :
    fresnelCosInt (-z) = -fresnelCosInt z ∧ fresnelSinInt (-z) = -fresnelSinInt z := by
  sorry

/-- fresnel mul I. -/
@[dlmf 7.4.E6]
theorem fresnel_mul_I (z : ℂ) :
    fresnelCosInt (I*z) = I*fresnelCosInt z ∧ fresnelSinInt (I*z) = -I*fresnelSinInt z := by
  sorry

/-- fresnelAux mul I. -/
@[dlmf 7.4.E7]
theorem fresnelAux_mul_I (z : ℂ) :
    fresnelAuxFComplex (I*z)=exp (π*I/4-π*I*z^2/2)/Real.sqrt 2-I*fresnelAuxFComplex z ∧ fresnelAuxGComplex (I*z)=exp (-π*I/4-π*I*z^2/2)/Real.sqrt 2+I*fresnelAuxGComplex z := by
  sorry

/-- fresnelAux negative. -/
@[dlmf 7.4.E8]
theorem fresnelAux_negative (z : ℂ) :
    fresnelAuxFComplex (-z)=Real.sqrt 2*cos (π/4+π*z^2/2)-fresnelAuxFComplex z ∧ fresnelAuxGComplex (-z)=Real.sqrt 2*sin (π/4+π*z^2/2)-fresnelAuxGComplex z := by
  sorry

/-- dawsonF faddeeva. -/
@[dlmf 7.5.E1]
theorem dawsonF_faddeeva (z : ℂ) :
    dawsonF z = I*Real.sqrt π/2*(exp (-z^2)-faddeevaW z) ∧ dawsonF z = -I*Real.sqrt π/2*exp (-z^2)*erf (I*z) := by
  sorry

/-- fresnel sum tail. -/
@[dlmf 7.5.E2]
theorem fresnel_sum_tail (z : ℂ) :
    fresnelCosInt z+I*fresnelSinInt z=(1+I)/2-fresnelTail z := by
  unfold fresnelTail
  ring

/-- fresnelCosInt aux. -/
@[dlmf 7.5.E3]
theorem fresnelCosInt_aux (z : ℂ) :
    fresnelCosInt z=1/2+fresnelAuxFComplex z*sin (π*z^2/2)-fresnelAuxGComplex z*cos (π*z^2/2) := by
  sorry

/-- fresnelSinInt aux. -/
@[dlmf 7.5.E4]
theorem fresnelSinInt_aux (z : ℂ) :
    fresnelSinInt z=1/2-fresnelAuxFComplex z*cos (π*z^2/2)-fresnelAuxGComplex z*sin (π*z^2/2) := by
  sorry

/-- fresnelTail aux. -/
@[dlmf 7.5.E5]
theorem fresnelTail_aux (z : ℂ) :
    exp (-π*I*z^2/2)*fresnelTail z=fresnelAuxGComplex z+I*fresnelAuxFComplex z := by
  sorry

/-- fresnel signed tail. -/
@[dlmf 7.5.E6]
theorem fresnel_signed_tail (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    exp (ε*π*I*z^2/2)*(fresnelAuxGComplex z+ε*I*fresnelAuxFComplex z)=(1+ε*I)/2-(fresnelCosInt z+ε*I*fresnelSinInt z) := by
  sorry

/-- Signed Fresnel-to-Gaussian change of variable. -/
@[dlmf 7.5.E7]
def fresnelZetaComplex (ε : ℝ) (z : ℂ) : ℂ :=
  Real.sqrt π/2*(1-ε*I)*z

/-- fresnel signed erf. -/
@[dlmf 7.5.E8]
theorem fresnel_signed_erf (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelCosInt z+ε*I*fresnelSinInt z=(1+ε*I)/2*erf (fresnelZetaComplex ε z) := by
  sorry

/-- fresnel signed faddeeva. -/
@[dlmf 7.5.E9]
theorem fresnel_signed_faddeeva (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelCosInt z+ε*I*fresnelSinInt z=(1+ε*I)/2*(1-exp (ε*π*I*z^2/2)*faddeevaW (I*fresnelZetaComplex ε z)) := by
  sorry

/-- fresnelAux signed erfc. -/
@[dlmf 7.5.E10]
theorem fresnelAux_signed_erfc (z : ℂ) {ε : ℝ} (hε : ε=1 ∨ ε = -1) :
    fresnelAuxGComplex z+ε*I*fresnelAuxFComplex z=(1+ε*I)/2*exp ((fresnelZetaComplex ε z)^2)*erfc (fresnelZetaComplex ε z) := by
  sorry

/-- fresnelTail norm sq nonneg. -/
@[dlmf 7.5.E11]
theorem fresnelTail_norm_sq_nonneg {x : ℝ} (hx : 0 ≤ x) :
    ‖fresnelTail x‖^2 = fresnelAuxF x^2+fresnelAuxG x^2 := by
  sorry

/-- fresnelTail norm sq nonpos. -/
@[dlmf 7.5.E12]
theorem fresnelTail_norm_sq_nonpos {x : ℝ} (hx : x ≤ 0) :
    ‖fresnelTail x‖^2 = 2+fresnelAuxF (-x)^2+fresnelAuxG (-x)^2-2*Real.sqrt 2*Real.cos (π/4+π*x^2/2)*fresnelAuxF (-x)-2*Real.sqrt 2*Real.cos (π/4-π*x^2/2)*fresnelAuxG (-x) := by
  sorry

/-- goodwinStatonG dawson. -/
@[dlmf 7.5.E13]
theorem goodwinStatonG_dawson {x : ℝ} (hx : 0 < x) :
    goodwinStatonG x=Real.sqrt π*dawsonF x-Real.exp (-x^2)/2*Real.expIntEi (x^2) := by
  sorry

/-- iteratedDeriv erf hermite. -/
@[dlmf 7.10.E1]
theorem iteratedDeriv_erf_hermite (n : ℕ) (z : ℂ) :
    iteratedDeriv (n+1) erf z = (-1 : ℂ)^n*2/Real.sqrt π*hermitePolyHEval n z*exp (-z^2) := by
  sorry

/-- hasDerivAt faddeevaW. -/
@[dlmf 7.10.E2]
theorem hasDerivAt_faddeevaW (z : ℂ) :
    HasDerivAt faddeevaW (-2*z*faddeevaW z+2*I/Real.sqrt π) z := by
  sorry

/-- iteratedDeriv faddeevaW recurrence. -/
@[dlmf 7.10.E3]
theorem iteratedDeriv_faddeevaW_recurrence (n : ℕ) (z : ℂ) :
    iteratedDeriv (n+2) faddeevaW z+2*z*iteratedDeriv (n+1) faddeevaW z+2*(n+1)*iteratedDeriv n faddeevaW z=0 := by
  sorry

/-- hasDerivAt fresnelAux. -/
@[dlmf 7.10.E4]
theorem hasDerivAt_fresnelAux (z : ℂ) :
    HasDerivAt fresnelAuxFComplex (-π*z*fresnelAuxGComplex z) z ∧ HasDerivAt fresnelAuxGComplex (π*z*fresnelAuxFComplex z-1) z := by
  sorry

/-- erf lowerIncGamma. -/
@[dlmf 7.11.E1]
theorem erf_lowerIncGamma {z : ℂ} (hz : 0 < z.re) :
    erf z=lowerIncGamma (1/2) (z^2)/Real.sqrt π := by
  sorry

/-- erfc upperIncGamma. -/
@[dlmf 7.11.E2]
theorem erfc_upperIncGamma {z : ℂ} (hz : 0 < z.re) :
    erfc z=upperIncGamma (1/2) (z^2)/Real.sqrt π := by
  sorry

/-- erfc genExpIntE. -/
@[dlmf 7.11.E3]
theorem erfc_genExpIntE {z : ℂ} (hz : 0 < z.re) :
    erfc z=z/Real.sqrt π*genExpIntE (1/2) (z^2) := by
  sorry

/-- erf kummerM pair. -/
@[dlmf 7.11.E4]
theorem erf_kummerM_pair (z : ℂ) :
    erf z=2*z/Real.sqrt π*kummerM (1/2) (3/2) (-z^2) ∧ erf z=2*z/Real.sqrt π*exp (-z^2)*kummerM 1 (3/2) (z^2) := by
  sorry

/-- erfc kummerU pair. -/
@[dlmf 7.11.E5]
theorem erfc_kummerU_pair {z : ℂ} (hz : 0 < z.re) :
    erfc z=exp (-z^2)/Real.sqrt π*kummerU (1/2) (1/2) (z^2) ∧ erfc z=z/Real.sqrt π*exp (-z^2)*kummerU 1 (3/2) (z^2) := by
  sorry

/-- fresnel kummerM pair. -/
@[dlmf 7.11.E6]
theorem fresnel_kummerM_pair (z : ℂ) :
    fresnelCosInt z+I*fresnelSinInt z=z*kummerM (1/2) (3/2) (π*I*z^2/2) ∧ fresnelCosInt z+I*fresnelSinInt z=z*exp (π*I*z^2/2)*kummerM 1 (3/2) (-π*I*z^2/2) := by
  sorry

/-- fresnelCosInt hypergeometric. -/
@[dlmf 7.11.E7]
theorem fresnelCosInt_hypergeometric (z : ℂ) :
    fresnelCosInt z=z*Gamma (5/4)*Gamma (1/2)*regularizedHGFun {1/4} {5/4,1/2} (-π^2*z^4/16) := by
  sorry

/-- fresnelSinInt hypergeometric. -/
@[dlmf 7.11.E8]
theorem fresnelSinInt_hypergeometric (z : ℂ) :
    fresnelSinInt z=π*z^3/6*Gamma (7/4)*Gamma (3/2)*regularizedHGFun {3/4} {7/4,3/2} (-π^2*z^4/16) := by
  sorry

end AAR.Confluent
