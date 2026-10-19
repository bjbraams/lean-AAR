/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Integrals

/-!
# The oscillatory parabolic cylinder function W

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

open AAR.Bessel

/-- pcfWZero. -/
@[dlmf 12.14.E1]
def pcfWZero (a : ℝ) : ℝ :=
  2^(-3/4:ℝ)*Real.sqrt ‖Gamma (1/4+I*a/2)/Gamma (3/4+I*a/2)‖

/-- pcfWDerivZero. -/
@[dlmf 12.14.E2]
def pcfWDerivZero (a : ℝ) : ℝ :=
  -2^(-1/4:ℝ)*Real.sqrt ‖Gamma (3/4+I*a/2)/Gamma (1/4+I*a/2)‖

/-- pcfWEven. -/
@[dlmf 12.14.E15]
def pcfWEven (a z : ℂ) : ℂ :=
  pcfEven (-I*a) (exp (π*I/4)*z)

/-- pcfWOdd. -/
@[dlmf 12.14.E16]
def pcfWOdd (a z : ℂ) : ℂ :=
  exp (-π*I/4)*pcfOdd (-I*a) (exp (π*I/4)*z)

/-- pcfW. -/
@[dlmf 12.14.E8]
def pcfW (a : ℝ) (z : ℂ) : ℂ :=
  pcfWZero a*pcfWEven a z+pcfWDerivZero a*pcfWOdd a z

/-- pcfW initial. -/
@[dlmf 12.14.E1, dlmf 12.14.E2]
theorem pcfW_initial (a : ℝ) :
    pcfW a 0=pcfWZero a ∧ HasDerivAt (pcfW a) (pcfWDerivZero a) 0 := by
  sorry

/-- pcfW ode. -/
@[dlmf 12.2.E3]
theorem pcfW_ode (a : ℝ) :
    IsOscillatoryCylinderSolution a (pcfW a) := by
  sorry

/-- W is real on the real axis. -/
theorem pcfW_real (a x : ℝ) :
    (pcfW a x).im=0 := by
  sorry

/-- pcfW wronskian. -/
@[dlmf 12.14.E3]
theorem pcfW_wronskian (a : ℝ) (z : ℂ) :
    pcfW a z*(-deriv (pcfW a) (-z))-pcfW a (-z)*deriv (pcfW a) z=1 := by
  sorry

/-- pcfWK. -/
@[dlmf 12.14.E5]
def pcfWK (a : ℝ) : ℝ :=
  Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a)

/-- pcfWK inv. -/
@[dlmf 12.14.E5]
theorem pcfWK_inv (a : ℝ) :
    0 < pcfWK a ∧ (pcfWK a)⁻¹=Real.sqrt (1+Real.exp (2*π*a))+Real.exp (π*a) := by
  unfold pcfWK
  have hE : Real.exp (2*π*a)=(Real.exp (π*a))^2 := by
    rw [show 2*π*a=π*a+π*a by ring, Real.exp_add, pow_two]
  have hs:=Real.sq_sqrt (by positivity : 0 ≤ 1+Real.exp (2*π*a))
  have hp : 0 < Real.sqrt (1+Real.exp (2*π*a))-Real.exp (π*a) := by
    nlinarith [hE, Real.sqrt_nonneg (1+Real.exp (2*π*a)),Real.exp_pos (π*a)]
  refine ⟨hp, ?_⟩
  apply (mul_eq_one_iff_inv_eq₀ hp.ne').mp
  nlinarith [hE]

/-- Continuous argument of Gamma along the vertical line, normalized to zero at a=0. -/
@[dlmf 12.14.E7]
def pcfGammaPhase (a : ℝ) : ℝ :=
  ∫ t : ℝ in 0..a, (Complex.digamma (1/2+I*t)).re

/-- pcfGammaPhase spec. -/
@[dlmf 12.14.E7]
theorem pcfGammaPhase_spec (a : ℝ) :
    Gamma (1/2+I*a) = ‖Gamma (1/2+I*a)‖*exp (I*pcfGammaPhase a) := by
  sorry

/-- pcfWRho. -/
@[dlmf 12.14.E6]
def pcfWRho (a : ℝ) : ℝ :=
  π/8+pcfGammaPhase a/2

/-- pcfW connection. -/
@[dlmf 12.14.E4]
theorem pcfW_connection (a : ℝ) (z : ℂ) :
    pcfW a z=(Real.sqrt (pcfWK a/2):ℂ)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))+exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  sorry

/-- Unnumbered companion connection formula in DLMF 12.14(iv). -/
theorem pcfW_connection_neg (a : ℝ) (z : ℂ) :
    pcfW a (-z)=-I/Real.sqrt (2*pcfWK a)*exp (π*a/4)*(exp (I*pcfWRho a)*pcfU (I*a) (z*exp (-π*I/4))-exp (-I*pcfWRho a)*pcfU (-I*a) (z*exp (π*I/4))) := by
  sorry

/-- Maclaurin recurrence for the pcfWAlpha coefficients. -/
def pcfWAlpha (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWAlpha a (n+1)-1/2*(n+1)*(2*n+1)*pcfWAlpha a n

/-- Maclaurin recurrence for the pcfWBeta coefficients. -/
def pcfWBeta (a : ℂ) : ℕ → ℂ
  | 0 => 1
  | 1 => a
  | n+2 => a*pcfWBeta a (n+1)-1/2*(n+1)*(2*n+3)*pcfWBeta a n

/-- pcfWEven series. -/
@[dlmf 12.14.E9, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWEven_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWAlpha a n*z^(2*n)/((2*n).factorial:ℂ)) (pcfWEven a z) := by
  sorry

/-- pcfWOdd series. -/
@[dlmf 12.14.E10, dlmf 12.14.E11, dlmf 12.14.E12]
theorem pcfWOdd_series (a z : ℂ) :
    HasSum (fun n : ℕ => pcfWBeta a n*z^(2*n+1)/((2*n+1).factorial:ℂ)) (pcfWOdd a z) := by
  sorry

/-- pcfWEven kummer. -/
@[dlmf 12.14.E15]
theorem pcfWEven_kummer (a z : ℂ) :
    pcfWEven a z = exp (-I*z^2/4)*kummerM (1/4-I*a/2) (1/2) (I*z^2/2) ∧ pcfWEven a z = exp (I*z^2/4)*kummerM (1/4+I*a/2) (1/2) (-I*z^2/2) := by
  sorry

/-- pcfWOdd kummer. -/
@[dlmf 12.14.E16]
theorem pcfWOdd_kummer (a z : ℂ) :
    pcfWOdd a z = z*exp (-I*z^2/4)*kummerM (3/4-I*a/2) (3/2) (I*z^2/2) ∧ pcfWOdd a z = z*exp (I*z^2/4)*kummerM (3/4+I*a/2) (3/2) (-I*z^2/2) := by
  sorry

/-- pcfW zero bessel 1. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_1 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(1:ℂ)*besselJ (1/4) (x^2/4)) := by
  sorry

/-- pcfW zero bessel deriv 1. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_1 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  sorry

/-- pcfW zero bessel 2. -/
@[dlmf 12.14.E13]
theorem pcfW_zero_bessel_2 {x : ℝ} (hx : 0 < x) :
    pcfW 0 (-1*x)=2^(-5/4:ℂ)*(π*x:ℂ)^(1/2:ℂ)*(besselJ (-1/4) (x^2/4)-(-1:ℂ)*besselJ (1/4) (x^2/4)) := by
  sorry

/-- pcfW zero bessel deriv 2. -/
@[dlmf 12.14.E14]
theorem pcfW_zero_bessel_deriv_2 {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => pcfW 0 (-1*t)) (-2^(-9/4:ℂ)*x*(π*x:ℂ)^(1/2:ℂ)*(besselJ (3/4) (x^2/4)+(-1:ℂ)*besselJ (-3/4) (x^2/4))) x := by
  sorry

/-- pcfWOmega. -/
@[dlmf 12.14.E19]
def pcfWOmega (a x : ℝ) : ℝ :=
  x^2/4-a*Real.log x+π/4+pcfGammaPhase a/2

/-- Combined exact amplitude s1+i s2, recovered from the two real W solutions. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
def pcfWS (a x : ℝ) : ℂ :=
  exp (-I*pcfWOmega a x)*(Real.sqrt (x/(2*pcfWK a))*pcfW a x+I*Real.sqrt (pcfWK a*x/2)*pcfW a (-x))

/-- pcfW amplitude. -/
@[dlmf 12.14.E17, dlmf 12.14.E18]
theorem pcfW_amplitude (a : ℝ) {x : ℝ} (hx : 0 < x) :
    pcfW a x=Real.sqrt (2*pcfWK a/x)*((pcfWS a x).re*Real.cos (pcfWOmega a x)-(pcfWS a x).im*Real.sin (pcfWOmega a x)) ∧ pcfW a (-x)=Real.sqrt (2/(pcfWK a*x))*((pcfWS a x).re*Real.sin (pcfWOmega a x)+(pcfWS a x).im*Real.cos (pcfWOmega a x)) := by
  sorry

/-- pcfWCoeff. -/
@[dlmf 12.14.E22]
def pcfWCoeff (a : ℝ) (r : ℕ) : ℂ :=
  poch (1/2+I*a) (2*r)

/- DLMF 12.14.22 is Mathlib's `Complex.Gamma_add_nat_div_Gamma_eq`,
with z=1/2+i*a and n=2*r. The real part of z is positive, so its regularity
hypothesis holds. `pcfWCoeff` uses the equivalent Pochhammer definition.
This upstream gamma-ratio identity is not reproved here. -/

/-- pcfWS asymptotic. -/
@[dlmf 12.14.E20, dlmf 12.14.E21, dlmf 12.14.E23]
theorem pcfWS_asymptotic (a : ℝ) (N : ℕ) :
    (fun x : ℝ => pcfWS a x-∑ r ∈ Finset.range N, (-I)^r*pcfWCoeff a r/(2^r*(r.factorial:ℂ)*(x:ℂ)^(2*r))) =O[atTop] (fun x : ℝ => (x:ℂ)^(-(2*N:ℤ))) := by
  sorry

/-- pcfWF. -/
@[dlmf 12.14.E37]
def pcfWF (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)‖

/-- pcfWTheta. -/
@[dlmf 12.14.E37]
def pcfWTheta (a x : ℝ) : ℝ :=
  arg ((1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)))

/-- pcfWF phase. -/
@[dlmf 12.14.E37]
theorem pcfWF_phase (a x : ℝ) :
    0 < pcfWF a x ∧ 1/Real.sqrt (pcfWK a)*(pcfW a) x+I*Real.sqrt (pcfWK a)*(pcfW a) (-x)=(pcfWF a x*exp (I*pcfWTheta a x)) := by
  sorry

/-- pcfWG. -/
@[dlmf 12.14.E38]
def pcfWG (a x : ℝ) : ℝ :=
  ‖1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)‖

/-- pcfWPsi. -/
@[dlmf 12.14.E38]
def pcfWPsi (a x : ℝ) : ℝ :=
  arg (-(1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)))

/-- pcfWG phase. -/
@[dlmf 12.14.E38]
theorem pcfWG_phase (a x : ℝ) :
    0 < pcfWG a x ∧ 1/Real.sqrt (pcfWK a)*(deriv (pcfW a)) x+I*Real.sqrt (pcfWK a)*(deriv (pcfW a)) (-x)=-(pcfWG a x*exp (I*pcfWPsi a x)) := by
  sorry

end AAR.Confluent
