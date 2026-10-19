/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ParabolicCylinder.Basic
public import AAR.ErrorFunctions.Repeated
public import AAR.Confluent.Whittaker

/-!
# Parabolic cylinder special functions and addition formulas

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

/-- pcfV nat add half. -/
@[dlmf 12.7.E3]
theorem pcfV_nat_add_half (n : ℕ) (z : ℂ) :
    pcfV (n+1/2) z=(Real.sqrt (2/π):ℂ)*exp (z^2/4)*(-I)^n*Polynomial.aeval (I*z) (Polynomial.hermite n) := by
  rw [pcfV_eq_mul_I]
  rw [show (1/2:ℂ)-(n+1/2)=-(n:ℂ) by ring, Gamma_neg_nat_eq_zero]
  simp only [div_zero, zero_mul, zero_add]
  have hu := pcfD_nat n (I*z)
  simp only [pcfD] at hu
  rw [show -(n+1/2:ℂ)=-(n:ℂ)-1/2 by ring, hu]
  have he : exp (-I*π*((n+1/2:ℂ)/2-1/4))=(-I)^n := by
    rw [show -I*π*((n+1/2:ℂ)/2-1/4)=(n:ℂ)*(-π/2*I) by ring,
      Complex.exp_nat_mul, Complex.exp_neg_pi_div_two_mul_I]
  rw [he]
  have hz : -(I*z)^2/4=z^2/4 := by rw [mul_pow, I_sq]; ring
  rw [hz]
  ring

/-- pcfV neg half. -/
@[dlmf 12.7.E4]
theorem pcfV_neg_half (z : ℂ) :
    pcfV (-1/2) z=2/Real.sqrt π*exp (z^2/4)*dawsonF (z/Real.sqrt 2) := by
  sorry

/-- pcfU half. -/
@[dlmf 12.7.E5]
theorem pcfU_half (z : ℂ) :
    pcfU (1/2) z=(Real.sqrt (π/2):ℂ)*exp (z^2/4)*erfc (z/Real.sqrt 2) := by
  sorry

/-- pcfU nat add half deriv. -/
@[dlmf 12.7.E6]
theorem pcfU_nat_add_half_deriv (n : ℕ) (z : ℂ) :
    pcfU (n+1/2) z=(Real.sqrt (π/2):ℂ)*(-1)^n/(n.factorial:ℂ)*exp (-z^2/4)*iteratedDeriv n (fun z : ℂ => exp (z^2/2)*erfc (z/Real.sqrt 2)) z := by
  sorry

/-- hhFunction. -/
@[dlmf 12.7.E7]
def hhFunction (n : ℤ) (z : ℂ) : ℂ :=
  if n = -1 then exp (-z^2/2) else (∫ t : ℝ in Ioi 0, (t:ℂ)^n.toNat/(n.toNat.factorial:ℂ)*exp (-(z+t)^2/2))

/-- pcfU hh. -/
@[dlmf 12.7.E7]
theorem pcfU_hh (n : ℤ) (hn : -1 ≤ n) (z : ℂ) :
    pcfU (n+1/2) z=exp (z^2/4)*hhFunction n z ∧ pcfU (n+1/2) z=Real.sqrt π*2^(((n:ℂ)-1)/2)*exp (z^2/4)*iteratedErfc n (z/Real.sqrt 2) := by
  sorry

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E8]
theorem pcfU_bessel_8 {z : ℂ} (hz : 0 < z.re) :
    pcfU (-2) z=z^(5/2:ℂ)/(4*Real.sqrt (2*π))*(2*besselK (1/4) (z^2/4)+3*besselK (3/4) (z^2/4)-besselK (5/4) (z^2/4)) := by
  sorry

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E9]
theorem pcfU_bessel_9 {z : ℂ} (hz : 0 < z.re) :
    pcfU (-1) z=z^(3/2:ℂ)/(2*Real.sqrt (2*π))*(besselK (1/4) (z^2/4)+besselK (3/4) (z^2/4)) := by
  sorry

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E10]
theorem pcfU_bessel_10 {z : ℂ} (hz : 0 < z.re) :
    pcfU (0) z=(z/(2*π))^(1/2:ℂ)*besselK (1/4) (z^2/4) := by
  sorry

/-- Principal branches in the right half-plane; continuation elsewhere inherits the logarithm of z squared. -/
@[dlmf 12.7.E11]
theorem pcfU_bessel_11 {z : ℂ} (hz : 0 < z.re) :
    pcfU (1) z=z^(3/2:ℂ)/Real.sqrt (2*π)*(besselK (3/4) (z^2/4)-besselK (1/4) (z^2/4)) := by
  sorry

/-- pcfU kummerU odd. -/
@[dlmf 12.7.E14]
theorem pcfU_kummerU_odd (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    pcfU a z=2^(-3/4-a/2)*z*exp (-z^2/4)*kummerU (a/2+3/4) (3/2) (z^2/2) := by
  sorry

/-- pcfU whittaker. -/
@[dlmf 12.7.E14]
theorem pcfU_whittaker (a : ℂ) {z : ℂ} (hz : 0 < z.re) :
    pcfU a z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (1/4) (z^2/2) ∧ pcfU a z=2^(-a/2)*z^(-1/2:ℂ)*whittakerW (-a/2) (-1/4) (z^2/2) := by
  sorry

/-- pcfU addition 1. -/
@[dlmf 12.13.E1]
theorem pcfU_addition_1 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-y)^m/(m.factorial:ℂ))*pcfU (a-m) x) (pcfU a (x+y)) := by
  sorry

/-- pcfU addition 2. -/
@[dlmf 12.13.E2]
theorem pcfU_addition_2 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (-1*(x*y/2+y^2/4))*((-1)^m*poch (a+1/2) m*y^m/(m.factorial:ℂ))*pcfU (a+m) x) (pcfU a (x+y)) := by
  sorry

/-- pcfV addition 3. -/
@[dlmf 12.13.E3]
theorem pcfV_addition_3 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (1*(x*y/2+y^2/4))*((-1)^m*poch (1/2-a) m*y^m/(m.factorial:ℂ))*pcfV (a-m) x) (pcfV a (x+y)) := by
  sorry

/-- pcfV addition 4. -/
@[dlmf 12.13.E4]
theorem pcfV_addition_4 (a x y : ℂ) :
    HasSum (fun m : ℕ => exp (-1*(x*y/2+y^2/4))*(y^m/(m.factorial:ℂ))*pcfV (a+m) x) (pcfV a (x+y)) := by
  sorry

/-- pcfU rotational addition. -/
@[dlmf 12.13.E5]
theorem pcfU_rotational_addition {a : ℂ} (ha : a.re ≤ -1/2) (x y : ℂ) {t : ℝ} (ht : 0 ≤ t) (htπ : t ≤ π/4) (hend : t = π/4 → |y.im| ≤ x.re) :
    HasSum (fun m : ℕ => exp ((x*Real.sin t-y*Real.cos t)^2/4)*(-1)^m*poch (a+1/2) m/(m.factorial:ℂ)*(Real.tan t:ℂ)^m*pcfU (m+a) x*pcfU (-m-1/2) y) (pcfU a (x*Real.cos t+y*Real.sin t)) := by
  sorry

/- DLMF 12.13.6 as printed fails at n = 0, z = 0: the left side is
√(π/2), the right side 1. It is intentionally not admitted. See
`DLMF111214Acquisition.md` for the checked counterexample and source status. -/

end AAR.Confluent
