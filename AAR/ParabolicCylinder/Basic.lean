/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.DLMF.Framework
public import AAR.Confluent.ParabolicCylinder
public import AAR.Gamma.Digamma

/-!
# Additional parabolic cylinder definitions and entire dependence

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- IsQuadraticCylinderSolution. -/
@[dlmf 12.2.E1]
def IsQuadraticCylinderSolution (a b c : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(a*z^2+b*z+c)*f z=0

/-- IsOscillatoryCylinderSolution. -/
@[dlmf 12.2.E3]
def IsOscillatoryCylinderSolution (a : ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z, iteratedDeriv 2 f z+(z^2/4-a)*f z=0

/-- quadraticCylinder transform. -/
@[dlmf 12.2.E1]
theorem quadraticCylinder_transform {a b c s : ℂ} (ha : a ≠ 0) (hs : s^4 = -4*a) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (hf2 : Differentiable ℂ (deriv f)) (hode : ∀ z, iteratedDeriv 2 f z-(z^2/4+(b^2/(4*a)-c)/s^2)*f z=0) :
    IsQuadraticCylinderSolution a b c (fun z => f (s*(z+b/(2*a)))) := by
  sorry

/-- pcfD ode. -/
@[dlmf 12.2.E4]
theorem pcfD_ode (ν z : ℂ) :
    iteratedDeriv 2 (pcfD ν) z+(ν+1/2-z^2/4)*pcfD ν z=0 := by
  unfold pcfD
  rw [show iteratedDeriv 2 (pcfU (-ν-1/2)) z = deriv (deriv (pcfU (-ν-1/2))) z by rw [show 2=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one],
    deriv_deriv_pcfU]
  ring

/-- Entire dependence on the argument. -/
theorem pcfU_entire (a : ℂ) :
    Differentiable ℂ (pcfU a) := by
  intro z
  exact (hasDerivAt_pcfU a z).differentiableAt

/-- Entire dependence on the parameter. -/
theorem pcfU_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfU a z) := by
  sorry

/-- Reality on real parameters and arguments. -/
theorem pcfU_real (a x : ℝ) :
    (pcfU a x).im=0 := by
  sorry

/-- Entire dependence on the argument. -/
theorem pcfV_entire (a : ℂ) :
    Differentiable ℂ (pcfV a) := by
  intro z
  exact (hasDerivAt_pcfV a z).differentiableAt

/-- Entire dependence on the parameter. -/
theorem pcfV_entire_order (z : ℂ) :
    Differentiable ℂ (fun a => pcfV a z) := by
  sorry

/-- Reality on real parameters and arguments. -/
theorem pcfV_real (a x : ℝ) :
    (pcfV a x).im=0 := by
  sorry

/-- The barred U solution; meaningful only away from positive half-integral parameters, not complex conjugation. -/
@[dlmf 12.2.E21]
def pcfUBar (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfV a z

/-- pcfUBarDeriv. -/
def pcfUBarDeriv (a z : ℂ) : ℂ :=
  Gamma (1/2-a)*pcfVDeriv a z

/-- pcfF. -/
@[dlmf 12.2.E22]
def pcfF (a x : ℝ) : ℝ :=
  ‖pcfU a x+I*pcfUBar a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E22]
def pcfTheta (a x : ℝ) : ℝ :=
  arg ((pcfU a x+I*pcfUBar a x))

/-- pcfF phase. -/
@[dlmf 12.2.E22]
theorem pcfF_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < pcfF a x ∧ pcfU a x+I*pcfUBar a x=(pcfF a x*exp (I*pcfTheta a x)) := by
  sorry

/-- pcfG. -/
@[dlmf 12.2.E23]
def pcfG (a x : ℝ) : ℝ :=
  ‖pcfUDeriv a x+I*pcfUBarDeriv a x‖

/-- Principal phase representative; a continuous lift differs by integral multiples of two pi. -/
@[dlmf 12.2.E23]
def pcfPsi (a x : ℝ) : ℝ :=
  arg (-(pcfUDeriv a x+I*pcfUBarDeriv a x))

/-- pcfG phase. -/
@[dlmf 12.2.E23]
theorem pcfG_phase {a : ℝ} (ha : ∀ n : ℕ, a ≠ n+1/2) (x : ℝ) :
    0 < pcfG a x ∧ pcfUDeriv a x+I*pcfUBarDeriv a x=-(pcfG a x*exp (I*pcfPsi a x)) := by
  sorry

/-- pcfU rotated connection pos. -/
@[dlmf 12.2.E18]
theorem pcfU_rotated_connection_pos {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*pcfU a z=Gamma (1/2-a)*(exp (-(1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((1:ℂ)*I*z)+exp ((1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(1:ℂ)*I*z)) := by
  sorry

/-- pcfU rotated connection entire pos. -/
@[dlmf 12.2.E19]
theorem pcfU_rotated_connection_entire_pos (a z : ℂ) :
    pcfU a z=(1:ℂ)*I*exp ((1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((1:ℂ)*I*π*(a/2-1/4))*pcfU (-a) ((1:ℂ)*I*z) := by
  sorry

/-- pcfU rotated connection neg. -/
@[dlmf 12.2.E18]
theorem pcfU_rotated_connection_neg {a : ℂ} (ha : ∀ n : ℕ, a ≠ n+1/2) (z : ℂ) :
    (Real.sqrt (2*π):ℂ)*pcfU a z=Gamma (1/2-a)*(exp (-(-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) ((-1:ℂ)*I*z)+exp ((-1:ℂ)*I*π*(a/2+1/4))*pcfU (-a) (-(-1:ℂ)*I*z)) := by
  sorry

/-- pcfU rotated connection entire neg. -/
@[dlmf 12.2.E19]
theorem pcfU_rotated_connection_entire_neg (a z : ℂ) :
    pcfU a z=(-1:ℂ)*I*exp ((-1:ℂ)*I*π*a)*pcfU a (-z)+(Real.sqrt (2*π):ℂ)/Gamma (1/2+a)*exp ((-1:ℂ)*I*π*(a/2-1/4))*pcfU (-a) ((-1:ℂ)*I*z) := by
  sorry

/-- pcfEven series 3. -/
@[dlmf 12.4.E3]
theorem pcfEven_series_3 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+1/2+2*r))*z^(2*k)/((2*k).factorial:ℂ)) (pcfEven a z) := by
  sorry

/-- pcfEven series 5. -/
@[dlmf 12.4.E5]
theorem pcfEven_series_5 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-1/2-2*r))*z^(2*k)/((2*k).factorial:ℂ)) (pcfEven a z) := by
  sorry

/-- pcfOdd series 4. -/
@[dlmf 12.4.E4]
theorem pcfOdd_series_4 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (-1*z^2/4)*(∏ r ∈ Finset.range k, (a+3/2+2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ)) (pcfOdd a z) := by
  sorry

/-- pcfOdd series 6. -/
@[dlmf 12.4.E6]
theorem pcfOdd_series_6 (a z : ℂ) :
    HasSum (fun k : ℕ => exp (1*z^2/4)*(∏ r ∈ Finset.range k, (a-3/2-2*r))*z^(2*k+1)/((2*k+1).factorial:ℂ)) (pcfOdd a z) := by
  sorry

/-- pcfEven kummer alternative. -/
@[dlmf 12.7.E12]
theorem pcfEven_kummer_alternative (a z : ℂ) :
    pcfEven a z = exp (z^2/4)*kummerM (-a/2+1/4) (1/2) (-z^2/2) := by
  sorry

/-- pcfOdd kummer alternative. -/
@[dlmf 12.7.E13]
theorem pcfOdd_kummer_alternative (a z : ℂ) :
    pcfOdd a z = z*exp (z^2/4)*kummerM (-a/2+3/4) (3/2) (-z^2/2) := by
  sorry

/-- pcfU iterated deriv 9. -/
@[dlmf 12.8.E9]
theorem pcfU_iterated_deriv_9 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*pcfU a z) z = (-1)^m*poch (1/2+a) m*exp (1*z^2/4)*pcfU (a+m) z := by
  sorry

/-- pcfU iterated deriv 10. -/
@[dlmf 12.8.E10]
theorem pcfU_iterated_deriv_10 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*pcfU a z) z = (-1)^m*exp (-1*z^2/4)*pcfU (a-m) z := by
  sorry

/-- pcfV iterated deriv 11. -/
@[dlmf 12.8.E11]
theorem pcfV_iterated_deriv_11 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (1*z^2/4)*pcfV a z) z = 1*exp (1*z^2/4)*pcfV (a+m) z := by
  sorry

/-- pcfV iterated deriv 12. -/
@[dlmf 12.8.E12]
theorem pcfV_iterated_deriv_12 (a z : ℂ) (m : ℕ) :
    iteratedDeriv m (fun z : ℂ => exp (-1*z^2/4)*pcfV a z) z = (-1)^m*poch (1/2-a) m*exp (-1*z^2/4)*pcfV (a-m) z := by
  sorry

/-- The barred solution satisfies the U recurrences on its parameter domain. -/
theorem pcfUBar_recurrences {a : ℂ} (ha : ∀ n : ℤ, a ≠ n+1/2) (z : ℂ) :
    z*pcfUBar a z-pcfUBar (a-1) z+(a+1/2)*pcfUBar (a+1) z=0 ∧ pcfUBarDeriv a z+z/2*pcfUBar a z+(a+1/2)*pcfUBar (a+1) z=0 ∧ pcfUBarDeriv a z-z/2*pcfUBar a z+pcfUBar (a-1) z=0 ∧ 2*pcfUBarDeriv a z+pcfUBar (a-1) z+(a+1/2)*pcfUBar (a+1) z=0 := by
  sorry

/-- IsGeneralizedCylinderSolution. -/
@[dlmf 12.15.E1]
def IsGeneralizedCylinderSolution (ν lam : ℂ) (f : ℂ → ℂ) (z : ℂ) : Prop :=
  lam ≠ 0 ∧ iteratedDeriv 2 f z+(ν+1/lam-z^lam/lam^2)*f z=0

end AAR.Confluent
