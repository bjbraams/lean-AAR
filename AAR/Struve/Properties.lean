/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Struve.Basic
public import AAR.Bessel.Elementary
public import AAR.Struve.Poisson

/-!
# Struve half-integer orders, recurrences and Bessel expansions

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.

The proved calculus uses the regularized quadratic gauge from `Basic`; integral
orders extend across the origin by entire-function uniqueness. Half-integer
formulas reuse the proved Bessel derivative ladders and elementary values.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Struve

open AAR.Bessel

/-- struveH neg nat sub half. -/
@[dlmf 11.4.E3]
theorem struveH_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-n-1/2) z = (-1)^n*besselJ (n+1/2) z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul]
    rw [struveH,struveHCore_eq_regularized,besselJ_eq_regularized]
    norm_num only
    rw [regularized1F2_one_one]
    congr 2; ring
  | succ n ih =>
    have hd := hasDerivAt_struveQuadratic (-(n:ℂ)-1/2) (-1) hz
    rw [funext (struveQuadratic_H (-(n:ℂ)-1/2))] at hd
    simp only [struveQuadratic_H] at hd
    have hev : struveH (-(n:ℂ)-1/2)=ᶠ[𝓝 z] (fun w => (-1:ℂ)^n*besselJ (n+1/2) w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd.deriv
    rw [hev.deriv_eq,deriv_const_mul_field,(hasDerivAt_besselJ (ν:=(n:ℂ)+1/2) hz).deriv,ih hz] at he
    push_cast
    rw [show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring,
      show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    rw [pow_succ]
    linear_combination -he

/-- struveL neg nat sub half. -/
@[dlmf 11.4.E4]
theorem struveL_neg_nat_sub_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-n-1/2) z = besselI (n+1/2) z := by
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul]
    rw [struveL,struveLCore_eq_regularized,besselI]
    norm_num only
    rw [regularized1F2_one_one]
  | succ n ih =>
    have hd := hasDerivAt_struveQuadratic (-(n:ℂ)-1/2) 1 hz
    rw [funext (struveQuadratic_L (-(n:ℂ)-1/2))] at hd
    simp only [struveQuadratic_L] at hd
    have hev : struveL (-(n:ℂ)-1/2)=ᶠ[𝓝 z] (fun w => besselI (n+1/2) w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd.deriv
    rw [hev.deriv_eq,(hasDerivAt_besselI (ν:=(n:ℂ)+1/2) hz).deriv,ih hz] at he
    push_cast
    rw [show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring,
      show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    linear_combination -he

/-- The reciprocal half-power forcing has the standard Bessel normalization. -/
theorem struve_half_prefactor {z : ℂ} (hz : z∈slitPlane) :
    (z/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ)=(2/(π*z))^(1/2:ℂ) := by
  have hp : (π:ℂ)^(1/2:ℂ)=(Real.sqrt π:ℂ) :=
    Complex.Gamma_one_half_eq.symm.trans AAR.Confluent.Gamma_one_half_eq_sqrt
  rw [cpow_half_inv_div_two hz,cpow_half_two_div_pi_z hz,cpow_half_div_pi,hp]
  ring

/-- The other elementary half-power shares the inherited slit-plane branch. -/
theorem struve_positive_half_prefactor {z : ℂ} (hz : z∈slitPlane) :
    (z/(2*π))^(1/2:ℂ)=(z/2)^(1/2:ℂ)/(Real.sqrt π:ℂ) ∧
      (z/2)^(1/2:ℂ)/(Real.sqrt π:ℂ)=(2/(π*z))^(1/2:ℂ)*z/2 := by
  have hz0 := slitPlane_ne_zero hz
  have hp : (π:ℂ)^(1/2:ℂ)=(Real.sqrt π:ℂ) :=
    Complex.Gamma_one_half_eq.symm.trans AAR.Confluent.Gamma_one_half_eq_sqrt
  constructor
  · rw [show z/(2*π)=(((π:ℝ)⁻¹:ℝ):ℂ)*(z/2) by push_cast; ring,
      AAR.Confluent.ofReal_mul_cpow_of_pos (by positivity) (div_ne_zero hz0 (by norm_num)) (1/2:ℂ),
      Complex.ofReal_inv,inv_cpow_ofReal_nonneg Real.pi_pos.le,hp]
    ring
  · have he : (z/2)^(1/2:ℂ)=(z/2)^(-(1/2):ℂ)*(z/2) := by
      calc
        (z/2)^(1/2:ℂ)=(z/2)^(-(1/2)+1:ℂ) := by congr 1; ring
        _ = _ := by rw [cpow_add _ _ (div_ne_zero hz0 (by norm_num)),cpow_one]
    rw [he]
    linear_combination (z/2)*(struve_half_prefactor hz)

/-- Rotating the entire 0F1 series gives the modified half-integer Bessel values. -/
theorem besselI_elementary_halves {z : ℂ} (hz : z∈slitPlane) :
    besselI (1/2) z=(2/(π*z))^(1/2:ℂ)*sinh z ∧
      besselI (-(1/2)) z=(2/(π*z))^(1/2:ℂ)*cosh z := by
  have hz0 := slitPlane_ne_zero hz
  have hs := regularized0F1_three_halves_eq_sinc (mul_ne_zero I_ne_zero hz0 : I*z≠0)
  have hc := regularized0F1_half_eq_cos (z:=I*z)
  have ha : -((I*z)^2/4)=z^2/4 := by simp [mul_pow,I_sq]; ring
  have hsin : sin (I*z)=I*sinh z := by rw [mul_comm I,sin_mul_I]; ring
  have hcos : cos (I*z)=cosh z := by rw [mul_comm I,cos_mul_I]
  rw [ha,hsin] at hs
  rw [ha,hcos] at hc
  have hs' : regularizedHGFun ∅ {3/2} (z^2/4)=2*sinh z/(z*Gamma (1/2)) := by
    rw [hs]
    field_simp
  constructor
  · rw [besselI,show (1/2:ℂ)+1=3/2 by ring,hs',← bessel_half_prefactor hz]
    field_simp
  · rw [besselI,show -(1/2:ℂ)+1=1/2 by ring,hc,AAR.Confluent.Gamma_one_half_eq_sqrt]
    linear_combination cosh z*(struve_half_prefactor hz)

/-- struve special 6. -/
@[dlmf 11.4.E6]
theorem struve_special_6 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-1/2) z = (2/(π*z))^(1/2:ℂ)*sin z := by
  rw [show (-1:ℂ)/2= -(1/2) by ring]
  have h : struveH (-(1/2)) z=besselJ (1/2) z := by
    simpa only [Nat.cast_zero,neg_zero,zero_sub,pow_zero,one_mul,zero_add] using struveH_neg_nat_sub_half 0 hz
  exact h.trans (besselJ_half z hz)

/-- struve special 10. -/
@[dlmf 11.4.E10]
theorem struve_special_10 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cos z-sin z/z) := by
  have hs := struveH_neg_nat_sub_half 1 hz
  have hr := besselJ_add_sub (ν:=(1/2:ℂ)) (slitPlane_ne_zero hz)
  norm_num only [Nat.cast_one,pow_one] at hs
  rw [show (-3:ℂ)/2= -(3/2) by ring,hs]
  rw [show (1/2:ℂ)-1= -(1/2) by ring,show (1/2:ℂ)+1=3/2 by ring,
    besselJ_half z hz,besselJ_neg_half z hz] at hr
  linear_combination hr

/-- struve special 5. -/
@[dlmf 11.4.E5]
theorem struve_special_5 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (1/2) z = (2/(π*z))^(1/2:ℂ)*(1-cos z) := by
  have hr := struveQuadratic_recurrence (-(1/2)) (-1) hz
  simp only [struveQuadratic_H,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show -(1/2:ℂ)-1= -3/2 by ring,show -(1/2:ℂ)+1=1/2 by ring,
    show -(1/2:ℂ)+3/2=1 by ring,Gamma_one,mul_one,
    show -(1/2:ℂ)=(-1:ℂ)/2 by ring,struve_special_10 hz,struve_special_6 hz] at hr
  rw [show (-1:ℂ)/2= -(1/2) by ring,struve_half_prefactor hz] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hr

/-- struve special 8. -/
@[dlmf 11.4.E8]
theorem struve_special_8 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-1/2) z = (2/(π*z))^(1/2:ℂ)*sinh z := by
  have he : struveL (-(1/2)) z=besselI (1/2) z := by
    simpa only [Nat.cast_zero,neg_zero,zero_sub,zero_add] using struveL_neg_nat_sub_half 0 hz
  rw [show (-1:ℂ)/2= -(1/2) by ring]
  exact he.trans (besselI_elementary_halves hz).1

/-- struve special 12. -/
@[dlmf 11.4.E12]
theorem struve_special_12 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (-3/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-sinh z/z) := by
  have hs := struveL_neg_nat_sub_half 1 hz
  have hr := besselI_sub_add (ν:=(1/2:ℂ)) (slitPlane_ne_zero hz)
  norm_num only [Nat.cast_one] at hs
  rw [show (-3:ℂ)/2= -(3/2) by ring,hs]
  rw [show (1/2:ℂ)-1= -(1/2) by ring,show (1/2:ℂ)+1=3/2 by ring,
    (besselI_elementary_halves hz).1,(besselI_elementary_halves hz).2] at hr
  linear_combination hr

/-- struve special 7. -/
@[dlmf 11.4.E7]
theorem struve_special_7 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (1/2) z = (2/(π*z))^(1/2:ℂ)*(cosh z-1) := by
  have hr := struveQuadratic_recurrence (-(1/2)) 1 hz
  simp only [struveQuadratic_L,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show -(1/2:ℂ)-1= -3/2 by ring,show -(1/2:ℂ)+1=1/2 by ring,
    show -(1/2:ℂ)+3/2=1 by ring,Gamma_one,mul_one,
    show -(1/2:ℂ)=(-1:ℂ)/2 by ring,struve_special_12 hz,struve_special_8 hz] at hr
  rw [show (-1:ℂ)/2= -(1/2) by ring,struve_half_prefactor hz] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) -hr

/-- struve special 9. -/
@[dlmf 11.4.E9]
theorem struve_special_9 {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (3/2) z = (z/(2*π))^(1/2:ℂ)*(1+2/z^2)-(2/(π*z))^(1/2:ℂ)*(sin z+cos z/z) := by
  have hr := struveQuadratic_recurrence (1/2) (-1) hz
  simp only [struveQuadratic_H,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show (1/2:ℂ)-1= -1/2 by ring,show (1/2:ℂ)+1=3/2 by ring,
    show (1/2:ℂ)+3/2=2 by ring,show Gamma (2:ℂ)=1 by simpa using Gamma_nat_eq_factorial 1,
    mul_one,struve_special_6 hz,struve_special_5 hz] at hr
  rw [(struve_positive_half_prefactor hz).1,(struve_positive_half_prefactor hz).2]
  rw [(struve_positive_half_prefactor hz).2] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) hr

/-- struve special 11. -/
@[dlmf 11.4.E11]
theorem struve_special_11 {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (3/2) z = -(z/(2*π))^(1/2:ℂ)*(1-2/z^2)+(2/(π*z))^(1/2:ℂ)*(sinh z-cosh z/z) := by
  have hr := struveQuadratic_recurrence (1/2) 1 hz
  simp only [struveQuadratic_L,neg_one_mul,sub_neg_eq_add,one_mul] at hr
  rw [show (1/2:ℂ)-1= -1/2 by ring,show (1/2:ℂ)+1=3/2 by ring,
    show (1/2:ℂ)+3/2=2 by ring,show Gamma (2:ℂ)=1 by simpa using Gamma_nat_eq_factorial 1,
    mul_one,struve_special_8 hz,struve_special_7 hz] at hr
  rw [(struve_positive_half_prefactor hz).1,(struve_positive_half_prefactor hz).2]
  rw [(struve_positive_half_prefactor hz).2] at hr
  linear_combination (norm := (field_simp [slitPlane_ne_zero hz]; ring)) -hr

/-- Factorial coefficient of a half-integer Struve Laurent polynomial. -/
def struveHalfCoeff (n m : ℕ) : ℂ :=
  ((2*m).factorial:ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)

/-- The signed finite Laurent polynomial occurring at positive half-integer orders. -/
def struveHalfPoly (σ : ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ m∈Finset.range (n+1), σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)

/-- Shifting the summation index multiplies its coefficient by the next odd factor. -/
theorem struveHalfCoeff_succ (n m : ℕ) :
    struveHalfCoeff (n+1) (m+1)=struveHalfCoeff n m*(2*m+1)/2 := by
  unfold struveHalfCoeff
  rw [show 2*(m+1)=(2*m+1)+1 by omega,Nat.factorial_succ,Nat.factorial_succ,Nat.factorial_succ,
    Nat.add_sub_add_right]
  push_cast
  rw [show -(2*((m:ℤ)+1))= -(2*m)-2 by ring,zpow_sub₀ (by norm_num)]
  norm_num only [zpow_ofNat]
  field_simp
  ring

/-- The finite polynomial ladder includes its new leading monomial. -/
theorem struveHalfPoly_succ (σ : ℂ) (n : ℕ) {z : ℂ} (hz : z≠0) :
    struveHalfPoly σ (n+1) z=(z/2)^(n+1)/(n+1).factorial+
      σ/z*∑ m∈Finset.range (n+1), (2*m+1)*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m) := by
  rw [struveHalfPoly,Finset.sum_range_succ']
  simp only [pow_zero,struveHalfCoeff,Nat.mul_zero,Nat.factorial_zero,Int.natCast_zero,
    mul_zero,neg_zero,zpow_zero,one_mul,mul_one,Nat.sub_zero,sub_zero,zpow_natCast]
  rw [add_comm]
  congr 1
  · norm_num
    ring
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    change σ^(m+1)*struveHalfCoeff (n+1) (m+1)*(z/2)^(((n+1:ℕ):ℤ)-2*(m+1))=_
    rw [struveHalfCoeff_succ,pow_succ]
    have he : ((n+1:ℕ):ℤ)-2*(m+1)=(n:ℤ)-2*m-1 := by push_cast; ring
    rw [he,zpow_sub₀ (div_ne_zero hz (by norm_num)),zpow_one]
    unfold struveHalfCoeff
    field_simp
/-- Differentiating the Laurent polynomial multiplies each monomial by its integer exponent. -/
theorem hasDerivAt_struveHalfPoly (σ : ℂ) (n : ℕ) {z : ℂ} (hz : z≠0) :
    HasDerivAt (struveHalfPoly σ n)
      (∑ m∈Finset.range (n+1), ((n:ℂ)-2*m)/z*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)) z := by
  apply HasDerivAt.fun_sum
  intro m hm
  have hd := ((hasDerivAt_zpow ((n:ℤ)-2*m) (z/2) (Or.inl (div_ne_zero hz (by norm_num)))).comp z
    ((hasDerivAt_id z).div_const 2)).const_mul (σ^m*struveHalfCoeff n m)
  have hd' : HasDerivAt (fun w=>σ^m*struveHalfCoeff n m*(w/2)^((n:ℤ)-2*m)) _ z :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)
  refine hd'.congr_deriv ?_
  rw [zpow_sub₀ (div_ne_zero hz (by norm_num)),zpow_one]
  push_cast
  field_simp

/-- The elementary half-power times the Laurent polynomial obeys the signed order ladder. -/
theorem hasDerivAt_struveHalf_finite (σ : ℂ) (hσ : σ^2=1) (n : ℕ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly σ n w)
      (((n:ℂ)+1/2)/z*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ n z)-
        σ*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ (n+1) z)+
        σ*(2/(π*z))^(1/2:ℂ)*(z/2)^(n+1)/(n+1).factorial) z := by
  have hp := (hasDerivAt_besselPrefactor (-(1/2):ℂ) hz).div_const (Real.sqrt π:ℂ)
  have hev : (fun w=>(w/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ))=ᶠ[𝓝 z]
      (fun w=>(2/(π*w))^(1/2:ℂ)) := by
    filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
    exact struve_half_prefactor hw
  have hp' := hp.congr_of_eventuallyEq hev.symm
  have hd := hp'.mul (hasDerivAt_struveHalfPoly σ n (slitPlane_ne_zero hz))
  have hd' : HasDerivAt (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly σ n w) _ z :=
    hd.congr_of_eventuallyEq (Eventually.of_forall fun w=>rfl)
  have hsum : (2/(π*z))^(1/2:ℂ)*(-(1/2)/z)*struveHalfPoly σ n z+
      (2/(π*z))^(1/2:ℂ)*(∑ m∈Finset.range (n+1),
        ((n:ℂ)-2*m)/z*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m))=
      ((n:ℂ)+1/2)/z*((2/(π*z))^(1/2:ℂ)*struveHalfPoly σ n z)-
        (2/(π*z))^(1/2:ℂ)/z*(∑ m∈Finset.range (n+1),
          (2*m+1)*σ^m*struveHalfCoeff n m*(z/2)^((n:ℤ)-2*m)) := by
    rw [struveHalfPoly]
    simp only [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  refine hd'.congr_deriv ?_
  rw [show (z/2)^(-(1/2):ℂ)*(-(1/2)/z)/(Real.sqrt π:ℂ)=
      ((z/2)^(-(1/2):ℂ)/(Real.sqrt π:ℂ))*(-(1/2)/z) by ring,struve_half_prefactor hz,
    hsum,struveHalfPoly_succ σ n (slitPlane_ne_zero hz)]
  ring_nf
  rw [hσ]
  ring

/-- The Struve forcing at a positive half-integer order is the leading finite monomial. -/
theorem struveHalf_forcing (n : ℕ) {z : ℂ} (hz : z∈slitPlane) :
    (z/2)^((n:ℂ)+1/2)/((Real.sqrt π:ℂ)*Gamma ((n:ℂ)+1/2+3/2))=
      (2/(π*z))^(1/2:ℂ)*(z/2)^(n+1)/(n+1).factorial := by
  rw [show (n:ℂ)+1/2+3/2=((n+1:ℕ):ℂ)+1 by push_cast; ring,Gamma_nat_eq_factorial]
  rw [← struve_half_prefactor hz]
  have he : (z/2)^((n:ℂ)+1/2)=(z/2)^(-(1/2):ℂ)*(z/2)^(n+1) := by
    rw [← cpow_natCast,← cpow_add _ _ (div_ne_zero (slitPlane_ne_zero hz) (by norm_num))]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- The Struve derivative in raising-order form, with its forcing term. -/
theorem hasDerivAt_struve_raise (ν σ : ℂ) {z : ℂ} (hz : z∈slitPlane) :
    HasDerivAt (struveQuadratic ν σ)
      (ν/z*struveQuadratic ν σ z+σ*struveQuadratic (ν+1) σ z+
        (z/2)^ν/(Real.sqrt π*Gamma (ν+3/2))) z := by
  refine (hasDerivAt_struveQuadratic ν σ hz).congr_deriv ?_
  linear_combination struveQuadratic_recurrence ν σ hz

/-- struveK nat add half. -/
@[dlmf 11.4.E1]
theorem struveK_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveK (n+1/2) z = (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), ((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  suffices h : struveK (n+1/2) z=(2/(π*z))^(1/2:ℂ)*struveHalfPoly 1 n z by
    simpa only [struveHalfPoly,struveHalfCoeff,one_pow,one_mul,mul_div_assoc,mul_assoc] using h
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,zero_add,struveHalfPoly,Finset.sum_range_one,struveHalfCoeff,
      pow_zero,zpow_zero,Nat.factorial_zero,Int.natCast_zero,Nat.mul_zero,mul_zero,neg_zero,
      Nat.sub_zero,div_one,mul_one,one_mul,sub_zero]
    rw [struveK,struve_special_5 hz,besselY_half hz]
    ring
  | succ n ih =>
    have hdH := hasDerivAt_struve_raise ((n:ℂ)+1/2) (-1) hz
    rw [funext (struveQuadratic_H ((n:ℂ)+1/2))] at hdH
    simp only [struveQuadratic_H] at hdH
    have hd := hdH.sub (hasDerivAt_besselY ((n:ℂ)+1/2) hz)
    have hd' : HasDerivAt (struveK ((n:ℂ)+1/2)) _ z := hd
    have hev : struveK ((n:ℂ)+1/2)=ᶠ[𝓝 z]
        (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly 1 n w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      exact ih hw
    have he := hd'.deriv
    rw [hev.deriv_eq,(hasDerivAt_struveHalf_finite 1 (by norm_num) n hz).deriv,
      struveHalf_forcing n hz] at he
    simp only [struveK] at ih ⊢
    have hi := ih hz
    push_cast
    rw [show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring]
    linear_combination he+((n:ℂ)+1/2)/z*hi

/-- struveL nat add half. -/
@[dlmf 11.4.E2]
theorem struveL_nat_add_half (n : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (n+1/2) z = besselI (-n-1/2) z - (2/(π*z))^(1/2:ℂ) * ∑ m ∈ Finset.range (n+1), (-1)^m*((2*m).factorial : ℂ)*2^(-(2*m:ℤ))/((m.factorial:ℂ)*(n-m).factorial)*(z/2)^((n:ℤ)-2*m) := by
  suffices h : struveL (n+1/2) z=besselI (-n-1/2) z-(2/(π*z))^(1/2:ℂ)*struveHalfPoly (-1) n z by
    simpa only [struveHalfPoly,struveHalfCoeff,mul_div_assoc,mul_assoc] using h
  induction n generalizing z with
  | zero =>
    simp only [Nat.cast_zero,zero_add,neg_zero,zero_sub,struveHalfPoly,Finset.sum_range_one,struveHalfCoeff,
      pow_zero,zpow_zero,Nat.factorial_zero,Int.natCast_zero,Nat.mul_zero,mul_zero,
      Nat.sub_zero,div_one,mul_one,one_mul,sub_zero]
    rw [struve_special_7 hz,(besselI_elementary_halves hz).2]
    ring
  | succ n ih =>
    have hdL := hasDerivAt_struve_raise ((n:ℂ)+1/2) 1 hz
    rw [funext (struveQuadratic_L ((n:ℂ)+1/2))] at hdL
    simp only [struveQuadratic_L] at hdL
    have hd := (hasDerivAt_besselI' (ν:= -(n:ℂ)-1/2) hz).sub hdL
    have hev : (fun w=>besselI (-(n:ℂ)-1/2) w-struveL ((n:ℂ)+1/2) w)=ᶠ[𝓝 z]
        (fun w=>(2/(π*w))^(1/2:ℂ)*struveHalfPoly (-1) n w) := by
      filter_upwards [isOpen_slitPlane.mem_nhds hz] with w hw
      linear_combination -ih hw
    have hd' : HasDerivAt (fun w=>besselI (-(n:ℂ)-1/2) w-struveL ((n:ℂ)+1/2) w) _ z := hd
    have he := hd'.deriv
    rw [hev.deriv_eq,(hasDerivAt_struveHalf_finite (-1) (by norm_num) n hz).deriv,
      struveHalf_forcing n hz] at he
    have hi := ih hz
    push_cast
    rw [show (n:ℂ)+1+1/2=(n:ℂ)+1/2+1 by ring,
      show -((n:ℂ)+1)-1/2=(-(n:ℂ)-1/2)-1 by ring]
    linear_combination he-((n:ℂ)+1/2)/z*hi

/-- For `p ≥ 0` and `x > 0`, `∫₀¹ (1-t²)^p sin(xt) dt ≥ 0` (one integration by parts). -/
theorem integral_rpow_mul_sin_nonneg {p x : ℝ} (hp : 0 ≤ p) (hx : 0 < x) :
    0 ≤ ∫ t : ℝ in 0..1, (1-t^2)^p * Real.sin (x*t) := by
  set u : ℝ → ℝ := fun t => (1-t^2)^p
  set u' : ℝ → ℝ := fun t => (-(2*t)) * p * (1-t^2)^(p-1)
  set v : ℝ → ℝ := fun t => (1 - Real.cos (x*t))/x
  have hu : ContinuousOn u (uIcc 0 1) :=
    ((continuous_const.sub (continuous_pow 2)).rpow_const (fun _ => Or.inr hp)).continuousOn
  have hv : ContinuousOn v (uIcc 0 1) := by fun_prop
  have huu' : ∀ t ∈ Ioo (min 0 1) (max 0 1), HasDerivAt u (u' t) t := by
    intro t ht
    simp only [zero_le_one, min_eq_left, max_eq_right] at ht
    have hb : (1:ℝ)-t^2 ≠ 0 := by nlinarith [ht.1, ht.2]
    have := ((hasDerivAt_pow 2 t).const_sub 1).rpow_const (p := p) (Or.inl hb)
    convert this using 1
    simp only [u']; push_cast; ring
  have hvv' : ∀ t ∈ Ioo (min 0 1) (max 0 1), HasDerivAt v (Real.sin (x*t)) t := by
    intro t _
    have := (((Real.hasDerivAt_cos (x*t)).comp t ((hasDerivAt_id t).const_mul x)).const_sub 1
      ).div_const x
    convert this using 1
    · funext s; simp [v]
    · field_simp
  have hu' : IntervalIntegrable u' volume 0 1 := by
    have h := intervalIntegral.intervalIntegrable_deriv_of_nonneg (g := fun t => -u t)
      (g' := fun t => -u' t) hu.neg (fun t ht => (huu' t ht).neg) (fun t ht => by
        simp only [zero_le_one, min_eq_left, max_eq_right] at ht
        simp only [u']
        have : 0 ≤ (1-t^2)^(p-1) := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
        have := mul_nonneg (mul_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2*t) hp) this
        linarith)
    have := h.neg
    refine this.congr (fun t _ => ?_)
    simp
  have hv' : IntervalIntegrable (fun t => Real.sin (x*t)) volume 0 1 :=
    (by fun_prop : Continuous fun t : ℝ => Real.sin (x*t)).intervalIntegrable _ _
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hu hv huu' hvv'
    hu' hv'
  change 0 ≤ ∫ t : ℝ in 0..1, u t * Real.sin (x*t)
  rw [hibp]
  have h1 : 0 ≤ u 1 * v 1 := mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    (div_nonneg (by linarith [Real.cos_le_one (x*1)]) hx.le)
  have h0 : u 0 * v 0 = 0 := by simp [v]
  have h2 : (∫ t : ℝ in 0..1, u' t * v t) ≤ 0 := by
    rw [← neg_nonneg, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_nonneg zero_le_one fun t ht => ?_
    simp only [u', v]
    have : 0 ≤ (1-t^2)^(p-1) := Real.rpow_nonneg (by nlinarith [ht.1, ht.2]) _
    have hc : 0 ≤ (1 - Real.cos (x*t))/x := div_nonneg (by linarith [Real.cos_le_one (x*t)]) hx.le
    have := mul_nonneg (mul_nonneg (mul_nonneg (by linarith [ht.1] : (0:ℝ) ≤ 2*t) hp) this) hc
    linarith
  linarith

/-- struveH nonneg, from Poisson's integral and one integration by parts. -/
@[dlmf 11.4.E13]
theorem struveH_nonneg {ν x : ℝ} (hν : 1/2 ≤ ν) (hx : 0 < x) :
    0 ≤ (struveH ν x).re ∧ (struveH ν x).im = 0 := by
  have hν' : -1/2 < (ν:ℂ).re := by simp; linarith
  have hP := struveH_eq_poisson hν' (z := x) (ofReal_ne_zero.2 hx.ne')
  have hint : (∫ t : ℝ in 0..1, (1-(t:ℂ)^2)^((ν:ℂ)-1/2)*sin ((x:ℂ)*t)) =
      ((∫ t : ℝ in 0..1, (1-t^2)^(ν-1/2) * Real.sin (x*t) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le zero_le_one] at ht
    rw [ofReal_mul, ofReal_cpow (by nlinarith [ht.1, ht.2])]
    push_cast; ring_nf
  have hpre : 2*((x:ℂ)/2)^(ν:ℂ)/(Real.sqrt π*Gamma ((ν:ℂ)+1/2)) =
      ((2*(x/2)^ν/(Real.sqrt π*Real.Gamma (ν+1/2)) : ℝ) : ℂ) := by
    rw [show ((x:ℂ)/2) = ((x/2:ℝ):ℂ) by push_cast; ring, ← ofReal_cpow (by positivity),
      show (ν:ℂ)+1/2 = ((ν+1/2:ℝ):ℂ) by push_cast; ring, Complex.Gamma_ofReal]
    push_cast; ring
  rw [hint, hpre, ← ofReal_mul] at hP
  rw [hP, ofReal_re, ofReal_im]
  refine ⟨mul_nonneg (div_nonneg (by positivity) (mul_nonneg (Real.sqrt_nonneg _)
    (Real.Gamma_pos_of_pos (by linarith)).le)) ?_, rfl⟩
  exact integral_rpow_mul_sin_nonneg (by linarith) hx

/-- Relative-error bound, with minimum distance to reciprocal-gamma zeros explicit.
DLMF 11.4.15 prints `2/3 * exp(|z|^2/(4|ν₀+3/2|) - 1)`, which is false: at `ν = 1000`,
`z = i*y` with `y^2/4 = |ν+3/2|` the error exceeds `0.93 > 2/3`. The bound proved by the
termwise estimate `(3/2)_n ≥ (3/2) n!` is `2/3 * (exp(|z|^2/(4|ν₀+3/2|)) - 1)`, stated here
(corrected 2026-10-20). -/
@[dlmf 11.4.E14, dlmf 11.4.E15]
theorem struveH_relative_bound {ν z : ℂ} (hν : ∀ n : ℕ, ν+3/2 ≠ -n) (hz : z ≠ 0) (d : ℝ) (hd : 0 < d) (hmin : ∀ n : ℕ, d ≤ ‖ν+3/2+n‖) (hatt : ∃ n : ℕ, d = ‖ν+3/2+n‖) :
    ∃ θ : ℂ, struveH ν z = 2*(z/2)^(ν+1)/(Real.sqrt π*Gamma (ν+3/2))*(1+θ) ∧ ‖θ‖ < 2/3*(Real.exp (‖z‖^2/(4*d))-1) := by
  sorry

/-- struveH bessel series 18. The hypothesis `hν'` excludes `ν + 1/2 ∈ -ℕ`, where DLMF's
term with `2k+2ν+1 = 0` is a removable quotient but the totalized Lean term is `0`
(added 2026-10-20; at `ν = -1/2` the unrestricted statement claims `H_{-1/2} = 0`). -/
@[dlmf 11.4.E18]
theorem struveH_bessel_series_18 (ν : ℂ) (hν : ∀ n : ℕ, ν ≠ -(n+1))
    (hν' : ∀ n : ℕ, ν + 1/2 ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (4/(Real.sqrt π*Gamma (ν+1/2))) * ((2*k+ν+1)*Gamma (k+ν+1)/((k.factorial:ℂ)*(2*k+1)*(2*k+2*ν+1))*besselJ (2*k+ν+1) z)) (struveH ν z) := by
  sorry

/-- struveH bessel series 19. -/
@[dlmf 11.4.E19]
theorem struveH_bessel_series_19 (ν : ℂ)  {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/(2*π))^(1/2:ℂ) * ((z/2)^k/((k.factorial:ℂ)*(k+1/2))*besselJ (k+ν+1/2) z)) (struveH ν z) := by
  sorry

/-- struveH bessel series 20. -/
@[dlmf 11.4.E20]
theorem struveH_bessel_series_20 (ν : ℂ) (hν : ∀ n : ℕ, ν+1/2 ≠ -n) {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => (z/2)^(ν+1/2)/Gamma (ν+1/2) * ((z/2)^k/((k.factorial:ℂ)*(k+ν+1/2))*besselJ (k+1/2) z)) (struveH ν z) := by
  sorry

/-- struveH zero odd. -/
@[dlmf 11.4.E21]
theorem struveH_zero_odd {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*k+1) z/(2*k+1)) (struveH 0 z) := by
  sorry

/-- struveH zero products. -/
@[dlmf 11.4.E21]
theorem struveH_zero_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 2*(-1)^k*(besselJ (k+1/2) (z/2))^2) (struveH 0 z) := by
  sorry

/-- struveH one even. -/
@[dlmf 11.4.E22]
theorem struveH_one_even {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4/π*besselJ (2*(k+1)) z/(4*(k+1:ℂ)^2-1)) (struveH 1 z-2/π*(1-besselJ 0 z)) := by
  sorry

/-- struveH one products. -/
@[dlmf 11.4.E22]
theorem struveH_one_products {z : ℂ} (hz : z ∈ slitPlane) :
    HasSum (fun k : ℕ => 4*besselJ (2*k+1/2) (z/2)*besselJ (2*k+3/2) (z/2)) (struveH 1 z) := by
  sorry

/-- struveH recurrence. -/
@[dlmf 11.4.E23]
theorem struveH_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveH (ν-1) z + struveH (ν+1) z = 2*ν/z*struveH ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  have h := struveQuadratic_recurrence ν (-1) hz
  simpa only [struveQuadratic_H, neg_one_mul, sub_neg_eq_add, one_mul] using h

/-- struveH derivative. -/
@[dlmf 11.4.E24]
theorem struveH_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveH ν) ((struveH (ν-1) z - struveH (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  have hd := hasDerivAt_struveQuadratic ν (-1) hz
  rw [funext (struveQuadratic_H ν)] at hd
  simp only [struveQuadratic_H] at hd
  refine hd.congr_deriv ?_
  have hr := struveH_recurrence ν hz
  linear_combination hr/2

/-- struveH weighted deriv 27. -/
@[dlmf 11.4.E27, dlmf 11.7.E1]
theorem struveH_weighted_deriv_27 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveH ν z) (z^ν*struveH (ν-1) z) z := by
  have hd := hasDerivAt_weighted_struveQuadratic ν (-1) hz
  simpa only [struveQuadratic_H, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- struveH weighted deriv 28. -/
@[dlmf 11.4.E28, dlmf 11.7.E2]
theorem struveH_weighted_deriv_28 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveH ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) - z^(-ν)*struveH (ν+1) z) z := by
  have hd := hasDerivAt_inverse_weighted_struveQuadratic ν (-1) hz
  simpa only [struveQuadratic_H, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- struveH iterated weighted deriv. -/
@[dlmf 11.4.E31]
theorem struveH_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveH ν z) z = z^(ν-m)*struveH (ν-m) z := by
  have he := iterated_weighted_struveQuadratic ν (-1) m hz
  simpa only [struveQuadratic_H] using he

/-- struveH zero deriv. -/
@[dlmf 11.4.E32]
theorem struveH_zero_deriv (z : ℂ) :
    HasDerivAt (struveH 0) (2/π - struveH 1 z) z := by
  have hf : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have hg : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have he : deriv (struveH 0)=(fun z => 2/(π:ℂ)-struveH 1 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      have hd := struveH_weighted_deriv_28 0 hz
      norm_num only [mul_zero,neg_zero,cpow_zero,one_mul,zero_add] at hd
      rw [hd.deriv]
      have hG := Gamma_oddProduct 0
      norm_num [oddProduct] at hG
      have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
      have hc : (Real.sqrt π:ℂ)*Gamma (3/2)=π/2 := by rw [hG]; linear_combination hp/2
      rw [hc]
      congr 1
      field_simp
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- struveH one weighted deriv. -/
@[dlmf 11.4.E32]
theorem struveH_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveH 1 z) (z*struveH 0 z) z := by
  have h0 : Differentiable ℂ (struveH 0) := by simpa using struveH_nat_entire 0
  have h1 : Differentiable ℂ (struveH 1) := by simpa using struveH_nat_entire 1
  have hf : Differentiable ℂ (fun z => z*struveH 1 z) := by fun_prop
  have he : deriv (fun z => z*struveH 1 z)=(fun z => z*struveH 0 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      simpa using (struveH_weighted_deriv_27 1 hz).deriv
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- struveL recurrence. -/
@[dlmf 11.4.E25]
theorem struveL_recurrence (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    struveL (ν-1) z - struveL (ν+1) z = 2*ν/z*struveL ν z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)) := by
  have h := struveQuadratic_recurrence ν (1) hz
  simpa only [struveQuadratic_L, neg_one_mul, sub_neg_eq_add, one_mul] using h

/-- struveL derivative. -/
@[dlmf 11.4.E26]
theorem struveL_derivative (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (struveL ν) ((struveL (ν-1) z + struveL (ν+1) z+(z/2)^ν/(Real.sqrt π*Gamma (ν+3/2)))/2) z := by
  have hd := hasDerivAt_struveQuadratic ν (1) hz
  rw [funext (struveQuadratic_L ν)] at hd
  simp only [struveQuadratic_L] at hd
  refine hd.congr_deriv ?_
  have hr := struveL_recurrence ν hz
  linear_combination hr/2

/-- struveL weighted deriv 29. -/
@[dlmf 11.4.E29, dlmf 11.7.E3]
theorem struveL_weighted_deriv_29 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(1*ν)*struveL ν z) (z^ν*struveL (ν-1) z) z := by
  have hd := hasDerivAt_weighted_struveQuadratic ν (1) hz
  simpa only [struveQuadratic_L, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- struveL weighted deriv 30. -/
@[dlmf 11.4.E30, dlmf 11.7.E4]
theorem struveL_weighted_deriv_30 (ν : ℂ) {z : ℂ} (hz : z ∈ slitPlane) :
    HasDerivAt (fun z : ℂ => z^(-1*ν)*struveL ν z) (2^(-ν)/(Real.sqrt π*Gamma (ν+3/2)) + z^(-ν)*struveL (ν+1) z) z := by
  have hd := hasDerivAt_inverse_weighted_struveQuadratic ν (1) hz
  simpa only [struveQuadratic_L, one_mul, neg_one_mul, neg_mul, ← sub_eq_add_neg] using hd

/-- struveL iterated weighted deriv. -/
@[dlmf 11.4.E31]
theorem struveL_iterated_weighted_deriv (ν : ℂ) (m : ℕ) {z : ℂ} (hz : z ∈ slitPlane) :
    ((fun f : ℂ → ℂ => fun z => deriv f z/z)^[m]) (fun z => z^ν*struveL ν z) z = z^(ν-m)*struveL (ν-m) z := by
  have he := iterated_weighted_struveQuadratic ν (1) m hz
  simpa only [struveQuadratic_L] using he

/-- struveL zero deriv. -/
@[dlmf 11.4.E33]
theorem struveL_zero_deriv (z : ℂ) :
    HasDerivAt (struveL 0) (2/π + struveL 1 z) z := by
  have hf : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have hg : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have he : deriv (struveL 0)=(fun z => 2/(π:ℂ)+struveL 1 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      have hd := struveL_weighted_deriv_30 0 hz
      norm_num only [mul_zero,neg_zero,cpow_zero,one_mul,zero_add] at hd
      rw [hd.deriv]
      have hG := Gamma_oddProduct 0
      norm_num [oddProduct] at hG
      have hp : (Real.sqrt π:ℂ)^2=(π:ℂ) := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
      have hc : (Real.sqrt π:ℂ)*Gamma (3/2)=π/2 := by rw [hG]; linear_combination hp/2
      rw [hc]
      congr 1
      field_simp
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

/-- struveL one weighted deriv. -/
@[dlmf 11.4.E33]
theorem struveL_one_weighted_deriv (z : ℂ) :
    HasDerivAt (fun z => z*struveL 1 z) (z*struveL 0 z) z := by
  have h0 : Differentiable ℂ (struveL 0) := by simpa using struveL_nat_entire 0
  have h1 : Differentiable ℂ (struveL 1) := by simpa using struveL_nat_entire 1
  have hf : Differentiable ℂ (fun z => z*struveL 1 z) := by fun_prop
  have he : deriv (fun z => z*struveL 1 z)=(fun z => z*struveL 0 z) := by
    apply Complex.eq_of_differentiable_of_eqOn_pos_reals
    · exact fun z => ((hf.differentiableOn.analyticOnNhd isOpen_univ) z (mem_univ z)).deriv.differentiableAt
    · fun_prop
    · intro x hx
      have hz : (x:ℂ)∈slitPlane := Or.inl (by simpa using hx)
      simpa using (struveL_weighted_deriv_29 1 hz).deriv
  exact (hf z).hasDerivAt.congr_deriv (congrFun he z)

end AAR.Struve
