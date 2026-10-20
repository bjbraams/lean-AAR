/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.Legendre.Associated

/-!
# Ferrers and associated Legendre connection formulas

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
Theorem statements were initially admitted; remaining `sorry` declarations are
not completed proofs. See `DLMF111214Acquisition.md` for coverage and validation.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Legendre

/-- ferrers connection 1. -/
@[dlmf 14.9.E1]
theorem ferrers_connection_1 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*sin (μ*π)/(2*Gamma (ν-μ+1))*ferrersP ν (-μ) x=-ferrersQ ν μ x/Gamma (ν+μ+1)+cos (μ*π)/Gamma (ν-μ+1)*ferrersQ ν (-μ) x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersQ_even_odd, ferrersQ_neg_even_odd ν μ hx,
    legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  have hμπ : μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 := by ring
  rw [hμπ, sin_sub, cos_sub]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (sb*h1*E*g1-cb*h2*g2*O)*pytha

/-- ferrers connection 2. -/
@[dlmf 14.9.E2]
theorem ferrers_connection_2 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2*sin (μ*π)/(π*Gamma (ν-μ+1))*ferrersQ ν (-μ) x=ferrersP ν μ x/Gamma (ν+μ+1)-cos (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_regular hplus hx, ferrersQ_neg_even_odd ν μ hx,
    legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, sin_sub, cos_sub]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (sb*h2*g2*O + cb*h1*E*g1)*pytha

/-- ferrers connection 5. -/
@[dlmf 14.9.E5]
theorem ferrers_connection_5 (ν μ : ℂ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP (-ν-1) μ x=ferrersP ν μ x := by
  have hp : 1+(x:ℂ) ∈ slitPlane := Or.inl (by simp; linarith [hx.1])
  unfold ferrersP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add hp)]

/-- ferrers connection 6. -/
@[dlmf 14.9.E6]
theorem ferrers_connection_6 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) (hother : LegendreQRegular (-ν-1) μ) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π*cos (ν*π)*cos (μ*π)*ferrersP ν μ x=sin ((ν+μ)*π)*ferrersQ ν μ x-sin ((ν-μ)*π)*ferrersQ (-ν-1) μ x := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hk1, hk2⟩ := legendre_Gamma_half_ne_zero hother
  rw [show (-ν-1+μ+1)/2 = (μ-ν)/2 by ring] at hk1
  rw [show (-ν-1+μ+2)/2 = (1-ν+μ)/2 by ring] at hk2
  obtain ⟨hA, hB⟩ := legendre_reflection_inv hplus
  obtain ⟨-, -, e2, o2⟩ := legendre_reflections ν μ
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_regular hplus hx, ferrersQ_even_odd, ferrersQ_neg_degree_even_odd ν μ hx, hA, hB]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    cos_sub, cos_add, legendre_sin_two_mul_half, legendre_sin_two_mul_half]
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha o2
  generalize cos ((ν-μ)*π/2) = ca at pytha e2
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1 e2
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2 o2
  generalize Gamma ((μ-ν)/2) = k1 at hk1 o2
  generalize Gamma ((1-ν+μ)/2) = k2 at hk2 e2
  generalize (2:ℂ)^μ = T at hT
  generalize (π:ℂ) = P at hP e2 o2
  have e2' : P = ca*k2*h1 := by field_simp at e2; linear_combination e2
  have o2' : P = -sa*k1*h2 := by field_simp at o2; linear_combination o2
  field_simp
  linear_combination (cb*ca^2*g1*E*h1)*o2' - (sb*sa^2*h2*g2*O)*e2' +
    P*g1*E*h1*cb*(ca^2*pyth - sb^2*pytha) + P*h2*g2*O*sb*(cb^2*pytha - sa^2*pyth)

/-- ferrers connection 7. -/
@[dlmf 14.9.E7]
theorem ferrers_connection_7 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    sin ((ν-μ)*π)/Gamma (ν+μ+1)*ferrersP ν μ x=sin (ν*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) x-sin (μ*π)/Gamma (ν-μ+1)*ferrersP ν (-μ) (-x) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersEven_neg,
    ferrersOdd_neg, ferrersP_regular hplus hx, legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    sin_sub, sin_add, legendre_sin_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (Real.sqrt π:ℂ) = S at hs
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (0:ℂ)*pyth

/-- ferrers connection 8. -/
@[dlmf 14.9.E8]
theorem ferrers_connection_8 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    π/2*sin ((ν-μ)*π)*ferrersP ν (-μ) x=-cos ((ν-μ)*π)*ferrersQ ν (-μ) x-ferrersQ ν (-μ) (-x) := by
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersQ_neg_even_odd ν μ hx, ferrersQ_neg_even_odd ν μ (ferrers_neg_mem_Ioo hx),
    ferrersEven_neg, ferrersOdd_neg, cpow_neg]
  rw [legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (2*ca*g2*h2*O)*pytha

/-- ferrers connection 9. -/
@[dlmf 14.9.E9]
theorem ferrers_connection_9 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/(Gamma (ν+μ+1)*Gamma (μ-ν))*ferrersQ ν μ x=-cos (ν*π)*ferrersP ν (-μ) x+cos (μ*π)*ferrersP ν (-μ) (-x) := by
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hA, hB⟩ := legendre_reflection_inv_neg hminus
  have pyth := sin_sq_add_cos_sq ((ν+μ)*π/2)
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hs2 : (Real.sqrt π:ℂ)^2 = π := by rw [← ofReal_pow, Real.sq_sqrt Real.pi_pos.le]
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersEven_neg,
    ferrersOdd_neg, ferrersQ_even_odd, div_eq_mul_inv, mul_inv, legendre_inv_Gamma_sub, hA, hB,
    legendre_Gamma_plus, cpow_neg]
  rw [show μ*π = (ν+μ)*π/2 - (ν-μ)*π/2 by ring, show ν*π = (ν+μ)*π/2 + (ν-μ)*π/2 by ring,
    cos_sub, cos_add]
  generalize sin ((ν+μ)*π/2) = sb at pyth
  generalize cos ((ν+μ)*π/2) = cb at pyth
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  rw [← hs2]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize (Real.sqrt π:ℂ) = S at hs
  field_simp
  linear_combination (0:ℂ)*pyth

/-- ferrers connection 10. -/
@[dlmf 14.9.E10]
theorem ferrers_connection_10 (ν μ : ℂ) (hplus : LegendreQRegular ν μ) (hminus : LegendreQRegular ν (-μ)) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    2/π*sin ((ν-μ)*π)*ferrersQ ν (-μ) x=cos ((ν-μ)*π)*ferrersP ν (-μ) x-ferrersP ν (-μ) (-x) := by
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hminus
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hplus
  have pytha := sin_sq_add_cos_sq ((ν-μ)*π/2)
  have hT : (2:ℂ)^μ ≠ 0 := by simp
  have hP : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [ferrersP_neg_regular hminus hx, ferrersP_neg_regular hminus (ferrers_neg_mem_Ioo hx), ferrersQ_neg_even_odd ν μ hx,
    ferrersEven_neg, ferrersOdd_neg, cpow_neg]
  rw [legendre_sin_two_mul_half, legendre_cos_two_mul_half]
  generalize ferrersEven ν μ x = E
  generalize ferrersOdd ν μ x = O
  generalize Gamma ((ν+μ+1)/2) = g1 at hg1
  generalize Gamma ((ν+μ+2)/2) = g2 at hg2
  generalize Gamma ((ν-μ+1)/2) = h1 at hh1
  generalize Gamma ((ν-μ+2)/2) = h2 at hh2
  generalize (2:ℂ)^μ = T at hT
  generalize sin ((ν-μ)*π/2) = sa at pytha
  generalize cos ((ν-μ)*π/2) = ca at pytha
  generalize (π:ℂ) = P at hP
  field_simp
  linear_combination (-(2*ca*h1*E*g1))*pytha

/-- ferrersP negative integer order. -/
@[dlmf 14.9.E3]
theorem ferrersP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersP ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersP ν m x := by
  have hG := Gamma_add_nat_ne_zero ν m h
  rcases m with _ | k
  · simp only [Nat.cast_zero, neg_zero, sub_zero, add_zero, pow_zero, one_mul] at hG ⊢
    rw [div_self hG, one_mul]
  have hw := mem_cutPlane_of_one_add (show 1+(x:ℂ) ∈ slitPlane from Or.inl (by simp; linarith [hx.1]))
  have hp := poch_mul_poch_neg_mul_Gamma ν (k+1) h
  have hg := ferrers_gauge_neg_nat (k+1) hx
  unfold ferrersP
  rw [show 1-(-((k+1:ℕ):ℂ)) = ((k+1:ℕ):ℂ)+1 by ring, regularizedGaussHG_legendre_neg_nat ν k hw]
  have hm1 : (-1:ℂ)^(k+1) = poch (ν+1) (k+1) * poch (-ν) (k+1) * Gamma (ν-((k+1:ℕ):ℂ)+1) /
      Gamma (ν+((k+1:ℕ):ℂ)+1) := by rw [hp]; field_simp
  have hsq : (-1:ℂ)^(k+1)*(-1)^(k+1) = 1 := by rw [← mul_pow]; norm_num
  rw [← hg]
  set A := (((1+x)/(1-x):ℝ):ℂ)^(((k+1:ℕ):ℂ)/2) * ((1-(x:ℂ))/2)^(k+1) *
    ((1-(1-(x:ℂ))/2)^(k+1))⁻¹ * regularizedGaussHG (ν+1) (-ν) ((k+1:ℕ)+1) ((1-x)/2) with hA
  linear_combination (-A) * hsq + (-1:ℂ)^(k+1) * A * hm1

/-- ferrersQ negative integer order. -/
@[dlmf 14.9.E4]
theorem ferrersQ_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {x : ℝ} (hx : x ∈ Ioo (-1:ℝ) 1) :
    ferrersQ ν (-m) x=(-1)^m*Gamma (ν-m+1)/Gamma (ν+m+1)*ferrersQ ν m x := by
  have hm : LegendreQRegular ν (-(m:ℂ)) := fun n hn => h n (by linear_combination hn)
  have hp : LegendreQRegular ν (m:ℂ) := fun n hn => h (n+2*m) (by push_cast; linear_combination hn)
  obtain ⟨hg1, hg2⟩ := legendre_Gamma_half_ne_zero hp
  obtain ⟨hh1, hh2⟩ := legendre_Gamma_half_ne_zero_neg hm
  have hs : (Real.sqrt π:ℂ) ≠ 0 := ofReal_ne_zero.mpr (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hT : (2:ℂ)^(m:ℂ) ≠ 0 := by simp
  have hN : (2:ℂ)^ν ≠ 0 := by simp
  have hσ : ((-1:ℂ)^m)^2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [ferrersQ_neg_even_odd ν m hx, ferrersQ_even_odd, legendre_Gamma_plus, legendre_Gamma_minus, cpow_neg,
    show (ν-m)*π/2 = (ν+m)*π/2 - m*π by ring, legendre_sin_sub_nat_mul_pi, legendre_cos_sub_nat_mul_pi]
  generalize ferrersEven ν m x = E
  generalize ferrersOdd ν m x = O
  generalize Gamma ((ν+m+1)/2) = g1 at hg1
  generalize Gamma ((ν+m+2)/2) = g2 at hg2
  generalize Gamma ((ν-m+1)/2) = h1 at hh1
  generalize Gamma ((ν-m+2)/2) = h2 at hh2
  generalize (2:ℂ)^(m:ℂ) = T at hT
  generalize (2:ℂ)^ν = N at hN
  generalize (-1:ℂ)^m = σ at hσ
  generalize (Real.sqrt π:ℂ) = S at hs
  field_simp

/-- associated connection 11. -/
@[dlmf 14.9.E11]
theorem associated_connection_11 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP (-ν-1) μ z=associatedP ν μ z := by
  unfold associatedP
  rw [show -(-ν-1)=ν+1 by ring, show -ν-1+1 = -ν by ring,
    regularizedGaussHG_symm _ _ _ (mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz))]

/-- associated connection 14. -/
@[dlmf 14.9.E14]
theorem associated_connection_14 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    olverQ ν (-μ) z=olverQ ν μ z := by
  refine legendre_eq_of_continuous_nonint (f := fun μ => olverQ ν (-μ) z) (g := fun μ => olverQ ν μ z)
    ((olverQ_entire_order ν z hz).continuous.comp continuous_neg) (olverQ_entire_order ν z hz).continuous
    (fun μ hμ => ?_) μ
  have hμ' : ∀ n : ℤ, -μ ≠ n := fun n hn => hμ (-n) (by push_cast; linear_combination -hn)
  have h1 := olverQ_connection ν μ hz
  have h2 := olverQ_connection ν (-μ) hz
  rw [neg_neg, show ν+-μ+1 = ν-μ+1 by ring, show ν- -μ+1 = ν+μ+1 by ring, neg_mul, sin_neg] at h2
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have : 2*sin (μ*π)/π*(olverQ ν μ z - olverQ ν (-μ) z) = 0 := by linear_combination h1 + h2
  rcases mul_eq_zero.mp this with h | h
  · exact absurd h (div_ne_zero (mul_ne_zero two_ne_zero hs) hpi)
  · linear_combination -h

/-- associated connection 12. -/
@[dlmf 14.9.E12]
theorem associated_connection_12 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    cos (ν*π)*associatedP ν (-μ) z=-olverQ ν μ z/Gamma (μ-ν)+olverQ (-ν-1) μ z/Gamma (ν+μ+1) := by
  refine legendre_eq_of_continuous_nonint
    (f := fun μ => cos (ν*π)*associatedP ν (-μ) z)
    (g := fun μ => -olverQ ν μ z*(Gamma (μ-ν))⁻¹+olverQ (-ν-1) μ z*(Gamma (ν+μ+1))⁻¹)
    (continuous_const.mul (continuous_associatedP_neg_order ν hz))
    ((((olverQ_entire_order ν z hz).continuous.neg.mul (continuous_inv_Gamma.comp (by fun_prop)))).add
      ((olverQ_entire_order (-ν-1) z hz).continuous.mul (continuous_inv_Gamma.comp (by fun_prop))))
    (fun μ hμ => ?_) μ |>.trans (by simp only [div_eq_mul_inv])
  rw [(olverQ_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds, (olverQ_reflect_eventuallyEq_nonint ν μ hμ hz).eq_of_nhds]
  have r1 := legendre_inv_Gamma_reflection (ν+μ+1)
  have r2 := legendre_inv_Gamma_reflection (ν-μ+1)
  rw [show 1-(ν+μ+1) = -ν-1-μ+1 by ring] at r1
  rw [show 1-(ν-μ+1) = μ-ν by ring] at r2
  rw [show -ν-1+μ+1 = μ-ν by ring]
  have t1 : sin (π*(ν+μ+1)) = -(sin (ν*π)*cos (μ*π)+cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν+μ+1) = ν*π+μ*π+π by ring, sin_add_pi, sin_add]
  have t2 : sin (π*(ν-μ+1)) = -(sin (ν*π)*cos (μ*π)-cos (ν*π)*sin (μ*π)) := by
    rw [show (π:ℂ)*(ν-μ+1) = ν*π-μ*π+π by ring, sin_add_pi, sin_sub]
  generalize (Gamma (ν+μ+1))⁻¹ = g1 at r1 ⊢
  generalize (Gamma (ν-μ+1))⁻¹ = g2 at r2 ⊢
  generalize (Gamma (μ-ν))⁻¹ = h1 at r2 ⊢
  generalize (Gamma (-ν-1-μ+1))⁻¹ = h2 at r1 ⊢
  have hs := legendre_sin_ne_zero hμ
  have hs' : sin (π*μ) ≠ 0 := by rwa [mul_comm]
  have hpi : (π:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  have hE : g1*h2-g2*h1 = -2*cos (ν*π)*sin (μ*π)/π := by
    rw [eq_div_iff hpi]; linear_combination r1 - r2 + t1 - t2
  linear_combination (norm := skip) (π/(2*sin (μ*π))*associatedP ν (-μ) z)*hE
  field_simp
  ring



/-- associated connection 15. -/
@[dlmf 14.9.E15]
theorem associated_connection_15 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    2*sin (μ*π)/π*olverQ ν μ z=associatedP ν μ z/Gamma (ν+μ+1)-associatedP ν (-μ) z/Gamma (ν-μ+1) := by
  exact olverQ_connection ν μ hz

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E16]
theorem associated_connection_16 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    olverQ ν μ z=(π/2:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*associatedP (-μ-1/2) (-ν-1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  sorry

/-- Principal-sheet formula; Whipple transformation is stated in the right half-plane to fix its inherited branch. -/
@[dlmf 14.9.E17]
theorem associated_connection_17 (ν μ : ℂ) {z : ℂ} (hz : z-1 ∈ slitPlane) (hre : 0 < z.re) :
    associatedP ν μ z=(2/π:ℂ)^(1/2:ℂ)*legendreBranchPower (-1/2) z*olverQ (-μ-1/2) (ν+1/2) (z/exp ((log (z-1)+log (z+1))/2)) := by
  sorry

/-- associatedP negative integer order. -/
@[dlmf 14.9.E13]
theorem associatedP_negative_integer_order (ν : ℂ) (m : ℕ) (h : ∀ n : ℕ, ν-m+1 ≠ -n) {z : ℂ} (hz : z-1 ∈ slitPlane) :
    associatedP ν (-m) z=Gamma (ν-m+1)/Gamma (ν+m+1)*associatedP ν m z := by
  have hG := Gamma_add_nat_ne_zero ν m h
  rcases m with _ | k
  · simp only [Nat.cast_zero, neg_zero, sub_zero, add_zero] at hG ⊢
    rw [div_self hG, one_mul]
  have hw := mem_cutPlane_of_one_add (one_add_mem_slitPlane_of_sub_one hz)
  have hp := poch_mul_poch_neg_mul_Gamma ν (k+1) h
  have hg := associated_gauge_neg_nat (k+1) hz
  unfold associatedP
  rw [show 1-(-((k+1:ℕ):ℂ)) = ((k+1:ℕ):ℂ)+1 by ring, regularizedGaussHG_legendre_neg_nat ν k hw]
  calc _ = ((-1)^(k+1)*(-1)^(k+1)) * exp (-((k+1:ℕ):ℂ)/2*(log (z+1)-log (z-1))) *
        regularizedGaussHG (ν+1) (-ν) ((k+1:ℕ)+1) ((1-z)/2) := by
          rw [← mul_pow, show (-1:ℂ)*(-1) = 1 by ring, one_pow, one_mul]
    _ = _ := by
      have hm1 : (-1:ℂ)^(k+1) = poch (ν+1) (k+1) * poch (-ν) (k+1) * Gamma (ν-((k+1:ℕ):ℂ)+1) /
          Gamma (ν+((k+1:ℕ):ℂ)+1) := by rw [hp]; field_simp
      rw [mul_assoc ((-1:ℂ)^(k+1)), ← hg, hm1]
      ring

end AAR.Legendre
