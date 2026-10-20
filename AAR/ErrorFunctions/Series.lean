/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations

/-!
# Power and spherical Bessel series, DLMF §7.6

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- hasSum erf complex. -/
@[dlmf 7.6.E1]
theorem hasSum_erf_complex (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*(-1 : ℂ)^n*z^(2*n+1)/((n.factorial : ℂ)*(2*n+1))) (erf z) := by
  have hs (w : ℂ) : HasSum (fun n : ℕ => ((-1:ℂ)^n/n.factorial)*w^(2*n)) (exp (-w^2)) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (-w^2)
    rw [← Complex.exp_eq_exp_ℂ] at he
    convert he using 1
    funext n
    rw [neg_pow, pow_mul]
    ring
  have hb (R : ℝ) (_ : 0 ≤ R) : Summable (fun n : ℕ => ‖(-1:ℂ)^n/n.factorial‖*R^(2*n)) := by
    convert Real.summable_pow_div_factorial (R^2) using 1
    funext n
    simp [pow_mul]
    ring
  have h := (hasSum_primitive_monomials _ (fun n => 2*n) hs hb z).mul_left (2/(Real.sqrt π:ℂ))
  rw [← erf_complex_segment_integral] at h
  refine h.congr_fun fun n => ?_
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The rising factorial `(3/2)_n` times `2^n` is the odd product `1·3···(2n+1)`. -/
theorem poch_three_half_mul_two_pow (n : ℕ) : poch (3/2) n*(2:ℂ)^n = oddProduct n := by
  induction n with
  | zero => simp [oddProduct, poch_zero]
  | succ n ih =>
    rw [poch_succ, oddProduct, Finset.prod_range_succ, ← oddProduct, ← ih, pow_succ]
    push_cast
    ring

/-- hasSum erf scaled. -/
@[dlmf 7.6.E2]
theorem hasSum_erf_scaled (z : ℂ) :
    HasSum (fun n : ℕ => 2/Real.sqrt π*exp (-z^2)*(2 : ℂ)^n*z^(2*n+1)/oddProduct n) (erf z) := by
  have h := (hasSum_kummerM (a:=1) three_half_ne_neg_nat (z^2)).mul_left
    (2*z/Real.sqrt π*exp (-z^2))
  rw [← (erf_kummerM_pair z).2] at h
  refine h.congr_fun fun n => ?_
  have hp : poch (3/2:ℂ) n ≠ 0 := by
    intro h0
    have := poch_three_half_mul_two_pow n
    rw [h0, zero_mul] at this
    have hne : oddProduct n ≠ 0 := by
      unfold oddProduct
      rw [Finset.prod_ne_zero_iff]
      intro j _
      exact_mod_cast (show (2*j+1 : ℕ) ≠ 0 by omega)
    exact hne this.symm
  rw [← poch_three_half_mul_two_pow, kummerMCoeff, poch_nat_one]
  have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  field_simp
  ring

/-- Half-integer Gamma values: `Γ(m+3/2)·2^m = (√π/2)·1·3···(2m+1)`. -/
theorem Gamma_nat_add_three_half_mul_two_pow (m : ℕ) :
    Gamma ((m:ℂ)+3/2)*(2:ℂ)^m = Real.sqrt π/2*oddProduct m := by
  induction m with
  | zero =>
    have h := Complex.Gamma_add_one (1/2:ℂ) (by norm_num)
    rw [Gamma_one_half_eq_sqrt] at h
    norm_num [oddProduct] at h ⊢
    rw [h]; ring
  | succ m ih =>
    have hne : (m:ℂ)+3/2 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)]
    rw [show ((m+1:ℕ):ℂ)+3/2 = ((m:ℂ)+3/2)+1 by push_cast; ring, Complex.Gamma_add_one _ hne,
      oddProduct, Finset.prod_range_succ, ← oddProduct, pow_succ]
    rw [show ((m:ℂ)+3/2)*Gamma ((m:ℂ)+3/2)*((2:ℂ)^m*2) =
      (Gamma ((m:ℂ)+3/2)*(2:ℂ)^m)*(2*m+3) by ring, ih]
    push_cast
    ring

/-- hasSum faddeevaW. -/
@[dlmf 7.6.E3]
theorem hasSum_faddeevaW (z : ℂ) :
    HasSum (fun n : ℕ => (I*z)^n/Gamma ((n : ℂ)/2+1)) (faddeevaW z) := by
  obtain ⟨u, hu⟩ : ∃ u, u = I*z := ⟨_, rfl⟩
  simp_rw [← hu]
  have hz : -z^2 = u^2 := by rw [hu, mul_pow, I_sq]; ring
  have hev : HasSum (fun m : ℕ => u^(2*m)/Gamma (((2*m:ℕ) : ℂ)/2+1)) (exp (u^2)) := by
    have he := NormedSpace.expSeries_div_hasSum_exp (u^2)
    rw [← Complex.exp_eq_exp_ℂ] at he
    refine he.congr_fun fun m => ?_
    rw [show (((2*m:ℕ) : ℂ)/2+1) = (m:ℂ)+1 by push_cast; ring, Complex.Gamma_nat_eq_factorial,
      pow_mul]
  have h1 : exp (u^2)*exp (-u^2) = 1 := by rw [← Complex.exp_add]; simp
  have hπ : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hod : HasSum (fun m : ℕ => u^(2*m+1)/Gamma (((2*m+1:ℕ) : ℂ)/2+1)) (exp (u^2)*erf u) := by
    have h := (hasSum_erf_scaled u).mul_left (exp (u^2))
    refine h.congr_fun fun m => ?_
    have hG := Gamma_nat_add_three_half_mul_two_pow m
    have hG0 : Gamma ((m:ℂ)+3/2) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by
      simp; linarith [(Nat.cast_nonneg m : (0:ℝ) ≤ m)])
    have hO : oddProduct m = 2*(Gamma ((m:ℂ)+3/2)*(2:ℂ)^m)/Real.sqrt π := by
      rw [hG]; field_simp
    have hr : exp (u^2)*(2/Real.sqrt π*exp (-u^2)*(2:ℂ)^m*u^(2*m+1)/oddProduct m) =
        (exp (u^2)*exp (-u^2))*(2/Real.sqrt π*(2:ℂ)^m*u^(2*m+1)/oddProduct m) := by ring
    rw [show (((2*m+1:ℕ) : ℂ)/2+1) = (m:ℂ)+3/2 by push_cast; ring, hr, h1, one_mul, hO]
    have h2 : (2:ℂ)^m ≠ 0 := pow_ne_zero _ two_ne_zero
    field_simp
  have h := HasSum.even_add_odd (f := fun n : ℕ => u^n/Gamma ((n:ℂ)/2+1)) hev hod
  convert h using 1
  rw [faddeevaW, hz, erfc, show -I*z = -u by rw [hu]; ring,
    show erf (-u) = -erf u by simp [erf]]
  ring



/-- Convergent auxiliary series of DLMF 7.6.5 and 7.6.7. -/
def fresnelAlternateSeries (odd : Bool) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)

/-- The odd product dominates the factorial: `k! ≤ 1·3···(2k+1)`. -/
theorem factorial_le_norm_oddProduct (k : ℕ) : (k ! : ℝ) ≤ ‖oddProduct k‖ := by
  have he : oddProduct k = ((∏ j ∈ Finset.range (k+1), (2*j+1) : ℕ) : ℂ) := by
    simp [oddProduct]
  rw [he, Complex.norm_natCast]
  have h : k ! ≤ ∏ j ∈ Finset.range (k+1), (2*j+1) := by
    rw [Finset.prod_range_succ, ← Finset.prod_range_add_one_eq_factorial]
    calc ∏ x ∈ Finset.range k, (x+1) ≤ ∏ j ∈ Finset.range k, (2*j+1) := by
          exact Finset.prod_le_prod fun j _ => by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  exact_mod_cast h

/-- fresnelAlternateSeries summable. -/
theorem fresnelAlternateSeries_summable (odd : Bool) (z : ℂ) :
    Summable (fun n : ℕ => (-1 : ℂ)^n*π^(2*n+if odd then 1 else 0)*z^(4*n+if odd then 3 else 1)/oddProduct (2*n+if odd then 1 else 0)) := by
  set e : ℕ := if odd then 1 else 0 with he
  have h4 : (4*· + if odd then 3 else 1) = fun n : ℕ => 2*(2*n+e)+1 := by
    funext n; cases odd <;> simp [he] <;> ring
  have hinj : Function.Injective (fun n : ℕ => 2*n+e) := by intro a b h; simp at h; omega
  have hs := ((Real.summable_pow_div_factorial (π*‖z‖^2)).comp_injective hinj).mul_left ‖z‖
  refine Summable.of_norm_bounded hs fun n => ?_
  have hk := factorial_le_norm_oddProduct (2*n+e)
  have hpos : (0:ℝ) < ((2*n+e) ! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hz : z^(4*n+if odd then 3 else 1) = z^(2*(2*n+e)+1) := by
    congr 1; cases odd <;> simp [he] <;> ring
  rw [hz]
  simp only [Function.comp_apply, norm_div, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [mul_pow, ← pow_mul, pow_succ, show 2*(2*n+e) = (2*n+e)*2 by ring]
  rw [div_le_iff₀ (lt_of_lt_of_le hpos hk)]
  calc π^(2*n+e)*(‖z‖^((2*n+e)*2)*‖z‖) = ‖z‖*(π^(2*n+e)*‖z‖^((2*n+e)*2)/((2*n+e) ! : ℝ))*((2*n+e) ! : ℝ) := by
        field_simp
    _ ≤ _ := by gcongr

/-- Signed combination of the Fresnel integrals as a modulated series:
`C(z) + iε S(z) = e^{iεπz²/2} (A(z) - iε B(z))` with `A`, `B` the alternate series. -/
theorem fresnel_signed_alternate (z : ℂ) {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    fresnelCosInt z+ε*I*fresnelSinInt z = exp (ε*I*(π*z^2/2))*
      (fresnelAlternateSeries false z-ε*I*fresnelAlternateSeries true z) := by
  have hε2 : (ε:ℂ)^2 = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hπ : (Real.sqrt π:ℂ)^2 = π := by exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hπ0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [fresnel_signed_erf z hε]
  set ζ := fresnelZetaComplex ε z with hζdef
  have hζ : ζ = Real.sqrt π/2*(1-ε*I)*z := rfl
  have hζ2 : ζ^2 = -(ε*π*I*z^2/2) := by
    rw [hζ, mul_pow, mul_pow, div_pow, hπ, sub_sq, mul_pow, I_sq, hε2]; ring
  set X : ℂ := -(ε*π*I)*z^2 with hX
  set c : ℕ → ℂ := fun n => (-(ε*π*I))^n*z^(2*n+1)/oddProduct n with hc
  set K : ℂ := exp (-(ε*I*(π*z^2/2)))*((1+ε*I)/2) with hK
  have hfull : HasSum c (K*erf ζ) := by
    have h := (hasSum_erf_scaled ζ).mul_left K
    refine h.congr_fun fun n => ?_
    have hE : exp (-(ε*I*(π*z^2/2)))*exp (-ζ^2) = 1 := by
      rw [← Complex.exp_add, hζ2]; ring_nf; simp
    have hz1 : (1+ε*I)/2*(2/Real.sqrt π)*ζ = z := by
      rw [hζ]; field_simp
      rw [show (1+ε*I)*(1-ε*I) = 1 - (ε:ℂ)^2*I^2 by ring, hε2, I_sq]; ring
    have hp : (2:ℂ)^n*ζ^(2*n+1) = ζ*X^n := by
      rw [pow_succ, pow_mul, hX, show -((ε:ℂ)*π*I)*z^2 = 2*ζ^2 by rw [hζ2]; ring, mul_pow]; ring
    have hr : c n = z*X^n/oddProduct n := by
      simp only [hc, hX]; rw [mul_pow, pow_succ, pow_mul]; ring
    rw [hr]
    simp only [hK]
    rw [show 2/(Real.sqrt π:ℂ)*exp (-ζ^2)*(2:ℂ)^n*ζ^(2*n+1)/oddProduct n =
      2/(Real.sqrt π:ℂ)*exp (-ζ^2)*((2:ℂ)^n*ζ^(2*n+1))/oddProduct n by ring, hp]
    linear_combination (-((1+ε*I)/2*(2/Real.sqrt π)*ζ*X^n/oddProduct n))*hE - (X^n/oddProduct n)*hz1
  have hA := (fresnelAlternateSeries_summable false z).hasSum
  have hB := ((fresnelAlternateSeries_summable true z).hasSum).mul_left (-(ε*I))
  have hsplit : HasSum c (fresnelAlternateSeries false z + -(ε*I)*fresnelAlternateSeries true z) := by
    refine HasSum.even_add_odd (f := c) ?_ ?_
    · refine hA.congr_fun fun m => ?_
      simp only [hc, Bool.false_eq_true, ite_false, add_zero]
      rw [pow_mul, show (-((ε:ℂ)*π*I))^2 = -(π^2) by
        rw [neg_sq, mul_pow, mul_pow, hε2, I_sq]; ring, neg_pow, pow_mul]
      congr 2; ring_nf
    · refine hB.congr_fun fun m => ?_
      simp only [hc, ite_true]
      rw [pow_succ, pow_mul, show (-((ε:ℂ)*π*I))^2 = -(π^2) by
        rw [neg_sq, mul_pow, mul_pow, hε2, I_sq]; ring, neg_pow, ← pow_mul]
      rw [show 2*(2*m+1)+1 = 4*m+3 by ring, show 2*m+1 = 2*m+1 from rfl]
      ring
  have heq := hfull.unique hsplit
  have hK0 : exp (ε*I*(π*z^2/2))*exp (-(ε*I*(π*z^2/2))) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [show fresnelAlternateSeries false z - ε*I*fresnelAlternateSeries true z =
    fresnelAlternateSeries false z + -(ε*I)*fresnelAlternateSeries true z by ring, ← heq]
  simp only [hK]
  linear_combination (-((1+ε*I)/2*erf ζ))*hK0

/-- fresnelCosInt alternate series. -/
@[dlmf 7.6.E5]
theorem fresnelCosInt_alternate_series (z : ℂ) :
    fresnelCosInt z=cos (π*z^2/2)*fresnelAlternateSeries false z+sin (π*z^2/2)*fresnelAlternateSeries true z := by
  have h1 := fresnel_signed_alternate z (Or.inl rfl)
  have h2 := fresnel_signed_alternate z (Or.inr rfl)
  push_cast at h1 h2
  rw [Complex.cos, Complex.sin]
  rw [show (-1:ℂ)*I*(π*z^2/2) = -((π:ℂ)*z^2/2)*I by ring] at h2
  rw [show (1:ℂ)*I*(π*z^2/2) = (π:ℂ)*z^2/2*I by ring] at h1
  linear_combination h1/2 + h2/2

/-- fresnelSinInt alternate series. -/
@[dlmf 7.6.E7]
theorem fresnelSinInt_alternate_series (z : ℂ) :
    fresnelSinInt z = -cos (π*z^2/2)*fresnelAlternateSeries true z+sin (π*z^2/2)*fresnelAlternateSeries false z := by
  have h1 := fresnel_signed_alternate z (Or.inl rfl)
  have h2 := fresnel_signed_alternate z (Or.inr rfl)
  push_cast at h1 h2
  rw [Complex.cos, Complex.sin]
  rw [show (-1:ℂ)*I*(π*z^2/2) = -((π:ℂ)*z^2/2)*I by ring] at h2
  rw [show (1:ℂ)*I*(π*z^2/2) = (π:ℂ)*z^2/2*I by ring] at h1
  linear_combination (-I/2)*h1 + (I/2)*h2 + (fresnelSinInt z + (exp ((π:ℂ)*z^2/2*I) +
    exp (-((π:ℂ)*z^2/2)*I))*fresnelAlternateSeries true z/2)*I_sq

/-- erf spherical series. -/
@[dlmf 7.6.E8]
theorem erf_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*(-1 : ℂ)^n*(sphericalI (2*n) (z^2)-sphericalI (2*n+1) (z^2))) (erf z) := by
  sorry

/-- erf chebyshev spherical series. -/
@[dlmf 7.6.E9]
theorem erf_chebyshev_spherical_series {a : ℝ} (ha : -1 ≤ a) (ha1 : a ≤ 1) (z : ℂ) :
    HasSum (fun n : ℕ => 2*z/Real.sqrt π*exp ((1/2-(a : ℂ)^2)*z^2)*(Polynomial.Chebyshev.T ℝ (2*n+1 : ℤ)).eval a*sphericalI n (z^2/2)) (erf (a*z)) := by
  sorry

/-- fresnelCosInt spherical series. -/
@[dlmf 7.6.E10]
theorem fresnelCosInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+0) (π*z^2/2)) (fresnelCosInt z) := by
  sorry

/-- fresnelSinInt spherical series. -/
@[dlmf 7.6.E11]
theorem fresnelSinInt_spherical_series (z : ℂ) :
    HasSum (fun n : ℕ => z*sphericalJ (2*n+1) (π*z^2/2)) (fresnelSinInt z) := by
  sorry

end AAR.Confluent
