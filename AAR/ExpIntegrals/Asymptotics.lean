/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ExpIntegrals.Expansions

/-!
# Sectorial asymptotic expansions and explicit remainders, DLMF §6.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- The n-th auxiliary-function asymptotic term; aux=true means g. -/
def expIntAsymptoticTerm (aux : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^n * ((2*n + if aux then 1 else 0).factorial : ℂ) / z^(2*n + if aux then 2 else 1)

/-- Finite auxiliary-function remainder. -/
@[dlmf 6.12.E5, dlmf 6.12.E6]
def expIntAsymptoticRemainder (aux : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  (if aux then expIntAuxG z else expIntAuxF z) - ∑ n ∈ Finset.range N, expIntAsymptoticTerm aux n z

/-- A convergent improper integral of an integrable function is its Lebesgue integral. -/
theorem _root_.AAR.DLMF.HasIntegralAtTop.eq_integral_Ioi {f : ℝ → ℂ} {a : ℝ} {v : ℂ}
    (h : HasIntegralAtTop f a v) (hi : IntegrableOn f (Ioi a)) : ∫ t in Ioi a, f t = v :=
  tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi a hi tendsto_id) h

/-- Laplace transforms of natural powers, `∫₀^∞ e^{-zt} t^m dt = m!/z^{m+1}`. -/
theorem laplace_nat_pow {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(t:ℂ)^m) (Ioi 0) ∧
    ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^m = m.factorial/z^(m+1) := by
  have ha : 0 < ((m:ℂ)+1).re := by simp; positivity
  have he : ∀ t : ℝ, exp (-z*t)*(t:ℂ)^((m:ℂ)+1-1)*(1+(t:ℂ))^(((m:ℂ)+1+1)-((m:ℂ)+1)-1) =
      exp (-z*t)*(t:ℂ)^m := fun t => by
    rw [show (m:ℂ)+1-1 = (m:ℕ) by ring, cpow_natCast, show (m:ℂ)+1+1-((m:ℂ)+1)-1 = 0 by ring, cpow_zero, mul_one]
  constructor
  · have := kummerU_laplace_integrable (b := (m:ℂ)+1+1) ha hz
    simpa only [he] using this
  · have h1 := kummerU_laplace_shift_one ha hz
    rw [kummerU_shift_one _ (Or.inl hz)] at h1
    simp only [he] at h1
    have hG : Gamma ((m:ℂ)+1) = m.factorial := by exact_mod_cast Complex.Gamma_nat_eq_factorial m
    rw [hG] at h1
    have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
    have hz0 : z ≠ 0 := fun h => by simp [h] at hz
    rw [show -((m:ℂ)+1) = -((m+1:ℕ):ℂ) by push_cast; ring, cpow_neg, cpow_natCast] at h1
    field_simp at h1 ⊢
    linear_combination -h1

/-- `|t²+1| ≥ 1` on the real line. -/
lemma norm_ofReal_sq_add_one_ge (t : ℝ) : 1 ≤ ‖(t:ℂ)^2+1‖ := by
  rw [show ((t:ℂ)^2+1) = ((t^2+1:ℝ):ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]
  nlinarith [sq_nonneg t]

/-- `t²+1 ≠ 0` on the real line. -/
lemma ofReal_sq_add_one_ne (t : ℝ) : (t:ℂ)^2+1 ≠ 0 := fun h => by
  have := norm_ofReal_sq_add_one_ge t; rw [h, norm_zero] at this; linarith

/-- Integrability of the Laplace rational kernels `e^{-zt} t^m/(t²+1)`. -/
theorem integrableOn_laplace_rational {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    IntegrableOn (fun t : ℝ => exp (-z*t)*(t:ℂ)^m/((t:ℂ)^2+1)) (Ioi 0) := by
  refine ((laplace_nat_pow hz m).1.norm).mono' ?_ (Eventually.of_forall fun t => ?_)
  · exact (Continuous.div (by fun_prop) (by fun_prop) ofReal_sq_add_one_ne).aestronglyMeasurable
  · rw [norm_div]
    exact div_le_self (norm_nonneg _) (norm_ofReal_sq_add_one_ge t)

/-- The reduction `t^{m+2}/(t²+1) = t^m - t^m/(t²+1)` under the Laplace integral. -/
theorem laplace_rational_succ {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^(m+2)/((t:ℂ)^2+1) =
      m.factorial/z^(m+1) - ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^m/((t:ℂ)^2+1) := by
  rw [← (laplace_nat_pow hz m).2, ← integral_sub (laplace_nat_pow hz m).1 (integrableOn_laplace_rational hz m)]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  have := ofReal_sq_add_one_ne t
  field_simp
  ring

/-- Real Laplace representations of `f` and `g` for `re z > 0`. -/
theorem expIntAux_laplace_Ioi {z : ℂ} (hz : 0 < z.re) :
    expIntAuxF z = ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^0/((t:ℂ)^2+1) ∧
    expIntAuxG z = ∫ t : ℝ in Ioi 0, exp (-z*t)*(t:ℂ)^1/((t:ℂ)^2+1) := by
  have hz0 : z ≠ 0 := fun h => by simp [h] at hz
  obtain ⟨h1, h2⟩ := expIntAux_laplace_hasIntegralAtTop hz0 hz.le
  constructor
  · rw [← (h1.congr fun t _ => by simp).eq_integral_Ioi (integrableOn_laplace_rational hz 0)]
  · rw [← (h2.congr fun t _ => by ring).eq_integral_Ioi (integrableOn_laplace_rational hz 1)]

/-- The auxiliary-function remainders as Laplace integrals, for both `f` and `g`. -/
theorem expIntAux_remainder_integral_general (aux : Bool) {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder aux N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0,
      exp (-z*t)*(t : ℂ)^(2*N+if aux then 1 else 0)/((t : ℂ)^2+1) := by
  induction N with
  | zero =>
    simp only [expIntAsymptoticRemainder, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      one_mul, mul_zero, zero_add]
    cases aux
    · simpa using (expIntAux_laplace_Ioi hz).1
    · simpa using (expIntAux_laplace_Ioi hz).2
  | succ N ih =>
    have hs := laplace_rational_succ hz (2*N+if aux then 1 else 0)
    rw [show 2*N+(if aux = true then 1 else 0)+2 = 2*(N+1)+(if aux = true then 1 else 0) by ring] at hs
    rw [hs]
    simp only [expIntAsymptoticRemainder, Finset.sum_range_succ] at ih ⊢
    rw [← sub_sub, ih, expIntAsymptoticTerm]
    have : (2*N + if aux = true then 2 else 1) = 2*N+(if aux = true then 1 else 0)+1 := by
      cases aux <;> simp
    rw [this, pow_succ]
    ring


/-- expIntE1 logSector asymptotic. -/
@[dlmf 6.12.E1]
theorem expIntE1_logSector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/2) :
    HasAsymptoticExpansion (logSector (3*π/2-δ)) (fun n w => exp (-exp w-(n+1 : ℂ)*w)) (fun n => (-1 : ℂ)^n*n.factorial) expIntE1OnLog := by
  sorry

/-- expIntEi asymptotic. -/
@[dlmf 6.12.E2]
theorem expIntEi_asymptotic  :
    HasAsymptoticExpansion atTop (fun n (x : ℝ) => Real.exp x / x^(n+1)) (fun n => (n.factorial : ℝ)) Real.expIntEi := by
  sorry

/-- expIntAuxF sector asymptotic. -/
@[dlmf 6.12.E3]
theorem expIntAuxF_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun n z => z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*((2*n+0).factorial : ℂ)) expIntAuxF := by
  sorry

/-- expIntAuxF remainder integral. -/
@[dlmf 6.12.E7]
theorem expIntAuxF_remainder_integral {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder false N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+0)/((t : ℂ)^2+1) := by
  simpa using expIntAux_remainder_integral_general false hz N

/-- expIntAuxG sector asymptotic. -/
@[dlmf 6.12.E4]
theorem expIntAuxG_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π) :
    HasAsymptoticExpansion (sector (π-δ)) (fun n z => z^(-(2*(n : ℂ)+2))) (fun n => (-1 : ℂ)^n*((2*n+1).factorial : ℂ)) expIntAuxG := by
  sorry

/-- expIntAuxG remainder integral. -/
@[dlmf 6.12.E8]
theorem expIntAuxG_remainder_integral {z : ℂ} (hz : 0 < z.re) (N : ℕ) :
    expIntAsymptoticRemainder true N z = (-1 : ℂ)^N * ∫ t : ℝ in Ioi 0, exp (-z*t)*(t : ℂ)^(2*N+1)/((t : ℂ)^2+1) := by
  simpa using expIntAux_remainder_integral_general true hz N

/-- First omitted term and csc multiplier from DLMF §6.12(i). -/
theorem expIntE1_remainder_bound {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π) (N : ℕ) :
    ‖genExpIntE 1 z - exp (-z)*∑ n ∈ Finset.range N, (-1 : ℂ)^n*(n.factorial : ℂ)/z^(n+1)‖ ≤ (if |arg z| ≤ π/2 then 1 else 1/Real.sin |arg z|) * ‖exp (-z)*(N.factorial : ℂ)/z^(N+1)‖ := by
  sorry

/-- The tails `e^{-t}/t^m` are integrable on every right half-line with positive endpoint. -/
theorem integrableOn_exp_neg_div_pow {x : ℝ} (hx : 0 < x) (m : ℕ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t)/t^m) (Ioi x) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi x one_pos).div_const (x^m)) ?_ ?_
  · exact (ContinuousOn.div (by fun_prop) (by fun_prop)
      fun t ht => pow_ne_zero _ (lt_trans hx ht).ne').aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hx ht
    rw [Real.norm_eq_abs, abs_of_pos (div_pos (Real.exp_pos _) (pow_pos ht0 m)), neg_one_mul]
    exact div_le_div_of_nonneg_left (Real.exp_pos _).le (pow_pos hx m)
      (pow_le_pow_left₀ hx.le (le_of_lt ht) m)

/-- One integration by parts in the `E₁` tail. -/
theorem integral_exp_neg_div_pow_succ {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (∫ t in Ioi x, Real.exp (-t)/t^(k+1)) =
      Real.exp (-x)/x^(k+1) - (k+1)*∫ t in Ioi x, Real.exp (-t)/t^(k+2) := by
  have hd : ∀ t : ℝ, 0 < t → HasDerivAt (fun t => -(Real.exp (-t)/t^(k+1)))
      (Real.exp (-t)/t^(k+1) + (k+1)*(Real.exp (-t)/t^(k+2))) t := by
    intro t ht
    have ht0 : t ≠ 0 := ht.ne'
    have h := (((hasDerivAt_neg t).exp).div (hasDerivAt_pow (k+1) t) (pow_ne_zero _ ht0)).neg
    convert h using 1
    field_simp
    push_cast
    ring
  have hlim : Tendsto (fun t => -(Real.exp (-t)/t^(k+1))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.exp (-t)/t^(k+1)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_neg_atTop_nhds_zero).div_atTop
        (tendsto_pow_atTop (Nat.succ_ne_zero k))
      exact this
    simpa using h1.neg
  have hi1 := integrableOn_exp_neg_div_pow hx (k+1)
  have hi2 := (integrableOn_exp_neg_div_pow hx (k+2)).const_mul ((k:ℝ)+1)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (hd x hx).continuousAt.continuousWithinAt
    (fun t ht => hd t (lt_trans hx ht)) (hi1.add hi2) hlim
  rw [integral_add hi1 hi2, integral_const_mul] at h
  linear_combination h

/-- Signed real remainder in DLMF §6.12(i). -/
theorem expIntE1_remainder_sign {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N * ((genExpIntE 1 x).re - Real.exp (-x)*∑ n ∈ Finset.range N, (-1 : ℝ)^n*(n.factorial : ℝ)/x^(n+1)) := by
  have hE : (genExpIntE 1 x).re = ∫ t in Ioi x, Real.exp (-t)/t^(0+1) := by
    rw [genExpIntE_one_eq_integral hx, Complex.ofReal_re]
    simp
  have key : ∀ N : ℕ, (genExpIntE 1 x).re - Real.exp (-x)*∑ n ∈ Finset.range N,
      (-1 : ℝ)^n*(n.factorial : ℝ)/x^(n+1) =
      (-1:ℝ)^N*N.factorial*∫ t in Ioi x, Real.exp (-t)/t^(N+1) := by
    intro N
    induction N with
    | zero => simp [hE]
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ← sub_sub, ih, integral_exp_neg_div_pow_succ hx N,
        Nat.factorial_succ]
      push_cast
      ring
  have h1 : (-1:ℝ)^N*(-1)^N = 1 := by rw [← pow_add, ← two_mul, pow_mul]; simp
  rw [key, ← mul_assoc, ← mul_assoc, h1, one_mul]
  refine mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Ioi fun t ht => ?_)
  exact div_nonneg (Real.exp_pos _).le (pow_nonneg (lt_trans hx ht).le _)

/-- The χ-dependent Ei remainder estimate in DLMF §6.12(i). -/
theorem expIntEi_remainder_bound {x : ℝ} (hx : 0 < x) (N : ℕ) :
    |Real.expIntEi x - Real.exp x*∑ n ∈ Finset.range N, (n.factorial : ℝ)/x^(n+1)| ≤ (1+Real.sqrt π*Real.Gamma (1+(N+1 : ℝ)/2)/Real.Gamma (1/2+(N+1 : ℝ)/2))*Real.exp x*(N.factorial : ℝ)/x^(N+1) := by
  sorry

/-- First omitted term and csc multiplier in DLMF §6.12(ii). -/
theorem expIntAux_remainder_bound (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (N : ℕ) :
    ‖expIntAsymptoticRemainder aux N z‖ ≤ (if |arg z| ≤ π/4 then 1 else 1/Real.sin (2*|arg z|)) * ‖expIntAsymptoticTerm aux N z‖ := by
  sorry

/-- Signed real auxiliary-function remainder. -/
theorem expIntAux_remainder_sign (aux : Bool) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (expIntAsymptoticRemainder aux N x).re * (expIntAsymptoticTerm aux N x).re := by
  set m := 2*N+if aux then 1 else 0
  have hr := expIntAux_remainder_integral_general aux (z := x) (by simpa using hx) N
  have hI : (∫ t : ℝ in Ioi 0, exp (-(x:ℂ)*t)*(t : ℂ)^m/((t : ℂ)^2+1)) =
      ((∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    push_cast; rfl
  have hpos : 0 ≤ ∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => by
      have : 0 < t := ht
      positivity
  rw [hr, hI, expIntAsymptoticTerm]
  have h1 : ((-1:ℂ)^N*((∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) : ℝ) : ℂ)).re =
      (-1:ℝ)^N*∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1) := by
    rw [show (-1:ℂ)^N = (((-1:ℝ)^N : ℝ) : ℂ) by push_cast; rfl, ← ofReal_mul, ofReal_re]
  have h2 : ((-1 : ℂ)^N * ((2*N + if aux then 1 else 0).factorial : ℂ) / (x:ℂ)^(2*N + if aux then 2 else 1)).re =
      (-1:ℝ)^N * ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) := by
    rw [show (-1 : ℂ)^N * ((2*N + if aux then 1 else 0).factorial : ℂ) / (x:ℂ)^(2*N + if aux then 2 else 1) =
      (((-1:ℝ)^N * ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) : ℝ) : ℂ) by
      push_cast; rfl, ofReal_re]
  rw [h1, h2]
  have : 0 ≤ ((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1) := by positivity
  have e : (-1:ℝ)^N*(-1:ℝ)^N = 1 := by rw [← mul_pow]; simp
  calc 0 ≤ (∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1)) *
        (((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1)) := mul_nonneg hpos this
    _ = _ := by rw [mul_div_assoc]; linear_combination (-(∫ t : ℝ in Ioi 0, Real.exp (-x*t)*t^m/(t^2+1)) *
        (((2*N + if aux then 1 else 0).factorial : ℝ) / x^(2*N + if aux then 2 else 1)))*e

end AAR.Confluent
