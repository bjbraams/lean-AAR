/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import AAR.ErrorFunctions.Relations

/-!
# Inequalities, continued fractions and asymptotic remainders, DLMF §§7.8–7.9 and 7.12

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics AAR.Hypergeometric AAR.DLMF
open scoped Real Topology Nat
namespace AAR.Confluent

/-- Mills ratio in DLMF normalization. -/
@[dlmf 7.8.E1]
def Real.millsRatio (x : ℝ) : ℝ :=
  Real.sqrt π/2*Real.exp (x^2)*(erfc x).re

/-- Real.millsRatio integral. -/
@[dlmf 7.8.E1]
theorem Real.millsRatio_integral (x : ℝ) :
    Real.millsRatio x=Real.exp (x^2)*(∫ t : ℝ in Ioi x, Real.exp (-t^2)) := by
  have hre : (erfc x).re = TauCeti.Real.erfc x := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; simp
  have hd (t : ℝ) : HasDerivAt (fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t)) (Real.exp (-t^2)) t := by
    have hπ : Real.sqrt π ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
    convert ((TauCeti.Real.hasDerivAt_erfc t).const_mul (Real.sqrt π/2)).neg using 1
    field_simp
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => -(Real.sqrt π/2*TauCeti.Real.erfc t))
    (m := 0) (a := x) (hd x).continuousAt.continuousWithinAt (fun t _ => hd t)
    (by simpa using (integrable_exp_neg_mul_sq one_pos).integrableOn)
    (by simpa using (TauCeti.Real.tendsto_erfc_atTop.const_mul (Real.sqrt π/2)).neg)
  rw [Real.millsRatio, hre, hi]
  ring

/-- Real.millsRatio bound 2. -/
@[dlmf 7.8.E2]
theorem Real.millsRatio_bound_2 {x : ℝ} (hx : 0 ≤ x) :
    1/(x+Real.sqrt (x^2+2)) < Real.millsRatio x ∧ Real.millsRatio x ≤ 1/(x+Real.sqrt (x^2+4/π)) := by
  sorry

/-- Real.millsRatio bound 3. -/
@[dlmf 7.8.E3]
theorem Real.millsRatio_bound_3 {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt π/(2*Real.sqrt π*x+2) ≤ Real.millsRatio x ∧ Real.millsRatio x < 1/(x+1) := by
  sorry

/-- Real.millsRatio bound four. -/
@[dlmf 7.8.E4]
theorem Real.millsRatio_bound_four {x : ℝ} (hx : -Real.sqrt 2/2 < x) :
    Real.millsRatio x < 2/(3*x+Real.sqrt (x^2+4)) := by
  sorry

/-- Real.millsRatio rational bounds. -/
@[dlmf 7.8.E5]
theorem Real.millsRatio_rational_bounds {x : ℝ} (hx : 0 ≤ x) :
    x^2/(2*x^2+1) ≤ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ∧ x^2*(2*x^2+5)/(4*x^4+12*x^2+3) ≤ x*Real.millsRatio x ∧ x*Real.millsRatio x < (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) ∧ (2*x^4+9*x^2+4)/(4*x^4+20*x^2+15) < (x^2+1)/(2*x^2+3) := by
  sorry

/-- Real.exp sq integral bound. -/
@[dlmf 7.8.E6]
theorem Real.exp_sq_integral_bound {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (∫ t in (0 : ℝ)..x, Real.exp (a*t^2)) < (2*Real.exp (a*x^2)+a*x^2-2)/(3*a*x) := by
  sorry

/-- Real.dawsonF integral bounds. -/
@[dlmf 7.8.E7]
theorem Real.dawsonF_integral_bounds {x : ℝ} (hx : 0 < x) :
    Real.sinh (x^2)/x < Real.exp (x^2)*Real.dawsonF x ∧ Real.exp (x^2)*Real.dawsonF x < (Real.exp (x^2)-1)/x := by
  sorry

/-- Real.erf exponential bound. -/
@[dlmf 7.8.E8]
theorem Real.erf_exponential_bound {x : ℝ} (hx : 0 < x) :
    (erf x).re < Real.sqrt (1-Real.exp (-4*x^2/π)) := by
  sorry

/-- Monotonicity theorem stated in the prose of DLMF §7.8. -/
theorem Real.dawsonF_normalized_strictAnti  :
    StrictAntiOn (fun x : ℝ => Real.dawsonF x/Real.sqrt (1-Real.exp (-2*x^2))) (Ioi 0) := by
  sorry

/-- erfc continuedFraction one. -/
@[dlmf 7.9.E1]
theorem erfc_continuedFraction_one {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then z else (k : ℂ)/2) (fun k => if Even k then z^2 else 1) (Real.sqrt π*exp (z^2)*erfc z) := by
  sorry

/-- erfc continuedFraction two. -/
@[dlmf 7.9.E2]
theorem erfc_continuedFraction_two {z : ℂ} (hz : 0 < z.re) :
    HasContinuedFraction (fun k => if k=0 then 2*z else -(2*k-1 : ℂ)*(2*k)) (fun k => 2*z^2+4*k+1) (Real.sqrt π*exp (z^2)*erfc z) := by
  sorry

/-- faddeevaW continuedFraction. -/
@[dlmf 7.9.E3]
theorem faddeevaW_continuedFraction {z : ℂ} (hz : 0 < z.im) :
    HasContinuedFraction (fun k => if k=0 then I/Real.sqrt π else -(k : ℂ)/2) (fun _ => z) (faddeevaW z) := by
  sorry

/-- erfc sector asymptotic. -/
@[dlmf 7.12.E1]
theorem erfc_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 3*π/4) :
    HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) erfc ∧ HasAsymptoticExpansion (sector (3*π/4-δ)) (fun n z => exp (-z^2)*z^(-(2*(n : ℂ)+1))) (fun n => -(-1 : ℂ)^n*poch (1/2) n/Real.sqrt π) (fun z => erfc (-z)-2) := by
  sorry

/-- Unnormalized erfc remainder. -/
def erfcAsymptoticRemainder (N : ℕ) (z : ℂ) : ℂ :=
  erfc z-exp (-z^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/z^(2*n+1)

/-- Sector-dependent next-term bounds from DLMF §7.12(i). -/
theorem erfc_remainder_bound {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/2) (N : ℕ) :
    ‖erfcAsymptoticRemainder N z‖ ≤ (if |arg z| ≤ π/4 then 1 else 1/Real.sin (2*|arg z|))*‖exp (-z^2)/Real.sqrt π*poch (1/2) N/z^(2*N+1)‖ := by
  sorry

/-- `(1/2)_n = Γ(n+1/2)/√π`, as a real number. -/
theorem poch_half_eq_Gamma (n : ℕ) :
    poch (1/2) n = ((Real.Gamma (n+1/2)/Real.sqrt π : ℝ) : ℂ) := by
  induction n with
  | zero =>
    rw [poch_zero]; simp only [Nat.cast_zero, zero_add, Real.Gamma_one_half_eq]
    rw [div_self (Real.sqrt_pos.mpr Real.pi_pos).ne']; simp
  | succ n ih =>
    rw [poch_succ, ih]
    have : ((n+1:ℕ):ℝ)+1/2 = ((n:ℝ)+1/2)+1 := by push_cast; ring
    rw [this, Real.Gamma_add_one (by positivity)]
    push_cast; ring

/-- Real Laplace form of `erfc x` for `x > 0`. -/
theorem erfc_ofReal_eq_laplace {x : ℝ} (hx : 0 < x) :
    TauCeti.Real.erfc x = Real.exp (-x^2)/π *
      ∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) := by
  have h := erfc_eq_laplace (z := (x:ℂ)) (by simpa using hx) (by rw [← ofReal_pow, ofReal_re]; positivity)
  have hk : (∫ t : ℝ in Ioi 0, exp (-(x:ℂ)^2*t) * (t:ℂ)^(-1/2:ℂ) * (1+(t:ℂ))^(-1:ℂ)) =
      ((∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have ht : (0:ℝ) < t := ht
    push_cast
    rw [ofReal_cpow ht.le, ofReal_cpow (by linarith)]
    push_cast; ring_nf
  have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
    rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
  rw [hk, herfc] at h
  have := congrArg re h
  rw [ofReal_re] at this
  rw [this, show -(x:ℂ)^2 = ((-x^2:ℝ):ℂ) by push_cast; ring, ← ofReal_exp,
    show ((Real.exp (-x^2):ℂ)/(π:ℂ)) = ((Real.exp (-x^2)/π:ℝ):ℂ) by push_cast; ring,
    ← ofReal_mul, ofReal_re]

/-- Signed real remainder from DLMF §7.12(i). -/
theorem erfc_remainder_sign {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(erfcAsymptoticRemainder N x).re := by
  set r := x^2 with hr
  have hr0 : 0 < r := by positivity
  -- moments
  have hmom (n : ℕ) : (∫ u in Ioi (0:ℝ), u^((n:ℝ)-1/2) * Real.exp (-(r*u))) =
      Real.Gamma (n+1/2) / x^(2*n+1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (n:ℝ)+1/2) (by positivity) hr0
    rw [show (n:ℝ)+1/2-1 = (n:ℝ)-1/2 by ring] at this
    rw [this, Real.div_rpow zero_le_one hr0.le, Real.one_rpow, hr, ← Real.rpow_two,
      ← Real.rpow_mul hx.le, show 2*((n:ℝ)+1/2) = ((2*n+1:ℕ):ℝ) by push_cast; ring,
      Real.rpow_natCast]
    ring
  have hint (n : ℕ) : IntegrableOn (fun u : ℝ => u^((n:ℝ)-1/2) * Real.exp (-(r*u))) (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (n:ℝ)-1/2) (b := r)
      (by have : (0:ℝ) ≤ n := Nat.cast_nonneg n; linarith) one_pos hr0
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioi
    simp [Real.rpow_one, neg_mul]
  set g : ℝ → ℝ := fun u => u^((N:ℝ)-1/2) * Real.exp (-(r*u)) * (1+u)⁻¹ with hg
  have hgint : IntegrableOn g (Ioi 0) := by
    refine (hint N).mono' ?_ ?_
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ioi
      have hu : (0:ℝ) < u := hu
      refine ContinuousAt.continuousWithinAt ?_
      have : 1 + u ≠ 0 := by linarith
      exact ((Real.continuousAt_rpow_const _ _ (Or.inl hu.ne')).mul (by fun_prop)).mul
        ((continuousAt_const.add continuousAt_id).inv₀ this)
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
      have hu : (0:ℝ) < u := hu
      rw [Real.norm_of_nonneg (by positivity)]
      have h1 : (1+u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      have : 0 ≤ u^((N:ℝ)-1/2) * Real.exp (-(r*u)) := by positivity
      simp only [hg]
      nlinarith
  have hgnn : 0 ≤ ∫ u in Ioi (0:ℝ), g u :=
    setIntegral_nonneg measurableSet_Ioi fun u hu => by
      have hu : (0:ℝ) < u := hu; positivity
  -- the kernel decomposition
  have hdec : (∫ u in Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ)) =
      ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) +
        (-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u := by
    have hpt : ∀ u ∈ Ioi (0:ℝ), Real.exp (-(x^2*u)) * u^(-1/2:ℝ) * (1+u)^(-1:ℝ) =
        ∑ n ∈ Finset.range N, (-1:ℝ)^n * (u^((n:ℝ)-1/2) * Real.exp (-(r*u))) + (-1:ℝ)^N * g u := by
      intro u hu
      have hu : (0:ℝ) < u := hu
      have hgeom : (1+u)⁻¹ = ∑ n ∈ Finset.range N, (-u)^n + (-u)^N * (1+u)⁻¹ := by
        have h := geom_sum_mul (-u) N
        have h1 : 1 + u ≠ 0 := by linarith
        have hS : (∑ n ∈ Finset.range N, (-u)^n) = (1 - (-u)^N) * (1+u)⁻¹ := by
          rw [eq_mul_inv_iff_mul_eq₀ h1]; linear_combination (-1)*h
        rw [hS]; ring
      have hpow (n : ℕ) : u^((n:ℝ)-1/2) = u^(-1/2:ℝ) * u^n := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hu]; ring_nf
      rw [Real.rpow_neg_one, hgeom, mul_add, Finset.mul_sum]
      simp only [hg, hpow, hr]
      congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_; rw [neg_pow]; ring
      · rw [neg_pow]; ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_add, integral_finsetSum]
    · congr 1
      · refine Finset.sum_congr rfl fun n _ => ?_
        rw [integral_const_mul, hmom]
      · rw [integral_const_mul]
    · exact fun n _ => (hint n).const_mul _
    · exact integrable_finsetSum _ fun n _ => (hint n).const_mul _
    · exact hgint.const_mul _
  -- the remainder
  have hR : (erfcAsymptoticRemainder N x).re = Real.exp (-x^2)/π * ((-1:ℝ)^N * ∫ u in Ioi (0:ℝ), g u) := by
    have hsum : (exp (-(x:ℂ)^2)/Real.sqrt π*∑ n ∈ Finset.range N, (-1 : ℂ)^n*poch (1/2) n/(x:ℂ)^(2*n+1)) =
        ((Real.exp (-x^2)/π * ∑ n ∈ Finset.range N, (-1:ℝ)^n * (Real.Gamma (n+1/2) / x^(2*n+1)) : ℝ) : ℂ) := by
      simp only [poch_half_eq_Gamma]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      have hp : (Real.sqrt π:ℂ)*Real.sqrt π = π := by exact_mod_cast Real.mul_self_sqrt Real.pi_pos.le
      have hp0 : (Real.sqrt π:ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
      rw [← hp]; field_simp
    have herfc : erfc (x:ℂ) = (TauCeti.Real.erfc x : ℂ) := by
      rw [erfc, erf_ofReal, TauCeti.Real.erfc_def]; push_cast; ring
    rw [erfcAsymptoticRemainder, hsum, herfc, ← ofReal_sub, ofReal_re, erfc_ofReal_eq_laplace hx, hdec]
    ring
  rw [hR, ← mul_assoc, mul_comm ((-1:ℝ)^N), mul_assoc, ← mul_assoc ((-1:ℝ)^N), ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
  have : 0 ≤ Real.exp (-x^2)/π := by positivity
  exact mul_nonneg this hgnn

/-- The n-th auxiliary Fresnel asymptotic term. -/
def fresnelAsymptoticTerm (aux : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  (-1 : ℂ)^n*poch (1/2) (2*n+if aux then 1 else 0)/(π*z*(π*z^2/2)^(2*n+if aux then 1 else 0))

/-- Finite Fresnel auxiliary remainder. -/
@[dlmf 7.12.E4, dlmf 7.12.E5]
def fresnelAsymptoticRemainder (aux : Bool) (N : ℕ) (z : ℂ) : ℂ :=
  (if aux then fresnelAuxGComplex z else fresnelAuxFComplex z)-∑ n ∈ Finset.range N, fresnelAsymptoticTerm aux n z

/-- fresnelAuxFComplex sector asymptotic. -/
@[dlmf 7.12.E2]
theorem fresnelAuxFComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+1))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+0)*(2/π)^(2*n+0)/π) fresnelAuxFComplex := by
  sorry

/-- fresnelAuxFComplex remainder integral. -/
@[dlmf 7.12.E6]
theorem fresnelAuxFComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder false N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+0-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  sorry

/-- fresnelAuxGComplex sector asymptotic. -/
@[dlmf 7.12.E3]
theorem fresnelAuxGComplex_sector_asymptotic {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < π/2) :
    HasAsymptoticExpansion (sector (π/2-δ)) (fun n z => z^(-(4*(n : ℂ)+3))) (fun n => (-1 : ℂ)^n*poch (1/2) (2*n+1)*(2/π)^(2*n+1)/π) fresnelAuxGComplex := by
  sorry

/-- fresnelAuxGComplex remainder integral. -/
@[dlmf 7.12.E7]
theorem fresnelAuxGComplex_remainder_integral {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    fresnelAsymptoticRemainder true N z=(-1 : ℂ)^N/(π*Real.sqrt 2)*(∫ t : ℝ in Ioi 0, exp (-π*z^2*t/2)*(t : ℂ)^(2*N+1-1/2 : ℂ)/((t : ℂ)^2+1)) := by
  sorry

/-- Sector-dependent Fresnel next-term bounds. -/
theorem fresnelAux_remainder_bound (aux : Bool) {z : ℂ} (hz0 : z ≠ 0) (hz : |arg z| < π/4) (N : ℕ) :
    ‖fresnelAsymptoticRemainder aux N z‖ ≤ (if |arg z| ≤ π/8 then 1 else |1/Real.sin (4*arg z)|)*‖fresnelAsymptoticTerm aux N z‖ := by
  sorry

/-- Signed real Fresnel remainder. -/
theorem fresnelAux_remainder_sign (aux : Bool) {x : ℝ} (hx : 0 < x) (N : ℕ) :
    0 ≤ (-1 : ℝ)^N*(fresnelAsymptoticRemainder aux N x).re := by
  sorry

end AAR.Confluent
