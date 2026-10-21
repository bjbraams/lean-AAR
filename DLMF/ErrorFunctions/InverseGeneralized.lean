/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import DLMF.ErrorFunctions.BoundsAsymptotics

/-!
# Generalized and inverse error functions, DLMF §§7.16–7.17

Statement acquisition from NIST DLMF, checked 2026-10-19. Graphical results and
application notes are excluded. Existing Mathlib results are referenced, not reproved.
New theorem statements are initially admitted and are not completed proofs.
-/

@[expose] public noncomputable section
open Complex Filter Set MeasureTheory Asymptotics DLMF.Hypergeometric DLMF
open scoped Real Topology Nat
namespace DLMF.Confluent

/-- Generalized error integral of DLMF §7.16. -/
def Real.generalizedErrorIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (-t^p)

/-- Generalized unscaled Dawson integral of DLMF §7.16. -/
def Real.generalizedDawsonIntegral (p x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..x, Real.exp (t^p)

/-- Change of variable to incomplete Gamma in DLMF §7.16. -/
theorem Real.generalizedErrorIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedErrorIntegral p x : ℂ)=lowerIncGamma (1/p) ((x^p : ℝ) : ℂ)/p := by
  have hxp : 0 < x^p := Real.rpow_pos_of_pos hx p
  -- real change of variables u = t^p
  let G : ℝ → ℝ := fun u => u^(1/p-1)*Real.exp (-u)/p
  have hreal : (∫ t in (0:ℝ)..x, Real.exp (-t^p)) = ∫ u in (0:ℝ)..x^p, G u := by
    rw [intervalIntegral.integral_of_le hx.le, intervalIntegral.integral_of_le hxp.le]
    have h := integral_comp_rpow_Ioi_of_pos (g := (Iic (x^p)).indicator G) hp
    have hR : (∫ y in Ioi 0, (Iic (x^p)).indicator G y) = ∫ u in Ioc 0 (x^p), G u := by
      rw [integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
        Iic_inter_Ioi]
    have hL : (∫ t in Ioi 0, (p * t^(p-1)) • (Iic (x^p)).indicator G (t^p)) =
        ∫ t in Ioc 0 x, Real.exp (-t^p) := by
      rw [← Iic_inter_Ioi, ← Measure.restrict_restrict measurableSet_Iic,
        ← integral_indicator measurableSet_Iic]
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 < t := ht
      by_cases htx : t ≤ x
      · have h1 : t^p ≤ x^p := Real.rpow_le_rpow ht0.le htx hp.le
        rw [indicator_of_mem (show t^p ∈ Iic (x^p) from h1),
          indicator_of_mem (show t ∈ Iic x from htx), smul_eq_mul]
        simp only [G]
        rw [← Real.rpow_mul ht0.le, show p*(1/p-1) = 1-p by field_simp]
        have h2 : t^(p-1)*t^(1-p) = 1 := by
          rw [← Real.rpow_add ht0, show p-1+(1-p) = 0 by ring, Real.rpow_zero]
        calc p*t^(p-1)*(t^(1-p)*Real.exp (-t^p)/p) = (t^(p-1)*t^(1-p))*Real.exp (-t^p) := by
              field_simp
          _ = _ := by rw [h2, one_mul]
      · have h1 : ¬ t^p ≤ x^p := fun h => htx ((Real.rpow_le_rpow_iff ht0.le hx.le hp).mp h)
        rw [indicator_of_notMem (show t^p ∉ Iic (x^p) from h1),
          indicator_of_notMem (show t ∉ Iic x from htx), smul_zero]
    rw [← hL, h, hR]
  have hpc : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [lowerIncGamma_eq_integral (by simp [hp]) hxp, Real.generalizedErrorIntegral, hreal,
    ← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_div]
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun u hu => ?_)
  rw [uIoc_of_le hxp.le] at hu
  simp only [G]
  push_cast
  rw [Complex.ofReal_cpow hu.1.le]
  push_cast
  ring

/-- `(a)_n (a+n) = a (a+1)_n`. -/
theorem poch_mul_add_nat (a : ℂ) (n : ℕ) : poch a n*(a+n) = a*poch (a+1) n := by
  induction n with
  | zero => simp [poch_zero]
  | succ n ih =>
    rw [poch_succ, poch_succ, mul_assoc, ← mul_assoc (poch a n), ih]; push_cast; ring

/-- Termwise integration of `exp(t^p)` on `[0, x]`. -/
theorem hasSum_generalizedDawsonIntegral {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    HasSum (fun n : ℕ => x^(p*n+1)/((p*n+1)*(n ! : ℝ))) (Real.generalizedDawsonIntegral p x) := by
  have hexp (y : ℝ) : HasSum (fun n : ℕ => y^n/(n ! : ℝ)) (Real.exp y) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp y
  have hc : Continuous fun t : ℝ => t^p := Real.continuous_rpow_const hp.le
  have h := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := x)
    (F := fun (n : ℕ) (t : ℝ) => (t^p)^n/(n ! : ℝ)) (f := fun t => Real.exp (t^p))
    (fun n t => (t^p)^n/(n ! : ℝ))
    (fun n => ((hc.pow n).div_const _).aestronglyMeasurable)
    (fun n => Eventually.of_forall fun t ht => by
      rw [uIoc_of_le hx.le] at ht
      have : 0 ≤ (t^p)^n/(n ! : ℝ) := by
        have := Real.rpow_nonneg ht.1.le p; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg this])
    (Eventually.of_forall fun t _ => (hexp _).summable)
    (by
      have : (fun t : ℝ => ∑' n : ℕ, (t^p)^n/(n ! : ℝ)) = fun t => Real.exp (t^p) :=
        funext fun t => (hexp _).tsum_eq
      rw [this]; exact (Real.continuous_exp.comp hc).intervalIntegrable _ _)
    (Eventually.of_forall fun t _ => hexp _)
  refine h.congr_fun fun n => ?_
  rw [intervalIntegral.integral_div]
  have he : ∫ t in (0:ℝ)..x, (t^p)^n = ∫ t in (0:ℝ)..x, t^(p*n) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [uIcc_of_le hx.le] at ht
    rw [Real.rpow_mul ht.1, Real.rpow_natCast]
  rw [he, integral_rpow (Or.inl (by nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)])),
    Real.zero_rpow (by positivity)]
  field_simp
  ring

/-- The negative-argument Gamma formula retains the compensating branch factor. -/
theorem Real.generalizedDawsonIntegral_gamma {p x : ℝ} (hp : 0 < p) (hx : 0 < x) :
    (Real.generalizedDawsonIntegral p x : ℂ)=exp (-π*I/p)/p*lowerIncGamma (1/p) (-(x^p : ℝ)) := by
  set X : ℝ := x^p with hXdef
  have hX : 0 < X := Real.rpow_pos_of_pos hx p
  set a : ℂ := ((1/p:ℝ):ℂ) with ha
  have hpc : (p:ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hxc : (x:ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- the Kummer series
  have hS : HasSum (fun n : ℕ => poch a n/(poch (a+1) n*n !)*(X:ℂ)^n)
      ((Real.generalizedDawsonIntegral p x : ℂ)/x) := by
    have h := (Complex.hasSum_ofReal.mpr (hasSum_generalizedDawsonIntegral hp hx)).div_const (x:ℂ)
    refine h.congr_fun fun n => ?_
    have hna : (a+1) ∉ Set.range (fun k : ℕ => -(k:ℂ)) := by
      rintro ⟨k, hk⟩
      have := congrArg Complex.re hk
      simp [ha] at this
      have : (0:ℝ) < p⁻¹+1 := by positivity
      linarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
    have hp0 : poch (a+1) n ≠ 0 := poch_ne_zero_of_not_neg_nat
      (fun k hk => hna ⟨k, hk.symm⟩) n
    have han : a+n ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp [ha] at this
      have : (0:ℝ) < p⁻¹ := by positivity
      linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    have hpoch : poch a n = a*poch (a+1) n/(a+n) := by
      rw [← poch_mul_add_nat]; field_simp
    rw [hpoch]
    have hxn : ((x^(p*n+1):ℝ):ℂ) = (x:ℂ)*(X:ℂ)^n := by
      rw [Real.rpow_add hx, Real.rpow_one, Real.rpow_mul hx.le, Real.rpow_natCast]; push_cast; ring
    push_cast
    rw [hxn]
    have hf : (n ! : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
    have hpn : (p:ℂ)*n+1 ≠ 0 := by
      intro h0; have := congrArg Complex.re h0; simp at this
      nlinarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
    rw [show a*poch (a+1) n/(a+n)/(poch (a+1) n*n !) = a/((a+n)*n !) by field_simp]
    have hpn' : 1+(p:ℂ)*n ≠ 0 := by rw [add_comm]; exact hpn
    rw [ha]
    push_cast
    field_simp
    ring
  have hM : kummerM a (a+1) X = (Real.generalizedDawsonIntegral p x : ℂ)/x := by
    unfold kummerM; exact hS.tsum_eq
  have hpow : ((-(X:ℂ)))^a = x*exp (π*I*a) := by
    rw [show -(X:ℂ) = ((-X:ℝ):ℂ) by push_cast; ring, ofReal_cpow_of_nonpos (by linarith),
      show -((-X:ℝ):ℂ) = ((X:ℝ):ℂ) by push_cast; ring, ha, ← ofReal_cpow hX.le, one_div,
      hXdef, Real.rpow_rpow_inv hx.le hp.ne']
  have ha0 : a ≠ 0 := by simp [ha, hp.ne']
  rw [lowerIncGamma, show (1/(p:ℂ)) = a by simp [ha], hpow, neg_neg, hM]
  simp only [ha]
  push_cast
  have he' : exp (-(π*I/p))*exp (π*I/p) = 1 := by rw [← Complex.exp_add]; simp
  field_simp
  linear_combination (-(Real.generalizedDawsonIntegral p x:ℂ))*he'

/-- Inverse erf on (-1,1), reusing TauCeti; zero outside that interval. -/
@[dlmf 7.17.E1]
def Real.invErf (x : ℝ) : ℝ :=
  _root_.Real.erfInv x

/-- Inverse erfc on (0,2), with totalization inherited from invErf. -/
@[dlmf 7.17.E1]
def Real.invErfc (x : ℝ) : ℝ :=
  Real.invErf (1-x)

/-- Inverse identity; `Real.erf_erfInv` from TauCeti supplies the real theorem. -/
theorem Real.invErf_spec {x : ℝ} (hx : |x| < 1) :
    (erf (Real.invErf x)).re=x := by
  rw [erf_ofReal]
  simpa [Real.invErf] using _root_.Real.erf_erfInv (abs_lt.mp hx)

/-- Inverse complementary error function identity. -/
theorem Real.invErfc_spec {x : ℝ} (hx : 0 < x) (hx2 : x < 2) :
    (erfc (Real.invErfc x)).re=x := by
  have h : |1-x| < 1 := abs_lt.mpr (by constructor <;> linarith)
  have he := Real.invErf_spec h
  change (erfc (Real.invErf (1-x))).re=x
  change (1-erf (Real.invErf (1-x))).re=x
  simp only [Complex.sub_re, Complex.one_re, he]
  ring

/-- Coefficients of the inverse-erf series from the unnumbered recurrence after 7.17.2. -/
def invErfSeriesCoeff : ℕ → ℝ
  | 0 => 1
  | m+1 => (∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*
      invErfSeriesCoeff (m-n)*invErfSeriesCoeff (m-(m-n)))/(2*m+3)
termination_by m => m

/-- invErfSeriesCoeff initial. -/
@[dlmf 7.17.E2]
theorem invErfSeriesCoeff_initial  :
    ∀ n < 4, invErfSeriesCoeff n=([1,1/3,7/30,127/630] : List ℝ)[n]! := by
  intro n hn
  interval_cases n <;> norm_num [invErfSeriesCoeff, Finset.sum_range_succ]

/-- hasSum invErf. -/
@[dlmf 7.17.E2]
theorem hasSum_invErf {x : ℝ} (hx : |x| < 1) :
    HasSum (fun m : ℕ => invErfSeriesCoeff m*(Real.sqrt π*x/2)^(2*m+1)) (Real.invErf x) := by
  sorry

/-- The unnumbered inverse-erf coefficient recurrence. -/
theorem invErfSeriesCoeff_recurrence (m : ℕ) :
    invErfSeriesCoeff (m+1)=(∑ n ∈ Finset.range (m+1), (2*n+1 : ℝ)/(m-n+1 : ℕ)*invErfSeriesCoeff n*invErfSeriesCoeff (m-n))/(2*m+3) := by
  rw [invErfSeriesCoeff]
  congr 1
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [Nat.sub_sub_self (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))]
  ring

/-- Small-argument inverse-erfc variable u. -/
@[dlmf 7.17.E5]
def invErfcAsymptoticU (x : ℝ) : ℝ :=
  -2/Real.log (π*x^2*Real.log (1/x))

/-- Small-argument inverse-erfc logarithmic variable v. -/
@[dlmf 7.17.E6]
def invErfcAsymptoticV (x : ℝ) : ℝ :=
  Real.log (Real.log (1/x))-2+Real.log π

/-- All-order expansion with polynomial logarithmic coefficients. -/
@[dlmf 7.17.E3, dlmf 7.17.E4]
theorem invErfc_asymptotic  :
    ∃ c : ℕ → Polynomial ℝ, (∀ v : ℝ, (c 0).eval v=1 ∧ (c 1).eval v=0 ∧ (c 2).eval v=v/8 ∧ (c 3).eval v = -(v^2+6*v-6)/32 ∧ (c 4).eval v=(4*v^3+27*v^2+108*v-300)/384) ∧ ∀ N : ℕ, IsBigO (𝓝[>] (0 : ℝ)) (fun x => Real.invErfc x-∑ n ∈ Finset.range N, (c n).eval (invErfcAsymptoticV x)*(invErfcAsymptoticU x)^((n : ℝ)-1/2)) (fun x => (invErfcAsymptoticU x)^((N : ℝ)-1/2)*(1+|invErfcAsymptoticV x|)^N) := by
  sorry

end DLMF.Confluent
